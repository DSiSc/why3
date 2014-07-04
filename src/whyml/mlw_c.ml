(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(**
   Implementation details:
    * All values are boxed where « typename void* value; »
    * Exceptions handled with a monadic method: all functions which can return
      an exception will have a last parameter « struct Exn *exn » where Exn is
      « struct Exn {
          const *name;
          value args[];
        };
      »
    * Variants are encoded like:
      « struct Variant {
          int key;
          value args[];
        };
      »
    * Records can be encoded with C structs
    * We'll use the Boehm GC
*)

open Format
open Pp

open Stdlib
open Number
open Ident
open Ty
open Term
open Decl
open Theory
open Printer

module Module = Mlw_c_module

(* TODO: Remove this hack *)
let hack_fmt = ref None

let clean_fname fname =
  let fname = Filename.basename fname in
  (try Filename.chop_extension fname with _ -> fname)

let modulename ?(separator="__") ?fname path t =
  let fname = match fname, path with
    | Some fname, _ -> clean_fname fname
    | None, [] -> "why3"
    | None, _ -> String.concat separator path
  in
  fname ^ separator ^ t

let extract_filename ?fname th =
  (modulename ?fname th.th_path th.th_name.Ident.id_string) ^ ".c"

type info = {
  info_syn: syntax_map;
  converters: syntax_map;
  current_theory: Theory.theory;
  current_module: Mlw_module.modul option;
  th_known_map: Decl.known_map;
  mo_known_map: Mlw_decl.known_map;
  fname: string option;
}

type value =
  | Value of Module.value
  | Env of int

let is_constructor info ls =
  (* eprintf "is_constructor: ls=%s@." ls.ls_name.id_string; *)
  match Mid.find_opt ls.ls_name info.th_known_map with
    | Some { d_node = Ddata dl } ->
        let constr (_,csl) = List.exists (fun (cs,_) -> ls_equal cs ls) csl in
        List.exists constr dl
    | _ -> false

let get_record info ls =
  match Mid.find_opt ls.ls_name info.th_known_map with
    | Some { d_node = Ddata dl } ->
        let rec lookup = function
        | [] -> []
        | (_, [cs, pjl]) :: _ when ls_equal cs ls ->
          (try List.map Opt.get pjl with _ -> [])
        | _ :: dl -> lookup dl
        in
        lookup dl
    | Some _ | None ->
        []

let c_keywords = []

let iprinter =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer c_keywords ~sanitizer:isanitize

let get_qident ?(separator="__") info id =
  try
    let lp, t, p =
      try Mlw_module.restore_path id
      with Not_found -> Theory.restore_path id in
    let s = String.concat separator p in
    let s = Ident.sanitizer char_to_alpha char_to_alnumus s in
    let fname = if lp = [] then info.fname else None in
    let m = modulename ~separator ?fname lp t in
    Module.value_of_string (sprintf "%s%s%s" m separator s)
  with Not_found ->
    Module.value_of_string (id_unique iprinter id)

let get_ls info ls = get_qident info ls.ls_name
let get_ts info ts = get_qident info ts.ts_name

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let has_syntax info id = Mid.mem id info.info_syn

let has_syntax_or_nothing info id =
  if not (has_syntax info id) then
    assert false

let filter_ghost ls def al =
  let flt fd arg = if fd.Mlw_expr.fd_ghost then def else arg in
  try List.map2 flt (Mlw_expr.restore_pl ls).Mlw_expr.pl_args al
  with Not_found -> al

let print_pdata_decl info (ts, csl) =
  let get_field x = x.ls_name.id_string in
  match csl with
    | [cs, _] ->
        let pjl = get_record info cs in
        if pjl <> [] then
          Module.define_record (get_ts info ts) (List.map get_field pjl)
    | _ ->
        ()

let print_const = function
  | ConstInt c ->
      (* Use GMP:
         let f () =
           let x = 1 in
           x
         <=>
         void *M_f(void *, void * ) {
           mpz_t *__fresh_var; (* WHAT ABOUT THE GC *)
           mpz_init(__fresh_var);
           mpz_set_si(__fresh_var, 1);
           void *x = (void* )&__fresh_var; (* PROBLEM *)
           return x;
         }
      *)
      assert false
  | ConstReal _ ->
      assert false

let print_if f builder (e,t1,t2) =
  let e = f e builder in
  let res = Module.create_value "NULL" builder in
  Module.append_block
    (sprintf "if(%s == __True)" (Module.string_of_value e))
    (fun builder ->
       let v = f t1 builder in
       Module.append_expr (sprintf "%s = %s" (Module.string_of_value res) (Module.string_of_value v)) builder
    )
    builder;
  Module.append_block
    "else"
    (fun builder ->
       let v = f t2 builder in
       Module.append_expr (sprintf "%s = %s" (Module.string_of_value res) (Module.string_of_value v)) builder
    )
    builder;
  res

let get_value info id gamma builder =
  match Mid.find_opt id gamma with
  | None ->
      get_qident info id
  | Some v ->
      begin match v with
      | Value v ->
          v
      | Env i ->
          Module.create_value (sprintf "Env__0[%d]" i) builder
      end

let fold_env env gamma builder =
  let aux id x (index, gamma) = match x with
    | Value v ->
        Module.append_expr (sprintf "%s[%d] = %s" (Module.string_of_value env) index (Module.string_of_value v)) builder;
        (succ index, Mid.add id (Env index) gamma)
    | Env i ->
        Module.append_expr (sprintf "%s[%d] = Env__0[%d]" (Module.string_of_value env) index i) builder;
        (succ index, Mid.add id (Env index) gamma)
  in
  snd (Mid.fold aux gamma (0, Mid.empty))

let bool_not b =
  Module.create_value (sprintf "((variant *)(%s)->key) ? __False : __True" (Module.string_of_value b))

let singleton_opt = function
  | [x] -> Some x
  | [] | _::_ -> None

let get_record_name info = function
  | Some {ty_node = Tyapp (ty, _); _} ->
      get_ts info ty
  | Some {ty_node = Tyvar _; _} ->
      assert false
  | None ->
      assert false

let rec simple_app fs info gamma builder tl =
  let rec aux f = function
    | [] ->
        f
    | x::xs ->
        let closure = Module.cast_to_closure ~raises:false f builder in
        let v = print_term info gamma x builder in
        let f = Module.create_value (sprintf "(%s->f)(%s, %s->env)" (Module.string_of_value closure) (Module.string_of_value v) (Module.string_of_value closure)) builder in
        aux f xs
  in
  aux (get_value info fs.ls_name gamma builder) tl

and print_variant_creation info gamma ~ls ~tl ~pjl builder =
  let tl = List.map (fun x -> print_term info gamma x builder) tl in
  let v = Module.malloc_env (List.length tl) builder in
  Lists.iteri (fun i x -> Module.append_expr (sprintf "%s[%d] = %s" (Module.string_of_value v) i (Module.string_of_value x)) builder) tl;
  let variant = Module.malloc_variant builder in
  Module.append_expr (sprintf "%s->key = %d" (Module.string_of_value variant) ls.ls_constr) builder;
  Module.append_expr (sprintf "%s->val = %s" (Module.string_of_value variant) (Module.string_of_value v)) builder;
  variant

and print_record_creation info gamma ~ls ~tl ~pjl builder =
  let tl = List.map (fun x -> print_term info gamma x builder) tl in
  let v = Module.malloc_record (get_record_name info ls.ls_value) builder in
  let aux (ls, t) =
    Module.append_expr (sprintf "%s->%s = %s" (Module.string_of_value v) ls.ls_name.id_string (Module.string_of_value t)) builder;
  in
  List.iter aux (List.combine pjl tl);
  v

and print_record_access info gamma ~t1 ~ls builder =
  let t1 = print_term info gamma t1 builder in
  let t1 = Module.cast_to_record ~st:(get_record_name info (singleton_opt ls.ls_args)) t1 builder in
  Module.create_value (sprintf "%s->%s" (Module.string_of_value t1) ls.ls_name.id_string) builder

and print_app ls info gamma builder tl =
  let isconstr = is_constructor info ls in
  let is_field (_, csl) = match csl with
    | [_, pjl] ->
        let is_ls = function None -> false | Some ls' -> ls_equal ls ls' in
        List.for_all ((<>) None) pjl && List.exists is_ls pjl
    | _ -> false in
  let isfield = match Mid.find_opt ls.ls_name info.th_known_map with
    | Some { d_node = Ddata dl } -> not isconstr && List.exists is_field dl
    | _ -> false
  in
  match tl with
  | [] ->
      get_value info ls.ls_name gamma builder
  | tl when isconstr ->
      let tl = filter_ghost ls Mlw_expr.t_void tl in
      let pjl = get_record info ls in
      if pjl = [] then
        print_variant_creation info gamma ~ls ~tl ~pjl builder
      else
        print_record_creation info gamma ~ls ~tl ~pjl builder
  | [t1] when isfield ->
      print_record_access info gamma ~t1 ~ls builder
  | tl ->
      simple_app ls info gamma builder tl

and print_term info gamma t builder = match t.t_node with
  | Tvar v ->
      get_value info v.vs_name gamma builder
  | Tconst c ->
      print_const c
  | Tapp (fs, tl) ->
      print_app fs info gamma builder tl
  | Tif (e, t1, t2) ->
      print_if (print_term info gamma) builder (e, t1, t2)
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      let t1 = print_term info gamma t1 builder in
      let gamma = Mid.add v.vs_name (Value t1) gamma in
      print_term info gamma t2 builder
  | Tcase (t1,bl) ->
      assert false
  | Teps _
  | Tquant _ ->
      assert false
  | Ttrue ->
      Module.create_value "__True" builder
  | Tfalse ->
      Module.create_value "__False" builder
  | Tbinop (Timplies,f1,f2) ->
      let f1 = print_term info gamma f1 builder in
      let res = bool_not f1 builder in
      Module.append_block
        (sprintf "if(%s == __True)" (Module.string_of_value f1))
        (fun builder ->
           let v = print_term info gamma f2 builder in
           Module.append_expr (sprintf "%s = %s" (Module.string_of_value res) (Module.string_of_value v)) builder
        )
        builder;
      res
  | Tbinop (Tand,f1,f2) ->
      let f1 = print_term info gamma f1 builder in
      let res = Module.create_value (Module.string_of_value f1) builder in
      Module.append_block
        (sprintf "if(%s == __True)" (Module.string_of_value f1))
        (fun builder ->
           let v = print_term info gamma f2 builder in
           Module.append_expr (sprintf "%s = %s" (Module.string_of_value res) (Module.string_of_value v)) builder
        )
        builder;
      res
  | Tbinop (Tor,f1,f2) ->
      let f1 = print_term info gamma f1 builder in
      let res = Module.create_value (Module.string_of_value f1) builder in
      Module.append_block
        (sprintf "if(%s == __False)" (Module.string_of_value f1))
        (fun builder ->
           let v = print_term info gamma f2 builder in
           Module.append_expr (sprintf "%s = %s" (Module.string_of_value res) (Module.string_of_value v)) builder
        )
        builder;
      res
  | Tbinop (Tiff,f1,f2) ->
      let f1 = print_term info gamma f1 builder in
      let f2 = print_term info gamma f2 builder in
      Module.create_value (sprintf "%s == %s" (Module.string_of_value f1) (Module.string_of_value f2)) builder
  | Tnot f ->
      let v = print_term info gamma f builder in
      bool_not v builder

let print_logic_decl info gamma builder (ls, ld) =
  if has_syntax info ls.ls_name then
    (* TODO *)
    ()
  else begin
    let vl,e = open_ls_defn ld in
    let store = get_ls info ls in
    Module.define_global store;
    let rec aux gamma builder = function
      | [] ->
          print_term info gamma e builder
      | arg::xs ->
          let closure = Module.malloc_closure ~raises:false builder in
          let gamma = Mid.add ls.ls_name (Value closure) gamma in
          let env = Module.malloc_env (Mid.cardinal gamma) builder in
          let gamma = fold_env env gamma builder in
          let lambda =
            Module.create_lambda
              ~raises:false
              (fun ~raise_expr builder ->
                 let gamma = Mid.add arg.vs_name (Value (Module.value_of_string "Param__0")) gamma in
                 aux gamma builder xs
              )
          in
          Module.append_expr (sprintf "%s->f = %s" (Module.string_of_value closure) (Module.string_of_value lambda)) builder;
          Module.append_expr (sprintf "%s->env = %s" (Module.string_of_value closure) (Module.string_of_value env)) builder;
          closure
    in
    let v = aux gamma builder vl in
    Module.append_expr (sprintf "%s = %s" (Module.string_of_value store) (Module.string_of_value v)) builder;
  end

(** Logic Declarations *)

(* TODO: Think that logical functions are shadowed by program functions *)

let logic_decl info builder d = match d.d_node with
  | Dtype _ ->
      ()
  | Ddata tl ->
      List.iter (print_pdata_decl info) tl;
  | Decl.Dparam ls ->
      assert false
  | Dlogic ll ->
      List.iter (print_logic_decl info Mid.empty builder) ll;
  | Dind (s, il) ->
      assert false
  | Dprop (_pk, _pr, _) ->
      assert false

let logic_decl info builder td = match td.td_node with
  | Decl d ->
      begin match Mlw_extract.get_exec_decl info.info_syn d with
      | Some d ->
          let union = Sid.union d.d_syms d.d_news in
          let inter = Mid.set_inter union info.mo_known_map in
          if Sid.is_empty inter then logic_decl info builder d
      | None ->
          ()
      end
  | Use _ | Clone _ | Meta _ ->
      ()

(** Theories *)

let extract_theory drv ?old ?fname fmt th =
  hack_fmt := Some fmt;
  ignore (old); ignore (fname);
  let info = {
    info_syn = drv.Mlw_driver.drv_syntax;
    converters = drv.Mlw_driver.drv_converter;
    current_theory = th;
    current_module = None;
    th_known_map = th.th_known;
    mo_known_map = Mid.empty;
    fname = Opt.map clean_fname fname; } in
  let builder = Module.init_builder in
  List.iter (logic_decl info builder) th.th_decls

(** Programs *)

open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl
open Mlw_module

let get_its info ts = get_ts info ts.its_ts
let get_pv info pv =
  if pv.pv_ghost then
    Module.unit_value
  else
    get_qident info pv.pv_vs.vs_name
let get_ps info ps =
  if ps.ps_ghost then
    Module.unit_value
  else
    get_qident info ps.ps_name
let get_lv info = function
  | LetV pv -> get_pv info pv
  | LetA ps -> get_ps info ps

let get_id_from_let = function
  | LetV pv -> pv.pv_vs.vs_name
  | LetA ps -> ps.ps_name

let get_xs ?separator info xs = get_qident ?separator info xs.xs_name

let rec print_expr info ~raise_expr gamma e builder =
  if e.e_ghost then
    Module.unit_value
  else match e.e_node with
  | Elogic t ->
      print_term info gamma t builder
  | Evalue v ->
      get_value info v.pv_vs.vs_name gamma builder
  | Earrow a ->
      get_value info a.ps_name gamma builder
  | Eapp (e,v,spec) ->
      let e = print_expr info ~raise_expr gamma e builder in
      let v = get_value info v.pv_vs.vs_name gamma builder in
      let raises = not (Sexn.is_empty spec.c_effect.eff_raises) in
      let closure = Module.cast_to_closure ~raises e builder in
      let exn = Module.create_exn builder in
      let res = Module.create_value (sprintf "(%s->f)(%s, %s->env%s)" (Module.string_of_value closure) (Module.string_of_value v) (Module.string_of_value closure) (if raises then sprintf ", &%s" (Module.string_of_value exn) else "")) builder in
      Module.append_block
        (sprintf "if(%s != NULL)" (Module.string_of_value exn))
        (fun builder -> raise_expr exn builder)
        builder;
      res
  | Elet ({ let_expr = e1 }, e2) when e1.e_ghost ->
      print_expr info ~raise_expr gamma e2 builder
  | Elet ({ let_sym = lv ; let_expr = e1 }, e2) ->
      let v = print_expr info ~raise_expr gamma e1 builder in
      let gamma = Mid.add (get_id_from_let lv) (Value v) gamma in
      print_expr info ~raise_expr gamma e2 builder
  | Eif (e0,e1,e2) ->
      print_if (print_expr info ~raise_expr gamma) builder (e0, e1, e2)
  | Eassign (pl,e,_,pv) ->
      let ty = match e.e_vty with
        | VTvalue {ity_node = Ityapp ({its_ts; _}, _, _)} ->
            get_qident info its_ts.ts_name
        | VTvalue {ity_node = Ityvar _}
        | VTvalue {ity_node = Itypur _}
        | VTarrow _ ->
            assert false
      in
      let e = print_expr info ~raise_expr gamma e builder in
      let e = Module.cast_to_record ~st:ty e builder in
      let pv = get_value info pv.pv_vs.vs_name gamma builder in
      Module.append_expr (sprintf "%s->%s = %s" (Module.string_of_value e) pl.pl_ls.ls_name.id_string (Module.string_of_value pv)) builder;
      Module.unit_value
  | Eloop (_,_,e) ->
      let exn = Module.create_exn builder in
      Module.append_block
        "while(true)"
        (fun builder ->
           let new_raise_expr value builder =
             Module.append_expr
               (sprintf "%s = %s" (Module.string_of_value exn) (Module.string_of_value value))
               builder;
             Module.append_expr "break" builder;
           in
           ignore (print_expr info ~raise_expr:new_raise_expr gamma e builder)
        )
        builder;
      Module.append_block
        (sprintf "if(%s != NULL)" (Module.string_of_value exn))
        (fun builder -> raise_expr exn builder)
        builder;
      Module.unit_value
  | Efor (pv,(pvfrom,dir,pvto),_,e) ->
      assert false
  | Eraise (xs,e) ->
      let e = print_expr info ~raise_expr gamma e builder in
      let value = Module.malloc_exn builder in
      Module.append_expr (sprintf "%s->key = tag_%s" (Module.string_of_value value) (Module.string_of_value (get_xs info xs))) builder;
      Module.append_expr (sprintf "%s->val = %s" (Module.string_of_value value) (Module.string_of_value e)) builder;
      raise_expr value builder;
      Module.null_value
  | Etry (e,bl) ->
      let exn = Module.create_exn builder in
      let res = Module.create_value "NULL" builder in
      Module.append_block
        "do"
        (fun builder ->
           let new_raise_expr value builder =
             Module.append_expr
               (sprintf "%s = %s" (Module.string_of_value exn) (Module.string_of_value value))
               builder;
             Module.append_expr "break" builder;
           in
           let value = print_expr info ~raise_expr:new_raise_expr gamma e builder in
           Module.append_expr (sprintf "%s = %s" (Module.string_of_value res) (Module.string_of_value value)) builder;
        )
        builder;
      Module.append_expr "while(false)" builder;
      Module.append_block
        (sprintf "if(%s != NULL)" (Module.string_of_value exn))
        (fun builder ->
           List.iteri
             (fun i x ->
                print_xbranch info ~first:(i = 0) gamma ~raise_expr ~exn ~res x builder;
                Module.append_block "else" (raise_expr exn) builder;
             )
             bl
        )
        builder;
      Module.unit_value
  | Eabstr (e,_) ->
      print_expr info ~raise_expr gamma e builder
  | Eabsurd ->
      Module.append_expr "abort()" builder;
      Module.null_value
  | Eassert _ ->
      Module.unit_value
  | Eghost _ ->
      assert false
  | Eany _ ->
      assert false
  | Ecase (e1, [_,e2]) when e1.e_ghost ->
      print_expr info ~raise_expr gamma e2 builder
  | Ecase (e1, bl) ->
      assert false
  | Erec (fdl, e) ->
      let local_arr = Module.create_array (List.length fdl) builder in
      let gamma =
        let aux gamma index fd =
          let store = Module.value_of_string (sprintf "%s[%d]" (Module.string_of_value local_arr) index) in
          Mid.add fd.fun_ps.ps_name (Value store) gamma
        in
        Lists.fold_lefti aux gamma fdl
      in
      let aux index fd =
        let store = Module.value_of_string (sprintf "%s[%d]" (Module.string_of_value local_arr) index) in
        if not fd.fun_ps.ps_ghost then begin
          let v = print_rec info ~env:Module.null_value ~raise_expr builder gamma fd in
          Module.append_expr (sprintf "%s = %s" (Module.string_of_value store) (Module.string_of_value v)) builder;
        end
      in
      Lists.iteri aux fdl;
      print_expr info ~raise_expr gamma e builder

and print_rec info ~env ~raise_expr builder gamma { fun_ps = ps ; fun_lambda = lam } =
  let raises = not (Sexn.is_empty ps.ps_aty.aty_spec.c_effect.eff_raises) in
  let rec aux ~raise_expr gamma builder = function
    | [] ->
        print_expr info ~raise_expr gamma lam.l_expr builder
    | arg::xs ->
        let closure = Module.malloc_closure ~raises builder in
        let gamma = Mid.add arg.pv_vs.vs_name (Value closure) gamma in
        let env = Module.malloc_env (Mid.cardinal gamma) builder in
        let gamma = fold_env env gamma builder in
        let lambda =
          Module.create_lambda
            ~raises
            (fun ~raise_expr builder ->
               let gamma = Mid.add arg.pv_vs.vs_name (Value (Module.value_of_string "Param__0")) gamma in
               aux ~raise_expr gamma builder xs
            )
        in
        Module.append_expr (sprintf "%s->f = %s" (Module.string_of_value closure) (Module.string_of_value lambda)) builder;
        Module.append_expr (sprintf "%s->env = %s" (Module.string_of_value closure) (Module.string_of_value env)) builder;
        closure
  in
  aux ~raise_expr gamma builder lam.l_args

and print_xbranch info ~first gamma ~raise_expr ~exn ~res (xs, pv, e) builder =
  if ity_equal xs.xs_ity ity_unit then
    Module.append_block
      (sprintf "%sif(%s->key == tag_%s)" (if first then "" else "else ") (Module.string_of_value exn) (Module.string_of_value (get_xs info xs)))
      (fun builder ->
         let value = print_expr info ~raise_expr gamma e builder in
         Module.append_expr (sprintf "%s = %s" (Module.string_of_value res) (Module.string_of_value value)) builder;
      )
      builder
  else
    (* TODO: Handle params *)
    assert false

and print_rec_decl info gamma builder fdl =
  let aux fd =
    let store = get_ps info fd.fun_ps in
    Module.define_global store;
    if not fd.fun_ps.ps_ghost then begin
      let v = print_rec info ~env:Module.null_value ~raise_expr:(fun _ _ -> assert false) builder gamma fd in
      Module.append_expr (sprintf "%s = %s" (Module.string_of_value store) (Module.string_of_value v)) builder;
    end
  in
  List.iter aux fdl
  (*forget_tvs ()*)

let is_ghost_lv = function
  | LetV pv -> pv.pv_ghost
  | LetA ps -> ps.ps_ghost

let print_pdata_decl info (its, csl, _) =
  let get_field x = x.ls_name.id_string in
  match csl with
    | [cs, _] ->
        let pjl = get_record info cs.pl_ls in
        if pjl <> [] then
          Module.define_record (get_its info its) (List.map get_field pjl)
    | _ ->
        ()

(* TODO: Handle driver *)
let print_exn_decl info xs =
  Module.append_global
    ~name:(sprintf "exn_tag tag_%s" (Module.string_of_value (get_xs info xs)))
    ~value:(sprintf "\"%s\"" (Module.string_of_value (get_xs ~separator:"." info xs)))

let rec pdecl info gamma builder = function
  | pd::decls ->
      Mlw_extract.check_exec_pdecl info.info_syn pd;
      begin match pd.pd_node with
      | PDtype _ ->
          pdecl info gamma builder decls
      | PDdata tl ->
          List.iter (print_pdata_decl info) tl;
          pdecl info gamma builder decls
      | PDval lv ->
          (* TODO *)
          pdecl info gamma builder decls
      | PDlet ld ->
          if not (is_ghost_lv ld.let_sym) then begin
            let store = get_lv info ld.let_sym in
            Module.define_global store;
            let v = print_expr info ~raise_expr:(fun _ _ -> assert false) gamma ld.let_expr builder in
            Module.append_expr (sprintf "%s = %s" (Module.string_of_value store) (Module.string_of_value v)) builder;
          end;
          pdecl info gamma builder decls
      | PDrec fdl ->
          print_rec_decl info gamma builder fdl;
          pdecl info gamma builder decls
      | PDexn xs ->
          print_exn_decl info xs;
          pdecl info gamma builder decls
      end
  | [] ->
      ()

(** Modules *)

let extract_module drv ?old ?fname fmt m =
  hack_fmt := Some fmt;
  ignore (old); ignore (fname);
  let th = m.mod_theory in
  let info = {
    info_syn = drv.Mlw_driver.drv_syntax;
    converters = drv.Mlw_driver.drv_converter;
    current_theory = th;
    current_module = Some m;
    th_known_map = th.th_known;
    mo_known_map = m.mod_known;
    fname = Opt.map clean_fname fname; } in
  let builder = Module.init_builder in
  pdecl info Mid.empty builder m.mod_decls

let finalize () =
  match !hack_fmt with
  | None ->
      ()
  | Some fmt ->
      fprintf fmt "%s" (Module.to_string ())
