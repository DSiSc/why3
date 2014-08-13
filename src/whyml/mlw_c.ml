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

open Number
open Ident
open Ty
open Term
open Decl
open Theory

module Module = Mlw_c_module

let extract_filename ?fname th =
  (Module.modulename ?fname th.th_path th.th_name.Ident.id_string) ^ ".c"

type info = Module.info = {
  info_syn: Printer.syntax_map;
  converters: Printer.syntax_map;
  current_theory: Theory.theory;
  current_module: Mlw_module.modul option;
  th_known_map: Decl.known_map;
  mo_known_map: Mlw_decl.known_map;
  fname: string option;
}

type value =
  | Value of Module.value
  | Env of int

let get_ts info ts = Module.get_ident info ts.ts_name

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

let has_syntax info id = Mid.mem id info.info_syn

let has_syntax_or_nothing info id =
  if not (has_syntax info id) then
    assert false

let has_syntax_or_ghost_or_nothing info is_ghost id =
  if not is_ghost then
    has_syntax_or_nothing info id

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

(** Inductive *)

let print_ind_decl info (ls, _) =
  has_syntax_or_nothing info ls.ls_name

let print_const builder = function
  | ConstInt c ->
      let (c, base) = match c with
        | IConstDec x -> (x, 10)
        | IConstHex x -> (x, 16)
        | IConstOct x -> (x, 8)
        | IConstBin x -> (x, 2)
      in
      Module.create_mpz c base builder
  | ConstReal _ ->
      assert false

let print_if f builder (e,t1,t2) =
  let e = f e builder in
  let res = Module.create_value Module.null_value builder in
  Module.build_if_true
    e
    (fun builder ->
       let v = f t1 builder in
       Module.build_store res v builder
    )
    builder;
  Module.build_else
    (fun builder ->
       let v = f t2 builder in
       Module.build_store res v builder
    )
    builder;
  res

let get_value info id gamma builder =
  match Mid.find_opt id gamma with
  | None ->
      Module.get_ident info id
  | Some v ->
      begin match v with
      | Value v ->
          v
      | Env i ->
          Module.build_access_array Module.env_value i builder
      end

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

let is_simple_pattern =
  let aux x =
    match (fst (t_open_branch x)).pat_node with
    | Pwild -> true
    | Papp (_, patterns) ->
        let aux {pat_node; _} = match pat_node with
          | Pwild | Pvar _ -> true
          | Papp _ | Por _ | Pas _ -> false
        in
        List.for_all aux patterns
    | Pvar _ | Por _ | Pas _ -> false
  in
  List.for_all aux

let rec print_variant_creation info ~ls ~tl builder =
  let v = Module.malloc_env (List.length tl) builder in
  Lists.iteri (fun i x -> Module.build_store_array v i x builder) tl;
  let variant = Module.malloc_variant builder in
  let index =
    let ty = match ls.ls_value with
      | Some {ty_node = Tyapp (tys, _); _} -> tys
      | Some {ty_node = Tyvar _; _}
      | None -> assert false
    in
    let constrs = Decl.find_constructors info.th_known_map ty in
    Lists.find_nth (fun (ls', _) -> ls_equal ls' ls) constrs
  in
  Module.build_store_field_int variant "key" index builder;
  Module.build_store_field variant "val" v builder;
  variant

and print_record_creation info ~ls ~tl ~pjl builder =
  let v = Module.malloc_record (get_record_name info ls.ls_value) builder in
  let aux (ls, t) =
    Module.build_store_field v ls.ls_name.id_string t builder;
  in
  List.iter aux (List.combine pjl tl);
  v

and print_record_access info ~t1 ~ls builder =
  let t1 = Module.cast_to_record ~st:(get_record_name info (singleton_opt ls.ls_args)) t1 builder in
  Module.build_access_field t1 ls.ls_name.id_string builder

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
  | tl when isconstr ->
      let pjl = get_record info ls in
      if pjl = [] then
        print_variant_creation info ~ls ~tl builder
      else
        print_record_creation info ~ls ~tl ~pjl builder
  | [] ->
      get_value info ls.ls_name gamma builder
  | [t1] when isfield ->
      print_record_access info ~t1 ~ls builder
  | tl ->
      let f = get_value info ls.ls_name gamma builder in
      Module.build_pure_call f tl builder

and print_term info gamma t builder = match t.t_node with
  | Tvar v ->
      get_value info v.vs_name gamma builder
  | Tconst c ->
      print_const builder c
  | Tapp (fs, tl) ->
      let tl = filter_ghost fs Mlw_expr.t_void tl in
      let tl = List.map (fun t -> print_term info gamma t builder) tl in
      begin match Printer.query_syntax info.info_syn fs.ls_name with
      | Some s -> Module.syntax_arguments s tl builder
      | None -> print_app fs info gamma builder tl
      end
  | Tif (e, t1, t2) ->
      print_if (print_term info gamma) builder (e, t1, t2)
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      let t1 = print_term info gamma t1 builder in
      let t1 = Module.create_named_value info v.vs_name t1 builder in
      let gamma = Mid.add v.vs_name (Value t1) gamma in
      print_term info gamma t2 builder
  | Tcase (t1, bl) when is_simple_pattern bl ->
      let t1 = print_term info gamma t1 builder in
      print_lbranches info gamma ~t1 ~bl builder
  | Tcase (t1, bl) ->
      let bl = List.map (fun x -> let (x, y) = t_open_branch x in ([x], y)) bl in
      let mk_case = t_case_close in
      let mk_let = t_let_close_simp in
      let e2 = Pattern.compile_bare ~mk_case ~mk_let [t1] bl in
      print_term info gamma e2 builder
  | Teps _
  | Tquant _ ->
      assert false
  | Ttrue ->
      Module.true_value
  | Tfalse ->
      Module.false_value
  | Tbinop (Timplies,f1,f2) ->
      let f1 = print_term info gamma f1 builder in
      let res = Module.build_not f1 builder in
      Module.build_if_true
        f1
        (fun builder ->
           let v = print_term info gamma f2 builder in
           Module.build_store res v builder
        )
        builder;
      res
  | Tbinop (Tand,f1,f2) ->
      let f1 = print_term info gamma f1 builder in
      let res = Module.create_value f1 builder in
      Module.build_if_false
        f1
        (fun builder ->
           let v = print_term info gamma f2 builder in
           Module.build_store res v builder
        )
        builder;
      res
  | Tbinop (Tor,f1,f2) ->
      let f1 = print_term info gamma f1 builder in
      let res = Module.create_value f1 builder in
      Module.build_if_false
        f1
        (fun builder ->
           let v = print_term info gamma f2 builder in
           Module.build_store res v builder
        )
        builder;
      res
  | Tbinop (Tiff,f1,f2) ->
      let f1 = print_term info gamma f1 builder in
      let f2 = print_term info gamma f2 builder in
      Module.build_equal f1 f2 builder
  | Tnot f ->
      let v = print_term info gamma f builder in
      Module.build_not v builder

and print_lbranches info gamma ~t1 ~bl builder =
  let t1 = Module.cast_to_variant t1 builder in
  let v = Module.build_access_field ~ty:Module.TyValuePtr t1 "val" builder in
  let res = Module.create_value Module.null_value builder in
  let bl =
    List.map
      (fun p ->
         let (p, t) = t_open_branch p in
         begin match p.pat_node with
         | Pwild ->
             let f builder =
               let t = print_term info gamma t builder in
               Module.build_store res t builder;
             in
             (None, f)
         | Papp (ls, patterns) ->
             let tys = match p.pat_ty.ty_node with
               | Tyvar _ -> assert false
               | Tyapp (tys, _) -> tys
             in
             let constructors = Decl.find_constructors info.th_known_map tys in
             let i = Lists.find_nth (fun (x, _) -> ls_equal x ls) constructors in
             let f builder =
               let gamma =
                 let aux gamma i {pat_node; _} = match pat_node with
                   | Pwild -> gamma
                   | Pvar vs ->
                       let v = Module.const_access_array v i in
                       let v = Module.create_named_value info vs.vs_name v builder in
                       Mid.add vs.vs_name (Value v) gamma
                   | Papp _ | Por _ | Pas _ -> assert false
                 in
                 Lists.fold_lefti aux gamma patterns
               in
               let t = print_term info gamma t builder in
               Module.build_store res t builder;
             in
             (Some i, f)
         | Pvar _ | Por _ | Pas _ ->
             assert false
         end
      )
      bl
  in
  Module.build_switch t1 bl builder;
  res

let print_param_decl info ls =
  has_syntax_or_nothing info ls.ls_name

let print_logic_decl info gamma (ls, ld) =
  if has_syntax info ls.ls_name then
    (* TODO *)
    ()
  else begin
    let vl,e = open_ls_defn ld in
    let func =
      Module.create_pure_function
        info
        ~name:ls.ls_name
        ~params:(List.map (fun x -> x.vs_name) vl)
        (fun ~params builder ->
           let gamma =
             let aux gamma x y = Mid.add x.vs_name (Value y) gamma in
             List.fold_left2 aux gamma vl params
           in
           print_term info gamma e builder
        )
    in
    ignore func;
  end

(** Logic Declarations *)

(* TODO: Think that logical functions are shadowed by program functions *)

let logic_decl info d = match d.d_node with
  | Dtype _ ->
      ()
  | Ddata tl ->
      List.iter (print_pdata_decl info) tl;
  | Decl.Dparam ls ->
      print_param_decl info ls;
  | Dlogic ll ->
      List.iter (print_logic_decl info Mid.empty) ll;
  | Dind (_, il) ->
      List.iter (print_ind_decl info) il;
  | Dprop (_pk, _pr, _) ->
      assert false

let logic_decl info td = match td.td_node with
  | Decl d ->
      begin match Mlw_extract.get_exec_decl info.info_syn d with
      | Some d ->
          let union = Sid.union d.d_syms d.d_news in
          let inter = Mid.set_inter union info.mo_known_map in
          if Sid.is_empty inter then logic_decl info d
      | None ->
          ()
      end
  | Use _ | Clone _ | Meta _ ->
      ()

(** Theories *)

let extract_theory drv ?fname fmt th =
  let info = {
    info_syn = drv.Mlw_driver.drv_syntax;
    converters = drv.Mlw_driver.drv_converter;
    current_theory = th;
    current_module = None;
    th_known_map = th.th_known;
    mo_known_map = Mid.empty;
    fname = Opt.map Module.clean_fname fname; } in
  List.iter (logic_decl info) th.th_decls;
  Module.dump fmt

(** Programs *)

open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl
open Mlw_module

let get_its info ts = get_ts info ts.its_ts

let get_xs ?separator info xs = Module.get_ident ?separator info xs.xs_name

let get_id_from_let = function
  | LetV pv -> pv.pv_vs.vs_name
  | LetA ps -> ps.ps_name

type pre_expr =
  | PreM of (term * (pattern * pre_expr) list)
  | PreL of (vsymbol * term * pre_expr)
  | Expr of expr

let create_env syms gamma builder =
  let is_used id =
    Spv.exists (fun x -> id_equal x.pv_vs.vs_name id) syms.syms_pv
    || Sps.exists (fun x -> id_equal x.ps_name id) syms.syms_ps
  in
  let gamma = Mid.filter (fun id _ -> is_used id) gamma in
  let env = Module.malloc_env (Mid.cardinal gamma) builder in
  let fold_env id x (index, gamma) = match x with
    | Value v ->
        Module.build_store_array env index v builder;
        (succ index, Mid.add id (Env index) gamma)
    | Env i ->
        Module.build_store_array_from_array env index Module.env_value i builder;
        (succ index, Mid.add id (Env index) gamma)
  in
  let gamma = snd (Mid.fold fold_env gamma (0, Mid.empty)) in
  (env, gamma)

let ity_of_expr = function
  | VTvalue ty -> ty
  | VTarrow _ -> assert false

let vs_from_term t = match t.t_node with
  | Tvar vs -> vs
  | Tconst _
  | Tapp _
  | Tif _
  | Tlet _
  | Tcase _
  | Teps _
  | Tquant _
  | Tbinop _
  | Tnot _
  | Ttrue
  | Tfalse -> assert false

let apply f ~raises ~raise_expr params builder =
  let closure = Module.cast_to_closure f builder in
  if raises then begin
    let exn = Module.create_exn builder in
    let res = Module.build_call closure params ~exn builder in
    Module.build_if_not_null exn (raise_expr exn) builder;
    res
  end else begin
    Module.build_call closure params builder
  end

let rec print_pattern ~current_is_ghost info ~raise_expr gamma map_ghost builder = function
  | PreM (t, bl) ->
      let vs = vs_from_term t in
      let is_ghost =
        try (restore_pv vs).pv_ghost with
        | Not_found ->
            match Mvs.find_opt vs map_ghost with
            | Some is_ghost -> is_ghost
            | None -> assert false
      in
      let current_is_ghost = is_ghost in
      if is_ghost then begin
        let branch = List.hd bl in
        print_pattern ~current_is_ghost info ~raise_expr gamma map_ghost builder (snd branch)
      end else begin
        let e1 = get_value info vs.vs_name gamma builder in
        print_branches ~current_is_ghost info ~raise_expr gamma map_ghost ~e1 ~bl builder
      end
  | PreL (vs, t, xs) ->
      let id = (vs_from_term t).vs_name in
      let value = match Mid.find_opt id gamma with
        | Some (Value x) -> x
        | Some (Env _) | None -> assert false
      in
      let value = Module.create_named_value info vs.vs_name value builder in
      let gamma = Mid.add vs.vs_name (Value value) gamma in
      print_pattern ~current_is_ghost info ~raise_expr gamma map_ghost builder xs
  | Expr e ->
      print_expr info ~raise_expr gamma e builder

and print_app info ~raise_expr gamma builder params e = match e.e_node with
  | Earrow ps ->
      let f = get_value info ps.ps_name gamma builder in
      let rec aux f a = function
        | [] ->
            f
        | params ->
            let spec =
              let rec aux = function
                | [(_, spec)] -> spec
                | (_, spec)::xs when eff_is_empty spec.c_effect -> aux xs
                | [] | _::_ -> assert false
              in
              aux params
            in
            let raises = not (Sexn.is_empty spec.c_effect.eff_raises) in
            let params_nbr = List.length a.aty_args in
            let given_params_nbr = List.length params in
            let remaining_params = params_nbr - given_params_nbr in
            if remaining_params <= 0 then begin
              let (params, rem) = Lists.split_at params_nbr params in
              let params = List.map fst params in
              let f = apply f ~raises ~raise_expr params builder in
              begin match a.aty_result with
              | VTvalue _ when rem = [] -> f
              | VTvalue _ -> assert false
              | VTarrow a ->
                  aux f a rem
              end
            end else begin
              let closure = Module.malloc_closure builder in
              let env = Module.malloc_env (Mid.cardinal gamma) builder in
              Lists.iteri (fun i (x, _) -> Module.build_store_array env i x builder) params;
              let params = Lists.chop given_params_nbr a.aty_args in
              let params = List.map (fun x -> x.pv_vs.vs_name) params in
              let func =
                Module.create_function
                  info
                  ~params
                  ~raises
                  (fun ~raise_expr ~params builder ->
                     let params =
                       let rec aux acc = function
                         | 0 -> acc
                         | i ->
                             let i = pred i in
                             let x =
                               Module.const_access_array Module.env_value i
                             in
                             aux (x :: acc) i
                       in
                       aux params given_params_nbr
                     in
                     apply f ~raises ~raise_expr params builder
                  )
              in
              Module.build_store_field closure "f" func builder;
              Module.build_store_field closure "env" env builder;
              closure
            end
      in
      aux f ps.ps_aty params
  | Eapp (e, v, spec) ->
      let v = get_value info v.pv_vs.vs_name gamma builder in
      print_app info ~raise_expr gamma builder ((v, spec) :: params) e
  | Elogic _
  | Evalue _
  | Elet _
  | Eif _
  | Eassign _
  | Eloop _
  | Efor _
  | Eraise _
  | Etry _
  | Eabstr _
  | Eabsurd
  | Eassert _
  | Eghost _
  | Eany _
  | Ecase _
  | Erec _ ->
      (* TODO *)
      assert false

and print_expr info ~raise_expr gamma e builder =
  if e.e_ghost then
    Module.unit_value
  else match e.e_node with
  | Elogic t ->
      print_term info gamma t builder
  | Evalue v ->
      get_value info v.pv_vs.vs_name gamma builder
  | Earrow _
  | Eapp _ ->
      print_app info ~raise_expr gamma builder [] e
  | Elet ({ let_expr = e1 }, e2) when e1.e_ghost ->
      print_expr info ~raise_expr gamma e2 builder
  | Elet ({ let_sym = lv ; let_expr = e1 }, e2) ->
      let id = get_id_from_let lv in
      let v = print_expr info ~raise_expr gamma e1 builder in
      let v = Module.create_named_value info id v builder in
      let gamma = Mid.add id (Value v) gamma in
      print_expr info ~raise_expr gamma e2 builder
  | Eif (e0,e1,e2) ->
      print_if (print_expr info ~raise_expr gamma) builder (e0, e1, e2)
  | Eassign (pl,e,_,pv) ->
      let ty = match e.e_vty with
        | VTvalue {ity_node = Ityapp ({its_ts; _}, _, _)} ->
            get_ts info its_ts
        | VTvalue {ity_node = Ityvar _}
        | VTvalue {ity_node = Itypur _}
        | VTarrow _ ->
            assert false
      in
      let e = print_expr info ~raise_expr gamma e builder in
      let e = Module.cast_to_record ~st:ty e builder in
      let pv = get_value info pv.pv_vs.vs_name gamma builder in
      Module.build_store_field e pl.pl_ls.ls_name.id_string pv builder;
      Module.unit_value
  | Eloop (_,_,e) ->
      let exn = Module.create_exn builder in
      Module.build_while
        (fun builder ->
           let new_raise_expr value builder =
             Module.build_store exn value builder;
             Module.build_break builder;
           in
           ignore (print_expr info ~raise_expr:new_raise_expr gamma e builder)
        )
        builder;
      Module.build_if_not_null exn (raise_expr exn) builder;
      Module.unit_value
  | Efor (pv, (pvfrom, dir, pvto), _, e) ->
      let exn = Module.create_exn builder in
      let i = get_value info pvfrom.pv_vs.vs_name gamma builder in
      let i = Module.clone_mpz i builder in
      let pvto = get_value info pvto.pv_vs.vs_name gamma builder in
      Module.build_while
        (fun builder ->
           let cmp = Module.build_mpz_cmp i pvto builder in
           Module.build_if_cmp_zero
             cmp
             (match dir with To -> "<=" | DownTo -> ">=")
             (fun builder ->
                let i = Module.clone_mpz i builder in
                let gamma = Mid.add pv.pv_vs.vs_name (Value i) gamma in
                let new_raise_expr value builder =
                  Module.build_store exn value builder;
                  Module.build_break builder;
                in
                ignore (print_expr info ~raise_expr:new_raise_expr gamma e builder)
             )
             builder;
           Module.build_else Module.build_break builder;
           Module.build_mpz_succ i builder;
        )
        builder;
      Module.build_if_not_null exn (raise_expr exn) builder;
      Module.unit_value
  | Eraise (xs,e) ->
      let e = print_expr info ~raise_expr gamma e builder in
      let value = Module.malloc_exn builder in
      Module.build_store_field value "key" (get_xs info xs) builder;
      Module.build_store_field value "val" e builder;
      raise_expr value builder;
      Module.null_value
  | Etry (e,bl) ->
      let exn = Module.create_exn builder in
      let res = Module.create_value Module.null_value builder in
      Module.build_do_while
        (fun builder ->
           let new_raise_expr value builder =
             Module.build_store exn value builder;
             Module.build_break builder;
           in
           let value = print_expr info ~raise_expr:new_raise_expr gamma e builder in
           Module.build_store res value builder;
        )
        builder;
      Module.build_if_not_null
        exn
        (fun builder ->
           Module.build_if_else_if_else
             (List.map (print_xbranch info gamma ~raise_expr ~exn ~res builder) bl)
             (raise_expr exn)
             builder
        )
        builder;
      res
  | Eabstr (e,_) ->
      print_expr info ~raise_expr gamma e builder
  | Eabsurd ->
      Module.build_abort builder;
      Module.null_value
  | Eassert _ ->
      Module.unit_value
  | Eghost _ ->
      assert false
  | Eany _ ->
      assert false
  | Ecase (e1, bl) ->
      let (matched_value, gamma) =
        match e1.e_node with
        | Evalue pv -> (t_var pv.pv_vs, gamma)
        | Elogic ({t_node = Tvar _; _} as t) -> (t, gamma)
        | _ ->
            let ghost = e1.e_ghost in
            let ty = ity_of_expr e1.e_vty in
            let pv = create_pvsymbol (id_fresh "matched_value") ~ghost ty in
            let e1 = print_expr info ~raise_expr gamma e1 builder in
            let gamma = Mid.add pv.pv_vs.vs_name (Value e1) gamma in
            (t_var pv.pv_vs, gamma)
      in
      let bl = List.map (fun (x, y) -> ([x.ppat_pattern], Expr y)) bl in
      let mk_case t pattern = PreM (t, pattern) in
      let mk_let vs t pe = PreL (vs, t, pe) in
      let e2 = Pattern.compile_bare ~mk_case ~mk_let [matched_value] bl in
      print_pattern ~current_is_ghost:false info ~raise_expr gamma Mvs.empty builder e2
  | Erec (fdl, e) ->
      let local_arr = Module.create_array (List.length fdl) builder in
      let gamma =
        let aux gamma index fd =
          let store = Module.const_access_array local_arr index in
          Mid.add fd.fun_ps.ps_name (Value store) gamma
        in
        Lists.fold_lefti aux gamma fdl
      in
      let aux index fd =
        if not fd.fun_ps.ps_ghost then begin
          let v = print_rec info builder gamma fd in
          Module.build_store_array local_arr index v builder;
        end
      in
      Lists.iteri aux fdl;
      print_expr info ~raise_expr gamma e builder

and print_rec info builder gamma {fun_ps = ps; fun_lambda = lam} =
  let raises = not (Sexn.is_empty ps.ps_aty.aty_spec.c_effect.eff_raises) in
  let closure = Module.malloc_closure builder in
  let (env, gamma) = create_env lam.l_expr.e_syms gamma builder in
  let func =
    Module.create_function
      info
      ~name:ps.ps_name
      ~params:(List.map (fun x -> x.pv_vs.vs_name) lam.l_args)
      ~raises
      (fun ~raise_expr ~params builder ->
         let gamma =
           let aux gamma x y = Mid.add x.pv_vs.vs_name (Value y) gamma in
           List.fold_left2 aux gamma lam.l_args params
         in
         print_expr info ~raise_expr gamma lam.l_expr builder
      )
  in
  Module.build_store_field closure "f" func builder;
  Module.build_store_field closure "env" env builder;
  closure

and print_xbranch info gamma ~raise_expr ~exn ~res builder (xs, pv, e) =
  let tag = get_xs info xs in
  let key = Module.build_access_field ~ty:Module.TyExnTag exn "key" builder in
  let cond = Module.const_equal key tag in
  let f builder =
    let gamma =
      if ity_equal xs.xs_ity ity_unit then
        gamma
      else
        let param = Module.build_access_field exn "val" builder in
        Mid.add pv.pv_vs.vs_name (Value param) gamma
    in
    let value = print_expr info ~raise_expr gamma e builder in
    Module.build_store res value builder;
  in
  (cond, f)

and print_branches ~current_is_ghost info ~raise_expr gamma map_ghost ~e1 ~bl builder =
  let e1 = Module.cast_to_variant e1 builder in
  let v = Module.build_access_field ~ty:Module.TyValuePtr e1 "val" builder in
  let res = Module.create_value Module.null_value builder in
  let bl =
    List.map
      (fun (p, e) ->
         begin match p.pat_node with
         | Pwild ->
             let f builder =
               let e = print_pattern ~current_is_ghost info ~raise_expr gamma map_ghost builder e in
               Module.build_store res e builder;
             in
             (None, f)
         | Papp (ls, patterns) ->
             let f_var vs i builder gamma =
               let v = Module.const_access_array v i in
               let v = Module.create_named_value info vs.vs_name v builder in
               Mid.add vs.vs_name (Value v) gamma
             in
             let tys = match p.pat_ty.ty_node with
               | Tyvar _ -> assert false
               | Tyapp (tys, _) -> tys
             in
             begin match try Some (restore_its tys) with Not_found -> None with
             | Some ity ->
                 let constructors = find_constructors info.mo_known_map ity in
                 let ((pls, _), i) =
                   try Lists.find_with_nth (fun (x, _) -> ls_equal x.pl_ls ls) constructors with
                   | Not_found -> assert false
                 in
                 let fields = pls.pl_args in
                 let f builder =
                   let (gamma, map_ghost) =
                     let aux (gamma, map_ghost) i {pat_node; _} field = match pat_node with
                       | Pwild -> (gamma, map_ghost)
                       | Pvar vs ->
                           let map_ghost = Mvs.add vs field.fd_ghost map_ghost in
                           if field.fd_ghost then
                             (gamma, map_ghost)
                           else
                             (f_var vs i builder gamma, map_ghost)
                       | Papp _ | Por _ | Pas _ -> assert false
                     in
                     Lists.fold_lefti2 aux (gamma, map_ghost) patterns fields
                   in
                   let e = print_pattern ~current_is_ghost info ~raise_expr gamma map_ghost builder e in
                   Module.build_store res e builder;
                 in
                 (Some i, f)
             | None ->
                 let constructors = Decl.find_constructors info.th_known_map tys in
                 let i = Lists.find_nth (fun (x, _) -> ls_equal x ls) constructors in
                 let f builder =
                   let (gamma, map_ghost) =
                     let aux (gamma, map_ghost) i {pat_node; _} = match pat_node with
                       | Pwild -> (gamma, map_ghost)
                       | Pvar vs ->
                           let map_ghost = Mvs.add vs false map_ghost in
                           (f_var vs i builder gamma, map_ghost)
                       | Papp _ | Por _ | Pas _ -> assert false
                     in
                     Lists.fold_lefti aux (gamma, map_ghost) patterns
                   in
                   let e = print_pattern ~current_is_ghost info ~raise_expr gamma map_ghost builder e in
                   Module.build_store res e builder;
                 in
                 (Some i, f)
             end
         | Pvar _ | Por _ | Pas _ ->
             assert false
         end
      )
      bl
  in
  Module.build_switch e1 bl builder;
  res

and print_rec_decl info gamma fdl =
  let aux fd =
    if not fd.fun_ps.ps_ghost then begin
      let {fun_ps = ps; fun_lambda = lam} = fd in
      let raises = not (Sexn.is_empty ps.ps_aty.aty_spec.c_effect.eff_raises) in
      let func =
        Module.create_function
          info
          ~name:ps.ps_name
          ~params:(List.map (fun x -> x.pv_vs.vs_name) lam.l_args)
          ~raises
          (fun ~raise_expr ~params builder ->
             let gamma =
               let aux gamma x y = Mid.add x.pv_vs.vs_name (Value y) gamma in
               List.fold_left2 aux gamma lam.l_args params
             in
             print_expr info ~raise_expr gamma lam.l_expr builder
          )
      in
      Module.define_global_closure info fd.fun_ps.ps_name func;
    end
  in
  List.iter aux fdl

let lv_name = function
  | LetV pv -> pv.pv_vs.vs_name
  | LetA ps -> ps.ps_name

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

let print_val_decl info lv =
  has_syntax_or_ghost_or_nothing info (is_ghost_lv lv) (lv_name lv)

(* TODO: Handle driver *)
let print_exn_decl info xs =
  Module.append_global_exn
    (get_xs info xs)
    (get_xs ~separator:"." info xs)

let rec pdecl info gamma = function
  | pd::decls ->
      Mlw_extract.check_exec_pdecl info.info_syn pd;
      begin match pd.pd_node with
      | PDtype _ ->
          pdecl info gamma decls
      | PDdata tl ->
          List.iter (print_pdata_decl info) tl;
          pdecl info gamma decls
      | PDval lv ->
          print_val_decl info lv;
          pdecl info gamma decls
      | PDlet _ ->
          assert false
      | PDrec fdl ->
          print_rec_decl info gamma fdl;
          pdecl info gamma decls
      | PDexn xs ->
          print_exn_decl info xs;
          pdecl info gamma decls
      end
  | [] ->
      ()

(** Modules *)

let extract_module drv ?fname fmt m =
  let th = m.mod_theory in
  let info = {
    info_syn = drv.Mlw_driver.drv_syntax;
    converters = drv.Mlw_driver.drv_converter;
    current_theory = th;
    current_module = Some m;
    th_known_map = th.th_known;
    mo_known_map = m.mod_known;
    fname = Opt.map Module.clean_fname fname; } in
  pdecl info Mid.empty m.mod_decls;
  Module.dump fmt
