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

let clean_fname fname =
  let fname = Filename.basename fname in
  (try Filename.chop_extension fname with _ -> fname)

let modulename ?fname path t =
  let fname = match fname, path with
    | Some fname, _ -> clean_fname fname
    | None, [] -> "why3"
    | None, _ -> String.concat "__" path
  in
  fname ^ "__" ^ t

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

module Module : sig
  type builder
  type value

  val append_function : ident -> (string -> string) -> (builder -> unit) -> unit
  val append_global : ident -> string -> unit
  val append_block : (string -> string) -> (builder -> unit) -> builder -> unit
  val append_builder : string -> builder -> unit
  val append_header : string -> unit

  val create_value : builder -> value
  val unit_value : value

  val value_of_string : string -> value
  val string_of_value : value -> string

  val clear : unit -> unit

  val to_string : unit -> string
end = struct
  type builder =
    { mutable builder : string list
    ; mutable ident : int
    }

  type value = string

  module M = Hashtbl.Make(struct
    type t = ident
    let equal = id_equal
    let hash = Hashtbl.hash
  end)

  let header = ref []
  let modul = M.create 64

  let define_global () =
    { builder = []
    ; ident = 0
    }

  let create_block builder =
    { builder = []
    ; ident = builder.ident
    }

  let create_value builder =
    let v = sprintf "X%i__" builder.ident in
    builder.ident <- succ builder.ident;
    v

  let string_of_builder builder =
    let builder = List.rev builder.builder in
    String.concat "\n" builder

  let value_of_string x = x

  let unit_value = "unit__Unit"

  let string_of_value x = x

  let append_global id x =
    if M.mem modul id then
      assert false;
    M.add modul id x

  let append_function id f g =
    let builder = define_global () in
    g builder;
    append_global id (f (string_of_builder builder))

  let append_builder x builder =
    builder.builder <- x :: builder.builder

  let append_header str =
    header := !header @ [str]

  let append_block f g builder =
    let builder' = create_block builder in
    g builder';
    append_builder (f (string_of_builder builder)) builder

  let clear () =
    header := [];
    M.clear modul

  let to_string () =
    let buf = Buffer.create 64 in
    let aux _ = Buffer.add_string buf in
    List.iter (Buffer.add_string buf) !header;
    M.iter aux modul;
    Buffer.contents buf
end

let get_qident info id =
  try
    let lp, t, p =
      try Mlw_module.restore_path id
      with Not_found -> Theory.restore_path id in
    let s = String.concat "__" p in
    let s = Ident.sanitizer char_to_alpha char_to_alnumus s in
    if Sid.mem id info.current_theory.th_local ||
       Opt.fold (fun _ m -> Sid.mem id m.Mlw_module.mod_local)
        false info.current_module
    then
      Module.value_of_string (sprintf "%s" s)
    else
      let fname = if lp = [] then info.fname else None in
      let m = modulename ?fname lp t in
      Module.value_of_string (sprintf "%s__%s" m s)
  with Not_found ->
    assert false (* TODO: Know what to do *)

let get_ls info fmt ls = get_qident info ls.ls_name

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let has_syntax info id = Mid.mem id info.info_syn

let has_syntax_or_nothing info id =
  if not (has_syntax info id) then
    assert false

let print_const ~paren fmt = function
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

let print_binop fmt = function
  | Tand -> fprintf fmt "&&"
  | Tor -> fprintf fmt "||"
  | Tiff -> fprintf fmt "=="
  | Timplies -> assert false

let rec print_term ?(paren=false) info fmt t = match t.t_node with
  | Tvar v ->
      assert false
  | Tconst c ->
      print_const ~paren fmt c
  | Tapp (fs, tl) ->
      assert false
  | Tif (f,t1,t2) ->
      assert false
  | Tlet (t1,tb) ->
      assert false
  | Tcase (t1,bl) ->
      assert false
  | Teps _
  | Tquant _ ->
      assert false
  | Ttrue ->
      fprintf fmt "true"
  | Tfalse ->
      fprintf fmt "false"
  | Tbinop (Timplies,f1,f2) ->
      fprintf fmt (protect_on paren "!%a || %a")
        (print_term_p info) f1 (print_term_p info) f2
  | Tbinop (b,f1,f2) ->
      fprintf fmt (protect_on paren "@[<hov 1>%a %a@ %a@]")
        (print_term_p info) f1 print_binop b (print_term_p info) f2
  | Tnot f ->
      fprintf fmt (protect_on paren "!%a") (print_term_p info) f

and print_term_p info fmt t = print_term ~paren:true info fmt t

(** Logic Declarations *)

let logic_decl info fmt d = match d.d_node with
  | Dtype _
  | Ddata _ ->
      () (* Types are useless for C *)
  | Decl.Dparam ls ->
(*      print_qident info fmt ls.ls_name;*)
      () (* Why is it a non_executable code ? *)
  | Dlogic ll ->
      () (* TODO *)
  | Dind (s, il) ->
      assert false
  | Dprop (_pk, _pr, _) ->
      assert false

let logic_decl info fmt td = match td.td_node with
  | Decl d ->
      if Mlw_exec.is_exec_decl info.info_syn d then begin
        let union = Sid.union d.d_syms d.d_news in
        let inter = Mid.set_inter union info.mo_known_map in
        if Sid.is_empty inter then logic_decl info fmt d
      end
  | Use _ | Clone _ | Meta _ ->
      ()

(** Theories *)

let extract_theory drv ?old ?fname fmt th =
  ignore (old); ignore (fname);
  let info = {
    info_syn = drv.Mlw_driver.drv_syntax;
    converters = drv.Mlw_driver.drv_converter;
    current_theory = th;
    current_module = None;
    th_known_map = th.th_known;
    mo_known_map = Mid.empty;
    fname = Opt.map clean_fname fname; } in
  print_list nothing (logic_decl info) fmt th.th_decls;
  fprintf fmt "@."

(** Programs *)

open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl
open Mlw_module

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

let get_xs info xs = get_qident info xs.xs_name

let rec print_expr ?(paren=false) info builder e =
  if e.e_ghost then
    Module.unit_value
  else match e.e_node with
  | Elogic t ->
      assert false
  | Evalue v ->
      get_pv info v
  | Earrow a ->
      assert false
  | Eapp (e,v,_) ->
      assert false
  | Elet ({ let_expr = e1 }, e2) when e1.e_ghost ->
      assert false
  | Elet ({ let_sym = lv ; let_expr = e1 }, e2) ->
      assert false
  | Eif (e0, e1, { e_node = Elogic { t_node = Tapp (ls, []) }})
    when ls_equal ls fs_void ->
      assert false
  | Eif (e0,e1,e2) ->
      let e0 = print_expr info builder e0 in
      Module.append_builder (sprintf "@[<hv>if()@]") builder;
      Module.unit_value
  | Eassign (pl,e,_,pv) ->
      assert false
  | Eloop (_,_,e) ->
      Module.append_block
        (sprintf "@[<hv>while(true) {@\n@;<1 2>@[%s@]}@]@\n")
        (fun builder -> ignore (print_expr info builder e))
        builder;
      Module.unit_value
  | Efor (pv,(pvfrom,dir,pvto),_,e) ->
      assert false
  | Eraise (xs,_) when xs_equal xs xs_exit ->
      assert false
  | Eraise (xs,e) ->
      assert false
  | Etry (e,bl) ->
      print_expr info builder e
  | Eabstr (e,_) ->
      assert false
  | Eabsurd ->
      Module.unit_value (* TODO: Change *)
  | Eassert _ ->
      Module.unit_value
  | Eghost _ ->
      assert false
  | Eany _ ->
      assert false
  | Ecase (e1, [_,e2]) when e1.e_ghost ->
      assert false
  | Ecase (e1, bl) ->
      assert false
  | Erec (fdl, e) ->
      assert false

and print_rec info { fun_ps = ps ; fun_lambda = lam } =
  if not ps.ps_ghost then
    Module.append_function
      ps.ps_name
      (sprintf "@[<hov 2>value __lambda1(value lol) {@\n%s}@\n@]")
      (fun builder ->
         let v = print_expr info builder lam.l_expr in
         Module.append_builder
           (sprintf "return %s;" (Module.string_of_value v))
           builder;
      )

and print_rec_decl info fd =
  print_rec info fd
  (*forget_tvs ()*)

let is_ghost_lv = function
  | LetV pv -> pv.pv_ghost
  | LetA ps -> ps.ps_ghost

(* TODO: Handle driver *)
let print_exn_decl info xs =
  Module.append_global
    xs.xs_name
    (sprintf "char const * const tag_%s = \"%s\";@\n@\n"
       (Module.string_of_value (get_xs info xs))
       (Module.string_of_value (get_xs info xs))
       (* TODO: Improve pretty-printing *)
    )

let pdecl info pd =
  Mlw_exec.check_exec_pdecl info.info_syn pd;
  match pd.pd_node with
  | PDtype ts ->
      assert false
  | PDdata tl ->
      assert false
  | PDval lv ->
      () (* LOL *)
  | PDlet ld ->
      assert false
  | PDrec fdl ->
      (* print defined, non-ghost first *)
      let cmp {fun_ps=ps1} {fun_ps=ps2} =
        Pervasives.compare
          (ps1.ps_ghost || has_syntax info ps1.ps_name)
          (ps2.ps_ghost || has_syntax info ps2.ps_name) in
      let fdl = List.sort cmp fdl in
      List.iter (print_rec_decl info) fdl;
  | PDexn xs ->
      print_exn_decl info xs

(** Modules *)

let extract_module drv ?old ?fname fmt m =
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
  Module.clear ();
  Module.append_header "#include <stdbool.h>";
  Module.append_header "#include <gmp.h>";
  Module.append_header "typedef void* value;";
  List.iter (pdecl info) m.mod_decls;
  fprintf fmt "%s@." (Module.to_string ())
