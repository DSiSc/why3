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

module Module : sig
  type builder
  type value

  val append_function : string -> (builder -> unit) -> unit
  val append_global : name:string -> value:string -> unit
  val define_global : string -> unit
  val append_block : string -> (builder -> unit) -> builder -> unit
  val append_expr : string -> builder -> unit
  val append_header : string -> unit

  val create_global_fresh_name : unit -> value

  val create_value : string -> builder -> value
  val create_exn : builder -> value
  val unit_value : value
  val null_value : value
  val malloc_closure : builder -> value

  val value_of_string : string -> value
  val string_of_value : value -> string

  val init_builder : builder

  val to_string : unit -> string
end = struct
  type builder =
    { mutable builder : string list
    ; mutable ident : int
    ; mutable indent_level : int
    }

  type value = string

  module M = Hashtbl.Make(struct
    type t = string
    let equal = (=)
    let hash = Hashtbl.hash
  end)

  let header = ref []
  let modul = M.create 64
  let ident = ref 0

  let initial_indent_level = 2

  let define_global () =
    { builder = []
    ; ident = 0
    ; indent_level = initial_indent_level
    }

  let create_block builder =
    { builder = []
    ; ident = builder.ident
    ; indent_level = builder.indent_level + initial_indent_level
    }

  let create_global_fresh_name () =
    let name = sprintf "Lambda%d__" !ident in
    incr ident;
    name

  let create_fresh_name builder =
    let v = sprintf "X%i__" builder.ident in
    builder.ident <- succ builder.ident;
    v

  let string_of_builder builder =
    let builder = List.rev builder.builder in
    String.concat "\n" builder

  let value_of_string x = x

  let unit_value = "Tuple0"
  let null_value = "NULL"

  let string_of_value x = x

  let append_global ~name x =
    if M.mem modul name then
      assert false;
    M.add modul name x

  let append_function name g =
    let builder = define_global () in
    g builder;
    let x = name ^ "\n" in
    let x = x ^ "{\n" in
    let x = x ^ string_of_builder builder ^ "\n" in
    let x = x ^ "}" in
    append_global ~name x

  let append_global ~name ~value =
    append_global ~name (sprintf "%s = %s;" name value)

  let append_builder x builder =
    let indent = String.make builder.indent_level ' ' in
    builder.builder <- (indent ^ x) :: builder.builder

  let append_expr x builder =
    append_builder (x ^ ";") builder

  let append_header str =
    header := str :: !header

  let define_global name =
    append_header ("value " ^ name ^ ";")

  let append_block x g builder =
    let builder' = create_block builder in
    g builder';
    append_builder x builder;
    append_builder "{" builder;
    builder.builder <- (string_of_builder builder') :: builder.builder;
    append_builder "}" builder

  let create_value value builder =
    let name = create_fresh_name builder in
    append_builder (sprintf "value %s = %s;" name value) builder;
    name

  let create_exn builder =
    let name = create_fresh_name builder in
    append_builder (sprintf "struct exn* %s = NULL;" name) builder;
    name

  let malloc_closure builder =
    let name = create_fresh_name builder in
    append_builder (sprintf "struct closure* %s = GC_malloc(sizeof(struct closure));" name) builder;
    name

  let init_builder =
    { builder = []
    ; ident = 0
    ; indent_level = initial_indent_level
    }

  let to_string () =
    let buf = Buffer.create 64 in
    let aux x =
      Buffer.add_char buf '\n';
      Buffer.add_string buf x;
      Buffer.add_char buf '\n';
    in
    let header = List.rev !header in
    List.iter (fun x -> Buffer.add_string buf x; Buffer.add_string buf "\n") header;
    M.iter (fun x _ -> aux (x ^ ";")) modul;
    Buffer.add_char buf '\n';
    M.iter (fun _ -> aux) modul;
    Buffer.add_char buf '\n';
    Buffer.add_string buf "void __init__()\n";
    Buffer.add_string buf "{\n";
    Buffer.add_string buf (string_of_builder init_builder ^ "\n");
    Buffer.add_string buf "}\n";
    Buffer.contents buf

  let () = begin
    append_header "#include <stdlib.h>";
    append_header "#include <stdbool.h>";
    append_header "#include <gc.h>";
    append_header "#include <gmp.h>";
    append_header "";
    append_header "typedef void* value;";
    append_header "typedef char const * const exn_tag;";
    append_header "struct variant {int key; value val;};";
    append_header "struct exn {exn_tag key; value val;};";
    append_header "struct closure {value f; value env;};";
    append_header "";
    append_header "struct variant ___False = {0, NULL};";
    append_header "value __False = &___False;";
    append_header "struct variant ___True = {1, NULL};";
    append_header "value __True = &___True;";
    append_header "struct variant ___Tuple0 = {0, NULL};";
    append_header "value Tuple0 = &___Tuple0;";
    append_header "\n";
  end
end

type value =
  | Value of Module.value
  | Env of int

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
    assert false (* TODO: Know what to do *)

let get_ls info ls = get_qident info ls.ls_name

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let has_syntax info id = Mid.mem id info.info_syn

let has_syntax_or_nothing info id =
  if not (has_syntax info id) then
    assert false

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

let get_value id gamma builder =
  match Mid.find_opt id gamma with
  | None ->
      Module.value_of_string id.id_string
  | Some v ->
      begin match v with
      | Value v ->
          v
      | Env i ->
          Module.create_value (sprintf "Env__[%d]" i) builder
      end

let bool_not b =
  Module.create_value (sprintf "((variant *)(%s)->key) ? __False : __True" (Module.string_of_value b))

let rec print_term info gamma t builder = match t.t_node with
  | Tvar v ->
      assert false
  | Tconst c ->
      print_const c
  | Tapp (fs, []) ->
      get_value fs.ls_name gamma builder
  | Tapp (fs, tl) ->
      assert false
  | Tif (e, t1, t2) ->
      print_if (print_term info gamma) builder (e, t1, t2)
  | Tlet (t1,tb) ->
      assert false
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

(*let print_logic_decl info (ls, ld) =*)

(** Logic Declarations *)

let logic_decl info builder d = match d.d_node with
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

let get_xs ?separator info xs = get_qident ?separator info xs.xs_name

let rec print_expr info ~raise_expr gamma e builder =
  if e.e_ghost then
    Module.unit_value
  else match e.e_node with
  | Elogic t ->
      print_term info gamma t builder
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
      print_if (print_expr info ~raise_expr gamma) builder (e0, e1, e2)
  | Eassign (pl,e,_,pv) ->
      assert false
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
      raise_expr e builder;
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
      assert false

and print_rec info gamma builder { fun_ps = ps ; fun_lambda = lam } =
  if not ps.ps_ghost then begin
    let fresh_name = Module.create_global_fresh_name () in
    Module.append_function
      (sprintf "value %s(value Param__, value Env__, struct exn **Exn__)" (Module.string_of_value fresh_name))
      (fun builder ->
         let raise_expr value builder =
           Module.append_expr
             (sprintf "*Exn__ = %s" (Module.string_of_value value))
             builder;
           Module.append_expr "return NULL" builder;
         in
         let v = print_expr info ~raise_expr gamma lam.l_expr builder in
         Module.append_expr
           (sprintf "return %s" (Module.string_of_value v))
           builder;
      );
    Module.define_global ps.ps_name.id_string;
    let value = Module.malloc_closure builder in
    Module.append_expr (sprintf "%s->f = %s" (Module.string_of_value value) (Module.string_of_value fresh_name)) builder;
    Module.append_expr (sprintf "%s->env = NULL" (Module.string_of_value value)) builder;
    Module.append_expr (sprintf "%s = %s" ps.ps_name.id_string (Module.string_of_value value)) builder;
  end

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

and print_rec_decl info gamma builder fd =
  print_rec info gamma builder fd
  (*forget_tvs ()*)

let is_ghost_lv = function
  | LetV pv -> pv.pv_ghost
  | LetA ps -> ps.ps_ghost

(* TODO: Handle driver *)
let print_exn_decl info xs =
  Module.append_global
    (sprintf "exn_tag tag_%s" (Module.string_of_value (get_xs info xs)))
    (sprintf "\"%s\"" (Module.string_of_value (get_xs ~separator:"." info xs)))

let rec pdecl info gamma builder = function
  | pd::decls ->
      Mlw_extract.check_exec_pdecl info.info_syn pd;
      begin match pd.pd_node with
      | PDtype ts ->
          (* TODO *)
          pdecl info gamma builder decls
      | PDdata tl ->
          (* TODO *)
          pdecl info gamma builder decls
      | PDval lv ->
          (* TODO *)
          pdecl info gamma builder decls
      | PDlet ld ->
          (* TODO *)
          pdecl info gamma builder decls
      | PDrec fdl ->
          (* print defined, non-ghost first *)
          let cmp {fun_ps=ps1} {fun_ps=ps2} =
            Pervasives.compare
              (ps1.ps_ghost || has_syntax info ps1.ps_name)
              (ps2.ps_ghost || has_syntax info ps2.ps_name) in
          let fdl = List.sort cmp fdl in
          List.iter (print_rec_decl info gamma builder) fdl;
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
