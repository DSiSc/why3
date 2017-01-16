(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Ty
open Term
open Decl
open Theory

let meta_keep_lit = register_meta "literal:keep" [MTtysymbol]
  ~desc:"Preserve@ literals@ of@ a@ given@ type."

let add_literal (known_lit, decl as acc) t c ls_proj =
  try acc, Mterm.find t known_lit with Not_found ->
  (* TODO: pretty-print the constant to have a readable name *)
  let ls = create_lsymbol (id_fresh "dummy") [] t.t_ty in
  let ls_decl = create_param_decl ls in
  let pr = create_prsymbol (id_derive "_axiom" ls.ls_name) in
  let ls_t = t_app ls [] t.t_ty in
  let f = t_app ls_proj [ls_t] ls_proj.ls_value in
  let f = t_equ f (t_const c (Opt.get f.t_ty)) in
  let ax_decl = create_prop_decl Paxiom pr f in
  let decl = ax_decl::ls_decl::decl in
  (Mterm.add t ls_t known_lit, decl), ls_t

(* TODO: remove int and real literals if not supported.
   NOTE: in this case, [add_literal] above is incorrect. *)
let rec abstract_terms kn metas type_kept acc t =
  match t.t_node, t.t_ty with
  | Tconst (Number.ConstInt _ as c), Some {ty_node = Tyapp (ts,[])}
    when not (ts_equal ts ts_int || Sts.mem ts type_kept) ->
    let (to_int,_,_) = Mts.find ts metas in
    add_literal acc t c to_int
  | Tconst (Number.ConstReal _ as c), Some {ty_node = Tyapp (ts,[])}
    when not (ts_equal ts ts_real || Sts.mem ts type_kept) ->
      let fi = Opt.get (find_float_decl kn ts) in
      add_literal acc t c fi.float_to_real
  | _ ->
      t_map_fold (abstract_terms kn metas type_kept) acc t

let elim le_int le_real abs_real type_kept kn metas d (known_lit,task) =
  match d.d_node with
  | Dtype ts when Mts.exists (fun ts' _ -> ts_equal ts ts') metas && not (Sts.mem ts type_kept) ->
    let (to_int,lo,hi) = Mts.find ts metas in
    let lo,hi = Number.int_const_dec lo, Number.int_const_dec hi in
    let ty_decl = create_ty_decl ts in
    let ls_decl = create_param_decl to_int in
    let pr = create_prsymbol (id_derive "_axiom" ts.ts_name) in
    (* TODO: why call it dummy? *)
    let v = create_vsymbol (id_fresh "dummy") (ty_app ts []) in
    let v_term = t_app to_int [t_var v] (Some ty_int) in
    let a_term = t_const (Number.ConstInt lo) ty_int in
    let b_term = t_const (Number.ConstInt hi) ty_int in
    let f = t_and (t_app le_int [a_term; v_term] None)
                  (t_app le_int [v_term; b_term] None)
    in
    let f = t_forall_close [v] [] f in
    let ax_decl = create_prop_decl Paxiom pr f in
    (known_lit, List.fold_left Task.add_decl task [ty_decl; ls_decl; ax_decl])
  | Dfloat fi when not (Sts.mem fi.float_ts type_kept) ->
    (* declare abstract type [t] *)
    let ty_decl = create_ty_decl fi.float_ts in
    (* declare projection to_real *)
    let proj_decl = create_param_decl fi.float_to_real in
    (* declare predicate is_finite *)
    let isFinite_decl = create_param_decl fi.float_is_finite in
    (* create defining axiom *)
    (* [forall v:t. is_finite v -> | to_real v | <= max] *)
    let pr = create_prsymbol (id_derive "_axiom" fi.float_ts.ts_name) in
    let v = create_vsymbol (id_fresh "dummy") (ty_app fi.float_ts []) in
    let v_term = t_app fi.float_to_real [t_var v] (Some ty_real) in
    (* compute max *)
    let emax = BigInt.pow_int_pos_bigint 2 (BigInt.pred fi.float_eb_val) in
    let m = BigInt.pred (BigInt.pow_int_pos_bigint 2 fi.float_sb_val) in
    let e = BigInt.sub emax fi.float_sb_val in
    Number.print_in_base 16 None Format.str_formatter m;
    let m_string = Format.flush_str_formatter () in
    Number.print_in_base 10 None Format.str_formatter e;
    let e_string = Format.flush_str_formatter () in
    let term = t_const (Number.ConstReal
      (Number.real_const_hex m_string "" (Some e_string))) ty_real in
    (* compose axiom *)
    let f = t_app le_real [t_app abs_real [v_term] (Some ty_real); term] None in
    let f = t_implies (t_app fi.float_is_finite [t_var v] None) f in
    let f = t_forall_close [v] [] f in
    let ax_decl = create_prop_decl Paxiom pr f in
    (known_lit, List.fold_left Task.add_decl task
       [ty_decl; proj_decl; isFinite_decl; ax_decl])
  | _ ->
    let (known_lit, local_decl), d =
      decl_map_fold (abstract_terms kn metas type_kept) (known_lit,[]) d in
    let t = List.fold_left Task.add_decl task (List.rev local_decl) in
    (known_lit, Task.add_decl t d)

let eliminate le_int le_real abs_real type_kept metas t (known_lit, acc) =
  match t.Task.task_decl.td_node with
  | Decl d ->
    elim le_int le_real abs_real type_kept
      t.Task.task_known metas d (known_lit, acc)
  | Use _ | Clone _ | Meta _ ->
    known_lit, Task.add_tdecl acc t.Task.task_decl

let eliminate_literal env =
  (* FIXME: int.Int.le_sym should be imported in the task *)
  let th = Env.read_theory env ["int"] "Int" in
  let le_int = ns_find_ls th.th_export ["infix <="] in
  let th = Env.read_theory env ["real"] "Real" in
  let le_real = ns_find_ls th.th_export ["infix <="] in
  let th = Env.read_theory env ["real"] "Abs" in
  let abs_real = ns_find_ls th.th_export ["abs"] in
  Trans.on_meta meta_range (fun metas ->
      let metas = List.fold_left (fun acc meta_arg ->
          match meta_arg with
          | [MAts ts; MAls to_int; MAstr lo; MAstr hi] ->
            Mts.add ts (to_int,lo,hi) acc
          | _ -> assert false) Mts.empty metas in
      Trans.on_tagged_ts meta_keep_lit
        (fun type_kept ->
           Trans.fold_map
             (eliminate le_int le_real abs_real type_kept metas)
             Mterm.empty None))

let () =
  Trans.register_env_transform "eliminate_literal" eliminate_literal
    ~desc:"Eliminate@ unsupported@ literals."
