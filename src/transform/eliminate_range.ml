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

let meta_keep_range = Theory.register_meta "range:keep" [Theory.MTtysymbol]
  ~desc:"Keep@ range@ type."

let elim le_sym prs d = match d.d_node with
  | Drange ri when not (Sts.mem ri.range_ts prs) ->
    let ty_decl = create_ty_decl ri.range_ts in
    let ls_decl = create_param_decl ri.range_proj in
    let pr = create_prsymbol (id_derive "_axiom" ri.range_ts.ts_name) in
    let v = create_vsymbol (id_fresh "dummy") (ty_app ri.range_ts []) in
    let v_term = t_app ri.range_proj [t_var v] (Some ty_int) in
    let a_term = t_const (Number.ConstInt ri.range_low_cst) in
    let b_term = t_const (Number.ConstInt ri.range_high_cst) in
    let f = t_and (t_app le_sym [a_term; v_term] None)
                  (t_app le_sym [v_term; b_term] None)
    in
    let f = t_forall_close [v] [] f in
    let ax_decl = create_prop_decl Paxiom pr f in
    [ty_decl; ls_decl; ax_decl]
  | _ -> [d]

let eliminate_range env =
  (* FIXME: int.Int.le_sym should be imported in the task *)
  let th = Env.read_theory env ["int"] "Int" in
  let le_sym = Theory.ns_find_ls th.Theory.th_export ["infix <="] in
  Trans.on_tagged_ts meta_keep_range
    (fun tss ->
       Trans.decl (elim le_sym tss) None)

let () =
  Trans.register_env_transform "eliminate_range" eliminate_range
    ~desc:"Eliminate@ range@ types.";
