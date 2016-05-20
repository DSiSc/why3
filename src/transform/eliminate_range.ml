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

let meta_keep_float = Theory.register_meta "float:keep" [Theory.MTtysymbol]
  ~desc:"Keep@ float@ type."

let elim_range le_int prs d = match d.d_node with
  | Drange ri when not (Sts.mem ri.range_ts prs) ->
    let ty_decl = create_ty_decl ri.range_ts in
    let ls_decl = create_param_decl ri.range_proj in
    let pr = create_prsymbol (id_derive "_axiom" ri.range_ts.ts_name) in
    let v = create_vsymbol (id_fresh "dummy") (ty_app ri.range_ts []) in
    let v_term = t_app ri.range_proj [t_var v] (Some ty_int) in
    let a_term = t_const (Number.ConstInt ri.range_low_cst) in
    let b_term = t_const (Number.ConstInt ri.range_high_cst) in
    let f = t_and (t_app le_int [a_term; v_term] None)
                  (t_app le_int [v_term; b_term] None)
    in
    let f = t_forall_close [v] [] f in
    let ax_decl = create_prop_decl Paxiom pr f in
    [ty_decl; ls_decl; ax_decl]
  | _ -> [d]

let elim_float le_real abs_real prs d = match d.d_node with
  | Dfloat fi when not (Sts.mem fi.float_ts prs) ->
    let ty_decl = create_ty_decl fi.float_ts in
    let proj_decl = create_param_decl fi.float_proj in
    let isFinite_decl = create_param_decl fi.float_isFinite in
    let get_rep_decl = create_param_decl fi.float_get_rep in
    let pr = create_prsymbol (id_derive "_axiom" fi.float_ts.ts_name) in
    let v = create_vsymbol (id_fresh "dummy") (ty_app fi.float_ts []) in
    let v_term = t_app fi.float_proj [t_var v] (Some ty_real) in
    let emax = BigInt.pow_int_pos_bigint 2 (BigInt.pred fi.float_eb_val) in
    let m = BigInt.pred (BigInt.pow_int_pos_bigint 2 fi.float_sb_val) in
    let e = BigInt.sub emax fi.float_sb_val in
    Number.print_in_base 16 None Format.str_formatter m;
    let m_string = Format.flush_str_formatter () in
    Number.print_in_base 10 None Format.str_formatter e;
    let e_string = Format.flush_str_formatter () in
    let term = t_const
        (Number.ConstReal
           (Number.real_const_hex m_string "" (Some e_string))) in
    let f = t_app le_real [t_app abs_real [v_term] (Some ty_real); term] None
    in
    let f = t_implies (t_app fi.float_isFinite [t_var v] None) f in
    let f = t_forall_close [v] [] f in
    let ax_decl = create_prop_decl Paxiom pr f in
    [ty_decl; proj_decl; isFinite_decl; get_rep_decl; ax_decl]
  | _ -> [d]

let eliminate_range env =
  (* FIXME: int.Int.le_sym should be imported in the task *)
  let th = Env.read_theory env ["int"] "Int" in
  let le_int = Theory.ns_find_ls th.Theory.th_export ["infix <="] in
  let th = Env.read_theory env ["real"] "Real" in
  let le_real = Theory.ns_find_ls th.Theory.th_export ["infix <="] in
  let th = Env.read_theory env ["real"] "Abs" in
  let abs_real = Theory.ns_find_ls th.Theory.th_export ["abs"] in
  Trans.seq
    [Trans.on_tagged_ts meta_keep_range
       (fun tss ->
          Trans.decl (elim_range le_int tss) None);
     Trans.on_tagged_ts meta_keep_float
       (fun tss ->
          Trans.decl (elim_float le_real abs_real tss) None)]

let () =
  Trans.register_env_transform "eliminate_range" eliminate_range
    ~desc:"Eliminate@ range@ types.";
