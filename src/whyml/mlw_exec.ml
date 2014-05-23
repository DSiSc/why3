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

open Decl
open Term
open Ty
open Mlw_decl
open Mlw_expr
open Mlw_ty
open Mlw_ty.T

let has_syntax syn id = Ident.Mid.mem id syn

let is_ghost_lv = function
  | LetV pv -> pv.Mlw_ty.pv_ghost
  | LetA ps -> ps.ps_ghost

let (mark_idents, is_exec_ident) =
  let marked_idents = Ident.Hid.create 30 in
  let aux syn id =
    if not (has_syntax syn id) then
      Ident.Hid.add marked_idents id ()
  in
  let mark_idents syn = List.iter (aux syn) in
  let is_exec_ident x = not (Ident.Hid.mem marked_idents x) in
  (mark_idents, is_exec_ident)

let is_exec_const = function
  | Number.ConstInt _ -> true
  | Number.ConstReal _ -> false

let is_exec_pv pv =
  if pv.pv_ghost then
    true
  else
    is_exec_ident pv.pv_vs.vs_name

let rec is_exec_term t = match t.t_node with
  | Ttrue
  | Tfalse ->
      true
  | Tvar e ->
      is_exec_ident e.vs_name
  | Tconst c ->
      is_exec_const c
  | Tapp (f, tl) ->
      is_exec_ident f.ls_name && List.for_all is_exec_term tl
  | Tif (t1, t2, t3) ->
      is_exec_term t1 && is_exec_term t2 && is_exec_term t3
  | Tlet (t1, b2) ->
      is_exec_term t1 && is_exec_bound b2
  | Tcase (t1, bl) ->
      is_exec_term t1 && List.for_all is_exec_branch bl
  | Teps _ | Tquant _ ->
      false (* TODO: improve? *)
  | Tbinop (_, t1, t2) ->
      is_exec_term t1 && is_exec_term t2
  | Tnot t ->
      is_exec_term t

and is_exec_branch b =
  let _, t = t_open_branch b in is_exec_term t

and is_exec_bound b =
  let _, t = t_open_bound b in is_exec_term t

let is_exec_logic (ls, ld) =
  let (_, e) = open_ls_defn ld in
  is_exec_term e

let get_non_exec_logic_idents x =
  if is_exec_logic x then
    [(fst x).ls_name]
  else
    []

let is_exec_decl syn d =
  let idents = match d.d_node with
    | Dtype _
    | Ddata _ ->
        []
    | Dparam ls ->
        [ls.ls_name]
    | Dlogic ll ->
        List.fold_left (fun acc x -> get_non_exec_logic_idents x @ acc) [] ll
    | Dind (_, l) ->
        List.map (fun (ls, _) -> ls.ls_name) l
    | Dprop (_, _, _) ->
        [] (* Using prop in code cannot happend *)
  in
  begin match idents with
  | [] ->
      true
  | idents ->
      mark_idents syn idents;
      false
  end

let rec is_exec_expr e =
  if e.e_ghost then
    true
  else match e.e_node with
    | Elogic t ->
        is_exec_term t
    | Evalue pv ->
        is_exec_pv pv
    | Earrow a ->
        true (* TODO: Is it good ?*)
    | Elet ({let_sym = lv; _}, e2) when is_ghost_lv lv ->
        is_exec_expr e2
    | Elet ({let_expr = e1; _}, e2) ->
        is_exec_expr e1 && is_exec_expr e2
    | Eapp (e, v, _) ->
        is_exec_expr e && is_exec_pv v
    | Erec (fdl, e) ->
        let aux = function
          | {fun_ps = {ps_ghost = true; _}; _} ->
              true
          | {fun_lambda = {l_expr; _}; _} ->
              is_exec_expr l_expr
        in
        List.for_all aux fdl && is_exec_expr e
    | Eif (e0,e1,e2) ->
        is_exec_expr e0 && is_exec_expr e1 && is_exec_expr e2
    | Ecase (e1, [_,e2]) when e1.e_ghost ->
        is_exec_expr e2
    | Ecase (e1, bl) ->
        let aux (_, e) = (* TODO: Should I ignore the ghost pattern ? *)
          is_exec_expr e
        in
        is_exec_expr e1 && List.for_all aux bl
    | Eassign (pl, e, _, pv) ->
        is_exec_expr e && is_exec_pv pv
    | Eghost _ ->
        assert false
    | Eany _ ->
        false
    | Eloop (_,_,e) ->
        is_exec_expr e
    | Efor (pv,(pvfrom, _, pvto),_,e) ->
        is_exec_pv pv
        && is_exec_pv pvfrom
        && is_exec_pv pvto
        && is_exec_expr e
    | Eraise (_, e) ->
        is_exec_expr e
    | Etry (e, bl) ->
        let aux (_, _, e) = (* TODO: Should we ignore this ? *)
          is_exec_expr e
        in
        is_exec_expr e && List.for_all aux bl
    | Eabstr (e,_) ->
        is_exec_expr e
    | Eassert _ ->
        true
    | Eabsurd ->
        true

let check_exec_pdecl pd =
  let is_exec = match pd.pd_node with
    | PDtype _
    | PDdata _ ->
        false
    | PDval lv when is_ghost_lv lv ->
        true
    | PDval _ ->
        false
    | PDlet {let_sym = lv; _} when is_ghost_lv lv ->
        true
    | PDlet ld ->
        is_exec_expr ld.let_expr
    | PDrec fdl ->
        let aux = function
          | {fun_ps = {ps_ghost = true; _}; _} ->
              true
          | {fun_lambda = {l_expr; _}; _} ->
              is_exec_expr l_expr
        in
        List.for_all aux fdl
    | PDexn _ ->
        true
  in
  if not is_exec then
    failwith "Cannot use undefined identifiers in programs"
