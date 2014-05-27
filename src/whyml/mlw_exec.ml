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
open Ident
open Mlw_decl
open Mlw_expr
open Mlw_ty

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

let is_exec_logic (_, ld) =
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

let rec check_exec_expr e =
  if not e.e_ghost then
    match e.e_node with
    | Elogic t ->
        if not (is_exec_term t) then
          Loc.errorm ?loc:e.e_loc "Cannot use logical terms in program";
    | Evalue _
    | Earrow _ ->
        ()
    | Elet ({let_expr = e1; _}, e2) ->
        check_exec_expr e1;
        check_exec_expr e2;
    | Eapp (e, _, _) ->
        check_exec_expr e
    | Erec (fdl, e) ->
        let aux f = check_exec_expr f.fun_lambda.l_expr in
        List.iter aux fdl;
        check_exec_expr e
    | Eif (e0, e1, e2) ->
        check_exec_expr e0;
        check_exec_expr e1;
        check_exec_expr e2;
    | Ecase (e1, bl) ->
        let aux (_, e) = check_exec_expr e in
        check_exec_expr e1;
        List.iter aux bl;
    | Eassign (_, e, _, _) ->
        check_exec_expr e;
    | Eghost _ ->
        assert false
    | Eany _ ->
        Loc.errorm ?loc:e.e_loc "Cannot use 'any' in programs"
    | Eloop (_, _, e) ->
        check_exec_expr e;
    | Efor (_, _, _, e) ->
        check_exec_expr e;
    | Eraise (_, e) ->
        check_exec_expr e;
    | Etry (e, bl) ->
        let aux (_, _, e) = check_exec_expr e in
        check_exec_expr e;
        List.iter aux bl
    | Eabstr (e,_) ->
        check_exec_expr e;
    | Eassert _
    | Eabsurd ->
        ()

let check_exec_pdecl syn pd = match pd.pd_node with
  | PDtype _
  | PDexn _
  | PDdata _ ->
      ()
  | PDlet {let_sym = lv; _}
  | PDval lv when is_ghost_lv lv ->
      ()
  | PDval (LetV {pv_vs = {vs_name = name}; _} | LetA {ps_name = name; _}) ->
      if not (has_syntax syn name) then
        Loc.errorm ?loc:name.id_loc "Value '%s' not defined" name.id_string;
  | PDlet ld ->
      check_exec_expr ld.let_expr
  | PDrec fdl ->
      let aux f = check_exec_expr f.fun_lambda.l_expr in
      List.iter aux fdl
