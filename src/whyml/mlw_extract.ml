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

let (mark_lsymbol, is_exec_lsymbol, get_htbl_length) =
  let marked_idents = Hls.create 30 in
  let mark_ident syn ls =
    if not (Hls.mem marked_idents ls) then
      if not (has_syntax syn ls.ls_name) then
        Hls.add marked_idents ls ()
  in
  let is_exec_ident x = not (Hls.mem marked_idents x) in
  (mark_ident, is_exec_ident, (fun () -> Hls.length marked_idents))

let fix f ll =
  let rec loop len =
    List.iter f ll;
    let new_len = get_htbl_length () in
    if len <> new_len then
      loop new_len
  in
  loop (get_htbl_length ())

let is_exec_const = function
  | Number.ConstInt _ -> true
  | Number.ConstReal _ -> false

let rec is_exec_term t = match t.t_node with
  | Ttrue
  | Tfalse ->
      true
  | Tvar _ ->
      true
  | Tconst c ->
      is_exec_const c
  | Tapp (f, tl) ->
      is_exec_lsymbol f && List.for_all is_exec_term tl
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

let is_exec_logic ld =
  let (_, e) = open_ls_defn ld in
  is_exec_term e

let get_exec_decl syn d =
  match d.d_node with
    | Dtype _
    | Ddata _ ->
        Some d
    | Dparam ls ->
        mark_lsymbol syn ls;
        None
    | Dlogic ll ->
        let aux (ls, ld) =
          let res = is_exec_logic ld in
          if not res then
            mark_lsymbol syn ls;
        in
        fix aux ll;
        begin match List.filter (fun (ls, _) -> is_exec_lsymbol ls) ll with
        | [] -> None
        | ll -> Some (create_logic_decl ll)
        end
    | Dind (_, l) ->
        List.iter (fun (ls, _) -> mark_lsymbol syn ls) l;
        None
    | Dprop (_, _, _) ->
        None (* Using prop in code cannot happend *)

let rec check_exec_expr e =
  if not e.e_ghost then
    match e.e_node with
    | Elogic t ->
        if not (is_exec_term t) then
          Loc.errorm
            ?loc:e.e_loc
            "Cannot use non-executable logical terms in program";
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
