(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Term
open Decl

(** Remove trivial assignments TODO *)

(** Auxiliary function TODO *)

(* Try to apply f recursively on every subterm of t until it succeed in which
   case it stops and replace the current term its application to f inside t. *)
let rec t_map (f: term -> term option) (t: term) =
  match f t with
  | None -> Term.t_map (t_map f) t
  | Some t' -> t'

(* Return list of binded variables *)
let fmla_remove_quant f =

  let rec fold_fun vsl f =
    match f.t_node with
    | Tquant (Tforall, fb) ->
        (* Triggers are not needed. This term won't be rebuild in a non-fully
           instantiated version anyway *)
        let vsl', _, f' = t_open_quant fb in
        fold_fun (vsl' @ vsl) f'
    | _ -> vsl, f
  in
  fold_fun [] f

(* Returns a list of variable, substituted terms as returned by trivial equality
   in the form of (v = t \/ v1 = t2 \/ t3) *)
let rec try_split_if vsl f_if =
  match f_if.t_node with
  | Tbinop (Tor, f1, f2) ->
      try_split_if vsl f1 @ try_split_if vsl f2
  | Tapp (ps_equ, [{t_node = Tvar v}; t]) |
    Tapp (ps_equ, [t; {t_node = Tvar v}])
    when List.mem v vsl ->
      [v, t]
  | _ -> []

(* Recursively collect trivial substitution found inside if terms.
   if (v = t \/ v1 = t1) then
     if (v4 = t2 \/ v5 = t3) then
   Collects these and create the appropriate substitutions. In this case we
   create 4: (v <- t, v4 <- t2) :: (v <- t, v5 <- t3) :: (v1 <- t1, v4 <- t2) ::
   (v1 <- t1, v5 <- t3)
*)
let rec collect_if_clauses vsl f =
  match f.t_node with
  | Tif (f_if, f_then, f_else) ->
    let ldisjoint: (vsymbol * Term.term) list = try_split_if vsl f_if in
    let l_acc_then = collect_if_clauses vsl f_then in
    let l_acc_else = collect_if_clauses vsl f_else in
    List.fold_left (fun (acc: (Term.term Mvs.t * Term.term) list) x ->
      acc @ (List.map (fun (m, f_last) -> Mvs.add (fst x) (snd x) m, f_last) l_acc_then))
      l_acc_else ldisjoint
  | _ -> [Mvs.empty, f]

exception Error

let collect_if_clauses vsl f =
  match f.t_node with
  | Tif _ ->
      collect_if_clauses vsl f
  | _ -> raise Error

(* TODO vsl not used but maybe we should check that it corresponds to m *)
let rebuild_term (m: term Mvs.t) vsl f =
  try
    (* TODO check that this is correct *)
    Some (t_subst m f)
  with
    (* TODO find the exception from Term.ml *)
    _ -> None

let rebuild_term_list (l: (term Mvs.t * term) list) vsl f =
  let inst_formula =
    List.fold_left (fun t_uc (mvs, t) ->
                   match rebuild_term mvs vsl t with
                   | Some new_f -> t_and_simp t_uc new_f
                   | None -> t_uc)
      t_true l
  in
  if inst_formula = t_true then
    None
  else
    Some (t_and_simp inst_formula f)

let simplify_quant_eq f =
  try
    let vsl, f_fq = fmla_remove_quant f in
    let subst_term_list = collect_if_clauses vsl f_fq in
    rebuild_term_list subst_term_list vsl f
  with _ -> None

let tr = Trans.rewrite (t_map simplify_quant_eq) None

let () = Trans.register_transform
  "simplify_quant_eq"
   tr
  ~desc:"TODO"

(*

phi : int -> int -> bool =
forall temp___428 temp___429: int.
    if temp____428 = 0 then
      if temp___429 = 2 \/ temp___429 = 3 then
        unknown1
      else
        if temp___429 = 1 then
          unknown2
        else
          if temp___429 = 0 then
            unknown3
          else
            unknown4
    else
      unknown5

translate into

unknown1[temp___428 <- 0, temp___429 <- 2] /\
unknown1[temp___428 <- 0, temp___429 <- 3] /\
forall temp___428. if temp___428 != 0 then unknown2[temp___429 <-1] /\
forall temp___428. if temp___428 != 0 then unknown3[temp___429 <-0] /\
forall temp___428. if temp___428 != 0 /\ temp___429 != 0 et != 1 then unknown4 /\
forall temp___428 temp___429. if temp___428 != 0 then unknown5


 (forall temp___428 temp___429 : int.
     (if (temp___428 = 0) then (
      (if ((temp___429 = 2 \/ (temp___429 = 3) )) then (
       ((Array__Int_Int__Array_aggregates__enum_t.get temp___423 temp___428 temp___429) = (Array_aggregates__enum_t__rep.of_rep temp___426)))
      else if ((temp___429 = 1)) then (
       ((Array__Int_Int__Array_aggregates__enum_t.get temp___423 temp___428 temp___429) = (Array_aggregates__enum_t__rep.of_rep temp___425)))  else if ((temp___429 = 0)) then (
       ((Array__Int_Int__Array_aggregates__enum_t.get temp___423 temp___428 temp___429) = (Array_aggregates__enum_t__rep.of_rep temp___424))) else (
       true))) else (
      ((Array__Int_Int__Array_aggregates__enum_t.get temp___423 temp___428 temp___429) = (Array_aggregates__enum_t__rep.of_rep temp___427)))))))
  )
*)
