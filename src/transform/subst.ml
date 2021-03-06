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

open Term
open Decl
open Generic_arg_trans_utils
open Args_wrapper

(* transformations "subst" and "subst_all" *)

let debug_subst = Debug.register_flag "subst" ~desc:"debug transformations subst and subst_all"

let rec subst_in_term sigma t =
  match t.t_node with
  | Tapp(ls,[]) ->
     begin
       try Mls.find ls sigma
       with Not_found -> t
     end
  | _ -> t_map (subst_in_term sigma) t

let subst_in_def sigma ls (d:ls_defn) =
  let (vl,t) = open_ls_defn d in
  make_ls_defn ls vl (subst_in_term sigma t)


(* [apply_subst prs sigma] is a transformation that operates on each decls.

   for each decl:

   - if d is a prop whose prsymbol belongs to prs, then it is removed

   - if d is a declaration of a constant symbol in the domain of sigma
     then it is removed

   - otherwise d is rewritten using the substitution sigma

   in [sigma], the right hand sides must not contain any symbols
   appearing in the left-hand-side

 *)
let _apply_subst ((prs,sigma) : (Spr.t * term Mls.t)) : Task.task Trans.trans =
  Trans.decl
    (fun d ->
     match d.d_node with
     | Dprop(_k,pr,_t) when Spr.mem pr prs -> []
     | Dprop(k,pr,t) -> [create_prop_decl k pr (subst_in_term sigma t)]
     | Dparam ls -> if Mls.mem ls sigma then [] else [d]
     | Dlogic ld ->
        let ld' =
          List.fold_right
            (fun (ls,ld) acc ->
             if Mls.mem ls sigma then acc
             else (subst_in_def sigma ls ld)::acc)
            ld
            []
        in
        begin
          match ld' with
          | [] -> []
          | _ -> [create_logic_decl ld']
        end
     | Dind ((is: ind_sign), (ind_list: ind_decl list)) ->
        let ind_list =
          List.map (fun ((ls: lsymbol), (idl: (prsymbol * term) list)) ->
                    let idl = List.map (fun (pr, t) -> (pr, subst_in_term sigma t)) idl in
                    (ls, idl)) ind_list
        in
        [create_ind_decl is ind_list]
     | Dtype _ | Ddata _ -> [d])
    None


let apply_subst ((prs,sigma) : (Spr.t * term Mls.t)) (tdl:Theory.tdecl list) : Task.task =
  let rec aux tdl tuc postponed =
    match tdl with
    | [] -> assert false
    | td :: rem ->
       match td.Theory.td_node with
       | Theory.Decl d ->
          begin
            match d.d_node with
            | Dprop(Pgoal,pr,t) ->
               begin match postponed with
                     | [] ->
                        let d = create_prop_decl Pgoal pr (subst_in_term sigma t) in
                        let td = Theory.create_decl d in
Task.add_tdecl tuc td
                     | _ -> raise (Arg_trans "apply_subst failed")
               end
            | Dprop(_k,pr,_t) when Spr.mem pr prs ->
               aux rem tuc postponed
            | Dprop(k,pr,t) ->
               let d = create_prop_decl k pr (subst_in_term sigma t) in
               let td = Theory.create_decl d in
               begin
                 match Task.add_tdecl tuc td with
                 | tuc ->
                     aux rem tuc postponed
                 | exception _ ->
                   aux rem tuc (td::postponed)
               end
            | Dparam ls ->
               if Mls.mem ls sigma then aux rem tuc postponed
               else let tuc = Task.add_decl tuc d in
                    aux (List.rev_append postponed rem) tuc []
          | Dlogic ld ->
             let ld' =
               List.fold_right
                 (fun (ls,ld) acc ->
                  if Mls.mem ls sigma then acc
                  else (subst_in_def sigma ls ld)::acc)
                 ld
                 []
             in
             begin
               match ld' with
               | [] -> aux rem tuc postponed
               | _ ->
                  let d = Theory.create_decl (create_logic_decl ld') in
                  begin
                    match Task.add_tdecl tuc d with
                    | tuc ->
                        aux (List.rev_append postponed rem) tuc []
                    | exception _ ->
                                aux rem tuc (d::postponed)
                  end
             end
          | Dind ((is: ind_sign), (ind_list: ind_decl list)) ->
             let ind_list =
               List.map (fun ((ls: lsymbol), (idl: (prsymbol * term) list)) ->
                         let idl = List.map (fun (pr, t) -> (pr, subst_in_term sigma t)) idl in
                         (ls, idl)) ind_list
             in
             let d = create_ind_decl is ind_list in
             let td = Theory.create_decl d in
             begin
               try let tuc = Task.add_tdecl tuc td in
                   aux (List.rev_append postponed rem) tuc []
               with _ -> aux rem tuc (td::postponed)
             end
          | Dtype _
          | Ddata _ ->
             let tuc = Task.add_decl tuc d in
             aux (List.rev_append postponed rem) tuc []

        end
     | _ -> aux rem (Task.add_tdecl tuc td) postponed
  in
  aux tdl None []

let rec occurs_in_term ls t =
  match t.t_node with
  | Tapp(ls',[]) when ls_equal ls' ls -> true
  | _ -> t_any (occurs_in_term ls) t


(* [find_equalities filter t] searches in task [t] for equalities of
   the form constant = term or term = constant, where constant does
   not occur in the term.  That function returns first the set of
   prsymbols for the equalities found, and second a map from the
   lsymbols of the constant to the associated term. That map is
   normalized in the sense that the terms on the right are fully
   substituted, for example if the equalities "x=t" and "y=x+u" are
   found, then the map contains "x -> t" and "y ->t+u".  The [filter]
   function applys a generic filter to the constants that can be taken
   into consideration.  if several equalities occur for the same
   constant, the first one is considered.
 *)
let find_equalities filter =
  Trans.fold_decl
    (fun d ((prs,sigma) as acc) ->
     match d.d_node with
     | Dprop (Pgoal, _, _) -> acc
     | Dprop (_, pr, t) ->
        begin
          match t.t_node with
          | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
             begin
               try match t1.t_node with
               | Tapp (ls, []) when
                      filter ls &&
                        not (Mls.mem ls sigma) ->
                  let t2' = subst_in_term sigma t2 in
                  if occurs_in_term ls t2' then raise Exit
                  else
                    let () = Debug.dprintf debug_subst "selected: %a -> %a@."
                                           Pretty.print_ls ls Pretty.print_term t2' in
                    let sigma' = Mls.add ls t2' Mls.empty in
                    let sigma = Mls.map (subst_in_term sigma') sigma in
                    (Spr.add pr prs, Mls.add ls t2' sigma)
               | _ -> raise Exit
               with Exit ->
                    match t2.t_node with
                    | Tapp (ls, []) when
                           filter ls &&
                             not (Mls.mem ls sigma) ->
                       let t1' = subst_in_term sigma t1 in
                       if occurs_in_term ls t1' then acc
                       else
                         let () = Debug.dprintf debug_subst "selected: %a -> %a@."
                                                Pretty.print_ls ls Pretty.print_term t1' in
                         let sigma' = Mls.add ls t1' Mls.empty in
                         let sigma = Mls.map (subst_in_term sigma') sigma in
                         (Spr.add pr prs, Mls.add ls t1' sigma)
                    | _ -> acc
             end
          | _ -> acc
        end
     | Dlogic ld ->
        List.fold_left
          (fun ((prs,sigma) as acc) (ls,ld) ->
           if filter ls then
             let vl, t = open_ls_defn ld in
             if vl = [] && not (occurs_in_term ls t) then
               let t = subst_in_term sigma t in
               (prs, Mls.add ls t sigma)
             else acc
           else acc)
          acc
          ld
     | Ddata _ | Dtype _ | Dparam _ | Dind _ -> acc)
    (Spr.empty, Mls.empty)

let get_decls =
  Trans.fold (fun th acc -> th.Task.task_decl :: acc) []

let apply_subst x t =
  apply_subst x (List.rev (Trans.apply get_decls t))

let subst_all =
  Trans.bind (find_equalities (fun _ -> true))
             (fun x -> Trans.store (apply_subst x))

let () =
  wrap_and_register ~desc:"substitutes with all equalities between a constant and a term"
    "subst_all"
    (Ttrans) subst_all

let subst tl =
  let to_subst =
    List.fold_left
      (fun acc t ->
       match t.t_node with
       | Tapp (ls, []) -> Sls.add ls acc
       | _ -> raise (Arg_trans "subst: %a is not a constant")) Sls.empty tl
  in
  Trans.bind (find_equalities (fun ls -> Sls.mem ls to_subst))
             (fun x -> Trans.store (apply_subst x))

let () =
  wrap_and_register ~desc:"substitutes with all equalities involving one of the given constants"
    "subst"
    (Ttermlist Ttrans) subst


(*
(* This found any equality which at one side contains a single lsymbol and is
   local. It gives same output as found_eq. *)
let find_eq2 is_local_decl =
    Trans.fold_decl (fun d acc ->
      match d.d_node with
      | Dprop (k, pr, t) when k != Pgoal && is_local_decl d ->
        begin
          let acc = (match t.t_node with
          | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
            (match t1.t_node, t2.t_node with
            | Tapp (_, []), _ ->
                Some (Some pr, t1, t2)
            | _, Tapp (_, []) ->
                Some (Some pr, t2, t1)
            | _ -> acc)
          | _ -> acc) in
          acc
        end
      | Dlogic [(ls, ld)] when is_local_decl d ->
        (* Function without arguments *)
        let vl, e = open_ls_defn ld in
        if vl = [] then
          Some (None, t_app_infer ls [], e)
        else
          acc
      | _ -> acc) None

let subst_eq found_eq =
  match found_eq with
    | None -> raise (Arg_trans "subst_eq")
    | Some (Some pr_eq, t1, t2) ->
      begin
        Trans.decl (fun d ->
          match d.d_node with
          (* Remove equality over which we subst *)
          | Dprop (_k, pr, _t) when pr_equal pr pr_eq  ->
            []
          (* Replace in all hypothesis *)
          | Dprop (kind, pr, t) ->
            [create_prop_decl kind pr (t_replace t1 t2 t)]
          | Dlogic ldecl_list ->
            let ldecl_list =
              List.map (fun (ls, ls_def) ->
                let (vl, t) = open_ls_defn ls_def in
                make_ls_defn ls vl (t_replace t1 t2 t)) ldecl_list
            in
            [create_logic_decl ldecl_list]

          (* TODO unbelievably complex for something that simple... *)
          | Dind ((is: ind_sign), (ind_list: ind_decl list)) ->
            let ind_list: ind_decl list =
              List.map (fun ((ls: lsymbol), (idl: (prsymbol * term) list)) ->
                let idl = List.map (fun (pr, t) -> (pr, t_replace t1 t2 t)) idl in
                (ls, idl)) ind_list
            in
            [create_ind_decl is ind_list]

          | Dtype _ | Ddata _ | Dparam _ -> [d]) None
      end
    | Some (None, t1, t2) ->
      begin
         Trans.decl (fun d ->
           match d.d_node with
           | Dlogic [(ls, _ld)] when try (t1 = Term.t_app_infer ls []) with _ -> false ->
              []
           (* Replace in all hypothesis *)
           | Dprop (kind, pr, t) ->
             [create_prop_decl kind pr (t_replace t1 t2 t)]

          | Dlogic ldecl_list ->
            let ldecl_list =
              List.map (fun (ls, ls_def) ->
                let (vl, t) = open_ls_defn ls_def in
                make_ls_defn ls vl (t_replace t1 t2 t)) ldecl_list
            in
            [create_logic_decl ldecl_list]

          (* TODO unbelievably complex for something that simple... *)
          | Dind ((is: ind_sign), (ind_list: ind_decl list)) ->
            let ind_list: ind_decl list =
              List.map (fun ((ls: lsymbol), (idl: (prsymbol * term) list)) ->
                let idl = List.map (fun (pr, t) -> (pr, t_replace t1 t2 t)) idl in
                (ls, idl)) ind_list
            in
            [create_ind_decl is ind_list]

          | Dtype _ | Ddata _ | Dparam _ -> [d]) None
       end

let subst_eq_list (found_eq_list, _) =
  List.fold_left (fun acc_tr found_eq ->
    Trans.compose (subst_eq found_eq) acc_tr) Trans.identity found_eq_list

let subst_all (is_local_decl: Decl.decl -> bool) =
   Trans.bind (find_eq2 is_local_decl) subst_eq

let return_local_decl task =
  let decl_list = get_local_task task in
  let is_local_decl d = List.exists (fun x -> Decl.d_equal d x) decl_list in
  is_local_decl

let return_local_decl = Trans.store return_local_decl

let subst_all = Trans.bind return_local_decl subst_all

let rec repeat f task =
  try
    let new_task = Trans.apply f task in
    (* TODO this is probably expansive. Use a checksum or an integer ? *)
    if Task.task_equal new_task task then
      raise Exit
    else
      repeat f new_task
  with
  | _ -> task

let repeat f = Trans.store (repeat f)

let subst_all = repeat subst_all

(* TODO implement subst_all as repeat subst ??? *)

let () =
  wrap_and_register ~desc:"substitute all ident equalities and remove them"
    "subst_all"
    (Ttrans) subst_all

 *)

(*********)
(* Subst *)
(*********)

    (*

(* Creation of as structure that associates the replacement of terms as a
   function of the
*)
type constant_subst_defining =
  | Cls of lsymbol
  | Cpr of prsymbol

module Csd = Stdlib.MakeMSHW (struct
  type t = constant_subst_defining
  let tag (c: t) = match c with
  | Cls ls -> ls.ls_name.Ident.id_tag
  | Cpr pr -> pr.pr_name.Ident.id_tag
end)

module Mcsd = Csd.M

(* We find the hypotheses that have a substitution equality for elements of the
   to_subst list. We check that we never take more than one equality per
   lsymbol to substitute.
*)
let find_eq_aux (to_subst: Term.lsymbol list) =
  Trans.fold_decl (fun d (acc, used) ->
    match d.d_node with
    | Dprop (k, pr, t) when k != Pgoal ->
        let acc, used = (match t.t_node with
        | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
          (* Allow to rewrite from the right *)
          begin
            match t1.t_node, t2.t_node with
            | Tapp (ls, []), _ when List.exists (ls_equal ls) to_subst &&
                                    (* Check ls is not already taken *)
                                    not (List.exists (ls_equal ls) used) ->
                Mcsd.add (Cpr pr) (t1, t2) acc, ls :: used
            | _, Tapp (ls, []) when List.exists (ls_equal ls) to_subst &&
                                    (* Check ls is not already taken *)
                                    not (List.exists (ls_equal ls) used) ->
                Mcsd.add (Cpr pr) (t2, t1) acc, ls :: used
            | _ -> acc, used
          end
        | _ -> acc, used) in
        acc, used
    | Dlogic [(ls, ld)] when List.exists (ls_equal ls) to_subst &&
                             (* Check ls is not already taken *)
                             not (List.exists (ls_equal ls) used) ->
      (* Function without arguments *)
      let vl, e = open_ls_defn ld in
      if vl = [] then
        Mcsd.add (Cls ls) (t_app_infer ls [], e) acc, ls :: used
      else
        acc, used
    | _ -> acc, used) (Mcsd.empty,[])

(* Wrap-around function to parse lsymbol instead of terms *)
let find_eq to_subst =
  let to_subst = (List.map
     (fun t -> match t.t_node with
     | Tapp (ls, []) -> ls
     | _ -> raise (Arg_trans "subst_eq")) to_subst)
  in
  find_eq_aux to_subst

(* This produce an ordered list of tdecl which is the original task minus the
   hypotheses/constants that were identified for substitution.
   This shall be done on tdecl.
*)
let remove_hyp_and_constants (replacing_hyps, used_ls) =
  (* The task_fold on tdecl is necessary as we *need* all the tdecl (in
     particular to identify local decls).
  *)
  Task.task_fold (fun (subst, list_tdecl) td ->
    match td.td_node with
    | Decl d ->
      begin
        match d.d_node with
        | Dprop (kind, pr, _t) when kind != Pgoal &&
                                    Mcsd.mem (Cpr pr) replacing_hyps ->
          let from_t, to_t = Mcsd.find (Cpr pr) replacing_hyps in
          (* TODO find a way to be more efficient than this *)
          let to_t = Generic_arg_trans_utils.replace_subst subst to_t in
          Mterm.add from_t to_t subst, list_tdecl
        | Dlogic [ls, _] when Mcsd.mem (Cls ls) replacing_hyps ->
          let from_t, to_t = Mcsd.find (Cls ls) replacing_hyps in
          (* TODO find a way to be more efficient than this *)
          let to_t = Generic_arg_trans_utils.replace_subst subst to_t in
          Mterm.add from_t to_t subst, list_tdecl
        | Dparam ls when List.exists (ls_equal ls) used_ls ->
          subst, list_tdecl
        | _ ->
          subst, (replace_tdecl subst td :: list_tdecl)
      end
    | _ -> (subst, td :: list_tdecl)
    ) (Mterm.empty, [])

let remove_hyp_and_constants (replacing_hyps, used_ls) =
  Trans.store (remove_hyp_and_constants (replacing_hyps, used_ls))

let is_goal td =
  match td.td_node with
  | Decl d ->
      begin
        match d.d_node with
        | Dprop (Pgoal, _, _) -> true
        | _ -> false
      end
  | _ -> false

(* Use the list of tdecl that should be able to be readded into a task if there
   was sufficiently few things that were removed to the task.
   To do this, we use Task.add_tdecl (because we think its the safest).
   Note that we also try to keep the order of the declarations (because
   usability). So, each time we add a new declaration, we try to add all the
   transformations that failed (supposedly because they use a variable declared
   after it).
*)
let readd_decls (list_decls, subst: tdecl list * _) =
  List.fold_left (fun (task_uc, list_to_add) (d: tdecl) ->
    let d = replace_tdecl subst d in
    let task_uc, list_to_add =
      List.fold_left (fun (task_uc, list_to_add) (d: tdecl) ->
        try
          let new_task_uc = Task.add_tdecl task_uc d in
          new_task_uc, list_to_add
        with
          (* TODO find all possible exceptions here *)
          _ -> task_uc, d :: list_to_add)
        (task_uc, []) list_to_add
    in
    (* We always need to add the goal last *)
    if is_goal d then
      if list_to_add != [] then
        raise (Arg_trans_decl ("subst_eq", list_to_add))
      else
        try
          (Task.add_tdecl task_uc d, [])
        with
        (* TODO find all possible exceptions here *)
          _ -> raise (Arg_trans_decl ("subst_eq", [d]))
    else
      try
        (Task.add_tdecl task_uc d, List.rev list_to_add)
      with
        _ -> (task_uc, List.rev (d :: list_to_add)))
    (None, []) list_decls

let readd_decls (subst, list_decls) =
  let (task, _l) = readd_decls (list_decls, subst) in
  Trans.return task

let find args = Trans.bind (find_eq args) remove_hyp_and_constants

let subst args = Trans.bind (find args) readd_decls

let () = wrap_and_register ~desc:"remove a literal using an equality on it"
    "subst"
    (Ttermlist Ttrans) subst
     *)
