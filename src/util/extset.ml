(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

module type S = Map_intf.Set

module MakeOfMap (M: Extmap.S) = struct
  module M = M
  type elt = M.key
  type t = unit M.t

  let is_true b = if b then Some () else None

  let empty = M.empty
  let is_empty = M.is_empty
  let mem = M.mem
  let add e s = M.add e () s
  let singleton e = M.singleton e ()
  let remove = M.remove
  let merge f s t =
    M.merge (fun e a b -> is_true (f e (a <> None) (b <> None))) s t
  let compare = M.set_compare
  let equal = M.set_equal
  let subset = M.set_submap
  let disjoint = M.set_disjoint
  let iter f s = M.iter (fun e _ -> f e) s
  let fold f s acc = M.fold (fun e _ -> f e) s acc
  let for_all f s = M.for_all (fun e _ -> f e) s
  let exists f s = M.exists (fun e _ -> f e) s
  let filter f s = M.filter (fun e _ -> f e) s
  let partition f s = M.partition (fun e _ -> f e) s
  let cardinal = M.cardinal
  let elements = M.keys
  let min_elt t = fst (M.min_binding t)
  let max_elt t = fst (M.max_binding t)
  let choose t = fst (M.choose t)
  let split e t = let l,m,r = M.split e t in l,(m <> None),r
  let change f x s = M.change (fun a -> is_true (f (a <> None))) x s
  let union = M.set_union
  let inter = M.set_inter
  let diff = M.set_diff
  let fold_left f acc s = M.fold_left (fun acc k () -> f acc k) acc s
  let fold2_inter f s t acc = M.fold2_inter (fun k _ _ acc -> f k acc) s t acc
  let fold2_union f s t acc = M.fold2_union (fun k _ _ acc -> f k acc) s t acc
  let translate = M.translate
  let add_new e x s = M.add_new e x () s
  let is_num_elt n m = M.is_num_elt n m
  let of_list l = List.fold_left (fun acc a -> add a acc) empty l
end

module Make(Ord: Map_intf.OrderedType) = MakeOfMap(Extmap.Make(Ord))
