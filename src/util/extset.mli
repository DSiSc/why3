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

(** Sets over ordered types *)

module type S = Map_intf.Set

module MakeOfMap (M : Extmap.S) : S with module M = M
(** Functor building an implementation of the set structure
    given a totally ordered type. *)

module Make (Ord : Map_intf.OrderedType) : S with type M.key = Ord.t
(** Functor building an implementation of the set structure
    given a totally ordered type. *)
