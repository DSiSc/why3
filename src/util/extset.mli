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


module MakeOfMap (M : Map_intf.MapUnit) : S with type 'a M.t = 'a M.t
                                             and type M.key = M.key
                                             and type 'a M.data = 'a M.data
(** Functor building an implementation of the set structure
    given a totally ordered type. *)

module Make (Ord : Map_intf.OrderedType) : S with type M.key = Ord.t
(** Functor building an implementation of the set structure
    given a totally ordered type. *)

module MakeHashcons(MH:Map_intf.Map_hashcons with type 'a data = unit):
  Map_intf.Set_hashcons with type 'a M.data = unit
                         and type 'a poly = 'a MH.poly
                         and type M.key = MH.key
(** Functor building an implementation of the hasconsed set structure
    given a totally ordered hashconsed map. *)
