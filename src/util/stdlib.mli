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

(** Specific instances of Set, Map, Hashtbl on int, string, float,
    and tagged types *)

module Mint : Map_intf.PMap with type key = int
module Sint : module type of Extset.MakeOfMap(Mint)
module Hint : Exthtbl.S with type key = int

module Mstr : Map_intf.PMap with type key = string
module Sstr : module type of Extset.MakeOfMap(Mstr)
module Hstr : Exthtbl.S with type key = string

module Mfloat : Map_intf.PMap with type key = float
module Sfloat : module type of Extset.MakeOfMap(Mfloat)
module Hfloat : Exthtbl.S with type key = float

(* Set, Map, Hashtbl on structures with a unique tag *)

module type TaggedType =
sig
  type t
  val tag : t -> int
end

module type OrderedHashedType =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module OrderedHashed (X : TaggedType) :
  OrderedHashedType with type t = X.t

module OrderedHashedList (X : TaggedType) :
  OrderedHashedType with type t = X.t list

module MakeMSH (X : TaggedType) :
sig
  module M : Map_intf.PMap with type key = X.t
  module S : Map_intf.Set with type M.key = X.t
                           and type 'a M.data = 'a
                           and type 'a M.t = 'a M.t
  module H : Exthtbl.S with type key = X.t
end

module MakeMSHW (X : Weakhtbl.Weakey) :
sig
  module M : Map_intf.PMap with type key = X.t
  module S : Map_intf.Set with type M.key = X.t
                           and type 'a M.data = 'a
                           and type 'a M.t = 'a M.t
  module H : Exthtbl.S with type key = X.t
  module W : Weakhtbl.S with type key = X.t
end
