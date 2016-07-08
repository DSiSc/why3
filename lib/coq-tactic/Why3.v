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

Require Import ZArith Reals Why3.BuiltIn.

Declare ML Module "why3tac".

Why3 Translate Coq.ZArith.BinInt.Z.add => "infix +" "int.Int".

(* TODO
- declare_object
- add_poly_arity
 *)

(*
...
Why3 Translate "Coq.ZArith.BinInt.Zgt" "int.Int.(>)" from "int.Int"
...
Why3 Translate "@Coq.Init.Logic.eq ?a ?x ?y" "((=) : ?a -> ?a -> bool)"
...
Why3 Translate "@Coq.Init.Logic.False" "false"
Why3 Translate "@Coq.Init.Logic.True" "true"


mauvaise idée, car traduit vers une fonction du premier ordre
Why3 Translate "@Coq.Init.Logic.eq ?a ?x ?y" "((=) : ?a -> ?a -> bool)"
*)

(*
coqide -R ~/why3/lib/coq Why3 -R ~/why3/lib/coq-tactic/ Why3 test.v

Require Import Why3.
Require Import ZArith.

Goal (1+1 = 2)%Z.
why3 "alt-ergo".

*)
