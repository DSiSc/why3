(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require Reals.Rbasic_fun.
Require Reals.R_sqrt.
Require Reals.Rtrigo_def.
Require Reals.Rtrigo1.
Require Reals.Ratan.
Require BuiltIn.
Require real.Real.
Require real.RealInfix.
Require real.Abs.
Require real.FromInt.
Require int.Int.
Require real.Square.
Require real.Trigonometry.
Require floating_point.Rounding.
Require floating_point.SingleFormat.
Require floating_point.Single.

(* Why3 assumption *)
Definition unit := unit.

Require Import Interval_tactic.


(* Why3 goal *)
Theorem WP_parameter_my_cosine : forall (x:floating_point.SingleFormat.single),
  ((Reals.Rbasic_fun.Rabs (floating_point.Single.value x)) <= (1 / 32)%R)%R ->
  ((Reals.Rbasic_fun.Rabs ((1%R - (((floating_point.Single.value x) * (floating_point.Single.value x))%R * (05 / 10)%R)%R)%R - (Reals.Rtrigo_def.cos (floating_point.Single.value x)))%R) <= (1 / 16777216)%R)%R.
(* Why3 intros x h1. *)
(* YOU MAY EDIT THE PROOF BELOW *)
intros x H.
interval with (i_bisect_diff (Single.value x)).
Qed.

