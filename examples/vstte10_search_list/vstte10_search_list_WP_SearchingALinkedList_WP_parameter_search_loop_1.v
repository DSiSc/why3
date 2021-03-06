(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.
Require option.Option.
Require list.List.
Require list.Length.
Require list.Nth.
Require list.HdTl.

(* Why3 assumption *)
Definition zero_at (l:(list Z)) (i:Z): Prop := ((list.Nth.nth i
  l) = (Init.Datatypes.Some 0%Z)) /\ forall (j:Z), ((0%Z <= j)%Z /\
  (j < i)%Z) -> ~ ((list.Nth.nth j l) = (Init.Datatypes.Some 0%Z)).

(* Why3 assumption *)
Definition no_zero (l:(list Z)): Prop := forall (j:Z), ((0%Z <= j)%Z /\
  (j < (list.Length.length l))%Z) -> ~ ((list.Nth.nth j
  l) = (Init.Datatypes.Some 0%Z)).

(* Why3 assumption *)
Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Axiom ref_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (ref a).
Existing Instance ref_WhyType.
Implicit Arguments mk_ref [[a]].

(* Why3 assumption *)
Definition contents {a:Type} {a_WT:WhyType a} (v:(ref a)): a :=
  match v with
  | (mk_ref x) => x
  end.

(* Why3 goal *)
Theorem VC_search_loop : forall (l:(list Z)), forall (s:(list Z)) (i:Z),
  ((0%Z <= i)%Z /\
  (((i + (list.Length.length s))%Z = (list.Length.length l)) /\
  ((forall (j:Z), (0%Z <= j)%Z -> ((list.Nth.nth j
  s) = (list.Nth.nth (i + j)%Z l))) /\ forall (j:Z), ((0%Z <= j)%Z /\
  (j < i)%Z) -> ~ ((list.Nth.nth j l) = (Init.Datatypes.Some 0%Z))))) ->
  (((list.List.is_nil s) <-> (s = Init.Datatypes.nil)) -> forall (o:bool),
  (((~ (list.List.is_nil s)) /\ exists o1:Z,
  ((list.HdTl.hd s) = (Init.Datatypes.Some o1)) /\ (((o1 = 0%Z) /\
  (o = false)) \/ ((~ (o1 = 0%Z)) /\ (o = true)))) \/ ((list.List.is_nil
  s) /\ (o = false))) -> ((~ (o = true)) -> ((((0%Z <= i)%Z /\
  (i < (list.Length.length l))%Z) /\ (zero_at l i)) \/
  ((i = (list.Length.length l)) /\ (no_zero l))))).
Proof.
intros l s i (h1,(h2,(h3,h4))) _ o h6 h7.
destruct s.
destruct h6.
now elim (proj1 H).
rewrite Zplus_0_r in h2.
right.
apply (conj h2).
intros j h6.
apply h4.
now rewrite h2.
left.
split.
apply (conj h1).
rewrite <- h2.
change (Length.length (cons z s))%Z with (1 + Length.length s)%Z.
generalize (Length.Length_nonnegative s).
omega.
simpl in h6.
split.
intuition.
generalize (h3 0%Z (Zle_refl 0)).
ring_simplify (i+0)%Z.
intros <-.
simpl.
now destruct H1 ; intuition ; subst.
easy.
Qed.

