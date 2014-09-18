(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.

(* Why3 assumption *)
Inductive list (a:Type) :=
  | Nil : list a
  | Cons : a -> (list a) -> list a.
Axiom list_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (list a).
Existing Instance list_WhyType.
Implicit Arguments Nil [[a]].
Implicit Arguments Cons [[a]].

Parameter num_occ: forall {a:Type} {a_WT:WhyType a}, a -> (list a) -> Z.

Axiom num_occ_def : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (l:(list
  a)),
  match l with
  | Nil => ((num_occ x l) = 0%Z)
  | (Cons y r) => ((x = y) -> ((num_occ x l) = (1%Z + (num_occ x r))%Z)) /\
      ((~ (x = y)) -> ((num_occ x l) = (0%Z + (num_occ x r))%Z))
  end.

Axiom Num_Occ_Positive : forall {a:Type} {a_WT:WhyType a}, forall (x:a)
  (l:(list a)), (0%Z <= (num_occ x l))%Z.

(* Why3 assumption *)
Fixpoint mem {a:Type} {a_WT:WhyType a} (x:a) (l:(list a)) {struct l}: Prop :=
  match l with
  | Nil => False
  | (Cons y r) => (x = y) \/ (mem x r)
  end.

Axiom Mem_Num_Occ : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (l:(list
  a)), (mem x l) <-> (0%Z < (num_occ x l))%Z.

(* Why3 assumption *)
Fixpoint infix_plpl {a:Type} {a_WT:WhyType a} (l1:(list a)) (l2:(list
  a)) {struct l1}: (list a) :=
  match l1 with
  | Nil => l2
  | (Cons x1 r1) => (Cons x1 (infix_plpl r1 l2))
  end.

Axiom Append_assoc : forall {a:Type} {a_WT:WhyType a}, forall (l1:(list a))
  (l2:(list a)) (l3:(list a)), ((infix_plpl l1 (infix_plpl l2
  l3)) = (infix_plpl (infix_plpl l1 l2) l3)).

Axiom Append_l_nil : forall {a:Type} {a_WT:WhyType a}, forall (l:(list a)),
  ((infix_plpl l (Nil : (list a))) = l).

(* Why3 assumption *)
Fixpoint length {a:Type} {a_WT:WhyType a} (l:(list a)) {struct l}: Z :=
  match l with
  | Nil => 0%Z
  | (Cons _ r) => (1%Z + (length r))%Z
  end.

Axiom Length_nonnegative : forall {a:Type} {a_WT:WhyType a}, forall (l:(list
  a)), (0%Z <= (length l))%Z.

Axiom Length_nil : forall {a:Type} {a_WT:WhyType a}, forall (l:(list a)),
  ((length l) = 0%Z) <-> (l = (Nil : (list a))).

Axiom Append_length : forall {a:Type} {a_WT:WhyType a}, forall (l1:(list a))
  (l2:(list a)), ((length (infix_plpl l1
  l2)) = ((length l1) + (length l2))%Z).

Axiom mem_append : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (l1:(list
  a)) (l2:(list a)), (mem x (infix_plpl l1 l2)) <-> ((mem x l1) \/ (mem x
  l2)).

Axiom mem_decomp : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (l:(list
  a)), (mem x l) -> exists l1:(list a), exists l2:(list a),
  (l = (infix_plpl l1 (Cons x l2))).

Axiom Append_Num_Occ : forall {a:Type} {a_WT:WhyType a}, forall (x:a)
  (l1:(list a)) (l2:(list a)), ((num_occ x (infix_plpl l1 l2)) = ((num_occ x
  l1) + (num_occ x l2))%Z).

(* Why3 assumption *)
Fixpoint reverse {a:Type} {a_WT:WhyType a} (l:(list a)) {struct l}: (list
  a) :=
  match l with
  | Nil => (Nil : (list a))
  | (Cons x r) => (infix_plpl (reverse r) (Cons x (Nil : (list a))))
  end.

Axiom reverse_append : forall {a:Type} {a_WT:WhyType a}, forall (l1:(list a))
  (l2:(list a)) (x:a), ((infix_plpl (reverse (Cons x l1))
  l2) = (infix_plpl (reverse l1) (Cons x l2))).

Axiom reverse_cons : forall {a:Type} {a_WT:WhyType a}, forall (l:(list a))
  (x:a), ((reverse (Cons x l)) = (infix_plpl (reverse l) (Cons x (Nil : (list
  a))))).

Axiom cons_reverse : forall {a:Type} {a_WT:WhyType a}, forall (l:(list a))
  (x:a), ((Cons x (reverse l)) = (reverse (infix_plpl l (Cons x (Nil : (list
  a)))))).

Axiom reverse_reverse : forall {a:Type} {a_WT:WhyType a}, forall (l:(list
  a)), ((reverse (reverse l)) = l).

Axiom reverse_mem : forall {a:Type} {a_WT:WhyType a}, forall (l:(list a))
  (x:a), (mem x l) <-> (mem x (reverse l)).

Axiom Reverse_length : forall {a:Type} {a_WT:WhyType a}, forall (l:(list a)),
  ((length (reverse l)) = (length l)).

Axiom reverse_num_occ : forall {a:Type} {a_WT:WhyType a}, forall (x:a)
  (l:(list a)), ((num_occ x l) = (num_occ x (reverse l))).

(* Why3 assumption *)
Definition permut {a:Type} {a_WT:WhyType a} (l1:(list a)) (l2:(list
  a)): Prop := forall (x:a), ((num_occ x l1) = (num_occ x l2)).

Axiom Permut_refl : forall {a:Type} {a_WT:WhyType a}, forall (l:(list a)),
  (permut l l).

Axiom Permut_sym : forall {a:Type} {a_WT:WhyType a}, forall (l1:(list a))
  (l2:(list a)), (permut l1 l2) -> (permut l2 l1).

Axiom Permut_trans : forall {a:Type} {a_WT:WhyType a}, forall (l1:(list a))
  (l2:(list a)) (l3:(list a)), (permut l1 l2) -> ((permut l2 l3) -> (permut
  l1 l3)).

Axiom Permut_cons : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (l1:(list
  a)) (l2:(list a)), (permut l1 l2) -> (permut (Cons x l1) (Cons x l2)).

Axiom Permut_swap : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (y:a)
  (l:(list a)), (permut (Cons x (Cons y l)) (Cons y (Cons x l))).

Axiom Permut_cons_append : forall {a:Type} {a_WT:WhyType a}, forall (x:a)
  (l1:(list a)) (l2:(list a)), (permut (infix_plpl (Cons x l1) l2)
  (infix_plpl l1 (Cons x l2))).

Axiom Permut_assoc : forall {a:Type} {a_WT:WhyType a}, forall (l1:(list a))
  (l2:(list a)) (l3:(list a)), (permut (infix_plpl (infix_plpl l1 l2) l3)
  (infix_plpl l1 (infix_plpl l2 l3))).

Axiom Permut_append : forall {a:Type} {a_WT:WhyType a}, forall (l1:(list a))
  (l2:(list a)) (k1:(list a)) (k2:(list a)), (permut l1 k1) -> ((permut l2
  k2) -> (permut (infix_plpl l1 l2) (infix_plpl k1 k2))).

Axiom Permut_append_swap : forall {a:Type} {a_WT:WhyType a}, forall (l1:(list
  a)) (l2:(list a)), (permut (infix_plpl l1 l2) (infix_plpl l2 l1)).

Axiom Permut_mem : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (l1:(list
  a)) (l2:(list a)), (permut l1 l2) -> ((mem x l1) -> (mem x l2)).

(* Why3 goal *)
Theorem Permut_length : forall {a:Type} {a_WT:WhyType a}, forall (l1:(list
  a)) (l2:(list a)), (permut l1 l2) -> ((length l1) = (length l2)).
intros a a_WT l1 l2 h1.
Require Import Why3.
Ltac cvc := why3 "CVC4,1.4,".
generalize dependent l2.
induction l1; intros.
destruct l2.
trivial.
cvc.
pose (h2 := h1).
clearbody h2.
specialize (h1 a0).
assert (mem a0 l2) by cvc.
apply mem_decomp in H.
destruct H as [l3 [l4 H]].
assert (permut l1 (infix_plpl l3 l4)).
intro.
cvc.
cvc.
Qed.

