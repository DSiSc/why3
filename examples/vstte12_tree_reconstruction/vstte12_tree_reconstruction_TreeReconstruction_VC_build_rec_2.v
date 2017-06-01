(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.
Require list.List.
Require list.Length.
Require list.Mem.
Require list.Append.

(* Why3 assumption *)
Definition unit := unit.

(* Why3 assumption *)
Inductive tree :=
  | Leaf : tree
  | Node : tree -> tree -> tree.
Axiom tree_WhyType : WhyType tree.
Existing Instance tree_WhyType.

(* Why3 assumption *)
Fixpoint depths (d:Z) (t:tree) {struct t}: (list Z) :=
  match t with
  | Leaf => (Init.Datatypes.cons d Init.Datatypes.nil)
  | (Node l r) => (Init.Datatypes.app (depths (d + 1%Z)%Z
      l) (depths (d + 1%Z)%Z r))
  end.

Axiom depths_head : forall (t:tree) (d:Z), match (depths d
  t) with
  | (Init.Datatypes.cons x _) => (d <= x)%Z
  | Init.Datatypes.nil => False
  end.

Axiom depths_unique : forall (t1:tree) (t2:tree) (d:Z) (s1:(list Z))
  (s2:(list Z)), ((Init.Datatypes.app (depths d
  t1) s1) = (Init.Datatypes.app (depths d t2) s2)) -> ((t1 = t2) /\
  (s1 = s2)).

Axiom depths_prefix : forall (t:tree) (d1:Z) (d2:Z) (s1:(list Z))
  (s2:(list Z)), ((Init.Datatypes.app (depths d1
  t) s1) = (Init.Datatypes.app (depths d2 t) s2)) -> (d1 = d2).

Axiom depths_prefix_simple : forall (t:tree) (d1:Z) (d2:Z), ((depths d1
  t) = (depths d2 t)) -> (d1 = d2).

Axiom depths_subtree : forall (t1:tree) (t2:tree) (d1:Z) (d2:Z)
  (s1:(list Z)), ((Init.Datatypes.app (depths d1 t1) s1) = (depths d2 t2)) ->
  (d2 <= d1)%Z.

Axiom depths_unique2 : forall (t1:tree) (t2:tree) (d1:Z) (d2:Z), ((depths d1
  t1) = (depths d2 t2)) -> ((d1 = d2) /\ (t1 = t2)).

(* Why3 assumption *)
Definition lex (x1:((list Z)* Z)%type) (x2:((list Z)* Z)%type): Prop :=
  match x1 with
  | (s1, d1) =>
      match x2 with
      | (s2, d2) => ((list.Length.length s1) < (list.Length.length s2))%Z \/
          (((list.Length.length s1) = (list.Length.length s2)) /\ match (s1,
          s2) with
          | ((Init.Datatypes.cons h1 _), (Init.Datatypes.cons h2 _)) =>
              (d2 < d1)%Z /\ ((d1 <= h1)%Z /\ (h1 = h2))
          | _ => False
          end)
      end
  end.

(* Why3 goal *)
Theorem VC_build_rec : forall (d:Z) (s:(list Z)), forall (x:Z) (x1:(list Z)),
  (s = (Init.Datatypes.cons x x1)) -> ((~ (x < d)%Z) -> ((~ (x = d)) ->
  ((forall (t:tree) (s':(list Z)), ~ ((Init.Datatypes.app (depths (d + 1%Z)%Z
  t) s') = s)) -> forall (t:tree) (s':(list Z)),
  ~ ((Init.Datatypes.app (depths d t) s') = s)))).
intros d s x x1 h1 h2 h3 h4 t s'.
subst.
intuition.
destruct t as [_|t1 t2].
(* t = Leaf *)
simpl in H.
injection H.
omega.
(* t = Node t1 t2 *)
simpl in H.
rewrite <- Append.Append_assoc in H.
apply (h4 _ _ H).

Qed.

