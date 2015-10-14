(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require list.List.
Require list.Length.
Require int.Int.
Require list.Mem.
Require map.Map.
Require map.Const.
Require list.Append.

(* Why3 assumption *)
Definition unit := unit.

Axiom set : forall (a:Type), Type.
Parameter set_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (set a).
Existing Instance set_WhyType.

Parameter mem: forall {a:Type} {a_WT:WhyType a}, a -> (set a) -> Prop.

(* Why3 assumption *)
Definition infix_eqeq {a:Type} {a_WT:WhyType a} (s1:(set a)) (s2:(set
  a)): Prop := forall (x:a), (mem x s1) <-> (mem x s2).

Axiom extensionality : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)), (infix_eqeq s1 s2) -> (s1 = s2).

(* Why3 assumption *)
Definition subset {a:Type} {a_WT:WhyType a} (s1:(set a)) (s2:(set
  a)): Prop := forall (x:a), (mem x s1) -> (mem x s2).

Axiom subset_refl : forall {a:Type} {a_WT:WhyType a}, forall (s:(set a)),
  (subset s s).

Axiom subset_trans : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)) (s3:(set a)), (subset s1 s2) -> ((subset s2 s3) -> (subset s1
  s3)).

Parameter empty: forall {a:Type} {a_WT:WhyType a}, (set a).

(* Why3 assumption *)
Definition is_empty {a:Type} {a_WT:WhyType a} (s:(set a)): Prop :=
  forall (x:a), ~ (mem x s).

Axiom empty_def1 : forall {a:Type} {a_WT:WhyType a}, (is_empty (empty : (set
  a))).

Axiom mem_empty : forall {a:Type} {a_WT:WhyType a}, forall (x:a), ~ (mem x
  (empty : (set a))).

Parameter add: forall {a:Type} {a_WT:WhyType a}, a -> (set a) -> (set a).

Axiom add_def1 : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (y:a),
  forall (s:(set a)), (mem x (add y s)) <-> ((x = y) \/ (mem x s)).

Parameter remove: forall {a:Type} {a_WT:WhyType a}, a -> (set a) -> (set a).

Axiom remove_def1 : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (y:a)
  (s:(set a)), (mem x (remove y s)) <-> ((~ (x = y)) /\ (mem x s)).

Axiom add_remove : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (s:(set
  a)), (mem x s) -> ((add x (remove x s)) = s).

Axiom remove_add : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (s:(set
  a)), ((remove x (add x s)) = (remove x s)).

Axiom subset_remove : forall {a:Type} {a_WT:WhyType a}, forall (x:a) (s:(set
  a)), (subset (remove x s) s).

Parameter union: forall {a:Type} {a_WT:WhyType a}, (set a) -> (set a) -> (set
  a).

Axiom union_def1 : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)) (x:a), (mem x (union s1 s2)) <-> ((mem x s1) \/ (mem x s2)).

Parameter inter: forall {a:Type} {a_WT:WhyType a}, (set a) -> (set a) -> (set
  a).

Axiom inter_def1 : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)) (x:a), (mem x (inter s1 s2)) <-> ((mem x s1) /\ (mem x s2)).

Parameter diff: forall {a:Type} {a_WT:WhyType a}, (set a) -> (set a) -> (set
  a).

Axiom diff_def1 : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)) (x:a), (mem x (diff s1 s2)) <-> ((mem x s1) /\ ~ (mem x s2)).

Axiom subset_diff : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)), (subset (diff s1 s2) s1).

Parameter choose: forall {a:Type} {a_WT:WhyType a}, (set a) -> a.

Axiom choose_def : forall {a:Type} {a_WT:WhyType a}, forall (s:(set a)),
  (~ (is_empty s)) -> (mem (choose s) s).

Parameter cardinal: forall {a:Type} {a_WT:WhyType a}, (set a) -> Z.

Axiom cardinal_nonneg : forall {a:Type} {a_WT:WhyType a}, forall (s:(set a)),
  (0%Z <= (cardinal s))%Z.

Axiom cardinal_empty : forall {a:Type} {a_WT:WhyType a}, forall (s:(set a)),
  ((cardinal s) = 0%Z) <-> (is_empty s).

Axiom cardinal_add : forall {a:Type} {a_WT:WhyType a}, forall (x:a),
  forall (s:(set a)), (~ (mem x s)) -> ((cardinal (add x
  s)) = (1%Z + (cardinal s))%Z).

Axiom cardinal_remove : forall {a:Type} {a_WT:WhyType a}, forall (x:a),
  forall (s:(set a)), (mem x s) -> ((cardinal s) = (1%Z + (cardinal (remove x
  s)))%Z).

Axiom cardinal_subset : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)), (subset s1 s2) -> ((cardinal s1) <= (cardinal s2))%Z.

Axiom subset_eq : forall {a:Type} {a_WT:WhyType a}, forall (s1:(set a))
  (s2:(set a)), (subset s1 s2) -> (((cardinal s1) = (cardinal s2)) ->
  (infix_eqeq s1 s2)).

Axiom cardinal1 : forall {a:Type} {a_WT:WhyType a}, forall (s:(set a)),
  ((cardinal s) = 1%Z) -> forall (x:a), (mem x s) -> (x = (choose s)).

Axiom vertex : Type.
Parameter vertex_WhyType : WhyType vertex.
Existing Instance vertex_WhyType.

Parameter vertices: (set vertex).

Parameter edges: (set (vertex* vertex)%type).

(* Why3 assumption *)
Definition edge (x:vertex) (y:vertex): Prop := (mem (x, y) edges).

Axiom edges_def : forall (x:vertex) (y:vertex), (mem (x, y) edges) -> ((mem x
  vertices) /\ (mem y vertices)).

Parameter s: vertex.

Axiom s_in_graph : (mem s vertices).

Axiom vertices_cardinal_pos : (0%Z < (cardinal vertices))%Z.

(* Why3 assumption *)
Inductive path: vertex -> (list vertex) -> vertex -> Prop :=
  | Path_empty : forall (x:vertex), (path x Init.Datatypes.nil x)
  | Path_cons : forall (x:vertex) (y:vertex) (z:vertex) (l:(list vertex)),
      (edge x y) -> ((path y l z) -> (path x (Init.Datatypes.cons x l) z)).

Axiom path_right_extension : forall (x:vertex) (y:vertex) (z:vertex)
  (l:(list vertex)), (path x l y) -> ((edge y z) -> (path x
  (Init.Datatypes.app l (Init.Datatypes.cons y Init.Datatypes.nil)) z)).

Axiom path_right_inversion : forall (x:vertex) (z:vertex) (l:(list vertex)),
  (path x l z) -> (((x = z) /\ (l = Init.Datatypes.nil)) \/ exists y:vertex,
  exists l':(list vertex), (path x l' y) /\ ((edge y z) /\
  (l = (Init.Datatypes.app l' (Init.Datatypes.cons y Init.Datatypes.nil))))).

Axiom path_trans : forall (x:vertex) (y:vertex) (z:vertex) (l1:(list vertex))
  (l2:(list vertex)), (path x l1 y) -> ((path y l2 z) -> (path x
  (Init.Datatypes.app l1 l2) z)).

Axiom empty_path : forall (x:vertex) (y:vertex), (path x Init.Datatypes.nil
  y) -> (x = y).

Axiom path_decomposition : forall (x:vertex) (y:vertex) (z:vertex)
  (l1:(list vertex)) (l2:(list vertex)), (path x
  (Init.Datatypes.app l1 (Init.Datatypes.cons y l2)) z) -> ((path x l1 y) /\
  (path y (Init.Datatypes.cons y l2) z)).

Parameter weight: vertex -> vertex -> Z.

(* Why3 assumption *)
Fixpoint path_weight (l:(list vertex)) (dst:vertex) {struct l}: Z :=
  match l with
  | Init.Datatypes.nil => 0%Z
  | (Init.Datatypes.cons x Init.Datatypes.nil) => (weight x dst)
  | (Init.Datatypes.cons x ((Init.Datatypes.cons y _) as r)) => ((weight x
      y) + (path_weight r dst))%Z
  end.

Axiom path_weight_right_extension : forall (x:vertex) (y:vertex)
  (l:(list vertex)),
  ((path_weight (Init.Datatypes.app l (Init.Datatypes.cons x Init.Datatypes.nil))
  y) = ((path_weight l x) + (weight x y))%Z).

Axiom path_weight_decomposition : forall (y:vertex) (z:vertex)
  (l1:(list vertex)) (l2:(list vertex)),
  ((path_weight (Init.Datatypes.app l1 (Init.Datatypes.cons y l2))
  z) = ((path_weight l1 y) + (path_weight (Init.Datatypes.cons y l2) z))%Z).

Axiom path_in_vertices : forall (v1:vertex) (v2:vertex) (l:(list vertex)),
  (mem v1 vertices) -> ((path v1 l v2) -> (mem v2 vertices)).

(* Why3 assumption *)
Definition pigeon_set (s1:(set vertex)): Prop := forall (l:(list vertex)),
  (forall (e:vertex), (list.Mem.mem e l) -> (mem e s1)) ->
  (((cardinal s1) < (list.Length.length l))%Z -> exists e:vertex,
  exists l1:(list vertex), exists l2:(list vertex), exists l3:(list vertex),
  (l = (Init.Datatypes.app l1 (Init.Datatypes.cons e (Init.Datatypes.app l2 (Init.Datatypes.cons e l3)))))).

Axiom Induction : (forall (s1:(set vertex)), (is_empty s1) -> (pigeon_set
  s1)) -> ((forall (s1:(set vertex)), (pigeon_set s1) -> forall (t:vertex),
  (~ (mem t s1)) -> (pigeon_set (add t s1))) -> forall (s1:(set vertex)),
  (pigeon_set s1)).

Axiom corner : forall (s1:(set vertex)) (l:(list vertex)),
  ((list.Length.length l) = (cardinal s1)) -> ((forall (e:vertex),
  (list.Mem.mem e l) -> (mem e s1)) -> ((exists e:vertex,
  (exists l1:(list vertex), (exists l2:(list vertex),
  (exists l3:(list vertex),
  (l = (Init.Datatypes.app l1 (Init.Datatypes.cons e (Init.Datatypes.app l2 (Init.Datatypes.cons e l3))))))))) \/
  forall (e:vertex), (mem e s1) -> (list.Mem.mem e l))).

Axiom pigeon_0 : (pigeon_set (empty : (set vertex))).

Axiom pigeon_1 : forall (s1:(set vertex)), (pigeon_set s1) ->
  forall (t:vertex), (pigeon_set (add t s1)).

Axiom pigeon_2 : forall (s1:(set vertex)), (pigeon_set s1).

Axiom pigeonhole : forall (s1:(set vertex)) (l:(list vertex)),
  (forall (e:vertex), (list.Mem.mem e l) -> (mem e s1)) ->
  (((cardinal s1) < (list.Length.length l))%Z -> exists e:vertex,
  exists l1:(list vertex), exists l2:(list vertex), exists l3:(list vertex),
  (l = (Init.Datatypes.app l1 (Init.Datatypes.cons e (Init.Datatypes.app l2 (Init.Datatypes.cons e l3)))))).

Axiom long_path_decomposition_pigeon1 : forall (l:(list vertex)) (v:vertex),
  (path s l v) -> ((~ (l = Init.Datatypes.nil)) -> forall (v1:vertex),
  (list.Mem.mem v1 (Init.Datatypes.cons v l)) -> (mem v1 vertices)).

Axiom long_path_decomposition_pigeon2 : forall (l:(list vertex)) (v:vertex),
  (forall (v1:vertex), (list.Mem.mem v1 (Init.Datatypes.cons v l)) -> (mem v1
  vertices)) ->
  (((cardinal vertices) < (list.Length.length (Init.Datatypes.cons v l)))%Z ->
  exists e:vertex, exists l1:(list vertex), exists l2:(list vertex),
  exists l3:(list vertex),
  ((Init.Datatypes.cons v l) = (Init.Datatypes.app l1 (Init.Datatypes.cons e (Init.Datatypes.app l2 (Init.Datatypes.cons e l3)))))).

Axiom long_path_decomposition_pigeon3 : forall (l:(list vertex)) (v:vertex),
  (exists e:vertex, (exists l1:(list vertex), (exists l2:(list vertex),
  (exists l3:(list vertex),
  ((Init.Datatypes.cons v l) = (Init.Datatypes.app l1 (Init.Datatypes.cons e (Init.Datatypes.app l2 (Init.Datatypes.cons e l3))))))))) ->
  ((exists l1:(list vertex), (exists l2:(list vertex),
  (l = (Init.Datatypes.app l1 (Init.Datatypes.cons v l2))))) \/
  exists n:vertex, exists l1:(list vertex), exists l2:(list vertex),
  exists l3:(list vertex),
  (l = (Init.Datatypes.app l1 (Init.Datatypes.cons n (Init.Datatypes.app l2 (Init.Datatypes.cons n l3)))))).

Axiom long_path_decomposition : forall (l:(list vertex)) (v:vertex), (path s
  l v) -> (((cardinal vertices) <= (list.Length.length l))%Z ->
  ((exists l1:(list vertex), (exists l2:(list vertex),
  (l = (Init.Datatypes.app l1 (Init.Datatypes.cons v l2))))) \/
  exists n:vertex, exists l1:(list vertex), exists l2:(list vertex),
  exists l3:(list vertex),
  (l = (Init.Datatypes.app l1 (Init.Datatypes.cons n (Init.Datatypes.app l2 (Init.Datatypes.cons n l3))))))).

Axiom simple_path : forall (v:vertex) (l:(list vertex)), (path s l v) ->
  exists l':(list vertex), (path s l' v) /\
  ((list.Length.length l') < (cardinal vertices))%Z.

(* Why3 assumption *)
Definition negative_cycle (v:vertex): Prop := (mem v vertices) /\
  ((exists l1:(list vertex), (path s l1 v)) /\ exists l2:(list vertex), (path
  v l2 v) /\ ((path_weight l2 v) < 0%Z)%Z).

Axiom key_lemma_1 : forall (v:vertex) (n:Z), (forall (l:(list vertex)), (path
  s l v) -> (((list.Length.length l) < (cardinal vertices))%Z ->
  (n <= (path_weight l v))%Z)) -> ((exists l:(list vertex), (path s l v) /\
  ((path_weight l v) < n)%Z) -> exists u:vertex, (negative_cycle u)).

(* Why3 assumption *)
Inductive t :=
  | Finite : Z -> t
  | Infinite : t.
Axiom t_WhyType : WhyType t.
Existing Instance t_WhyType.

(* Why3 assumption *)
Definition add1 (x:t) (y:t): t :=
  match x with
  | Infinite => Infinite
  | (Finite x1) =>
      match y with
      | Infinite => Infinite
      | (Finite y1) => (Finite (x1 + y1)%Z)
      end
  end.

(* Why3 assumption *)
Definition lt (x:t) (y:t): Prop :=
  match x with
  | Infinite => False
  | (Finite x1) =>
      match y with
      | Infinite => True
      | (Finite y1) => (x1 < y1)%Z
      end
  end.

(* Why3 assumption *)
Definition le (x:t) (y:t): Prop := (lt x y) \/ (x = y).

Axiom Refl : forall (x:t), (le x x).

Axiom Trans : forall (x:t) (y:t) (z:t), (le x y) -> ((le y z) -> (le x z)).

Axiom Antisymm : forall (x:t) (y:t), (le x y) -> ((le y x) -> (x = y)).

Axiom Total : forall (x:t) (y:t), (le x y) \/ (le y x).

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

(* Why3 assumption *)
Definition t1 (a:Type) := (ref (set a)).

(* Why3 assumption *)
Definition distmap := (map.Map.map vertex t).

(* Why3 assumption *)
Definition inv1 (m:(map.Map.map vertex t)) (pass:Z) (via:(set (vertex*
  vertex)%type)): Prop := forall (v:vertex), (mem v vertices) ->
  match (map.Map.get m
  v) with
  | (Finite n) => (exists l:(list vertex), (path s l v) /\ ((path_weight l
      v) = n)) /\ ((forall (l:(list vertex)), (path s l v) ->
      (((list.Length.length l) < pass)%Z -> (n <= (path_weight l v))%Z)) /\
      forall (u:vertex) (l:(list vertex)), (path s l u) ->
      (((list.Length.length l) < pass)%Z -> ((mem (u, v) via) ->
      (n <= ((path_weight l u) + (weight u v))%Z)%Z)))
  | Infinite => (forall (l:(list vertex)), (path s l v) ->
      (pass <= (list.Length.length l))%Z) /\ forall (u:vertex), (mem (u, v)
      via) -> forall (lu:(list vertex)), (path s lu u) ->
      (pass <= (list.Length.length lu))%Z
  end.

(* Why3 assumption *)
Definition inv2 (m:(map.Map.map vertex t)) (via:(set (vertex*
  vertex)%type)): Prop := forall (u:vertex) (v:vertex), (mem (u, v) via) ->
  (le (map.Map.get m v) (add1 (map.Map.get m u) (Finite (weight u v)))).

Axiom key_lemma_2 : forall (m:(map.Map.map vertex t)), (inv1 m
  (cardinal vertices) (empty : (set (vertex* vertex)%type))) -> ((inv2 m
  edges) -> forall (v:vertex), ~ (negative_cycle v)).

Require Import Why3.
Ltac ae := why3 "alt-ergo".
Require Import Classical.

(* Why3 goal *)
Theorem WP_parameter_relax : forall (m:(map.Map.map vertex t)) (u:vertex)
  (v:vertex) (pass:Z) (via:(set (vertex* vertex)%type)), ((((1%Z < pass)%Z \/
  (1%Z = pass)) /\ ((mem (u, v) edges) /\ ~ (mem (u, v) via))) /\
  forall (v1:vertex), (mem v1 vertices) -> match (map.Map.get m
  v1) with
  | (Finite n) => (exists l:(list vertex), (path s l v1) /\ ((path_weight l
      v1) = n)) /\ ((forall (l:(list vertex)), (path s l v1) ->
      (((list.Length.length l) < pass)%Z -> (n <= (path_weight l v1))%Z)) /\
      forall (u1:vertex) (l:(list vertex)), (path s l u1) ->
      (((list.Length.length l) < pass)%Z -> ((mem (u1, v1) via) ->
      (n <= ((path_weight l u1) + (weight u1 v1))%Z)%Z)))
  | Infinite => (forall (l:(list vertex)), (path s l v1) ->
      (pass <= (list.Length.length l))%Z) /\ forall (u1:vertex), (mem (u1,
      v1) via) -> forall (lu:(list vertex)), (path s lu u1) ->
      (pass <= (list.Length.length lu))%Z
  end) -> (match (map.Map.get m
  u) with
  | Infinite => False
  | (Finite x) => match (map.Map.get m
      v) with
      | Infinite => True
      | (Finite y) => ((x + (weight u v))%Z < y)%Z
      end
  end -> forall (m1:(map.Map.map vertex t)), (m1 = (map.Map.set m v
  match (map.Map.get m
  u) with
  | Infinite => Infinite
  | (Finite x) => (Finite (x + (weight u v))%Z)
  end)) -> forall (v1:vertex), (mem v1 vertices) -> forall (x:Z),
  ((map.Map.get m1 v1) = (Finite x)) -> exists l:(list vertex), (path s l
  v1) /\ ((path_weight l v1) = x)).
(* Why3 intros m u v pass via ((h1,(h2,h3)),h4) h5 m1 h6 v1 h7 x h8. *)
intros m u v pass via ((hpass, (h1, h2)), h3).
destruct (Map.get m u) as [] _eqn. 2:intuition.
intros hlt m1 eqm1 v1 hv1.
destruct (classic (v1 = v)) as [h|h].
subst m1 v1. rewrite Map.Select_eq; auto.
assert (H : exists lu: list vertex, path s lu u /\ path_weight lu u = z) by ae.
destruct H as (lu, (hu1, hu2)).
exists (app lu (cons u nil)); ae.
subst m1. rewrite Map.Select_neq; auto.
ae.
Qed.

