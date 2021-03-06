(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.
Require int.Abs.
Require int.EuclideanDivision.
Require int.ComputerDivision.
Require int.Power.
Require map.Map.
Require bool.Bool.

(* Why3 assumption *)
Definition unit := unit.

Axiom qtmark : Type.
Parameter qtmark_WhyType : WhyType qtmark.
Existing Instance qtmark_WhyType.

Axiom int31 : Type.
Parameter int31_WhyType : WhyType int31.
Existing Instance int31_WhyType.

Parameter to_int: int31 -> Z.

(* Why3 assumption *)
Definition in_bounds (n:Z): Prop := ((-1073741824%Z)%Z <= n)%Z /\
  (n <= 1073741823%Z)%Z.

Axiom to_int_in_bounds : forall (n:int31), (in_bounds (to_int n)).

Axiom extensionality : forall (x:int31) (y:int31),
  ((to_int x) = (to_int y)) -> (x = y).

Axiom val_two_power_size : (2147483648%Z = (int.Power.power 2%Z 31%Z)).

Axiom t : Type.
Parameter t_WhyType : WhyType t.
Existing Instance t_WhyType.

Parameter nth: t -> Z -> bool.

(* Why3 assumption *)
Definition eq (v1:t) (v2:t): Prop := forall (n:Z), ((0%Z <= n)%Z /\
  (n < 31%Z)%Z) -> ((nth v1 n) = (nth v2 n)).

Axiom Extensionality : forall (x:t) (y:t), (eq x y) -> (x = y).

Parameter zero: t.

Axiom Nth_zero : forall (n:Z), ((0%Z <= n)%Z /\ (n < 31%Z)%Z) -> ((nth zero
  n) = false).

Parameter ones: t.

Axiom Nth_ones : forall (n:Z), ((0%Z <= n)%Z /\ (n < 31%Z)%Z) -> ((nth ones
  n) = true).

Parameter bw_and: t -> t -> t.

Axiom Nth_bw_and : forall (v1:t) (v2:t) (n:Z), ((0%Z <= n)%Z /\
  (n < 31%Z)%Z) -> ((nth (bw_and v1 v2) n) = (Init.Datatypes.andb (nth v1
  n) (nth v2 n))).

Parameter bw_or: t -> t -> t.

Axiom Nth_bw_or : forall (v1:t) (v2:t) (n:Z), ((0%Z <= n)%Z /\
  (n < 31%Z)%Z) -> ((nth (bw_or v1 v2) n) = (Init.Datatypes.orb (nth v1
  n) (nth v2 n))).

Parameter bw_xor: t -> t -> t.

Axiom Nth_bw_xor : forall (v1:t) (v2:t) (n:Z), ((0%Z <= n)%Z /\
  (n < 31%Z)%Z) -> ((nth (bw_xor v1 v2) n) = (Init.Datatypes.xorb (nth v1
  n) (nth v2 n))).

Parameter bw_not: t -> t.

Axiom Nth_bw_not : forall (v:t) (n:Z), ((0%Z <= n)%Z /\ (n < 31%Z)%Z) ->
  ((nth (bw_not v) n) = (Init.Datatypes.negb (nth v n))).

Parameter rotate_left: t -> t.

Axiom Nth_rotate_left_high : forall (v:t) (n:Z), ((0%Z < n)%Z /\
  (n < 31%Z)%Z) -> ((nth (rotate_left v) n) = (nth v (n - 1%Z)%Z)).

Axiom Nth_rotate_left_low : forall (v:t), ((nth (rotate_left v) 0%Z) = (nth v
  (31%Z - 1%Z)%Z)).

Parameter rotate_right: t -> t.

Axiom Nth_rotate_right_high : forall (v:t), ((nth (rotate_right v)
  (31%Z - 1%Z)%Z) = (nth v 0%Z)).

Axiom Nth_rotate_right_low : forall (v:t) (n:Z), ((0%Z <= n)%Z /\
  (n < (31%Z - 1%Z)%Z)%Z) -> ((nth (rotate_right v) n) = (nth v
  (n + 1%Z)%Z)).

Parameter lsr: t -> Z -> t.

Axiom Lsr_nth_low : forall (b:t) (n:Z) (s:Z), ((0%Z <= s)%Z /\
  (s < 31%Z)%Z) -> (((0%Z <= n)%Z /\ (n < 31%Z)%Z) ->
  (((n + s)%Z < 31%Z)%Z -> ((nth (lsr b s) n) = (nth b (n + s)%Z)))).

Axiom Lsr_nth_high : forall (b:t) (n:Z) (s:Z), ((0%Z <= s)%Z /\
  (s < 31%Z)%Z) -> (((0%Z <= n)%Z /\ (n < 31%Z)%Z) ->
  ((31%Z <= (n + s)%Z)%Z -> ((nth (lsr b s) n) = false))).

Parameter lsr_bv: t -> t -> t.

Parameter asr: t -> Z -> t.

Axiom Asr_nth_low : forall (b:t) (n:Z) (s:Z), ((0%Z <= s)%Z /\
  (s < 31%Z)%Z) -> (((0%Z <= n)%Z /\ (n < 31%Z)%Z) ->
  (((0%Z <= (n + s)%Z)%Z /\ ((n + s)%Z < 31%Z)%Z) -> ((nth (asr b s)
  n) = (nth b (n + s)%Z)))).

Axiom Asr_nth_high : forall (b:t) (n:Z) (s:Z), ((0%Z <= s)%Z /\
  (s < 31%Z)%Z) -> (((0%Z <= n)%Z /\ (n < 31%Z)%Z) ->
  ((31%Z <= (n + s)%Z)%Z -> ((nth (asr b s) n) = (nth b (31%Z - 1%Z)%Z)))).

Parameter asr_bv: t -> t -> t.

Parameter lsl: t -> Z -> t.

Axiom Lsl_nth_high : forall (b:t) (n:Z) (s:Z), ((0%Z <= s)%Z /\
  (s < 31%Z)%Z) -> (((0%Z <= n)%Z /\ (n < 31%Z)%Z) ->
  (((0%Z <= (n - s)%Z)%Z /\ ((n - s)%Z < 31%Z)%Z) -> ((nth (lsl b s)
  n) = (nth b (n - s)%Z)))).

Axiom Lsl_nth_low : forall (b:t) (n:Z) (s:Z), ((0%Z <= s)%Z /\
  (s < 31%Z)%Z) -> (((0%Z <= n)%Z /\ (n < 31%Z)%Z) -> (((n - s)%Z < 0%Z)%Z ->
  ((nth (lsl b s) n) = false))).

Parameter lsl_bv: t -> t -> t.

Parameter to_uint: t -> Z.

Axiom to_uint_extensionality : forall (v:t) (v':t),
  ((to_uint v) = (to_uint v')) -> (v = v').

Axiom to_uint_zero : ((to_uint zero) = 0%Z).

Axiom to_uint_ones : ((to_uint ones) = 4294967295%Z).

Parameter to_int1: t -> Z.

Axiom to_int_extensionality : forall (v:t) (v':t),
  ((to_int1 v) = (to_int1 v')) -> (v = v').

Parameter of_int: Z -> t.

Axiom of_int_is_mod : forall (i:Z),
  ((to_uint (of_int i)) = (int.EuclideanDivision.mod1 i 2147483648%Z)).

Axiom of_int_extmod : forall (i:Z) (j:Z), ((of_int i) = (of_int j)) ->
  ((int.EuclideanDivision.mod1 i
  2147483648%Z) = (int.EuclideanDivision.mod1 j 2147483648%Z)).

Parameter of_int_const: Z -> t.

Axiom of_int_const_to_int : forall (i:Z),
  ((to_int1 (of_int_const i)) = (int.EuclideanDivision.mod1 i 2147483648%Z)).

Axiom of_int_const_to_uint : forall (i:Z),
  ((to_uint (of_int_const i)) = (int.EuclideanDivision.mod1 i 2147483648%Z)).

Parameter add: t -> t -> t.

Parameter sub: t -> t -> t.

Parameter neg: t -> t.

Parameter mul: t -> t -> t.

Parameter udiv: t -> t -> t.

Parameter urem: t -> t -> t.

Parameter sdiv: t -> t -> t.

Parameter srem: t -> t -> t.

Parameter smod: t -> t -> t.

(* Why3 assumption *)
Definition slt (v1:t) (v2:t): Prop := ((to_int1 v1) < (to_int1 v2))%Z.

(* Why3 assumption *)
Definition sle (v1:t) (v2:t): Prop := ((to_int1 v1) <= (to_int1 v2))%Z.

(* Why3 assumption *)
Definition sgt (v1:t) (v2:t): Prop := ((to_int1 v2) < (to_int1 v1))%Z.

(* Why3 assumption *)
Definition sge (v1:t) (v2:t): Prop := ((to_int1 v2) <= (to_int1 v1))%Z.

(* Why3 assumption *)
Definition ult (v1:t) (v2:t): Prop := ((to_uint v1) < (to_uint v2))%Z.

(* Why3 assumption *)
Definition ule (v1:t) (v2:t): Prop := ((to_uint v1) <= (to_uint v2))%Z.

(* Why3 assumption *)
Definition ugt (v1:t) (v2:t): Prop := ((to_uint v2) < (to_uint v1))%Z.

(* Why3 assumption *)
Definition uge (v1:t) (v2:t): Prop := ((to_uint v2) <= (to_uint v1))%Z.

(* Why3 assumption *)
Definition grid := (map.Map.map Z int31).

(* Why3 assumption *)
Definition is_index (i:Z): Prop := (0%Z <= i)%Z /\ (i < 81%Z)%Z.

(* Why3 assumption *)
Definition valid_values (g:(map.Map.map Z int31)): Prop := forall (i:Z),
  (is_index i) -> ((0%Z <= (to_int (map.Map.get g i)))%Z /\
  ((to_int (map.Map.get g i)) <= 9%Z)%Z).

(* Why3 assumption *)
Definition grid_eq_sub (g1:(map.Map.map Z int31)) (g2:(map.Map.map Z int31))
  (a:Z) (b:Z): Prop := forall (j:Z), ((a <= j)%Z /\ (j < b)%Z) ->
  ((map.Map.get g1 j) = (map.Map.get g2 j)).

Axiom grid_eq_sub1 : forall (g1:(map.Map.map Z int31)) (g2:(map.Map.map Z
  int31)) (a:Z) (b:Z), (((0%Z <= a)%Z /\ (a <= 81%Z)%Z) /\ (((0%Z <= b)%Z /\
  (b <= 81%Z)%Z) /\ (grid_eq_sub g1 g2 0%Z 81%Z))) -> (grid_eq_sub g1 g2 a
  b).

(* Why3 assumption *)
Inductive array
  (a:Type) :=
  | mk_array : int31 -> (map.Map.map Z a) -> array a.
Axiom array_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (array a).
Existing Instance array_WhyType.
Implicit Arguments mk_array [[a]].

(* Why3 assumption *)
Definition elts {a:Type} {a_WT:WhyType a} (v:(array a)): (map.Map.map Z a) :=
  match v with
  | (mk_array x x1) => x1
  end.

(* Why3 assumption *)
Definition length {a:Type} {a_WT:WhyType a} (v:(array a)): int31 :=
  match v with
  | (mk_array x x1) => x
  end.

(* Why3 assumption *)
Definition get {a:Type} {a_WT:WhyType a} (a1:(array a)) (i:Z): a :=
  (map.Map.get (elts a1) i).

(* Why3 assumption *)
Definition set {a:Type} {a_WT:WhyType a} (a1:(array a)) (i:Z) (v:a): (array
  a) := (mk_array (length a1) (map.Map.set (elts a1) i v)).

(* Why3 assumption *)
Definition make {a:Type} {a_WT:WhyType a} (n:int31) (v:a): (array a) :=
  (mk_array n (map.Map.const v: (map.Map.map Z a))).

(* Why3 assumption *)
Inductive sudoku_chunks :=
  | mk_sudoku_chunks : (array int31) -> (array int31) -> (array int31) ->
      (array int31) -> (array int31) -> (array int31) -> sudoku_chunks.
Axiom sudoku_chunks_WhyType : WhyType sudoku_chunks.
Existing Instance sudoku_chunks_WhyType.

(* Why3 assumption *)
Definition square_offsets (v:sudoku_chunks): (array int31) :=
  match v with
  | (mk_sudoku_chunks x x1 x2 x3 x4 x5) => x5
  end.

(* Why3 assumption *)
Definition square_start (v:sudoku_chunks): (array int31) :=
  match v with
  | (mk_sudoku_chunks x x1 x2 x3 x4 x5) => x4
  end.

(* Why3 assumption *)
Definition row_offsets (v:sudoku_chunks): (array int31) :=
  match v with
  | (mk_sudoku_chunks x x1 x2 x3 x4 x5) => x3
  end.

(* Why3 assumption *)
Definition row_start (v:sudoku_chunks): (array int31) :=
  match v with
  | (mk_sudoku_chunks x x1 x2 x3 x4 x5) => x2
  end.

(* Why3 assumption *)
Definition column_offsets (v:sudoku_chunks): (array int31) :=
  match v with
  | (mk_sudoku_chunks x x1 x2 x3 x4 x5) => x1
  end.

(* Why3 assumption *)
Definition column_start (v:sudoku_chunks): (array int31) :=
  match v with
  | (mk_sudoku_chunks x x1 x2 x3 x4 x5) => x
  end.

(* Why3 assumption *)
Definition chunk_valid_indexes (start:(array int31)) (offsets:(array
  int31)): Prop := ((to_int (length start)) = 81%Z) /\
  (((to_int (length offsets)) = 9%Z) /\ forall (i:Z) (o:Z), ((is_index i) /\
  ((0%Z <= o)%Z /\ (o < 9%Z)%Z)) -> (is_index ((to_int (get start
  i)) + (to_int (get offsets o)))%Z)).

(* Why3 assumption *)
Definition disjoint_chunks (start:(array int31)) (offsets:(array
  int31)): Prop := ((to_int (length start)) = 81%Z) /\
  (((to_int (length offsets)) = 9%Z) /\ forall (i1:Z) (i2:Z) (o:Z),
  ((is_index i1) /\ ((is_index i2) /\ ((0%Z <= o)%Z /\ (o < 9%Z)%Z))) ->
  let s2 := (to_int (get start i2)) in ((~ ((to_int (get start i1)) = s2)) ->
  ~ (i1 = (s2 + (to_int (get offsets o)))%Z))).

(* Why3 assumption *)
Definition well_formed_sudoku (s:sudoku_chunks): Prop := (chunk_valid_indexes
  (column_start s) (column_offsets s)) /\ ((chunk_valid_indexes (row_start s)
  (row_offsets s)) /\ ((chunk_valid_indexes (square_start s)
  (square_offsets s)) /\ ((disjoint_chunks (column_start s)
  (column_offsets s)) /\ ((disjoint_chunks (row_start s) (row_offsets s)) /\
  (disjoint_chunks (square_start s) (square_offsets s)))))).

(* Why3 assumption *)
Definition valid_chunk (g:(map.Map.map Z int31)) (i:Z) (start:(array int31))
  (offsets:(array int31)): Prop := let s := (to_int (get start i)) in
  forall (o1:Z) (o2:Z), (((0%Z <= o1)%Z /\ (o1 < 9%Z)%Z) /\
  (((0%Z <= o2)%Z /\ (o2 < 9%Z)%Z) /\ ~ (o1 = o2))) -> let i1 :=
  (s + (to_int (get offsets o1)))%Z in let i2 := (s + (to_int (get offsets
  o2)))%Z in ((((1%Z <= (to_int (map.Map.get g i1)))%Z /\
  ((to_int (map.Map.get g i1)) <= 9%Z)%Z) /\ ((1%Z <= (to_int (map.Map.get g
  i2)))%Z /\ ((to_int (map.Map.get g i2)) <= 9%Z)%Z)) ->
  ~ ((to_int (map.Map.get g i1)) = (to_int (map.Map.get g i2)))).

(* Why3 assumption *)
Definition valid_column (s:sudoku_chunks) (g:(map.Map.map Z int31))
  (i:Z): Prop := (valid_chunk g i (column_start s) (column_offsets s)).

(* Why3 assumption *)
Definition valid_row (s:sudoku_chunks) (g:(map.Map.map Z int31))
  (i:Z): Prop := (valid_chunk g i (row_start s) (row_offsets s)).

(* Why3 assumption *)
Definition valid_square (s:sudoku_chunks) (g:(map.Map.map Z int31))
  (i:Z): Prop := (valid_chunk g i (square_start s) (square_offsets s)).

(* Why3 assumption *)
Definition valid (s:sudoku_chunks) (g:(map.Map.map Z int31)): Prop :=
  forall (i:Z), (is_index i) -> ((valid_column s g i) /\ ((valid_row s g
  i) /\ (valid_square s g i))).

(* Why3 assumption *)
Definition full (g:(map.Map.map Z int31)): Prop := forall (i:Z), (is_index
  i) -> ((1%Z <= (to_int (map.Map.get g i)))%Z /\ ((to_int (map.Map.get g
  i)) <= 9%Z)%Z).

(* Why3 assumption *)
Definition included (g1:(map.Map.map Z int31)) (g2:(map.Map.map Z
  int31)): Prop := forall (i:Z), ((is_index i) /\
  ((1%Z <= (to_int (map.Map.get g1 i)))%Z /\ ((to_int (map.Map.get g1
  i)) <= 9%Z)%Z)) -> ((to_int (map.Map.get g2 i)) = (to_int (map.Map.get g1
  i))).

Axiom subset_valid_chunk : forall (g:(map.Map.map Z int31)) (h:(map.Map.map Z
  int31)), (included g h) -> forall (i:Z) (s:(array int31)) (o:(array
  int31)), ((is_index i) /\ ((chunk_valid_indexes s o) /\ (valid_chunk h i s
  o))) -> (valid_chunk g i s o).

Axiom subset_valid : forall (s:sudoku_chunks) (g:(map.Map.map Z int31))
  (h:(map.Map.map Z int31)), ((well_formed_sudoku s) /\ ((included g h) /\
  (valid s h))) -> (valid s g).

(* Why3 assumption *)
Definition is_solution_for (s:sudoku_chunks) (sol:(map.Map.map Z int31))
  (data:(map.Map.map Z int31)): Prop := (included data sol) /\ ((full sol) /\
  (valid s sol)).

(* Why3 assumption *)
Inductive array1 (a:Type) :=
  | mk_array1 : Z -> (map.Map.map Z a) -> array1 a.
Axiom array1_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (array1 a).
Existing Instance array1_WhyType.
Implicit Arguments mk_array1 [[a]].

(* Why3 assumption *)
Definition elts1 {a:Type} {a_WT:WhyType a} (v:(array1 a)): (map.Map.map Z
  a) := match v with
  | (mk_array1 x x1) => x1
  end.

(* Why3 assumption *)
Definition length1 {a:Type} {a_WT:WhyType a} (v:(array1 a)): Z :=
  match v with
  | (mk_array1 x x1) => x
  end.

(* Why3 assumption *)
Definition get1 {a:Type} {a_WT:WhyType a} (a1:(array1 a)) (i:Z): a :=
  (map.Map.get (elts1 a1) i).

(* Why3 assumption *)
Definition set1 {a:Type} {a_WT:WhyType a} (a1:(array1 a)) (i:Z)
  (v:a): (array1 a) := (mk_array1 (length1 a1) (map.Map.set (elts1 a1) i v)).

(* Why3 assumption *)
Definition make1 {a:Type} {a_WT:WhyType a} (n:Z) (v:a): (array1 a) :=
  (mk_array1 n (map.Map.const v: (map.Map.map Z a))).

(* Why3 assumption *)
Definition valid_chunk_up_to (g:(map.Map.map Z int31)) (i:Z) (start:(array
  int31)) (offsets:(array int31)) (off:Z): Prop := let s :=
  (to_int (get start i)) in forall (o1:Z) (o2:Z), (((0%Z <= o1)%Z /\
  (o1 < off)%Z) /\ (((0%Z <= o2)%Z /\ (o2 < off)%Z) /\ ~ (o1 = o2))) ->
  let i1 := (s + (to_int (get offsets o1)))%Z in let i2 :=
  (s + (to_int (get offsets o2)))%Z in ((((1%Z <= (to_int (map.Map.get g
  i1)))%Z /\ ((to_int (map.Map.get g i1)) <= 9%Z)%Z) /\
  ((1%Z <= (to_int (map.Map.get g i2)))%Z /\ ((to_int (map.Map.get g
  i2)) <= 9%Z)%Z)) -> ~ ((to_int (map.Map.get g i1)) = (to_int (map.Map.get g
  i2)))).

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
Theorem WP_parameter_check_valid_chunk : forall (g:int31) (g1:(map.Map.map Z
  int31)) (i:int31) (start:int31) (start1:(map.Map.map Z int31))
  (offsets:int31) (offsets1:(map.Map.map Z int31)), let offsets2 :=
  (mk_array offsets offsets1) in let start2 := (mk_array start start1) in
  (((((0%Z <= (to_int g))%Z /\ (0%Z <= (to_int start))%Z) /\
  (0%Z <= (to_int offsets))%Z) /\ (((to_int g) = 81%Z) /\ ((valid_values
  g1) /\ ((is_index (to_int i)) /\ (chunk_valid_indexes start2
  offsets2))))) -> ((in_bounds 0%Z) -> forall (n0:int31),
  ((to_int n0) = 0%Z) -> ((in_bounds 1%Z) -> forall (n1:int31),
  ((to_int n1) = 1%Z) -> ((in_bounds 9%Z) -> forall (n9:int31),
  ((to_int n9) = 9%Z) -> ((in_bounds 10%Z) -> forall (n10:int31),
  ((to_int n10) = 10%Z) -> (((0%Z <= (to_int i))%Z /\
  ((to_int i) < (to_int start))%Z) -> let s := (map.Map.get start1
  (to_int i)) in ((0%Z <= (to_int n10))%Z -> ((0%Z <= (to_int n10))%Z ->
  forall (off:int31) (b:(map.Map.map Z bool)), (((0%Z <= (to_int off))%Z /\
  ((to_int off) <= 9%Z)%Z) /\ ((valid_chunk_up_to g1 (to_int i) start2
  offsets2 (to_int off)) /\ ((forall (o:Z), ((0%Z <= o)%Z /\
  (o < (to_int off))%Z) -> let v := (map.Map.get g1
  ((to_int s) + (to_int (map.Map.get offsets1 o)))%Z) in
  (((1%Z <= (to_int v))%Z /\ ((to_int v) <= 9%Z)%Z) -> ((map.Map.get b
  (to_int v)) = true))) /\ forall (j:Z), ((1%Z <= j)%Z /\ (j <= 9%Z)%Z) ->
  (((map.Map.get b j) = true) -> exists o:Z, ((0%Z <= o)%Z /\
  (o < (to_int off))%Z) /\ ((to_int (map.Map.get g1
  ((to_int s) + (to_int (map.Map.get offsets1 o)))%Z)) = j))))) ->
  forall (result:bool), ((result = true) <->
  ((to_int off) < (to_int n9))%Z) -> ((result = true) ->
  (((0%Z <= (to_int off))%Z /\ ((to_int off) < (to_int offsets))%Z) ->
  let o := (map.Map.get offsets1 (to_int off)) in ((in_bounds
  ((to_int s) + (to_int o))%Z) -> forall (o1:int31),
  ((to_int o1) = ((to_int s) + (to_int o))%Z) -> (((0%Z <= (to_int o1))%Z /\
  ((to_int o1) < (to_int g))%Z) -> let v := (map.Map.get g1 (to_int o1)) in
  forall (result1:bool), ((result1 = true) <->
  ((to_int n1) <= (to_int v))%Z) -> ((result1 = true) ->
  forall (result2:bool), ((result2 = true) <->
  ((to_int v) <= (to_int n9))%Z) -> ((result2 = true) ->
  (((0%Z <= (to_int n10))%Z /\ ((0%Z <= (to_int v))%Z /\
  ((to_int v) < (to_int n10))%Z)) -> (((map.Map.get b (to_int v)) = true) ->
  ~ (valid_chunk g1 (to_int i) start2 offsets2))))))))))))))))).
intros g g1 i start start1 offsets offsets1 offsets2 start2
(((h1,h2),h3),(h4,(h5,(h6,h7)))) h8 n0 h9 h10 n1 h11 h12 n9 h13 h14 n10 h15
(h16,h17) s h18 h19 off b ((h20,h21),(h22,(h23,h24))) result h25 h26
(h27,h28) o h29 o1 h30 (h31,h32) v result1 h33 h34 result2 h35 h36
(h37,(h38,h39)) h40.
rewrite h15 in *.
assert (H1: (1 <= to_int v <= 9)%Z) by intuition.
generalize (h24 (to_int v) H1 h40); intros h; clear h24.
elim h; clear h.
intros x (Hx,H).
Require Why3.
unfold valid_chunk.
intro H2.
unfold s.
apply (H2 x (to_int off)); clear H2.
why3 "cvc4" timelimit 5.
red in h7.
subst v.
subst offsets2.
unfold get.
simpl.
subst s.
rewrite H.
why3 "alt-ergo" timelimit 5.
subst v.
subst offsets2.
unfold get.
simpl.
subst s.
rewrite H.
rewrite h30.
why3 "cvc4" timelimit 5.
Qed.

