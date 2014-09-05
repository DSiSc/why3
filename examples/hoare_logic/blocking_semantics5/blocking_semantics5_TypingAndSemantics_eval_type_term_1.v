(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require bool.Bool.
Require int.Int.
Require map.Map.
Require list.List.

(* Why3 assumption *)
Inductive datatype :=
  | TYunit : datatype
  | TYint : datatype
  | TYbool : datatype.
Axiom datatype_WhyType : WhyType datatype.
Existing Instance datatype_WhyType.

(* Why3 assumption *)
Inductive value :=
  | Vvoid : value
  | Vint : Z -> value
  | Vbool : bool -> value.
Axiom value_WhyType : WhyType value.
Existing Instance value_WhyType.

(* Why3 assumption *)
Inductive operator :=
  | Oplus : operator
  | Ominus : operator
  | Omult : operator
  | Ole : operator.
Axiom operator_WhyType : WhyType operator.
Existing Instance operator_WhyType.

Axiom mident : Type.
Parameter mident_WhyType : WhyType mident.
Existing Instance mident_WhyType.

Axiom mident_decide : forall (m1:mident) (m2:mident), (m1 = m2) \/
  ~ (m1 = m2).

Axiom ident : Type.
Parameter ident_WhyType : WhyType ident.
Existing Instance ident_WhyType.

Axiom ident_decide : forall (m1:ident) (m2:ident), (m1 = m2) \/ ~ (m1 = m2).

(* Why3 assumption *)
Inductive term :=
  | Tvalue : value -> term
  | Tvar : ident -> term
  | Tderef : mident -> term
  | Tbin : term -> operator -> term -> term.
Axiom term_WhyType : WhyType term.
Existing Instance term_WhyType.

(* Why3 assumption *)
Inductive fmla :=
  | Fterm : term -> fmla
  | Fand : fmla -> fmla -> fmla
  | Fnot : fmla -> fmla
  | Fimplies : fmla -> fmla -> fmla
  | Flet : ident -> term -> fmla -> fmla
  | Fforall : ident -> datatype -> fmla -> fmla.
Axiom fmla_WhyType : WhyType fmla.
Existing Instance fmla_WhyType.

(* Why3 assumption *)
Inductive stmt :=
  | Sskip : stmt
  | Sassign : mident -> term -> stmt
  | Sseq : stmt -> stmt -> stmt
  | Sif : term -> stmt -> stmt -> stmt
  | Sassert : fmla -> stmt
  | Swhile : term -> fmla -> stmt -> stmt.
Axiom stmt_WhyType : WhyType stmt.
Existing Instance stmt_WhyType.

Axiom decide_is_skip : forall (s:stmt), (s = Sskip) \/ ~ (s = Sskip).

(* Why3 assumption *)
Definition env := (map.Map.map mident value).

(* Why3 assumption *)
Definition stack := (list (ident* value)%type).

Parameter get_stack: ident -> (list (ident* value)%type) -> value.

Axiom get_stack_def : forall (i:ident) (pi:(list (ident* value)%type)),
  match pi with
  | Init.Datatypes.nil => ((get_stack i pi) = Vvoid)
  | (Init.Datatypes.cons (x, v) r) => ((x = i) -> ((get_stack i pi) = v)) /\
      ((~ (x = i)) -> ((get_stack i pi) = (get_stack i r)))
  end.

Axiom get_stack_eq : forall (x:ident) (v:value) (r:(list (ident*
  value)%type)), ((get_stack x (Init.Datatypes.cons (x, v) r)) = v).

Axiom get_stack_neq : forall (x:ident) (i:ident) (v:value) (r:(list (ident*
  value)%type)), (~ (x = i)) -> ((get_stack i (Init.Datatypes.cons (x,
  v) r)) = (get_stack i r)).

Parameter eval_bin: value -> operator -> value -> value.

Axiom eval_bin_def : forall (x:value) (op:operator) (y:value), match (x,
  y) with
  | ((Vint x1), (Vint y1)) =>
      match op with
      | Oplus => ((eval_bin x op y) = (Vint (x1 + y1)%Z))
      | Ominus => ((eval_bin x op y) = (Vint (x1 - y1)%Z))
      | Omult => ((eval_bin x op y) = (Vint (x1 * y1)%Z))
      | Ole => ((x1 <= y1)%Z -> ((eval_bin x op y) = (Vbool true))) /\
          ((~ (x1 <= y1)%Z) -> ((eval_bin x op y) = (Vbool false)))
      end
  | (_, _) => ((eval_bin x op y) = Vvoid)
  end.

(* Why3 assumption *)
Fixpoint eval_term (sigma:(map.Map.map mident value)) (pi:(list (ident*
  value)%type)) (t:term) {struct t}: value :=
  match t with
  | (Tvalue v) => v
  | (Tvar id) => (get_stack id pi)
  | (Tderef id) => (map.Map.get sigma id)
  | (Tbin t1 op t2) => (eval_bin (eval_term sigma pi t1) op (eval_term sigma
      pi t2))
  end.

(* Why3 assumption *)
Fixpoint eval_fmla (sigma:(map.Map.map mident value)) (pi:(list (ident*
  value)%type)) (f:fmla) {struct f}: Prop :=
  match f with
  | (Fterm t) => ((eval_term sigma pi t) = (Vbool true))
  | (Fand f1 f2) => (eval_fmla sigma pi f1) /\ (eval_fmla sigma pi f2)
  | (Fnot f1) => ~ (eval_fmla sigma pi f1)
  | (Fimplies f1 f2) => (eval_fmla sigma pi f1) -> (eval_fmla sigma pi f2)
  | (Flet x t f1) => (eval_fmla sigma (Init.Datatypes.cons (x,
      (eval_term sigma pi t)) pi) f1)
  | (Fforall x TYint f1) => forall (n:Z), (eval_fmla sigma
      (Init.Datatypes.cons (x, (Vint n)) pi) f1)
  | (Fforall x TYbool f1) => forall (b:bool), (eval_fmla sigma
      (Init.Datatypes.cons (x, (Vbool b)) pi) f1)
  | (Fforall x TYunit f1) => (eval_fmla sigma (Init.Datatypes.cons (x,
      Vvoid) pi) f1)
  end.

(* Why3 assumption *)
Definition valid_fmla (p:fmla): Prop := forall (sigma:(map.Map.map mident
  value)) (pi:(list (ident* value)%type)), (eval_fmla sigma pi p).

(* Why3 assumption *)
Inductive one_step: (map.Map.map mident value) -> (list (ident*
  value)%type) -> stmt -> (map.Map.map mident value) -> (list (ident*
  value)%type) -> stmt -> Prop :=
  | one_step_assign : forall (sigma:(map.Map.map mident value))
      (sigma':(map.Map.map mident value)) (pi:(list (ident* value)%type))
      (x:mident) (t:term), (sigma' = (map.Map.set sigma x (eval_term sigma pi
      t))) -> (one_step sigma pi (Sassign x t) sigma' pi Sskip)
  | one_step_seq_noskip : forall (sigma:(map.Map.map mident value))
      (sigma':(map.Map.map mident value)) (pi:(list (ident* value)%type))
      (pi':(list (ident* value)%type)) (s1:stmt) (s1':stmt) (s2:stmt),
      (one_step sigma pi s1 sigma' pi' s1') -> (one_step sigma pi (Sseq s1
      s2) sigma' pi' (Sseq s1' s2))
  | one_step_seq_skip : forall (sigma:(map.Map.map mident value))
      (pi:(list (ident* value)%type)) (s:stmt), (one_step sigma pi
      (Sseq Sskip s) sigma pi s)
  | one_step_if_true : forall (sigma:(map.Map.map mident value))
      (pi:(list (ident* value)%type)) (t:term) (s1:stmt) (s2:stmt),
      ((eval_term sigma pi t) = (Vbool true)) -> (one_step sigma pi (Sif t s1
      s2) sigma pi s1)
  | one_step_if_false : forall (sigma:(map.Map.map mident value))
      (pi:(list (ident* value)%type)) (t:term) (s1:stmt) (s2:stmt),
      ((eval_term sigma pi t) = (Vbool false)) -> (one_step sigma pi (Sif t
      s1 s2) sigma pi s2)
  | one_step_assert : forall (sigma:(map.Map.map mident value))
      (pi:(list (ident* value)%type)) (f:fmla), (eval_fmla sigma pi f) ->
      (one_step sigma pi (Sassert f) sigma pi Sskip)
  | one_step_while_true : forall (sigma:(map.Map.map mident value))
      (pi:(list (ident* value)%type)) (cond:term) (inv:fmla) (body:stmt),
      ((eval_fmla sigma pi inv) /\ ((eval_term sigma pi
      cond) = (Vbool true))) -> (one_step sigma pi (Swhile cond inv body)
      sigma pi (Sseq body (Swhile cond inv body)))
  | one_step_while_false : forall (sigma:(map.Map.map mident value))
      (pi:(list (ident* value)%type)) (cond:term) (inv:fmla) (body:stmt),
      ((eval_fmla sigma pi inv) /\ ((eval_term sigma pi
      cond) = (Vbool false))) -> (one_step sigma pi (Swhile cond inv body)
      sigma pi Sskip).

(* Why3 assumption *)
Inductive many_steps: (map.Map.map mident value) -> (list (ident*
  value)%type) -> stmt -> (map.Map.map mident value) -> (list (ident*
  value)%type) -> stmt -> Z -> Prop :=
  | many_steps_refl : forall (sigma:(map.Map.map mident value))
      (pi:(list (ident* value)%type)) (s:stmt), (many_steps sigma pi s sigma
      pi s 0%Z)
  | many_steps_trans : forall (sigma1:(map.Map.map mident value))
      (sigma2:(map.Map.map mident value)) (sigma3:(map.Map.map mident value))
      (pi1:(list (ident* value)%type)) (pi2:(list (ident* value)%type))
      (pi3:(list (ident* value)%type)) (s1:stmt) (s2:stmt) (s3:stmt) (n:Z),
      (one_step sigma1 pi1 s1 sigma2 pi2 s2) -> ((many_steps sigma2 pi2 s2
      sigma3 pi3 s3 n) -> (many_steps sigma1 pi1 s1 sigma3 pi3 s3
      (n + 1%Z)%Z)).

Axiom steps_non_neg : forall (sigma1:(map.Map.map mident value))
  (sigma2:(map.Map.map mident value)) (pi1:(list (ident* value)%type))
  (pi2:(list (ident* value)%type)) (s1:stmt) (s2:stmt) (n:Z), (many_steps
  sigma1 pi1 s1 sigma2 pi2 s2 n) -> (0%Z <= n)%Z.

(* Why3 assumption *)
Definition reductible (sigma:(map.Map.map mident value)) (pi:(list (ident*
  value)%type)) (s:stmt): Prop := exists sigma':(map.Map.map mident value),
  exists pi':(list (ident* value)%type), exists s':stmt, (one_step sigma pi s
  sigma' pi' s').

(* Why3 assumption *)
Definition type_value (v:value): datatype :=
  match v with
  | Vvoid => TYunit
  | (Vint _) => TYint
  | (Vbool _) => TYbool
  end.

(* Why3 assumption *)
Inductive type_operator: operator -> datatype -> datatype -> datatype ->
  Prop :=
  | Type_plus : (type_operator Oplus TYint TYint TYint)
  | Type_minus : (type_operator Ominus TYint TYint TYint)
  | Type_mult : (type_operator Omult TYint TYint TYint)
  | Type_le : (type_operator Ole TYint TYint TYbool).

(* Why3 assumption *)
Definition type_stack := (list (ident* datatype)%type).

Parameter get_vartype: ident -> (list (ident* datatype)%type) -> datatype.

Axiom get_vartype_def : forall (i:ident) (pi:(list (ident* datatype)%type)),
  match pi with
  | Init.Datatypes.nil => ((get_vartype i pi) = TYunit)
  | (Init.Datatypes.cons (x, ty) r) => ((x = i) -> ((get_vartype i
      pi) = ty)) /\ ((~ (x = i)) -> ((get_vartype i pi) = (get_vartype i r)))
  end.

(* Why3 assumption *)
Definition type_env := (map.Map.map mident datatype).

(* Why3 assumption *)
Inductive type_term: (map.Map.map mident datatype) -> (list (ident*
  datatype)%type) -> term -> datatype -> Prop :=
  | Type_value : forall (sigma:(map.Map.map mident datatype))
      (pi:(list (ident* datatype)%type)) (v:value), (type_term sigma pi
      (Tvalue v) (type_value v))
  | Type_var : forall (sigma:(map.Map.map mident datatype)) (pi:(list (ident*
      datatype)%type)) (v:ident) (ty:datatype), ((get_vartype v pi) = ty) ->
      (type_term sigma pi (Tvar v) ty)
  | Type_deref : forall (sigma:(map.Map.map mident datatype))
      (pi:(list (ident* datatype)%type)) (v:mident) (ty:datatype),
      ((map.Map.get sigma v) = ty) -> (type_term sigma pi (Tderef v) ty)
  | Type_bin : forall (sigma:(map.Map.map mident datatype)) (pi:(list (ident*
      datatype)%type)) (t1:term) (t2:term) (op:operator) (ty1:datatype)
      (ty2:datatype) (ty:datatype), ((type_term sigma pi t1 ty1) /\
      ((type_term sigma pi t2 ty2) /\ (type_operator op ty1 ty2 ty))) ->
      (type_term sigma pi (Tbin t1 op t2) ty).

(* Why3 assumption *)
Inductive type_fmla: (map.Map.map mident datatype) -> (list (ident*
  datatype)%type) -> fmla -> Prop :=
  | Type_term : forall (sigma:(map.Map.map mident datatype))
      (pi:(list (ident* datatype)%type)) (t:term), (type_term sigma pi t
      TYbool) -> (type_fmla sigma pi (Fterm t))
  | Type_conj : forall (sigma:(map.Map.map mident datatype))
      (pi:(list (ident* datatype)%type)) (f1:fmla) (f2:fmla), ((type_fmla
      sigma pi f1) /\ (type_fmla sigma pi f2)) -> (type_fmla sigma pi
      (Fand f1 f2))
  | Type_neg : forall (sigma:(map.Map.map mident datatype)) (pi:(list (ident*
      datatype)%type)) (f:fmla), (type_fmla sigma pi f) -> (type_fmla sigma
      pi (Fnot f))
  | Type_implies : forall (sigma:(map.Map.map mident datatype))
      (pi:(list (ident* datatype)%type)) (f1:fmla) (f2:fmla), (type_fmla
      sigma pi f1) -> ((type_fmla sigma pi f2) -> (type_fmla sigma pi
      (Fimplies f1 f2)))
  | Type_let : forall (sigma:(map.Map.map mident datatype)) (pi:(list (ident*
      datatype)%type)) (x:ident) (t:term) (f:fmla) (ty:datatype), (type_term
      sigma pi t ty) -> ((type_fmla sigma (Init.Datatypes.cons (x, ty) pi)
      f) -> (type_fmla sigma pi (Flet x t f)))
  | Type_forall : forall (sigma:(map.Map.map mident datatype))
      (pi:(list (ident* datatype)%type)) (x:ident) (f:fmla) (ty:datatype),
      (type_fmla sigma (Init.Datatypes.cons (x, ty) pi) f) -> (type_fmla
      sigma pi (Fforall x ty f)).

(* Why3 assumption *)
Inductive type_stmt: (map.Map.map mident datatype) -> (list (ident*
  datatype)%type) -> stmt -> Prop :=
  | Type_skip : forall (sigma:(map.Map.map mident datatype))
      (pi:(list (ident* datatype)%type)), (type_stmt sigma pi Sskip)
  | Type_seq : forall (sigma:(map.Map.map mident datatype)) (pi:(list (ident*
      datatype)%type)) (s1:stmt) (s2:stmt), (type_stmt sigma pi s1) ->
      ((type_stmt sigma pi s2) -> (type_stmt sigma pi (Sseq s1 s2)))
  | Type_assigns : forall (sigma:(map.Map.map mident datatype))
      (pi:(list (ident* datatype)%type)) (x:mident) (t:term) (ty:datatype),
      ((map.Map.get sigma x) = ty) -> ((type_term sigma pi t ty) ->
      (type_stmt sigma pi (Sassign x t)))
  | Type_if : forall (sigma:(map.Map.map mident datatype)) (pi:(list (ident*
      datatype)%type)) (t:term) (s1:stmt) (s2:stmt), (type_term sigma pi t
      TYbool) -> ((type_stmt sigma pi s1) -> ((type_stmt sigma pi s2) ->
      (type_stmt sigma pi (Sif t s1 s2))))
  | Type_assert : forall (sigma:(map.Map.map mident datatype))
      (pi:(list (ident* datatype)%type)) (p:fmla), (type_fmla sigma pi p) ->
      (type_stmt sigma pi (Sassert p))
  | Type_while : forall (sigma:(map.Map.map mident datatype))
      (pi:(list (ident* datatype)%type)) (cond:term) (body:stmt) (inv:fmla),
      (type_fmla sigma pi inv) -> ((type_term sigma pi cond TYbool) ->
      ((type_stmt sigma pi body) -> (type_stmt sigma pi (Swhile cond inv
      body)))).

(* Why3 assumption *)
Definition compatible_env (sigma:(map.Map.map mident value))
  (sigmat:(map.Map.map mident datatype)) (pi:(list (ident* value)%type))
  (pit:(list (ident* datatype)%type)): Prop := (forall (id:mident),
  ((type_value (map.Map.get sigma id)) = (map.Map.get sigmat id))) /\
  forall (id:ident), ((type_value (get_stack id pi)) = (get_vartype id pit)).

Axiom type_inversion : forall (v:value),
  match (type_value v) with
  | TYbool => exists b:bool, (v = (Vbool b))
  | TYint => exists n:Z, (v = (Vint n))
  | TYunit => (v = Vvoid)
  end.

Require Import Why3.

Ltac ae := why3 "alt-ergo" timelimit 3.

(* Why3 goal *)
Theorem eval_type_term : forall (t:term), forall (x:term) (x1:operator)
  (x2:term), (t = (Tbin x x1 x2)) -> ((forall (sigma:(map.Map.map mident
  value)) (pi:(list (ident* value)%type)) (sigmat:(map.Map.map mident
  datatype)) (pit:(list (ident* datatype)%type)) (ty:datatype),
  (compatible_env sigma sigmat pi pit) -> ((type_term sigmat pit x2 ty) ->
  ((type_value (eval_term sigma pi x2)) = ty))) ->
  ((forall (sigma:(map.Map.map mident value)) (pi:(list (ident* value)%type))
  (sigmat:(map.Map.map mident datatype)) (pit:(list (ident* datatype)%type))
  (ty:datatype), (compatible_env sigma sigmat pi pit) -> ((type_term sigmat
  pit x ty) -> ((type_value (eval_term sigma pi x)) = ty))) ->
  forall (sigma:(map.Map.map mident value)) (pi:(list (ident* value)%type))
  (sigmat:(map.Map.map mident datatype)) (pit:(list (ident* datatype)%type))
  (ty:datatype), (compatible_env sigma sigmat pi pit) -> ((type_term sigmat
  pit t ty) -> ((type_value (eval_term sigma pi t)) = ty)))).
(* Why3 intros t x x1 x2 h1 h2 h3 sigma pi sigmat pit ty h4 h5. *)
intros t x x1 x2 H;rewrite H in *;clear H.
simpl; intros.
inversion H2; subst; clear H2.
destruct H9 as (h1 & h2 & h3).
generalize (type_inversion (eval_term sigma pi x)).
generalize (type_inversion (eval_term sigma pi x2)).
destruct h3; ae.
Qed.

