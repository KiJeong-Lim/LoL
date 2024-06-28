Require Import LoL.Prelude.Prelude.
Require Import LoL.Data.Vector.

Section PRIMITIVE_RECURSION. (* Reference: "https://github.com/princeton-vl/CoqGym/blob/master/coq_projects/goedel/primRec.v" *)

#[local] Open Scope program_scope.

Let arity : Set := nat.

Fixpoint naryFun (n : arity) : Type :=
  match n with
  | O => nat
  | S n' => nat -> naryFun n'
  end.

Fixpoint naryRel (n : arity) : Type :=
  match n with
  | O => Prop
  | S n' => nat -> naryRel n'
  end.

Fixpoint eval_const {n : arity} (m : nat) {struct n} : naryFun n :=
  match n with
  | O => m
  | S n' => B.const (eval_const (n := n') m)
  end.

Fixpoint eval_proj {n : arity} {struct n} : Fin.t n -> naryFun n :=
  match n with
  | O => Fin.case0
  | S n' => Fin.caseS (eval_const (n := n')) (B.const ∘ eval_proj (n := n'))
  end.

Fixpoint eval_vec {n : arity} (xs : Vector.t nat n) {struct xs} : naryFun n -> nat :=
  match xs with
  | VNil => B.id
  | VCons n' x xs' => fun f => eval_vec (n := n') xs' (f x)
  end.

Fixpoint eval_vec_1 {n : arity} {m : arity} (x : nat) (xs : Vector.t (naryFun (S n)) m) {struct xs} : Vector.t (naryFun n) m :=
  match xs with
  | VNil => VNil
  | VCons m' f xs' => VCons m' (f x) (eval_vec_1 (n := n) (m := m') x xs')
  end.

Definition eval_compose {n : arity} {m : arity} : Vector.t (naryFun n) m -> naryFun m -> naryFun n :=
  nat_rect (fun n : nat => forall m : nat, Vector.t (naryFun n) m -> naryFun m -> naryFun n) (@eval_vec) (fun n' : nat => fun IH => fun m : nat => fun xs : Vector.t (naryFun (S n')) m => fun f : naryFun m => fun x : nat => IH m (eval_vec_1 x xs) f) n m.

Fixpoint eval_compose_2 {n : arity} {struct n} : naryFun n -> naryFun (S n) -> naryFun n :=
  match n with
  | O => fun x : nat => fun f : nat -> nat => f x
  | S n' => fun f : naryFun (S n') => fun g : naryFun (S (S n')) => fun a : nat => eval_compose_2 (n := n') (f a) (fun x : nat => g x a)
  end.

Fixpoint eval_primRec {n : arity} (g : naryFun n) (h : naryFun (S (S n))) (a : nat) {struct a} : naryFun n :=
  match a with
  | O => g
  | S a' => eval_compose_2 (n := n) (eval_primRec (n := n) g h a') (h a')
  end.

Example eval_primRec_example1
  (g := fun m : nat => m)
  (h := fun n : nat => fun acc : nat => fun m : nat => S acc)
  (add := @eval_primRec 1 g h)
  : add 2 3 = 5.
Proof.
  reflexivity.
Qed.

Example eval_primRec_example2
  (g := fun m : nat => 0)
  (h := fun n : nat => fun acc : nat => fun m : nat => m + acc)
  (mult := @eval_primRec 1 g h)
  : mult 2 3 = 6.
Proof.
  reflexivity.
Qed.

Inductive PrimRec : arity -> Set :=
  | PR_succ : PrimRec 1
  | PR_zero : PrimRec 0
  | PR_proj (n : arity) (i : Fin.t n) : PrimRec n
  | PR_compose (n : arity) (m : arity) (g : PrimRecs n m) (h : PrimRec m) : PrimRec n
  | PR_primRec (n : arity) (g : PrimRec n) (h : PrimRec (S (S n))) : PrimRec (S n)
with PrimRecs : arity -> arity -> Set :=
  | PRs_nil (n : arity) : PrimRecs n 0
  | PRs_cons (n : arity) (m : arity) (f : PrimRec n) (fs : PrimRecs n m) : PrimRecs n (S m).

Fixpoint runPrimRec {n : arity} (f : PrimRec n) {struct f} : naryFun n :=
  match f with
  | PR_succ => S
  | PR_zero => O
  | PR_proj n i => eval_proj (n := n) i
  | PR_compose n m g h => eval_compose (n := n) (m := m) (runPrimRecs g) (runPrimRec h)
  | PR_primRec n g h => eval_primRec (n := n) (runPrimRec g) (runPrimRec h)
  end
with runPrimRecs {n : arity} {m : arity} (fs : PrimRecs n m) {struct fs} : Vector.t (naryFun n) m :=
  match fs with
  | PRs_nil n' => VNil
  | PRs_cons n' m' f fs' => VCons m' (runPrimRec f) (runPrimRecs fs')
  end.

Lemma runPrimRec_unfold (n : arity) (f : PrimRec n) :
  runPrimRec f =
  match f with
  | PR_succ => S
  | PR_zero => O
  | PR_proj n i => eval_proj i
  | PR_compose n m g h => eval_compose (runPrimRecs g) (runPrimRec h)
  | PR_primRec n g h => eval_primRec (runPrimRec g) (runPrimRec h)
  end.
Proof.
  destruct f; reflexivity.
Defined.

Lemma runPrimRecs_unfold (n : arity) (m : arity) (fs : PrimRecs n m) :
  runPrimRecs fs =
  match fs with
  | PRs_nil n' => VNil
  | PRs_cons n' m' f fs' => VCons m' (runPrimRec f) (runPrimRecs fs')
  end.
Proof.
  destruct fs; reflexivity.
Defined.

End PRIMITIVE_RECURSION.

Fixpoint first_nat (p : nat -> bool) (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => if p (first_nat p n') then first_nat p n' else n
  end.

Theorem first_nat_spec (p : nat -> bool) (n : nat)
  (WITNESS : p n = true)
  (m := first_nat p n)
  : p m = true /\ ⟪ MIN : forall i, p i = true -> i >= m ⟫.
Proof with eauto.
  assert (claim1 : forall x, p x = true -> p (first_nat p x) = true).
  { induction x as [ | x IH]... simpl. destruct (p (first_nat p x)) as [ | ] eqn: ?... }
  unnw. split... intros i p_i_eq_true.
  enough (claim2 : forall x, first_nat p x <= x).
  enough (claim3 : forall x, p (first_nat p x) = true -> (forall y, x < y -> first_nat p x = first_nat p y)).
  enough (claim4 : forall x, forall y, p y = true -> first_nat p x <= y)...
  - intros x y p_y_eq_true. destruct (le_gt_dec x y) as [x_le_y | x_gt_y].
    + eapply Nat.le_trans...
    + replace (first_nat p x) with (first_nat p y)...
  - intros x p_first_nat_p_x_eq_true y x_gt_y. induction x_gt_y as [ | y x_gt_y IH]; simpl.
    + rewrite p_first_nat_p_x_eq_true...
    + rewrite <- IH, p_first_nat_p_x_eq_true...
  - induction x as [ | x IH]... simpl.
    destruct (p (first_nat p x)) as [ | ]...
Qed.

Theorem nat_search_lemma (p : nat -> bool)
  (EXISTENCE : exists n : nat, p n = true)
  : { n : nat | p n = true }.
Proof.
  assert (COUNTABLE : isCountable nat).
  { exists B.id Some. reflexivity. }
  assert (P_dec : forall x : nat, {p x = true} + {p x <> true}).
  { intros x. now destruct (p x) as [ | ]; [left | right]. }
  pose proof (FUEL := @Acc_flip_search_step_P_0 nat COUNTABLE (fun x : nat => p x = true) EXISTENCE).
  exists (@search_go nat COUNTABLE (fun x : nat => p x = true) P_dec 0 FUEL). eapply search_go_correct.
Defined.

Definition nullary_mu (f : nat -> nat)
  (EXISTENCE : exists n : nat, f n = 0)
  : { n : nat | f n = 0 /\ (forall i, f i = 0 -> i >= n) }.
Proof.
  pose (p := fun n : nat => Nat.eqb (f n) 0).
  assert (EXISTENCE' : exists n : nat, p n = true).
  { destruct EXISTENCE as [n f_n_eq_0]. exists n. unfold p. rewrite Nat.eqb_eq. exact f_n_eq_0. }
  pose proof (nat_search_lemma p EXISTENCE') as [n WITNESS].
  exists (first_nat p n). unnw. pose proof (first_nat_spec p n WITNESS) as claim.
  simpl in claim. unnw. destruct claim as [claim1 claim2]. split.
  - rewrite <- Nat.eqb_eq with (n := f (first_nat p n)) (m := 0). exact claim1.
  - intros i f_i_eq_0. eapply claim2. unfold p. rewrite Nat.eqb_eq. exact f_i_eq_0.
Defined.

Example nullary_mu_example1
  (f := fun n : nat => if Nat.ltb n 3 then 1 else 0)
  (EXISTENCE := @ex_intro nat (fun n : nat => f n = 0) 5 eq_refl)
  : proj1_sig (nullary_mu f EXISTENCE) = 3.
Proof.
  reflexivity.
Qed.

Section MU_RECURSIVE.

#[local] Close Scope list_scope.
#[local] Open Scope vector_scope.

#[local] Notation " [ ] " := (VNil).
#[local] Notation " x :: xs " := (VCons _ x xs).
#[local] Notation " [ x ] " := (VCons _ x VNil).

Let Arity : Set := nat.

Inductive MuRec : Arity -> Set :=
  | MR_succ : MuRec 1
  | MR_zero : MuRec 0
  | MR_proj (n : Arity) (i : Fin.t n) : MuRec n
  | MR_compose (n : Arity) (m : Arity) (g : MuRecs n m) (h : MuRec m) : MuRec n
  | MR_primRec (n : Arity) (g : MuRec n) (h : MuRec (S (S n))) : MuRec (S n)
  | MR_mu (n : Arity) (g : MuRec (S n)) : MuRec n
with MuRecs : Arity -> Arity -> Set :=
  | MRs_nil (n : Arity) : MuRecs n 0
  | MRs_cons (n : Arity) (m : Arity) (f : MuRec n) (fs : MuRecs n m) : MuRecs n (S m).

Let Value : Type := nat.

Fixpoint MuRecGraph {n : Arity} (f : MuRec n) {struct f} : Vector.t Value n -> Value -> Prop :=
  match f with
  | MR_succ => fun xs : Vector.t Value 1 => fun z : Value => S (V.head xs) = z
  | MR_zero => fun xs : Vector.t Value 0 => fun z : Value => O = z
  | MR_proj n i => fun xs : Vector.t Value n => fun z : Value => xs !! i = z
  | MR_compose n m g h => fun xs : Vector.t Value n => fun z : Value => exists ys, MuRecsGraph g xs ys /\ MuRecGraph h ys z
  | MR_primRec n g h => fun xs : Vector.t Value (S n) => nat_rect (fun _ => Value -> Prop) (fun z : Value => MuRecGraph g (V.tail xs) z) (fun m : Value => fun acc : Value -> Prop => fun z : Value => exists y, acc y /\ MuRecGraph h (m :: y :: V.tail xs) z) (V.head xs)
  | MR_mu n g => fun xs : Vector.t Value n => fun z : Value => MuRecGraph g (z :: xs) 0 /\ (forall y, MuRecGraph g (y :: xs) 0 -> y >= z)
  end
with MuRecsGraph {n : Arity} {m : Arity} (fs : MuRecs n m) {struct fs} : Vector.t Value n -> Vector.t Value m -> Prop :=
  match fs with
  | MRs_nil n => fun xs : Vector.t Value n => fun z : Vector.t Value O => [] = z
  | MRs_cons n m f fs => fun xs : Vector.t Value n => fun z : Vector.t Value (S m) => exists y, exists ys, MuRecGraph f xs y /\ MuRecsGraph fs xs ys /\ y :: ys = z
  end.

End MU_RECURSIVE.
