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
  | VCons n' x xs' => fun f => eval_vec xs' (f x)
  end.

Fixpoint eval_vec_1 {n : arity} {m : arity} (x : nat) (xs : Vector.t (naryFun (S n)) m) {struct xs} : Vector.t (naryFun n) m :=
  match xs with
  | VNil => VNil
  | VCons m' f xs' => VCons m' (f x) (eval_vec_1 x xs')
  end.

Definition eval_compose {n : arity} {m : arity} : Vector.t (naryFun n) m -> naryFun m -> naryFun n :=
  nat_rect (fun n : nat => forall m : nat, Vector.t (naryFun n) m -> naryFun m -> naryFun n) (@eval_vec) (fun n' : nat => fun IH => fun m : nat => fun xs : Vector.t (naryFun (S n')) m => fun f : naryFun m => fun x : nat => IH m (eval_vec_1 x xs) f) n m.

Fixpoint eval_compose_2 {n : arity} {struct n} : naryFun n -> naryFun (S n) -> naryFun n :=
  match n with
  | O => fun x : nat => fun f : nat -> nat => f x
  | S n' =>
    fun f : naryFun (S n') => fun g : naryFun (S (S n')) => fun a : nat =>
    eval_compose_2 (n := n') (f a) (fun x : nat => g x a)
  end.

Fixpoint eval_primRec {n : arity} (g : naryFun n) (h : naryFun (S (S n))) (a : arity) {struct a} : naryFun n :=
  match a with
  | O => g
  | S a' => eval_compose_2 (eval_primRec g h a') (h a')
  end.

Inductive PrimRec : arity -> Set :=
  | PR_succ : PrimRec 1
  | PR_zero : PrimRec 0
  | PR_proj (n : nat) (i : Fin.t n) : PrimRec n
  | PR_compose (n : nat) (m : nat) (g : PrimRecs n m) (h : PrimRec m) : PrimRec n
  | PR_primRec (n : nat) (g : PrimRec n) (h : PrimRec (S (S n))) : PrimRec (S n)
with PrimRecs : arity -> nat -> Set :=
  | PRs_nil (n : nat) : PrimRecs n 0
  | PRs_cons (n : nat) (m : nat) (f : PrimRec n) (fs : PrimRecs n m) : PrimRecs n (S m).

Fixpoint runPrimRec {n : arity} (f : PrimRec n) {struct f} : naryFun n :=
  match f with
  | PR_succ => S
  | PR_zero => 0
  | PR_proj n i => eval_proj i
  | PR_compose n m g h => eval_compose (n := n) (m := m) (runPrimRecs g) (runPrimRec h)
  | PR_primRec n g h => eval_primRec (n := n) (runPrimRec g) (runPrimRec h)
  end
with runPrimRecs {n : arity} {m : arity} (fs : PrimRecs n m) {struct fs} : Vector.t (naryFun n) m :=
  match fs with
  | PRs_nil n' => VNil
  | PRs_cons n' m' f fs' => VCons m' (runPrimRec f) (runPrimRecs fs')
  end.

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
