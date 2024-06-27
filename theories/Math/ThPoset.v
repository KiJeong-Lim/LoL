Require Import LoL.Prelude.Prelude.
Require Import LoL.Prelude.Notations.

Section POSET_basic1.

#[local] Infix "\in" := E.elem : type_scope.
#[local] Infix "\subseteq" := E.isSubsetOf : type_scope.

Lemma PreOrder_iff {A : Type} (R : A -> A -> Prop)
  : PreOrder R <-> (forall x, forall y, R x y <-> (forall z, R z x -> R z y)).
Proof.
  now firstorder.
Qed.

Lemma leProp_unfold {A : Type} `{A_isPoset : isPoset A} (x : A) (y : A)
  : x =< y <-> (forall z, z =< x -> z =< y).
Proof.
  exact (proj1 (PreOrder_iff leProp) leProp_PreOrder x y).
Qed.

#[local] Close Scope nat_scope.

#[local] Notation "x >= y" := (y =< x) (only parsing) : type_scope.

Context {D : Type}.

Definition fixedpoints_of `{SETOID : isSetoid D} (f : D -> D) : ensemble D :=
  fun x => x == f x.

Definition prefixedpoints_of `{POSET : isPoset D} (f : D -> D) : ensemble D :=
  fun x => x >= f x.

Definition postfixpedpoints_of `{POSET : isPoset D} (f : D -> D) : ensemble D :=
  fun x => x =< f x.

Definition upperbounds_of `{POSET : isPoset D} (X : ensemble D) : ensemble D :=
  fun u => forall x : D, forall IN : x \in X, x =< u.

Definition lowerbounds_of `{POSET : isPoset D} (X: ensemble D) : ensemble D :=
  fun l => forall x : D, forall IN : x \in X, x >= l.

Definition is_supremum_of `{POSET : isPoset D} (sup_X : D) (X : ensemble D) : Prop :=
  forall u : D, sup_X =< u <-> u \in upperbounds_of X.

Definition is_infimum_of `{POSET : isPoset D} (inf_X : D) (X : ensemble D) : Prop :=
  forall l : D, inf_X >= l <-> l \in lowerbounds_of X.

End POSET_basic1.

#[global] Hint Unfold fixedpoints_of : mathhints.
#[global] Hint Unfold prefixedpoints_of : mathhints.
#[global] Hint Unfold postfixedpoints_of : mathhints.
#[global] Hint Unfold upperbounds_of : mathhints.
#[global] Hint Unfold lowerbounds_of : mathhints.

Class isDecidableTotalOrder (A : Type) `{POSET : isPoset A} : Type :=
  { compare (lhs : A) (rhs : A) : comparison
  ; compare_LT_implies (lhs : A) (rhs : A) (H_lt : compare lhs rhs = Lt) : lhs =< rhs /\ ~ lhs == rhs
  ; compare_EQ_implies (lhs : A) (rhs : A) (H_eq : compare lhs rhs = Eq) : lhs == rhs
  ; compare_GT_implies (lhs : A) (rhs : A) (H_gt : compare lhs rhs = Gt) : rhs =< lhs /\ ~ lhs == rhs
  }.

#[global] Hint Resolve compare_LT_implies : mathhints.
#[global] Hint Resolve compare_EQ_implies : mathhints.
#[global] Hint Resolve compare_GT_implies : mathhints.

Section LEXICOGRAPHICAL_ORDER.

Import ListNotations.

Context {A: Type} `{POSET : isPoset A} `{DECIDABLETOTALORDER : isDecidableTotalOrder A (POSET := POSET)}.

#[local] Infix "`compare`" := compare.

Fixpoint lex_compare (xs : list A) (ys : list A) {struct xs} : comparison :=
  match xs, ys with
  | [], [] => Eq
  | [], y :: ys => Lt
  | x :: xs, [] => Gt
  | x :: xs, y :: ys =>
    match compare x y with
    | Lt => Lt
    | Eq => lex_compare xs ys
    | Gt => Gt
    end
  end.

Definition lex_eq (lhs : list A) (rhs : list A) : Prop :=
  lex_compare lhs rhs = Eq.

Definition lex_le (lhs : list A) (rhs : list A) : Prop :=
  lex_compare lhs rhs = Lt \/ lex_compare lhs rhs = Eq.

Lemma compare_spec (lhs : A) (rhs : A) :
  match lhs `compare` rhs with
  | Lt => lhs =< rhs /\ ~ lhs == rhs
  | Eq => lhs == rhs
  | Gt => rhs =< lhs /\ ~ lhs == rhs
  end.
Proof.
  destruct (lhs `compare` rhs) eqn: H_compare_result; eauto with *.
Qed.

#[local]
Instance lex_eq_Equivalence
  : Equivalence lex_eq.
Proof with discriminate || eauto with *.
  unfold lex_eq. split.
  - intros xs1; induction xs1 as [ | x1 xs1 IH]; simpl...
    pose proof (claim1 := compare_spec x1 x1).
    destruct (compare x1 x1) eqn: H_compare_result1...
    all: contradiction (proj2 claim1)...
  - intros xs1 xs2; revert xs1 xs2; induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl...
    pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x1).
    destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x1) eqn: H_compare_result2...
    all: contradiction (proj2 claim2)...
  - intros xs1 xs2 xs3; revert xs1 xs3; induction xs2 as [ | x2 xs2 IH]; destruct xs1 as [ | x1 xs1]; destruct xs3 as [ | x3 xs3]; simpl...
    pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x3); pose proof (claim3 := compare_spec x1 x3).
    destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x3) eqn: H_compare_result2; destruct (compare x1 x3) eqn: H_compare_result3...
    all: contradiction (proj2 claim3)...
Qed.

#[local]
Instance listPointwiseEquivalence : isSetoid (list A) :=
  { eqProp := lex_eq
  ; eqProp_Equivalence := lex_eq_Equivalence
  }.

#[local]
Instance lex_le_PreOrder
  : PreOrder lex_le.
Proof with discriminate || eauto with *.
  assert (lemma1 : forall x1 : A, forall x2 : A, x1 =< x2 -> x2 =< x1 -> x1 == x2). { ii... }
  assert (lemma2 : forall x1 : A, forall x2 : A, x1 == x2 -> x1 =< x2). { ii... }
  assert (lemma3 : forall x1 : A, forall x2 : A, x1 == x2 -> x2 =< x1). { ii... }
  unfold lex_le. split.
  - intros xs1; right. eapply lex_eq_Equivalence.
  - intros xs1 xs2 xs3; revert xs1 xs3; induction xs2 as [ | x2 xs2 IH]; destruct xs1 as [ | x1 xs1]; destruct xs3 as [ | x3 xs3]; simpl...
    intros [H_false | H_false]...
    pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x3); pose proof (claim3 := compare_spec x1 x3); pose proof (claim4 := IH xs1 xs3).
    destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x3) eqn: H_compare_result2; destruct (compare x1 x3) eqn: H_compare_result3...
    + contradiction (proj2 claim3)...
    + contradiction (proj2 claim2)...
    + contradiction (proj2 claim3); eapply lemma1; [transitivity x2 | exact (proj1 claim3)]. eapply lemma2... exact (proj1 claim2).
    + contradiction (proj2 claim2)...
    + contradiction (proj2 claim1)...
    + contradiction (proj2 claim3); eapply lemma1; [transitivity x2 | exact (proj1 claim3)]. exact (proj1 claim1). eapply lemma2...
    + contradiction (proj2 claim1); eapply lemma1; [exact (proj1 claim1) | transitivity x3]. exact (proj1 claim2). eapply lemma2...
    + contradiction (proj2 claim1); eapply lemma1; [exact (proj1 claim1) | transitivity x3]. exact (proj1 claim2). exact (proj1 claim3).
    + intros ? [? | ?]...
    + intros [? | ?]...
    + intros [? | ?]...
    + intros [? | ?]...
Qed.

Lemma lex_le_flip_spec (lhs : list A) (rhs : list A) :
  match lex_compare lhs rhs with
  | Lt => lex_compare rhs lhs = Gt
  | Eq => lex_compare rhs lhs = Eq
  | Gt => lex_compare rhs lhs = Lt
  end.
Proof with discriminate || eauto with *.
  revert lhs rhs.
  assert (lemma1 : forall x1 : A, forall x2 : A, x1 =< x2 -> x2 =< x1 -> x1 == x2). { ii... }
  assert (lemma2 : forall x1 : A, forall x2 : A, x1 == x2 -> x1 =< x2). { ii... }
  assert (lemma3 : forall x1 : A, forall x2 : A, x1 == x2 -> x2 =< x1). { ii... }
  assert (lemma4 : forall xs1 : list A, forall xs2 : list A, lex_compare xs1 xs2 = Lt <-> lex_compare xs2 xs1 = Gt).
  { induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl... split...
    pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x1); pose proof (claim3 := IH xs2).
    destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x1) eqn: H_compare_result2...
    - contradiction (proj2 claim2)...
    - contradiction (proj2 claim2)...
    - contradiction (proj2 claim1)...
    - contradiction (proj2 claim1). eapply lemma1; [exact (proj1 claim1) | exact (proj1 claim2)].
    - contradiction (proj2 claim1)...
    - contradiction (proj2 claim1). eapply lemma1; [exact (proj1 claim2) | exact (proj1 claim1)].
  }
  assert (lemma5 : forall xs1 : list A, forall xs2 : list A, lex_compare xs1 xs2 = Eq <-> lex_compare xs2 xs1 = Eq).
  { induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl; try done.
    pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x1); pose proof (claim3 := IH xs2).
    destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x1) eqn: H_compare_result2.
    - done.
    - contradiction (proj2 claim2)...
    - contradiction (proj2 claim2)...
    - contradiction (proj2 claim1)...
    - split...
    - done.
    - contradiction (proj2 claim1)...
    - split...
    - done.
  }
  assert (lemma6 : forall xs1 : list A, forall xs2 : list A, lex_compare xs1 xs2 = Gt <-> lex_compare xs2 xs1 = Lt) by firstorder.
  intros lhs rhs; destruct (lex_compare lhs rhs) eqn: H_compare_result; now firstorder.
Qed.

Corollary lex_le_flip_iff (lhs : list A) (rhs : list A) (compare_result : comparison) :
  lex_compare lhs rhs = compare_result <->
  match compare_result with
  | Lt => lex_compare rhs lhs = Gt
  | Eq => lex_compare rhs lhs = Eq
  | Gt => lex_compare rhs lhs = Lt
  end.
Proof.
  split.
  - ii; subst compare_result. exact (lex_le_flip_spec lhs rhs).
  - pose proof (lex_le_flip_spec rhs lhs) as claim1. intros H_eq.
    destruct compare_result eqn: H_compare_result; now rewrite H_eq in claim1.
Qed.

#[local]
Instance lex_le_PartialOrder
  : PartialOrder lex_eq lex_le.
Proof with discriminate || eauto with *.
  intros xs1 xs2; cbn. unfold flip, lex_eq, lex_le.
  pose proof (claim1 := lex_le_flip_spec xs1 xs2).
  destruct (lex_compare xs1 xs2) eqn: H_compare_result.
  - split...
  - split... intros [? [H_false | H_false]].
    all: rewrite H_false in claim1...
  - split... intros [[? | ?] ?]...
Qed.

#[local]
Instance listLexicographicalOrder : isPoset (list A) :=
  { leProp := lex_le
  ; Poset_isSetoid := listPointwiseEquivalence
  ; leProp_PreOrder := lex_le_PreOrder
  ; leProp_PartialOrder := lex_le_PartialOrder
  }.

#[local] Obligation Tactic := cbn; unfold lex_le, lex_eq; ii.
#[global, program] Instance listLexicographicalOrder_liftsDecidableTotalOrder : isDecidableTotalOrder (list A) :=
  { compare := lex_compare }.
Next Obligation.
  rewrite H_lt. split; [now left | congruence].
Qed.
Next Obligation.
  exact H_eq.
Qed.
Next Obligation.
  pose proof (lex_le_flip_spec lhs rhs) as H.
  rewrite H_gt in H. split; [now left | congruence].
Qed.

End LEXICOGRAPHICAL_ORDER.

Section NAT_TOSET.

#[local]
Instance nat_isPoset : isPoset nat :=
  { leProp := le
  ; Poset_isSetoid := trivialSetoid
  ; leProp_PreOrder := Nat.le_preorder
  ; leProp_PartialOrder := Nat.le_partialorder
  }.

Fixpoint nat_compare (x : nat) (y : nat) {struct x} : comparison :=
  match x, y with
  | O, O => Eq
  | O, S y' => Lt
  | S x', O => Gt
  | S x', S y' => nat_compare x' y'
  end.

Lemma nat_compare_lt (x : nat) (y : nat)
  (hyp_lt : nat_compare x y = Lt)
  : x <= y /\ x <> y.
Proof with eauto with *.
  revert x y hyp_lt. induction x as [ | x IH], y as [ | y]; simpl; try (congruence || lia).
  intros hyp_lt. pose proof (IH y hyp_lt) as [x_le_y x_ne_y]...
Qed.

Lemma nat_compare_eq (x : nat) (y : nat)
  (hyp_lt: nat_compare x y = Eq)
  : x = y.
Proof with eauto with *.
  revert x y hyp_lt. induction x as [ | x IH], y as [ | y]; simpl; ii.
  - reflexivity.
  - inversion hyp_lt.
  - inversion hyp_lt.
  - pose proof (IH y hyp_lt) as x_eq_y...
Qed.

Lemma nat_compare_gt (x : nat) (y : nat)
  (hyp_lt : nat_compare x y = Gt)
  : y <= x /\ x <> y.
Proof with eauto with *.
  cbn. revert x y hyp_lt. induction x as [ | x IH], y as [ | y]; simpl; ii.
  - inversion hyp_lt.
  - inversion hyp_lt.
  - split...
  - pose proof (IH y hyp_lt) as [y_le_x x_ne_y]...
Qed.

#[local]
Instance nat_hasDecidableTotalOrder : isDecidableTotalOrder nat (POSET := nat_isPoset) :=
  { compare := nat_compare
  ; compare_LT_implies := nat_compare_lt
  ; compare_EQ_implies := nat_compare_eq
  ; compare_GT_implies := nat_compare_gt
  }.

End NAT_TOSET.
