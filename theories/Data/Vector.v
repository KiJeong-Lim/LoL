Require Import LoL.Prelude.Prelude.
Require Import LoL.Prelude.Notations.
Require Import LoL.Math.ThN.

Module Fin.

Inductive t : nat -> Set :=
  | FZ (n : nat) : t (S n)
  | FS (n : nat) (i : t n) : t (S n).

#[global] Arguments FZ {n}%nat.
#[global] Arguments FS {n}%nat (i).

Lemma case0 {phi : Fin.t O -> Type}
  : forall i, phi i.
Proof.
  intros i.
  exact (
    match i as this in Fin.t n return (match n as m return Fin.t m -> Type with O => fun i => phi i | S n' => fun i => unit end) this with
    | @FZ n' => tt
    | @FS n' i' => tt
    end
  ).
Defined.

Lemma caseS {n' : nat} {phi : Fin.t (S n') -> Type}
  (phiFZ : phi (@FZ n'))
  (phiFS : forall i' : Fin.t n', phi (@FS n' i'))
  : forall i, phi i.
Proof.
  intros i; revert phi phiFZ phiFS.
  exact (
    match i as this in Fin.t n return (match n as m return Fin.t m -> Type with O => fun i => unit | S m' => fun i => forall phi' : Fin.t (S m') -> Type, phi' (@FZ m') -> (forall i' : Fin.t m', phi' (@FS m' i')) -> phi' i end) this with
    | @FZ n' => fun phi : Fin.t (S n') -> Type => fun phiFZ : phi (@FZ n') => fun phiFS : forall i' : Fin.t n', phi (@FS n' i') => phiFZ
    | @FS n' i' => fun phi : Fin.t (S n') -> Type => fun phiFS : phi (@FZ n') => fun phiFS : forall i' : Fin.t n', phi (@FS n' i') => phiFS i'
    end
  ).
Defined.

Lemma rectS (phi : forall n, Fin.t (S n) -> Type)
  (phiFZ : forall n : nat, phi n (@FZ n))
  (phiFS : forall n : nat, forall i : Fin.t (S n), phi n i -> phi (S n) (@FS (S n) i))
  : forall n, forall (i: Fin.t (S n)), phi n i.
Proof.  
  exact (
    fix rectS_fix (n : nat) (i : Fin.t (S n)) {struct i} : phi n i :=
    match i with
    | @FZ k => phiFZ k
    | @FS O i' => @case0 (fun i'' : Fin.t 0 => phi 0 (@FS 0 i'')) i'
    | @FS (S n') i' => phiFS n' i' (rectS_fix n' i')
    end
  ).
Defined.

Ltac case0 :=
  let i := fresh "i" in
  intro i; pattern i; revert i;
  apply case0.

Ltac caseS i' :=
  let i := fresh "i" in
  intro i; pattern i; revert i;
  apply caseS; [ | intros i'].

#[global]
Instance Fin_hasEqDec {n : nat}
  : hasEqDec (Fin.t n).
Proof.
  red. induction n as [ | n IH]; [Fin.case0 | Fin.caseS i1'; Fin.caseS i2'].
  - left; reflexivity.
  - right; congruence.
  - right; congruence.
  - pose proof (IH i1' i2') as [H_eq | H_ne]; [left | right].
    + f_equal. exact (H_eq). 
    + intros H_eq. contradiction H_ne.
      set (f := fun i: Fin.t (S n) =>
        match i in Fin.t m return Fin.t (pred m) -> Fin.t (pred m) with
        | @FZ n' => fun d: Fin.t n' => d
        | @FS n' i' => fun d: Fin.t n' => i'
        end
      ).
      apply f_equal2 with (f := f) (x1 := FS i1') (y1 := FS i2') (x2 := i1') (y2 := i1') in H_eq.
      { exact (H_eq). }
      { reflexivity. }
Defined.

Definition fin (n : nat) : Set := @sig nat (gt n).

Fixpoint runFin {n : nat} (i : Fin.t n) {struct i} : fin n :=
  match i in Fin.t x return @sig nat (gt x) with
  | @FZ n' => @exist nat (gt (S n')) O (le_intro_S_n_le_S_m le_intro_0_le_n)
  | @FS n' i' => @exist nat (gt (S n')) (S (proj1_sig (runFin i'))) (le_intro_S_n_le_S_m (proj2_sig (runFin i')))
  end.

Fixpoint getFin {n : nat} (m : nat) {struct n} : m < n -> Fin.t n :=
  match n as x return S m <= x -> Fin.t x with
  | O => lt_elim_n_lt_0
  | S n' =>
    match m as y return S y <= S n' -> Fin.t (S n') with
    | O => fun hyp_lt : O < S n' => FZ
    | S m' => fun hyp_lt : S m' < S n' => FS (getFin m' (lt_elim_n_lt_S_m hyp_lt))
    end
  end.

Lemma runFin_getFin_id {m : nat} {n : nat} (hyp_lt : m < n)
  : runFin (getFin m hyp_lt) = exist (gt n) m hyp_lt.
Proof.
  revert n hyp_lt. induction m as [ | m IH]; intros [ | n'] hyp_lt; cbn in *.
  - exact (lt_elim_n_lt_0 hyp_lt).
  - eapply f_equal, le_pirrel.
  - exact (lt_elim_n_lt_0 hyp_lt).
  - rewrite IH; cbn. eapply f_equal, le_pirrel.
Qed.

Lemma getFin_runFin_id {n : nat} (i : Fin.t n)
  : getFin (proj1_sig (runFin i)) (proj2_sig (runFin i)) = i.
Proof.
  induction i as [n' | n' i' IH].
  - reflexivity.
  - cbn. eapply f_equal. etransitivity; [eapply f_equal, le_pirrel | exact (IH)].
Qed.

Definition evalFin {n : nat} (i : Fin.t n) : nat :=
  proj1_sig (runFin i).

Lemma evalFin_unfold {n : nat} (i : Fin.t n) :
  evalFin i =
  match i with
  | FZ => O
  | FS i' => S (evalFin i')
  end.
Proof.
  destruct i; reflexivity.
Defined.

Lemma evalFin_inj {n : nat} (i1 : Fin.t n) (i2 : Fin.t n)
  (hyp_eq : evalFin i1 = evalFin i2)
  : i1 = i2.
Proof.
  unfold evalFin in hyp_eq.
  rewrite <- getFin_runFin_id with (i := i1).
  rewrite <- getFin_runFin_id with (i := i2).
  destruct (runFin i1) as [m1 hyp_lt1].
  destruct (runFin i2) as [m2 hyp_lt2].
  cbn in *. subst m1. eapply f_equal. eapply le_pirrel.
Qed.

Definition incrFin {m : nat} : forall n : nat, Fin.t m -> Fin.t (n + m) :=
  fix incrFin_fix (n : nat) (i : Fin.t m) {struct n} : Fin.t (n + m) :=
  match n as x return Fin.t (x + m) with
  | O => i
  | S n' => FS (incrFin_fix n' i)
  end.

Lemma incrFin_spec {m : nat} (n : nat) (i : Fin.t m)
  : evalFin (incrFin n i) = n + evalFin i.
Proof with eauto.
  induction n as [ | n IH]; simpl...
  rewrite evalFin_unfold. eapply f_equal...
Qed.

End Fin.

Notation FZ := Fin.FZ.
Notation FS := Fin.FS.

#[global] Declare Scope vec_scope.

Module Vector.

#[universes(template)]
Inductive t (A : Type) : nat -> Type :=
  | VNil : t A O
  | VCons (n : nat) (x : A) (xs : t A n) : t A (S n).

#[global] Arguments VNil {A}.
#[global] Arguments VCons {A} (n) (x) (xs).

#[global] Delimit Scope vec_scope with t.

End Vector.

#[global] Bind Scope vec_scope with Vector.t.

Notation " [ ] " := (@Vector.VNil _) : vec_scope.
Notation " x :: xs " := (@Vector.VCons _ _ x xs) : vec_scope.
Notation " [ x ] " := (@Vector.VCons _ _ x (@Vector.VNil _)) : vec_scope.

Notation VNil := Vector.VNil.
Notation VCons := Vector.VCons.

#[local] Open Scope vec_scope.

Module V.

Section Accessories.

Context {A : Type}.

#[local] Notation vec := (Vector.t A).

Definition cast {n : nat} {m : nat} (H_eq : n = m) : vec n -> vec m :=
  match H_eq with
  | eq_refl => fun xs => xs
  end.

Lemma case0 (phi : vec O -> Type)
  (phiVNil : phi [])
  : forall xs, phi xs.
Proof.
  refine (
    let claim1 (xs : vec O) : forall H_eq : O = O, phi (cast H_eq xs) :=
      match xs in Vector.t _ m return forall H_eq : m = O, phi (cast H_eq xs) with
      | VNil => fun H_eq : O = O => _
      | VCons n x' xs' => fun H_eq : S n = O => _
      end
    in _
  ).
  { intros xs. exact (claim1 xs eq_refl). }
Unshelve.
  - rewrite eq_pirrel_fromEqDec with (H_eq1 := H_eq) (H_eq2 := eq_refl).
    exact (phiVNil).
  - inversion H_eq.
Qed.

Lemma caseS {n' : nat} (phi : vec (S n') -> Type)
  (phiVCons: forall x' : A, forall xs' : vec n', phi (x' :: xs'))
  : forall xs, phi xs.
Proof.
  refine (
    let claim1 (xs : vec (S n')) : forall H_eq : S n' = S n', phi (cast H_eq xs) :=
      match xs in Vector.t _ m return forall H_eq : m = S n', phi (cast H_eq xs) with
      | VNil => fun H_eq : O = S n' => _
      | VCons n x' xs' => fun H_eq : S n = S n' => _
      end
    in _
  ).
  { intros xs. exact (claim1 xs eq_refl). }
Unshelve.
  - inversion H_eq.
  - pose proof (f_equal pred H_eq) as n_eq_n'. simpl in n_eq_n'. subst n'.
    rewrite eq_pirrel_fromEqDec with (H_eq1 := H_eq) (H_eq2 := eq_refl).
    exact (phiVCons x' xs').
Qed.

Lemma rectS (phi : forall n, vec (S n) -> Type)
  (phiOnce : forall x, phi 0 (x :: []))
  (phiCons : forall n, forall x, forall xs, phi n xs -> phi (S n) (x :: xs))
  : forall n, forall xs, phi n xs.
Proof.
  exact (
    fix rectS_fix (n : nat) (xs : vec (S n)) {struct xs} : phi n xs :=
    match xs with
    | VCons 0 x xs' =>
      match xs' with
      | VNil => phiOnce x
      end
    | VCons (S n') x xs' => phiCons n' x xs' (rectS_fix n' xs')
    end
  ).
Defined.

Let uncons' (n : nat) (xs : vec (S n)) : S n = S n -> A * vec n :=
  match xs in Vector.t _ m return S n = m -> A * vec (pred m) with
  | VNil => fun H_eq: S n = O => S_eq_O_elim H_eq
  | VCons n' x xs' => fun H_eq: S n = S n' => (x, xs')
  end.

Definition head {n : nat} (xs : vec (S n)) : A :=
  fst (uncons' n xs eq_refl).

Definition tail {n : nat} (xs : vec (S n)) : vec n :=
  snd (uncons' n xs eq_refl).

Fixpoint nth {n : nat} (xs : vec n) {struct xs} : Fin.t n -> A :=
  match xs with
  | [] => Fin.case0
  | x :: xs => Fin.caseS x (nth xs)
  end.

End Accessories.

#[local] Infix " !! " := nth.

#[local]
Tactic Notation "introVNil" :=
  let xs := fresh "xs" in
  intro xs; pattern xs; revert xs;
  apply V.case0.

#[local]
Tactic Notation "introVCons" ident( x' ) ident( xs' ) :=
  let xs := fresh "xs" in
  intro xs; pattern xs; revert xs;
  apply V.caseS; intros x' xs'.

Lemma nth_unfold {A : Type} {n : nat} (xs : Vector.t A n) (i : Fin.t n) :
  xs !! i = (match i in Fin.t m return Vector.t A m -> A with FZ => fun v => head v | FS i' => fun v => tail v !! i' end) xs.
Proof.
  revert i; destruct xs as [ | n' x' xs']; [Fin.case0 | Fin.caseS i']; reflexivity.
Qed.

Theorem vec_ext_eq {A : Type} {n : nat} (lhs : Vector.t A n) (rhs : Vector.t A n)
  : lhs = rhs <-> forall i, lhs !! i = rhs !! i.
Proof.
  split.
  - now intros ?; subst.
  - revert lhs rhs. induction n as [ | n IH].
    + introVNil; introVNil. intros H_eq.
      reflexivity.
    + introVCons x xs; introVCons y ys. intros H_eq.
      assert (x = y) as x_eq_y by exact (H_eq FZ).
      enough (xs = ys) as xs_eq_ys by congruence.
      eapply IH. intros i. eapply H_eq with (i := FS i).
Qed.

Fixpoint map {A : Type} {B : Type} {n : nat} (f : A -> B) (xs : Vector.t A n) {struct xs} : Vector.t B n :=
  match xs with
  | [] => []
  | x :: xs' => f x :: map f xs'
  end.

Lemma map_spec {A : Type} {B : Type} {n : nat} (f : A -> B) (xs : Vector.t A n)
  : forall i : Fin.t n, f (xs !! i) = map f xs !! i.
Proof.
  induction xs as [ | n x xs IH].
  - Fin.case0.
  - Fin.caseS i.
    + reflexivity.
    + exact (IH i).
Qed.

Fixpoint replicate {A : Type} {n : nat} {struct n} : A -> Vector.t A n :=
  match n with
  | O => fun x => []
  | S n' => fun x => x :: replicate (n := n') x
  end.

Lemma replicate_spec {A : Type} {n : nat} (x: A)
  : forall i : Fin.t n, x = replicate x !! i.
Proof.
  induction n; [Fin.case0 | Fin.caseS i]; simpl; eauto.
Qed.

Fixpoint diagonal {A : Type} {n : nat} {struct n} : Vector.t (Vector.t A n) n -> Vector.t A n :=
  match n with
  | O => fun xss => []
  | S n' => fun xss => head (head xss) :: diagonal (n := n') (map tail (tail xss))
  end.

Lemma diagonal_spec {A : Type} {n : nat} (xss: Vector.t (Vector.t A n) n)
  : forall i : Fin.t n, xss !! i !! i = diagonal xss !! i.
Proof.
  revert xss; induction n as [ | n IH].
  - introVNil; Fin.case0.
  - introVCons xs xss; Fin.caseS i; simpl.
    + now rewrite nth_unfold.
    + now rewrite nth_unfold; rewrite <- IH with (i := i); rewrite map_spec with (f := tail) (xs := xss) (i := i).
Qed.

Ltac red_vec := first
  [ rewrite <- diagonal_spec
  | rewrite <- map_spec
  | rewrite <- replicate_spec
  ].

Section INSTANCES.

#[global]
Instance vector_hasEqDec {A : Type} {n : nat}
  (A_hasEqDec : hasEqDec A)
  : hasEqDec (Vector.t A n).
Proof.
  red. induction n as [ | n IH]; intros lhs rhs.
  - left. revert lhs rhs. introVNil; introVNil; reflexivity.
  - pose proof (IH (tail lhs) (tail rhs)) as [H_EQ2 | H_NE2]; [pose proof (A_hasEqDec (head lhs) (head rhs)) as [H_EQ1 | H_NE1] | ].
    + left. revert lhs rhs H_EQ1 H_EQ2.
      introVCons x xs; introVCons y ys; intros H_head H_tail.
      cbv in *. congruence.
    + right. revert lhs rhs H_NE1 H_EQ2.
      introVCons x xs; introVCons y ys; intros H_head _ H_contradiction.
      now apply f_equal with (f := head) in H_contradiction.
    + right. revert lhs rhs H_NE2.
      introVCons x xs; introVCons y ys. intros H_tail H_contradiction.
      now apply f_equal with (f := tail) in H_contradiction.
Defined.

Definition vec (n : nat) (A : Type) : Type :=
  Vector.t A n.

#[local]
Instance vec_isMonad {n : nat} : isMonad (vec n) :=
  { pure {A} (x: A) := replicate x
  ; bind {A} {B} (m: vec n A) (k: A -> vec n B) := diagonal (map k m)
  }.

Definition zipWith {n : nat} {A : Type} {B : Type} {C : Type} (f : A -> B -> C) (xs : Vector.t A n) (ys : Vector.t B n) : Vector.t C n :=
  B.liftM2 (MONAD := vec_isMonad) (A := A) (B := B) (C := C) f xs ys.

Lemma zipWith_spec {n : nat} {A : Type} {B : Type} {C : Type} (f : A -> B -> C) (xs : Vector.t A n) (ys : Vector.t B n)
  : forall i, f (xs !! i) (ys !! i) = zipWith f xs ys !! i.
Proof.
  cbn; ii. repeat red_vec. reflexivity.
Qed.

#[local]
Instance vec_isSetoid (n : nat) (A : Type) `(A_isSetoid : isSetoid A) : isSetoid (vec n A) :=
  { eqProp (lhs : vec n A) (rhs : vec n A) := forall i, lhs !! i == rhs !! i
  ; eqProp_Equivalence := relation_on_image_liftsEquivalence (arrow_isSetoid (A := Fin.t n) (B := A) A_isSetoid).(eqProp_Equivalence) nth
  }.

#[local] Instance vec_isSetoid1 {n : nat} : isSetoid1 (vec n) := vec_isSetoid n.

#[global]
Instance vec_isNiceMonad {n: nat}
  : isNiceMonad (vec n) (M_isMonad := vec_isMonad) (M_isSetoid1 := vec_isSetoid1).
Proof.
  split; cbn; ii; (repeat red_vec); congruence.
Qed.

End INSTANCES.

Fixpoint foldr {A : Type} {B : Type} {n : nat} (f : A -> B -> B) (z : B) (xs : Vector.t A n) : B :=
  match xs with
  | [] => z
  | x :: xs => f x (foldr f z xs)
  end.

Lemma head_unfold {A : Type} (n : nat) (x : A) (xs : Vector.t A n)
  : head (x :: xs) = x.
Proof.
  reflexivity.
  Defined.

Lemma tail_unfold {A : Type} (n : nat) (x : A) (xs : Vector.t A n)
  : tail (x :: xs) = xs.
Proof.
  reflexivity.
Defined.

Fixpoint gen_nat_vec (n : nat) (seed : nat) : Vector.t nat n :=
  match n with
  | O => []
  | S n' => fst (cp seed) :: gen_nat_vec n' (snd (cp seed))
  end.

Fixpoint gen_nat_vec_linv {n : nat} (xs : Vector.t nat n) : nat :=
  match xs with
  | [] => O
  | x :: xs' => cpInv x (gen_nat_vec_linv xs')
  end.

Lemma gen_nat_vec_linv_left_inverse n (xs : Vector.t nat n)
  : gen_nat_vec n (gen_nat_vec_linv xs) = xs.
Proof.
  induction xs as [ | n x xs IH].
  - reflexivity.
  - simpl. destruct (cp (cpInv x (gen_nat_vec_linv xs))) as [E_x E_xs] eqn: H_OBS.
    simpl. rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. congruence.
Qed.

Section SECOND_CITIZEN_EQUALITY.

Context {A : Type}.

Fixpoint to_list {n : nat} (xs : Vector.t A n) {struct xs} : list A :=
  match xs with
  | [] => L.nil
  | x :: xs => L.cons x (to_list xs)
  end.

Lemma to_list_inj {n : nat} (xs1 : Vector.t A n) (xs2 : Vector.t A n)
  (EXT_EQ : to_list xs1 = to_list xs2)
  : xs1 = xs2.
Proof.
  revert xs1 xs2 EXT_EQ. induction xs1 as [ | n x1 xs1 IH].
  - introVNil; simpl. i. reflexivity.
  - introVCons x2 xs2; simpl. i. f_equal.
    + apply f_equal with (f := L.hd x1) in EXT_EQ. exact EXT_EQ.
    + apply f_equal with (f := @L.tl A) in EXT_EQ. eapply IH. exact EXT_EQ. 
Qed.

Fixpoint from_list (xs : list A) {struct xs} : Vector.t A (L.length xs) :=
  match xs with
  | L.nil => []
  | L.cons x xs => x :: from_list xs
  end.

Lemma to_list_from_list (xs : list A)
  : to_list (from_list xs) = xs.
Proof.
  induction xs as [ | x xs IH]; simpl.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Inductive vec_heq (n : nat) (xs : Vector.t A n) : forall m, Vector.t A m -> Prop :=
  | vec_ext_heq_refl
    : vec_heq n xs n xs.

#[local] Notation " xs =~= xs' " := (vec_heq _ xs _ xs') : type_scope.

Lemma len_eq_from_vec_heq (n : nat) (m : nat) (xs : Vector.t A n) (xs' : Vector.t A m)
  (HEQ : xs =~= xs')
  : n = m.
Proof.
  exact (
    match HEQ in vec_heq _ _ m xs' return n = m with
    | vec_ext_heq_refl _ _ => @eq_refl nat n
    end
  ).
Defined.

Lemma eq_from_vec_heq (n : nat) (xs : Vector.t A n) (xs' : Vector.t A n)
  (HEQ : xs =~= xs')
  : xs = xs'.
Proof.
  pose proof (
    match HEQ in vec_heq _ _ m xs' return @existT nat (Vector.t A) n xs = @existT nat (Vector.t A) m xs' with
    | vec_ext_heq_refl _ _ => @eq_refl (@sigT nat (Vector.t A)) (@existT nat (Vector.t A) n xs)
    end
  ) as EQ.
  apply B.projT2_eq in EQ.
  - exact EQ.
  - clear xs' HEQ EQ. intros xs' EQ. rewrite eq_pirrel_fromEqDec with (H_eq1 := EQ) (H_eq2 := eq_refl). reflexivity. 
Defined.

Lemma from_list_to_list (n : nat) (xs : Vector.t A n)
  : from_list (to_list xs) =~= xs.
Proof.
  induction xs as [ | n x xs IH]; simpl.
  - econs.
  - destruct IH. rewrite to_list_from_list. econs.
Qed.

Lemma heq_refl (n1 : nat) (xs1 : Vector.t A n1)
  : xs1 =~= xs1.
Proof.
  econs.
Qed.

Lemma heq_sym (n1 : nat) (n2 : nat) (xs1 : Vector.t A n1) (xs2 : Vector.t A n2)
  (EQ : xs1 =~= xs2)
  : xs2 =~= xs1.
Proof.
  destruct EQ. econs.
Qed.

Lemma heq_trans (n1 : nat) (n2 : nat) (n3 : nat) (xs1 : Vector.t A n1) (xs2 : Vector.t A n2) (xs3 : Vector.t A n3)
  (EQ : xs1 =~= xs2)
  (EQ' : xs2 =~= xs3)
  : xs1 =~= xs3.
Proof.
  destruct EQ. exact EQ'.
Qed.

Lemma heq_iff (n : nat) (m : nat) (xs : Vector.t A n) (xs' : Vector.t A m)
  : xs =~= xs' <-> to_list xs = to_list xs'.
Proof.
  split.
  - intros HEQ. destruct HEQ. reflexivity.
  - intros EQ. eapply heq_trans. 2: eapply from_list_to_list.
    rewrite <- EQ. eapply heq_sym. eapply from_list_to_list.
Qed.

Theorem heq_congruence (P : forall n : nat, Vector.t A n -> Prop) (n : nat) (n' : nat) (xs : Vector.t A n) (xs' : Vector.t A n')
  (HEQ : xs =~= xs')
  : P n xs <-> P n' xs'.
Proof.
  destruct HEQ. reflexivity.
Qed.

End SECOND_CITIZEN_EQUALITY.

Fixpoint snoc {A : Type} {n : nat} (xs : Vector.t A n) (x : A) {struct xs} : Vector.t A (S n) :=
  match xs with
  | [] => [x]
  | x' :: xs' => x' :: snoc xs' x
  end.

Lemma to_list_snoc {A : Type} {n : nat} (xs : Vector.t A n) (x : A)
  : to_list (snoc xs x) = L.app (to_list xs) (L.cons x L.nil).
Proof.
  revert x. induction xs as [ | n x' xs' IH]; simpl; i.
  - reflexivity.
  - f_equal. eapply IH.
Qed.

Fixpoint rev {A : Type} {n : nat} (xs : Vector.t A n) {struct xs} : Vector.t A n :=
  match xs with
  | [] => []
  | x :: xs => snoc (rev xs) x
  end.

Lemma to_list_rev {A : Type} {n : nat} (xs : Vector.t A n)
  : to_list (rev xs) = L.rev (to_list xs).
Proof.
  induction xs as [ | n x xs IH]; simpl.
  - reflexivity.
  - rewrite to_list_snoc. f_equal. exact IH.
Qed.

End V.

#[global]
Tactic Notation "introVNil" :=
  let xs := fresh "xs" in
  intro xs; pattern xs; revert xs;
  apply V.case0.

#[global]
Tactic Notation "introVCons" ident( x' ) ident( xs' ) :=
  let xs := fresh "xs" in
  intro xs; pattern xs; revert xs;
  apply V.caseS; intros x' xs'.

Infix "!!" := V.nth.
