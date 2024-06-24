Require Import LoL.Prelude.Prelude.
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

#[local]
Tactic Notation "introFZ" :=
  let i := fresh "i" in
  intro i; pattern i; revert i;
  apply case0.

#[local]
Tactic Notation "introFS" ident( i' ) :=
  let i := fresh "i" in
  intro i; pattern i; revert i;
  apply caseS; [ | intros i'].

#[global]
Instance Fin_hasEqDec {n : nat}
  : hasEqDec (Fin.t n).
Proof.
  red. induction n as [ | n IH]; [introFZ | introFS i1'; introFS i2'].
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

Fixpoint to_nat {n : nat} (i : Fin.t n) {struct i} : nat :=
  match i with
  | @FZ n' => O
  | @FS n' i' => S (to_nat i')
  end.

End Fin.

Notation FZ := Fin.FZ.
Notation FS := Fin.FS.

#[local]
Tactic Notation "introFZ" :=
  let i := fresh "i" in
  intro i; pattern i; revert i;
  apply Fin.case0.

#[local]
Tactic Notation "introFS" ident( i' ) :=
  let i := fresh "i" in
  intro i; pattern i; revert i;
  apply Fin.caseS; [ | intros i'].

#[global] Declare Scope vec_scope.

Module Vector.

#[universes(template)]
Inductive t (A : Type) : nat -> Type :=
  | VNil : t A O
  | VCons (n : nat) (x : A) (xs : t A n) : t A (S n).

#[global] Arguments VNil {A}.
#[global] Arguments VCons {A} (n) (x) (xs).

End Vector.

#[global] Bind Scope vec_scope with Vector.t.

Notation " [ ] " := (@Vector.VNil _) : vec_scope.
Notation " x :: xs " := (@Vector.VCons _ _ x xs) : vec_scope.

Notation VNil := Vector.VNil.
Notation VCons := Vector.VCons.

#[local] Open Scope vec_scope.

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

Infix " !! " := nth (left associativity, at level 25).

#[global]
Tactic Notation "introVNil" :=
  let xs := fresh "xs" in
  intro xs; pattern xs; revert xs;
  apply Vector.case0.

#[global]
Tactic Notation "introVCons" ident( x' ) ident( xs' ) :=
  let xs := fresh "xs" in
  intro xs; pattern xs; revert xs;
  apply Vector.caseS; intros x' xs'.

Lemma nth_unfold {A : Type} {n : nat} (xs : Vector.t A n) (i : Fin.t n) :
  xs !! i = (match i in Fin.t m return Vector.t A m -> A with FZ => fun v => head v | FS i' => fun v => tail v !! i' end) xs.
Proof. revert i; destruct xs as [ | n' x' xs']; [introFZ | introFS i']; reflexivity. Qed.

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
  - introFZ.
  - introFS i.
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
  induction n; [introFZ | introFS i]; simpl; eauto.
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
  - introVNil; introFZ.
  - introVCons xs xss; introFS i; simpl.
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

Definition vec (n : nat) (A : Type) : Type := Vector.t A n.

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
  ; eqProp_Equivalence := relation_on_image_liftsEquivalence nth (arrow_isSetoid (A := Fin.t n) (B := A) A_isSetoid).(eqProp_Equivalence)
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
Proof. reflexivity. Defined.

Lemma tail_unfold {A : Type} (n : nat) (x : A) (xs : Vector.t A n)
  : tail (x :: xs) = xs.
Proof. reflexivity. Defined.

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
