Require Import LoL.Prelude.Prelude.
Require Import LoL.Math.ThN.
Require Import LoL.Data.Vector.

Fixpoint first_nat (p : nat -> bool) (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => if p (first_nat p n') then first_nat p n' else n
  end.

Theorem first_nat_spec (p : nat -> bool) (n : nat)
  (WITNESS : p n = true)
  (m := first_nat p n)
  : p m = true /\ ⟪ MIN : forall i, p i = true -> i >= m ⟫.
Proof with eauto. (* This proof is assisted by "Clare Jang". *)
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
  : { n : nat | (forall i, i < n -> exists y, y > 0 /\ f i = y) /\ f n = 0 }.
Proof.
  pose (p := fun n : nat => Nat.eqb (f n) 0).
  assert (EXISTENCE' : exists n : nat, p n = true).
  { destruct EXISTENCE as [n f_n_eq_0]. exists n. unfold p. rewrite Nat.eqb_eq. exact f_n_eq_0. }
  pose proof (nat_search_lemma p EXISTENCE') as [n WITNESS].
  exists (first_nat p n). unnw. pose proof (first_nat_spec p n WITNESS) as claim.
  simpl in claim. unnw. destruct claim as [claim1 claim2]. split.
  - intros i H_lt. specialize claim2 with (i := i). unfold p in claim2. rewrite Nat.eqb_eq in claim2. fold p in claim2. destruct (f i) as [ | y'].
    + lia.
    + exists (S y'). lia.
  - rewrite <- Nat.eqb_eq with (n := f (first_nat p n)) (m := 0). exact claim1.
Defined.

Example nullary_mu_example1
  (f := fun n : nat => if Nat.ltb n 3 then 1 else 0)
  (EXISTENCE := @ex_intro nat (fun n : nat => f n = 0) 5 eq_refl)
  : proj1_sig (nullary_mu f EXISTENCE) = 3.
Proof.
  reflexivity.
Qed.

Section UNBOUNDED_MINIMIZATION. (* Reference: "https://github.com/DmxLarchey/Murec_Extraction/blob/murec_artifact/theories/standalone.v" *)

#[local] Infix "\in" := E.elem : type_scope.
#[local] Infix "\subseteq" := E.isSubsetOf : type_scope.

Section BETWEEN. (* Reference: "https://github.com/DmxLarchey/Murec_Extraction/blob/murec_artifact/theories/between.v" *)

Variable P : nat -> Prop.

Definition wBetween (n : nat) (m : nat) : Prop :=
  forall i, n <= i -> i < m -> P i.

Lemma wBetween_refl (n : nat)
  : wBetween n n.
Proof.
  red. lia.
Qed.

Lemma wBetween_next (n : nat)
  : forall m, wBetween n m -> P m -> wBetween n (S m).
Proof.
  ii. inv H2.
  - trivial.
  - eapply H; lia.
Qed.

Definition Between (n : nat) (m : nat) : Prop :=
  n <= m /\ wBetween n m.

Lemma Between_refl (n : nat)
  : Between n n.
Proof.
  split. lia. eapply wBetween_refl.
Qed.

Lemma Between_next (n : nat)
  : forall m, Between n m -> P m -> Between n (S m).
Proof.
  ii. destruct H. split.
  - lia.
  - eapply wBetween_next; trivial.
Qed.

End BETWEEN.

Lemma Between_ind (P : nat -> Prop) (a : nat) (b : nat)
  (H_Between : Between (fun n => P (S n) -> P n) a b)
  : P b -> P a.
Proof.
  destruct H_Between as [a_le_b H_wBetween]. red in H_wBetween.
  revert H_wBetween. induction a_le_b as [ | m LE IH].
  - i. exact H.
  - i. eapply IH.
    + i. eapply H_wBetween.
      * exact H0.
      * exact (le_S (S i) m H1).
      * exact H2.
    + eapply H_wBetween.
      * exact LE.
      * exact (le_n (S m)).
      * exact H.
Defined.

Variable F : nat -> nat -> Prop.

Definition umin s y := F y 0 /\ Between (fun n => exists k, F n (S k)) s y.

Definition umin' y :=  F y 0 /\ forall n, n < y -> exists k, F n (S k).

Variable Ffun : forall x, forall y1, forall y2, F x y1 -> F x y2 -> y1 = y2.

Variable f : forall x : nat, (exists y, F x y) -> { y : nat | F x y }.

Let T n := exists k, F n k.

Let P n := F n 0.

Let Q n := exists k, F n (S k).

Lemma PQ_absurd (n : nat)
  : P n -> Q n -> False.
Proof.
  intros p (y & q). red in p. pose proof (Ffun n 0 (S y) p q) as H_false. inv H_false.
Qed.

Inductive Dumin (n : nat) : Prop :=
  | Dumin_stop : T n -> P n -> Dumin n
  | Dumin_next : T n -> Dumin (S n) -> Dumin n.

#[local] Arguments Dumin_stop {_}.
#[local] Arguments Dumin_next {_}.

Definition Dumin_pi1 {n} (d : Dumin n) : T n :=
  match d with
  | Dumin_stop t _ => t
  | Dumin_next t _ => t
  end.

Definition Dumin_pi2 {n} (d : Dumin n) : Q n -> Dumin (S n) :=
  match d with
  | Dumin_stop t p  => fun q => False_ind _ (PQ_absurd n p q)
  | Dumin_next _ d' => fun _ => d'
  end.

Definition Pre_umin (s : nat) (n : nat) : Prop :=
  n \in E.intersection (E.intersection T P) (Between T s).

Definition Post_umin (s : nat) (n : nat) : Prop :=
  n \in E.intersection (E.intersection T P) (Between (E.intersection T Q) s).

Lemma Pre_umin_Dumin {s : nat}
  (EXISTENCE : exists n, Pre_umin s n)
  : Dumin s.
Proof.
  revert EXISTENCE. intros [n IN]. red in IN. autorewrite with datatypes in IN. des.
  pose proof (Dumin_stop IN IN1). revert H. eapply Between_ind.
  do 2 red in IN0. des. red. split. exact IN0. ii. eapply Dumin_next; trivial. eapply IN2; trivial.
Qed.

Fixpoint loop (s : nat) (n : nat) (d : Dumin n) (b : Between Q s n) {struct d} : { x : nat | umin s x }.
Proof.
  pose proof (f n (Dumin_pi1 d)) as [k H_k]. revert H_k. destruct k as [ | k']; i.
  - exists n. split.
    + exact H_k.
    + exact b.
  - eapply loop with (n := S n).
    + eapply Dumin_pi2.
      * exact d.
      * red. exists k'. exact H_k.
    + eapply Between_next.
      * exact b.
      * red. exists k'. exact H_k.
Defined.

Let linear_search (s : nat) : (exists x, Pre_umin s x) -> { x : nat | umin s x } :=
  fun EXISTENCE => loop s s (Pre_umin_Dumin EXISTENCE) (Between_refl Q s).

Lemma umin_incl_Pre_umin (s : nat)
  : umin s \subseteq Pre_umin s.
Proof.
  intros n IN. red. red. do 2 red in IN. destruct IN as [F_n_0 H_Between]. autorewrite with datatypes. split. split.
  - red. red. exists 0. exact F_n_0.
  - red. red. exact F_n_0.
  - destruct H_Between as [LE H_wBetween]. split; trivial. ii. red.
    pose proof (H_wBetween i H H0) as [k H_k]. exists (S k). exact H_k.
Qed.

Definition compute_umin (s : nat)
  (EXISTENCE : exists x, umin s x)
  : { x : nat | umin s x }.
Proof.
  eapply linear_search. destruct EXISTENCE as [x H_x]. exists x. eapply umin_incl_Pre_umin. exact H_x.
Defined.

Lemma compute_umin'
  (EXISTENCE : exists x, umin' x)
  : { x : nat | umin' x }.
Proof.
  assert (claim1 : exists x : nat, umin 0 x).
  { destruct EXISTENCE as [x H_x]. exists x. red. red in H_x. destruct H_x as [H_x H_wBetween].
    split; trivial. split. lia. ii. eapply H_wBetween. exact H0.
  }
  apply compute_umin with (s := 0) in claim1. destruct claim1 as [x H_x].
  exists x. red. red in H_x. destruct H_x as [H_x H_Between]. split; trivial.
  ii. destruct H_Between as [_ H_wBetween]. red in H_wBetween. eapply H_wBetween; lia.
Qed.

End UNBOUNDED_MINIMIZATION.

Section PRIMITIVE_RECURSION. (* Reference: "https://github.com/princeton-vl/CoqGym/blob/master/coq_projects/goedel/primRec.v" *)

#[local] Open Scope program_scope.

Let arity : Set := nat.

Fixpoint naryFun (n : arity) :=
  match n with
  | O => nat
  | S n' => nat -> naryFun n'
  end.

Fixpoint naryRel (n : arity) :=
  match n with
  | O => Prop
  | S n' => nat -> naryRel n'
  end.

Fixpoint eval_vec {n : arity} (xs : Vector.t nat n) : naryFun n -> nat :=
  match xs with
  | VNil => B.id
  | VCons n' x xs' => fun f => eval_vec xs' (f x)
  end.

Fixpoint eval_const {n : arity} (m : nat) : naryFun n :=
  match n with
  | O => m
  | S n' => B.const (eval_const m)
  end.

Fixpoint eval_proj {n : arity} (i : Fin.t n) : naryFun n :=
  match i with
  | FZ => eval_const
  | FS i' => B.const (eval_proj i')
  end.

Lemma eval_proj_spec (n : arity) (i : Fin.t n) (xs : Vector.t nat n)
  : eval_vec xs (eval_proj i) = xs !! i.
Proof.
  revert i. induction xs as [ | n x xs IH]; simpl.
  - Fin.case0.
  - Fin.caseS i.
    + simpl. clear IH. revert x xs. induction n as [ | n IH]; simpl.
      * intros x. introVNil. reflexivity.
      * intros x. introVCons x' xs'. simpl. unfold B.const. eapply IH.
    + eapply IH.
Qed.

Fixpoint eval_vec_1 {n : arity} {m : arity} (x : nat) (xs : Vector.t (naryFun (S n)) m) : Vector.t (naryFun n) m :=
  match xs with
  | VNil => VNil
  | VCons m' f xs' => VCons m' (f x) (eval_vec_1 x xs')
  end.

Fixpoint eval_compose {n : arity} {m : arity} : Vector.t (naryFun n) m -> naryFun m -> naryFun n :=
  match n with
  | O => fun xs => eval_vec xs
  | S n' => fun xs => fun f => fun x => eval_compose (eval_vec_1 x xs) f
  end.

Lemma eval_compose_spec (n : arity) (m : arity) (gs : Vector.t (naryFun n) m) (h : naryFun m) (xs : Vector.t nat n) (ys : Vector.t nat m) (z : nat)
  (gs_spec : V.map (eval_vec xs) gs = ys)
  (h_spec : eval_vec ys h = z)
  : eval_vec xs (eval_compose gs h) = z.
Proof.
  revert m gs h xs ys z gs_spec h_spec. induction n as [ | n IH]; simpl.
  - intros m gs h. introVNil. simpl. i.
    assert (claim1 : ys = gs).
    { rewrite <- gs_spec. clear ys z h gs_spec h_spec. induction gs as [ | n g gs IH]; simpl; trivial; f_equal; eauto. }
    subst gs. clear gs_spec. exact h_spec.
  - intros m gs h. introVCons x xs. simpl. i.
    assert (claim2 : V.map (eval_vec xs) (eval_vec_1 x gs) = ys).
    { rewrite <- gs_spec. clear ys gs_spec h_spec. clear z h IH. revert x xs. induction gs as [ | m g gs IH]; simpl.
      - reflexivity.
      - intros x xs. f_equal. eapply IH.
    }
    pose proof (claim3 := IH m (eval_vec_1 x gs) h xs ys z claim2 h_spec). congruence.
Qed.

Fixpoint eval_compose_2 {n : arity} : naryFun n -> naryFun (S n) -> naryFun n :=
  match n with
  | O => fun x => fun f => f x
  | S n' => fun f => fun g => fun a => eval_compose_2 (f a) (fun x => g x a)
  end.

Lemma eval_compose_2_spec (n : arity) (g : naryFun n) (h : naryFun (S n)) (xs : Vector.t nat n) (a : nat) (z : nat)
  (g_spec : eval_vec xs g = a)
  (h_spec : eval_vec (a :: xs) h = z)
  : eval_vec xs (eval_compose_2 g h) = z.
Proof.
  revert g h xs a z g_spec h_spec. induction n as [ | n IH]; simpl.
  - intros g h. introVNil. simpl. i. cbv in *. congruence.
  - intros g h. introVCons x xs. simpl. i.
    exact (IH (g x) (fun a => h a x) xs a z g_spec h_spec).
Qed.

Fixpoint eval_primRec {n : arity} (g : naryFun n) (h : naryFun (S (S n))) (a : nat) : naryFun n :=
  match a with
  | O => g
  | S a' => eval_compose_2 (eval_primRec g h a') (h a')
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

Section PrimRecs_case.

Let cast (x : nat) (n : nat) (m : nat) (EQ : n = m) : PrimRecs x n -> PrimRecs x m :=
  match EQ with
  | eq_refl => fun xs => xs
  end.

Lemma PrimRecs_case0 (phi : forall x, PrimRecs x O -> Type)
  (phi_nil : forall n, phi n (PRs_nil n))
  : forall x, forall fs, phi x fs.
Proof.
  refine (fun x : nat =>
    let claim1 (fs : PrimRecs x O) : forall H_eq : O = O, phi x (cast x O O H_eq fs) :=
      match fs in PrimRecs x m return forall H_eq : m = O, phi x (cast x m O H_eq fs) with
      | PRs_nil x => fun H_eq : O = O => _
      | PRs_cons x n f' fs' => fun H_eq : S n = O => _
      end
    in _
  ).
  { intros fs. exact (claim1 fs eq_refl). }
Unshelve.
  - rewrite eq_pirrel_fromEqDec with (H_eq1 := H_eq) (H_eq2 := eq_refl).
    exact (phi_nil x).
  - inversion H_eq.
Qed.

Lemma PrimRecs_caseS {n' : nat} (phi : forall x, PrimRecs x (S n') -> Type)
  (phi_cons: forall n, forall f', forall fs', phi n (PRs_cons n n' f' fs'))
  : forall x, forall fs, phi x fs.
Proof.
  refine (fun x : nat =>
    let claim1 (fs : PrimRecs x (S n')) : forall H_eq : S n' = S n', phi x (cast x (S n') (S n') H_eq fs) :=
      match fs in PrimRecs x m return forall H_eq : m = S n', phi x (cast x m (S n') H_eq fs) with
      | PRs_nil x => fun H_eq: O = S n' => _
      | PRs_cons x n x' xs' => fun H_eq: S n = S n' => _
      end
    in _
  ).
  { intros fs. exact (claim1 fs eq_refl). }
Unshelve.
  - inversion H_eq.
  - pose proof (f_equal Nat.pred H_eq) as n_eq_n'. simpl in n_eq_n'. subst n'.
    rewrite eq_pirrel_fromEqDec with (H_eq1 := H_eq) (H_eq2 := eq_refl).
    exact (phi_cons x x' xs').
Qed.

End PrimRecs_case.

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

#[local] Close Scope list_scope.
#[local] Open Scope vector_scope.

#[local] Notation " [ ] " := (VNil).
#[local] Notation " x :: xs " := (VCons _ x xs).
#[local] Notation " [ x ] " := (VCons _ x VNil).

Inductive PrimRecSpec : forall n : arity, PrimRec n -> Vector.t nat n -> nat -> Prop :=
  | PR_succ_spec x
    : PrimRecSpec 1 (PR_succ) [x] (S x)
  | PR_zero_spec
    : PrimRecSpec 0 (PR_zero) [] (O)
  | PR_proj_spec n xs i
    : PrimRecSpec n (PR_proj n i) xs (xs !! i)
  | PR_compose_spec n m g h xs ys z
    (g_spec : PrimRecsSpec n m g xs ys)
    (h_spec : PrimRecSpec m h ys z)
    : PrimRecSpec n (PR_compose n m g h) xs z
  | PR_primRec_spec_O n g h xs z
    (g_spec : PrimRecSpec n g xs z)
    : PrimRecSpec (S n) (PR_primRec n g h) (O :: xs) z
  | PR_primRec_spec_S n g h xs z a acc
    (ACC : PrimRecSpec (S n) (PR_primRec n g h) (a :: xs) acc)
    (h_spec : PrimRecSpec (S (S n)) h (a :: acc :: xs) z)
    : PrimRecSpec (S n) (PR_primRec n g h) (S a :: xs) z
with PrimRecsSpec : forall n : arity, forall m : arity, PrimRecs n m -> Vector.t nat n -> Vector.t nat m -> Prop :=
  | PRs_nil_spec n xs
    : PrimRecsSpec n (O) (PRs_nil n) xs []
  | PRs_cons_spec n m xs y ys f fs
    (f_spec : PrimRecSpec n f xs y)
    (fs_spec : PrimRecsSpec n m fs xs ys)
    : PrimRecsSpec n (S m) (PRs_cons n m f fs) xs (y :: ys).

Fixpoint PrimRecGraph {n : arity} (f : PrimRec n) : Vector.t nat n -> nat -> Prop :=
  match f with
  | PR_succ => fun xs => fun z => S (V.head xs) = z
  | PR_zero => fun xs => fun z => O = z
  | PR_proj n i => fun xs => fun z => xs !! i = z
  | PR_compose n m g h => fun xs => fun z => exists ys, PrimRecsGraph g xs ys /\ PrimRecGraph h ys z
  | PR_primRec n g h => fun xs => nat_rect _ (fun z => PrimRecGraph g (V.tail xs) z) (fun a => fun ACC => fun z => exists y, ACC y /\ PrimRecGraph h (a :: y :: V.tail xs) z) (V.head xs)
  end
with PrimRecsGraph {n : arity} {m : arity} (fs : PrimRecs n m) : Vector.t nat n -> Vector.t nat m -> Prop :=
  match fs with
  | PRs_nil n => fun xs => fun z => [] = z
  | PRs_cons n m f fs => fun xs => fun z => exists y, exists ys, PrimRecGraph f xs y /\ PrimRecsGraph fs xs ys /\ y :: ys = z
  end.

Fixpoint PrimRecGraph_sound (n : arity) (f : PrimRec n) {struct f}
  : forall xs, forall z, PrimRecGraph f xs z -> PrimRecSpec n f xs z
with PrimRecsGraph_sound (n : arity) (m : arity) (fs : PrimRecs n m) {struct fs}
  : forall xs, forall z, PrimRecsGraph fs xs z -> PrimRecsSpec n m fs xs z.
Proof.
  - destruct f; intros xs z CALL.
    + r in CALL. subst z. revert xs. introVCons x xs. revert xs. introVNil. cbv. econs 1.
    + r in CALL. subst z. revert xs. introVNil. econs 2.
    + r in CALL. subst z. econs 3.
    + simpl in CALL. destruct CALL as (ys&CALLs&CALL). econs 4.
      * eapply PrimRecsGraph_sound. exact CALLs.
      * eapply PrimRecGraph_sound. exact CALL.
    + simpl in CALL. revert xs CALL. introVCons a xs. revert z xs. induction a as [ | a ACC]; i.
      * simpl in CALL. unfold V.tail in CALL. simpl in CALL. econs 5.
        eapply PrimRecGraph_sound. exact CALL.
      * simpl in CALL. destruct CALL as [y [CALL IH]]. unfold V.tail in CALL. simpl in CALL. unfold V.tail in IH. simpl in IH. econs 6.
        { eapply ACC with (z := y). exact CALL. }
        { eapply PrimRecGraph_sound. exact IH. }
  - destruct fs; intros xs z CALL.
    + simpl in CALL. subst z. econs 1.
    + simpl in CALL. destruct CALL as [y [ys [CALL [CALLs ?]]]]. subst z. econs 2.
      * eapply PrimRecGraph_sound. exact CALL.
      * eapply PrimRecsGraph_sound. exact CALLs.
Qed.

Fixpoint PrimRecGraph_complete (n : arity) (f : PrimRec n) (xs : Vector.t nat n) (z : nat) (SPEC : PrimRecSpec n f xs z) {struct SPEC}
  : PrimRecGraph f xs z
with PrimRecsGraph_complete (n : arity) (m : arity) (fs : PrimRecs n m) (xs : Vector.t nat n) (z : Vector.t nat m) (SPEC : PrimRecsSpec n m fs xs z) {struct SPEC}
  : PrimRecsGraph fs xs z.
Proof.
  - destruct SPEC; simpl.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exists ys. split.
      * eapply PrimRecsGraph_complete. exact g_spec.
      * eapply PrimRecGraph_complete. exact SPEC.
    + eapply PrimRecGraph_complete. exact SPEC.
    + exists acc. unfold V.tail. simpl. split.
      * apply PrimRecGraph_complete in SPEC1. exact SPEC1.
      * apply PrimRecGraph_complete in SPEC2. exact SPEC2.
  - destruct SPEC; simpl.
    + reflexivity.
    + exists y, ys. split. 
      * eapply PrimRecGraph_complete. exact f_spec.
      * split.
        { eapply PrimRecsGraph_complete. exact SPEC. }
        { reflexivity. }
Qed.

Theorem PrimRecGraph_correct (n : arity) (f : PrimRec n) (xs : Vector.t nat n) (z : nat)
  : PrimRecGraph f xs z <-> PrimRecSpec n f xs z.
Proof.
  pose proof (LEFT := @PrimRecGraph_complete). pose proof (RIGHT := @PrimRecGraph_sound). now firstorder.
Qed.

Theorem PrimRecsGraph_correct (n : arity) (m : arity) (f : PrimRecs n m) (xs : Vector.t nat n) (z : Vector.t nat m)
  : PrimRecsGraph f xs z <-> PrimRecsSpec n m f xs z.
Proof.
  pose proof (LEFT := @PrimRecsGraph_complete). pose proof (RIGHT := @PrimRecsGraph_sound). now firstorder.
Qed.

Fixpoint PrimRecSpec_sound (n : arity) (f : PrimRec n) (xs : Vector.t nat n) (z : nat) (SPEC : PrimRecSpec n f xs z) {struct SPEC}
  : eval_vec xs (runPrimRec f) = z
with PrimRecsSpec_sound (n : arity) (m : arity) (fs : PrimRecs n m) (xs : Vector.t nat n) (z : Vector.t nat m) (SPEC : PrimRecsSpec n m fs xs z) {struct SPEC}
  : V.map (eval_vec xs) (runPrimRecs fs) = z.
Proof.
  - destruct SPEC.
    + reflexivity.
    + reflexivity.
    + eapply eval_proj_spec.
    + simpl. eapply eval_compose_spec.
      * eapply PrimRecsSpec_sound. exact g_spec.
      * eapply PrimRecSpec_sound. exact SPEC.
    + simpl. eapply PrimRecSpec_sound. exact SPEC.
    + simpl. eapply eval_compose_2_spec.
      * apply PrimRecSpec_sound in SPEC1. simpl in SPEC1. exact SPEC1.
      * apply PrimRecSpec_sound in SPEC2. simpl in SPEC2. simpl. exact SPEC2.
  - destruct SPEC.
    + reflexivity.
    + simpl. eapply f_equal2.
      * eapply PrimRecSpec_sound. exact f_spec.
      * eapply PrimRecsSpec_sound. exact SPEC.
Qed.

Fixpoint PrimRecSpec_complete (n : arity) (f : PrimRec n) {struct f}
  : forall xs, PrimRecSpec n f xs (eval_vec xs (runPrimRec f))
with PrimRecsSpec_complete (n : arity) (m : arity) (fs : PrimRecs n m) {struct fs}
  : forall xs, PrimRecsSpec n m fs xs (V.map (eval_vec xs) (runPrimRecs fs)).
Proof.
  - destruct f; simpl.
    + introVCons x xs. revert xs. introVNil. simpl. econs 1.
    + introVNil. econs 2.
    + i. erewrite eval_proj_spec. econs 3.
    + i. econs 4.
      * eapply PrimRecsSpec_complete.
      * erewrite eval_compose_spec.
        { eapply PrimRecSpec_complete. }
        { reflexivity. }
        { reflexivity. }
    + introVCons a xs. simpl. revert a xs. induction a as [ | a IH].
      * simpl. i. econs 5. eapply PrimRecSpec_complete.
      * simpl. i. econs 6. 
        { eapply IH. }
        { erewrite eval_compose_2_spec.
          - eapply PrimRecSpec_complete.
          - reflexivity.
          - reflexivity.
        }
  - destruct fs; simpl.
    + i. econs 1.
    + i. econs 2.
      * eapply PrimRecSpec_complete.
      * eapply PrimRecsSpec_complete.
Qed.

Theorem PrimRecSpec_iff (n : arity) (f : PrimRec n) (xs : Vector.t nat n) (z : nat)
  : PrimRecSpec n f xs z <-> eval_vec xs (runPrimRec f) = z.
Proof.
  split.
  - intros SPEC. eapply PrimRecSpec_sound; exact SPEC.
  - intros <-. eapply PrimRecSpec_complete.
Qed.

Theorem PrimRecsSpec_iff (n : arity) (m : arity) (f : PrimRecs n m) (xs : Vector.t nat n) (z : Vector.t nat m)
  : PrimRecsSpec n m f xs z <-> V.map (eval_vec xs) (runPrimRecs f) = z.
Proof.
  split.
  - intros SPEC. eapply PrimRecsSpec_sound; exact SPEC.
  - intros <-. eapply PrimRecsSpec_complete.
Qed.

End PRIMITIVE_RECURSION.

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
  | MR_proj {n : Arity} (i : Fin.t n) : MuRec n
  | MR_compose {n : Arity} {m : Arity} (g : MuRecs n m) (h : MuRec m) : MuRec n
  | MR_primRec {n : Arity} (g : MuRec n) (h : MuRec (S (S n))) : MuRec (S n)
  | MR_mu {n : Arity} (g : MuRec (S n)) : MuRec n
with MuRecs : Arity -> Arity -> Set :=
  | MRs_nil {n : Arity} : MuRecs n 0
  | MRs_cons {n : Arity} {m : Arity} (f : MuRec n) (fs : MuRecs n m) : MuRecs n (S m).

Let Value := nat.

Inductive MuRecSpec : forall n : Arity, MuRec n -> Vector.t Value n -> Value -> Prop :=
  | MR_succ_spec x
    : MuRecSpec 1 (MR_succ) [x] (S x)
  | MR_zero_spec
    : MuRecSpec 0 (MR_zero) [] (O)
  | MR_proj_spec n xs i
    : MuRecSpec n (MR_proj i) xs (xs !! i)
  | MR_compose_spec n m g h xs ys z
    (g_spec : MuRecsSpec n m g xs ys)
    (h_spec : MuRecSpec m h ys z)
    : MuRecSpec n (MR_compose g h) xs z
  | MR_primRec_spec_O n g h xs z
    (g_spec : MuRecSpec n g xs z)
    : MuRecSpec (S n) (MR_primRec g h) (O :: xs) z
  | MR_primRec_spec_S n g h xs z a acc
    (ACC : MuRecSpec (S n) (MR_primRec g h) (a :: xs) acc)
    (h_spec : MuRecSpec (S (S n)) h (a :: acc :: xs) z)
    : MuRecSpec (S n) (MR_primRec g h) (S a :: xs) z (* corrected by "SoonWon Moon" *)
  | MR_mu_spec n g xs z
    (g_spec : MuRecSpec (S n) g (z :: xs) 0)
    (MIN : forall y, y < z -> exists p, p > 0 /\ MuRecSpec (S n) g (y :: xs) p) (* corrected by "SoonWon Moon" *)
    : MuRecSpec n (MR_mu g) xs z
with MuRecsSpec : forall n : Arity, forall m : Arity, MuRecs n m -> Vector.t Value n -> Vector.t Value m -> Prop :=
  | MRs_nil_spec n xs
    : MuRecsSpec n (O) (MRs_nil) xs []
  | MRs_cons_spec n m xs y ys f fs
    (f_spec : MuRecSpec n f xs y)
    (fs_spec : MuRecsSpec n m fs xs ys)
    : MuRecsSpec n (S m) (MRs_cons f fs) xs (y :: ys).

Fixpoint MuRecGraph {n : Arity} (f : MuRec n) : Vector.t Value n -> Value -> Prop :=
  match f with
  | MR_succ => fun xs => fun z => S (V.head xs) = z
  | MR_zero => fun xs => fun z => O = z
  | MR_proj i => fun xs => fun z => xs !! i = z
  | MR_compose g h => fun xs => fun z => exists ys, MuRecsGraph g xs ys /\ MuRecGraph h ys z
  | MR_primRec g h => fun xs => nat_rect _ (fun z => MuRecGraph g (V.tail xs) z) (fun a => fun ACC => fun z => exists y, ACC y /\ MuRecGraph h (a :: y :: V.tail xs) z) (V.head xs)
  | MR_mu g => fun xs => fun z => (forall y, y < z -> exists p, p > 0 /\ MuRecGraph g (y :: xs) p) /\ MuRecGraph g (z :: xs) 0 (* corrected by "SoonWon Moon" *)
  end
with MuRecsGraph {n : Arity} {m : Arity} (fs : MuRecs n m) : Vector.t Value n -> Vector.t Value m -> Prop :=
  match fs with
  | MRs_nil => fun xs => fun z => [] = z
  | MRs_cons f fs => fun xs => fun z => exists y, exists ys, MuRecGraph f xs y /\ MuRecsGraph fs xs ys /\ y :: ys = z
  end.

Fixpoint MuRecGraph_sound (n : Arity) (f : MuRec n) {struct f}
  : forall xs, forall z, MuRecGraph f xs z -> MuRecSpec n f xs z
with MuRecsGraph_sound (n : Arity) (m : Arity) (fs : MuRecs n m) {struct fs}
  : forall xs, forall z, MuRecsGraph fs xs z -> MuRecsSpec n m fs xs z.
Proof.
  - destruct f; intros xs z CALL.
    + r in CALL. subst z. revert xs. introVCons x xs. revert xs. introVNil. cbv. econs 1.
    + r in CALL. subst z. revert xs. introVNil. econs 2.
    + r in CALL. subst z. econs 3.
    + simpl in CALL. destruct CALL as (ys&CALLs&CALL). econs 4.
      * eapply MuRecsGraph_sound. exact CALLs.
      * eapply MuRecGraph_sound. exact CALL.
    + simpl in CALL. revert xs CALL. introVCons a xs. revert z xs. induction a as [ | a ACC]; i.
      * simpl in CALL. unfold V.tail in CALL. simpl in CALL. econs 5.
        eapply MuRecGraph_sound. exact CALL.
      * simpl in CALL. destruct CALL as [y [CALL IH]]. unfold V.tail in CALL. simpl in CALL. unfold V.tail in IH. simpl in IH. econs 6.
        { eapply ACC with (z := y). exact CALL. }
        { eapply MuRecGraph_sound. exact IH. }
    + simpl in CALL. destruct CALL as [g_spec MIN]. econs 7.
      * eapply MuRecGraph_sound. exact MIN.
      * intros y y_lt_z. pose proof (g_spec y y_lt_z) as [p [p_gt_0 CALL]]. exists p. split. exact p_gt_0. eapply MuRecGraph_sound. exact CALL.
  - destruct fs; intros xs z CALL.
    + simpl in CALL. subst z. econs 1.
    + simpl in CALL. destruct CALL as [y [ys [CALL [CALLs ?]]]]. subst z. econs 2.
      * eapply MuRecGraph_sound. exact CALL.
      * eapply MuRecsGraph_sound. exact CALLs.
Qed.

Fixpoint MuRecGraph_complete (n : Arity) (f : MuRec n) (xs : Vector.t Value n) (z : Value) (SPEC : MuRecSpec n f xs z) {struct SPEC}
  : MuRecGraph f xs z
with MuRecsGraph_complete (n : Arity) (m : Arity) (fs : MuRecs n m) (xs : Vector.t Value n) (z : Vector.t Value m) (SPEC : MuRecsSpec n m fs xs z) {struct SPEC}
  : MuRecsGraph fs xs z.
Proof.
  - destruct SPEC; simpl.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exists ys. split.
      * eapply MuRecsGraph_complete. exact g_spec.
      * eapply MuRecGraph_complete. exact SPEC.
    + eapply MuRecGraph_complete. exact SPEC.
    + exists acc. unfold V.tail. simpl. split.
      * apply MuRecGraph_complete in SPEC1. exact SPEC1.
      * apply MuRecGraph_complete in SPEC2. exact SPEC2.
    + split.
      * intros y y_lt_z. pose proof (MIN y y_lt_z) as [p [p_gt_0 SPEC']].
        exists p. split. exact p_gt_0. eapply MuRecGraph_complete. exact SPEC'.
      * eapply MuRecGraph_complete. exact SPEC.
  - destruct SPEC; simpl.
    + reflexivity.
    + exists y, ys. split. 
      * eapply MuRecGraph_complete. exact f_spec.
      * split.
        { eapply MuRecsGraph_complete. exact SPEC. }
        { reflexivity. }
Qed.

Theorem MuRecGraph_correct (n : Arity) (f : MuRec n) (xs : Vector.t Value n) (z : Value)
  : MuRecGraph f xs z <-> MuRecSpec n f xs z.
Proof.
  pose proof (LEFT := @MuRecGraph_complete). pose proof (RIGHT := @MuRecGraph_sound). now firstorder.
Qed.

Theorem MuRecsGraph_correct (n : Arity) (m : Arity) (f : MuRecs n m) (xs : Vector.t Value n) (z : Vector.t Value m)
  : MuRecsGraph f xs z <-> MuRecsSpec n m f xs z.
Proof.
  pose proof (LEFT := @MuRecsGraph_complete). pose proof (RIGHT := @MuRecsGraph_sound). now firstorder.
Qed.

Fixpoint MuRec_isPartialFunction_aux (n : Arity) (f : MuRec n) (xs : Vector.t Value n) (z : Value) (SPEC : MuRecSpec n f xs z) {struct SPEC}
  : forall z', MuRecGraph f xs z' -> z = z'
with MuRecs_isPartialFunction_aux (n : Arity) (m : Arity) (fs : MuRecs n m) (xs : Vector.t Value n) (z : Vector.t Value m) (SPEC : MuRecsSpec n m fs xs z) {struct SPEC}
  : forall z', MuRecsGraph fs xs z' -> z = z'.
Proof.
  - destruct SPEC; intros z' CALL.
    + exact CALL.
    + exact CALL.
    + exact CALL.
    + simpl in CALL. eapply MuRec_isPartialFunction_aux.
      * exact SPEC.
      * destruct CALL as (ys'&CALLs&CALL).
        assert (claim : ys = ys').
        { eapply MuRecs_isPartialFunction_aux; [exact g_spec | exact CALLs]. }
        subst ys'. exact CALL.
    + simpl in CALL. unfold V.tail in CALL; simpl in CALL. eapply MuRec_isPartialFunction_aux.
      * eapply SPEC.
      * exact CALL.
    + simpl in CALL. destruct CALL as (y&ACC&CALL). unfold V.tail in ACC, CALL; simpl in ACC, CALL.
      assert (claim : acc = y).
      { eapply MuRec_isPartialFunction_aux.
        - exact SPEC1.
        - exact ACC. 
      }
      subst y. eapply MuRec_isPartialFunction_aux.
      * exact SPEC2.
      * exact CALL.
    + simpl in CALL. destruct CALL as [MIN' CALL].
      assert (NOT_LT : ~ z < z').
      { intros LT. pose proof (MIN' z LT) as (p&p_gt_0&CALL').
        enough (WTS : 0 = p) by lia.
        eapply MuRec_isPartialFunction_aux.
        - exact SPEC.
        - exact CALL'.
      }
      assert (NOT_LT' : ~ z' < z).
      { intros LT. pose proof (MIN z' LT) as (p&p_gt_0&CALL').
        enough (WTS : p = 0) by lia.
        eapply MuRec_isPartialFunction_aux. 
        - exact CALL'.
        - exact CALL.
      }
      lia.
  - destruct SPEC; intros z' CALL'.
    + revert z' CALL'. introVNil. i. reflexivity.
    + revert z' CALL'. introVCons y' ys'. i. simpl in CALL'.
      destruct CALL' as (y''&ys''&CALL''&CALLs''&EQ). rewrite <- EQ. eapply f_equal2.
      * eapply MuRec_isPartialFunction_aux; [exact f_spec | exact CALL''].
      * eapply MuRecs_isPartialFunction_aux; [exact SPEC | exact CALLs''].
Qed.

Theorem MuRec_isPartialFunction (n : Arity) (f : MuRec n) (xs : Vector.t Value n) (z : Value) (z' : Value)
  (SPEC : MuRecSpec n f xs z)
  (SPEC' : MuRecSpec n f xs z')
  : z = z'.
Proof.
  eapply MuRec_isPartialFunction_aux; [exact SPEC | rewrite MuRecGraph_correct; exact SPEC'].
Qed.

Theorem MuRecs_isPartialFunction (n : Arity) (m : Arity) (fs : MuRecs n m) (xs : Vector.t Value n) (z : Vector.t Value m) (z' : Vector.t Value m)
  (SPEC : MuRecsSpec n m fs xs z)
  (SPEC' : MuRecsSpec n m fs xs z')
  : z = z'.
Proof.
  eapply MuRecs_isPartialFunction_aux; [exact SPEC | rewrite MuRecsGraph_correct; exact SPEC'].
Qed.

Fixpoint MuRecInterpreter (n : Arity) (f : MuRec n) {struct f}
  : forall xs, (exists z, MuRecSpec n f xs z) -> { z : Value | MuRecSpec n f xs z }
with MuRecsInterpreter (n : Arity) (m : Arity) (fs : MuRecs n m) {struct fs}
  : forall xs, (exists z, MuRecsSpec n m fs xs z) -> { z : Vector.t Value m | MuRecsSpec n m fs xs z }.
Proof.
  - destruct f; simpl; intros xs EXISTENCE.
    + clear EXISTENCE. revert xs. introVCons x xs. revert xs. introVNil. exists (S x). econs 1.
    + clear EXISTENCE. revert xs. introVNil. exists O. econs 2.
    + clear EXISTENCE. exists (xs !! i). econs 3.
    + assert (claim1 : exists z : Vector.t Value m, MuRecsSpec n m g xs z).
      { destruct EXISTENCE as [z SPEC]. rewrite <- MuRecGraph_correct in SPEC. simpl in SPEC.
        destruct SPEC as (ys&CALLs&CALL). exists ys. rewrite <- MuRecsGraph_correct. exact CALLs.
      }
      pose proof (MuRecsInterpreter n m g xs claim1) as [ys ys_spec].
      assert (claim2 : exists z : Value, MuRecSpec m f ys z).
      { destruct EXISTENCE as [z SPEC]. rewrite <- MuRecGraph_correct in SPEC. simpl in SPEC.
        destruct SPEC as (ys'&CALLs&CALL). exists z. rewrite <- MuRecGraph_correct. replace ys with ys'. exact CALL.
        eapply MuRecs_isPartialFunction.
        - rewrite <- MuRecsGraph_correct. exact CALLs.
        - exact ys_spec.
      }
      pose proof (MuRecInterpreter m f ys claim2) as [z z_spec]. exists z.
      rewrite <- MuRecGraph_correct. simpl. exists ys. split.
      * rewrite MuRecsGraph_correct. exact ys_spec.
      * rewrite MuRecGraph_correct. exact z_spec.
    + revert xs EXISTENCE. introVCons a xs. revert xs. induction a as [ | a IH]; simpl; i.
      * assert (claim1 : exists z : Value, MuRecSpec n f1 xs z).
        { destruct EXISTENCE as [z SPEC]. rewrite <- MuRecGraph_correct in SPEC. simpl in SPEC.
          unfold V.tail in SPEC. simpl in SPEC. exists z. rewrite <- MuRecGraph_correct. exact SPEC.
        }
        pose proof (MuRecInterpreter n f1 xs claim1) as [z z_spec]. exists z.
        rewrite <- MuRecGraph_correct. simpl. unfold V.tail. simpl. rewrite MuRecGraph_correct. exact z_spec.
      * assert (claim1 : exists z : Value, MuRecSpec (S n) (MR_primRec f1 f2) (VCons n a xs) z).
        { destruct EXISTENCE as [z SPEC]. rewrite <- MuRecGraph_correct in SPEC. simpl in SPEC.
          unfold V.tail, V.head in SPEC. simpl in SPEC. destruct SPEC as [acc [CALL CALL']]. exists acc. rewrite <- MuRecGraph_correct. simpl.
          unfold V.tail, V.head. simpl. exact CALL.
        }
        pose proof (IH xs claim1) as [acc acc_spec].
        assert (claim2 : exists z : Value, MuRecSpec (S (S n)) f2 (VCons (S n) a (VCons n acc xs)) z).
        { destruct EXISTENCE as [z SPEC]. rewrite <- MuRecGraph_correct in SPEC. simpl in SPEC.
          unfold V.tail, V.head in SPEC. simpl in SPEC. destruct SPEC as [acc' [CALL CALL']].
          assert (EQ : acc = acc').
          { eapply MuRec_isPartialFunction.
            - exact acc_spec.
            - rewrite <- MuRecGraph_correct. simpl. unfold V.head, V.tail. simpl. exact CALL.
          }
          subst acc'. exists z. rewrite <- MuRecGraph_correct. exact CALL'.
        }
        pose proof (MuRecInterpreter (S (S n)) f2 (a :: acc :: xs) claim2) as [z z_spec].
        exists z. econs 6. exact acc_spec. exact z_spec.
    + pose (COUNTABLE := {| encode := id; decode := @Some nat; decode_encode (x : nat) := eq_refl |}). set (P := MuRecSpec n (MR_mu f) xs).
      pose proof (@Acc_flip_search_step_P_0 nat COUNTABLE P EXISTENCE) as ACC.
      assert (SEARCH : exists z, MuRecSpec n (MR_mu f) xs z /\ (forall x, x < z -> search_step P x (S x))).
      { destruct EXISTENCE as [z z_spec]. exists z. split. exact z_spec.
        rewrite <- MuRecGraph_correct in z_spec. simpl in z_spec.
        destruct z_spec as [MIN z_spec]. intros y y_lt_z. pose proof (MIN y y_lt_z) as (p&p_gt_0&CALL).
        eapply search_step_Some with (x := y). 2: reflexivity. unfold P. rewrite <- MuRecGraph_correct.
        intros [MIN' y_spec]. enough (FALSE : p = 0) by lia. eapply MuRec_isPartialFunction.
        - rewrite <- MuRecGraph_correct. exact CALL.
        - rewrite <- MuRecGraph_correct. exact y_spec.
      }
      clear EXISTENCE. unfold P. set (F := fun x : nat => fun y : nat => MuRecSpec (S n) f (x :: xs) y).
      assert (claim1 : forall x y1 y2 : nat, F x y1 -> F x y2 -> y1 = y2).
      { intros x y1 y2. unfold F. intros SPEC1 SPEC2. eapply MuRec_isPartialFunction. eapply SPEC1. eapply SPEC2. }
      assert (claim2 : forall x : nat, (exists y : nat, F x y) -> {y : nat | F x y}).
      { unfold F. intros x EXISTENCE. exact (MuRecInterpreter (S n) f (x :: xs) EXISTENCE). }
      assert (claim3 : exists x : nat, umin' F x).
      { destruct SEARCH as [z [SEARCH STEP]]. exists z. red. unfold F. rewrite <- MuRecGraph_correct in SEARCH. simpl in SEARCH.
        destruct SEARCH as [SEARCH MIN]. split.
        - rewrite <- MuRecGraph_correct. exact MIN.
        - intros i LT. pose proof (SEARCH i LT) as (p&p_gt_0&CALL). destruct p as [ | p'].
          + lia.
          + exists p'. rewrite <- MuRecGraph_correct. exact CALL.
      }
      pose proof (compute_umin' F claim1 claim2 claim3) as [x H_x].
      exists x. rewrite <- MuRecGraph_correct. simpl. red in H_x. unfold F in H_x. destruct H_x as [SPEC MIN]. split.
      * i. pose proof (MIN y H) as [p SPEC']. exists (S p). split. lia. rewrite <- MuRecGraph_correct in SPEC'. exact SPEC'.
      * rewrite <- MuRecGraph_correct in SPEC. exact SPEC.
  - destruct fs; intros xs EXISTENCE.
    + exists []. econs 1.
    + assert (claim1 : exists z : Value, MuRecSpec n f xs z).
      { destruct EXISTENCE as [z SPEC]. rewrite <- MuRecsGraph_correct in SPEC. simpl in SPEC.
        destruct SPEC as (y&ys&CALL&CALLs&EQ). exists y. rewrite <- MuRecGraph_correct. exact CALL.
      }
      assert (claim2 : exists z : Vector.t Value m, MuRecsSpec n m fs xs z).
      { destruct EXISTENCE as [z SPEC]. rewrite <- MuRecsGraph_correct in SPEC. simpl in SPEC.
        destruct SPEC as (y&ys&CALL&CALLs&EQ). exists ys. rewrite <- MuRecsGraph_correct. exact CALLs.
      }
      pose proof (MuRecInterpreter n f xs claim1) as [y y_spec].
      pose proof (MuRecsInterpreter n m fs xs claim2) as [ys ys_spec].
      exists (y :: ys). econs 2; [exact y_spec | exact ys_spec].
Qed.

End MU_RECURSIVE.
