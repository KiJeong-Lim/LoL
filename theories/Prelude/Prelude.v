Require Export LoL.Prelude.SfLib.
Require Export Coq.Arith.Compare_dec.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Arith.Wf_nat.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Lists.List.
Require Export Coq.micromega.Lia.
Require Export Coq.Program.Basics.
Require Export Coq.Program.Utils.
Require Export Coq.Program.Wf.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Relations.Relation_Operators.
Require Export Coq.Setoids.Setoid.

Notation " '⟪' x ':' t '⟫' " := (NW (fun x : unit => match x with tt => t end)) (x name, t at level 200, at level 0, no associativity) : type_scope.
Ltac done := first [congruence | simpl in *; congruence | lia | now firstorder; first [congruence | lia | eauto]].
Ltac obs_eqb n m :=
  let H_OBS := fresh "H_OBS" in
  destruct (Nat.eqb n m) as [ | ] eqn: H_OBS; [rewrite Nat.eqb_eq in H_OBS | rewrite Nat.eqb_neq in H_OBS].

Reserved Infix "==" (no associativity, at level 70).
Reserved Infix "=<" (no associativity, at level 70).
Reserved Infix "=~=" (no associativity, at level 70).
Reserved Infix "\in" (no associativity, at level 70).
Reserved Infix "\subseteq" (no associativity, at level 70).
Reserved Infix ">>=" (left associativity, at level 90).
Reserved Infix "≡" (no associativity, at level 70).

Module B.

Include Coq.Program.Basics.

Definition Some_dec {A : Type} (x : option A)
  : { x' : A | x = Some x' } + { x = None }.
Proof.
  destruct x as [x' | ].
  - left. exists x'. reflexivity.
  - right. reflexivity.
Defined.

Definition id {A : Type} : A -> A :=
  fun x : A => x.

#[projections(primitive)]
Record prod (A : Type) (B : Type) : Type :=
  pair { fst : A; snd : B }.

#[global] Arguments B.pair {A} {B}.
#[global] Arguments B.fst {A} {B} _.
#[global] Arguments B.snd {A} {B} _.

Inductive sum1 (F : Type -> Type) (G : Type -> Type) (X : Type) : Type :=
  | inl1 (FX : F X) : sum1 F G X
  | inr1 (GX : G X) : sum1 F G X.

#[global] Arguments inl1 {F}%type_scope {G}%type_scope {X}%type_scope FX.
#[global] Arguments inr1 {F}%type_scope {G}%type_scope {X}%type_scope GX.

#[projections(primitive)]
Record stateT (S : Type) (M : Type -> Type) (X : Type) : Type :=
  StateT { runStateT : S -> M (B.prod X S) }.

#[global] Arguments stateT (S) (M)%type_scope.
#[global] Arguments StateT {S} {M}%type_scope {X}.
#[global] Arguments runStateT {S} {M}%type_scope {X}.

Definition maybe {A : Type} {B : Type} (d : B) (f : A -> B) (m : option A) : B :=
  match m with
  | None => d
  | Some x => f x
  end.

Definition either {A : Type} {B : Type} {C : Type} (f : A -> C) (g : B -> C) (z : A + B) : C :=
  match z with
  | inl x => f x
  | inr y => g y
  end.

Definition uncurry {A : Type} {B : Type} {C : Type} (f : A -> B -> C) : B.prod A B -> C :=
  fun p => f (B.fst p) (B.snd p).

Definition curry {A : Type} {B : Type} {C : Type} (f : B.prod A B -> C) : A -> B -> C :=
  fun x => fun y => f (B.pair x y).

Lemma Some_ne_None {A : Type} (x : A)
  : Some x <> None.
Proof.
  assert (TRUE : option_rect (fun _ : option A => Prop) (fun _ : A => True) (False) (Some x)) by exact I.
  intros EQ. rewrite EQ in TRUE. exact TRUE.
Defined.

Class isFunctor (F : Type -> Type) : Type :=
  fmap (A : Type) (B : Type) (f : A -> B) : F A -> F B.

#[global] Arguments fmap {F}%type_scope {_} {A} {B}.

Class isMonad (M : Type -> Type) : Type :=
  { pure {A : Type} (x : A) : M A
  ; bind {A : Type} {B : Type} (m : M A) (k : A -> M B) : M B
  }.

Definition mkFunctorFromMonad {M : Type -> Type} `(MONAD : isMonad M) : isFunctor M :=
  fun A : Type => fun B : Type => fun f : A -> B => fun m : M A => MONAD.(bind) m (fun x : A => MONAD.(pure) (f x)).

Definition liftM2 {M : Type -> Type} {A : Type} {B : Type} {C : Type} `{MONAD : isMonad M} (f : A -> B -> C) (mx : M A) (my : M B) : M C :=
  bind mx (fun x : A => bind my (fun y : B => pure (f x y))).

#[universes(polymorphic=yes)]
Definition binary_relation_on_image@{dom_lv cod_lv} {dom: Type@{dom_lv}} {cod: Type@{cod_lv}} (bin_rel: cod -> cod -> Prop) (f: dom -> cod) (lhs: dom) (rhs: dom) : Prop :=
  bin_rel (f lhs) (f rhs).

Section IDENTITY.

Definition eq_reflexivity {A : Type} (x1 : A) : x1 = x1 :=
  @eq_refl A x1.

Definition eq_symmetry {A : Type} (x1 : A) (x2 : A) (x1_eq_x2 : x1 = x2) : x2 = x1 :=
  @eq_ind A x1 (fun x : A => x = x1) (@eq_refl A x1) x2 x1_eq_x2.

Definition eq_transitivity {A : Type} (x1 : A) (x2 : A) (x3 : A) (x1_eq_x2 : x1 = x2) (x2_eq_x3 : x2 = x3) : x1 = x3 :=
  @eq_ind A x2 (fun x : A => x1 = x) x1_eq_x2 x3 x2_eq_x3.

Section EQ_EM_implies_EQ_PIRREL. (* Reference: "https://coq.inria.fr/doc/v8.18/stdlib/Coq.Logic.Eqdep_dec.html" *)

Context {A : Type}.

Lemma eq_round_trip (x : A) (y : A)
  (x_eq_y : x = y)
  : eq_transitivity y x y (eq_symmetry x y x_eq_y) x_eq_y = eq_reflexivity y.
Proof.
  destruct x_eq_y; reflexivity.
Defined.

Variable x : A.

Section ABSTRACT_FORM.

Variable eq_encoder : forall y : A, x = y -> x = y.

Let eq_decoder (y : A) : x = y -> x = y :=
  eq_transitivity x x y (eq_symmetry x x (eq_encoder x (eq_reflexivity x))).

Lemma eq_decoder_correct (y : A)
  (x_eq_y : x = y)
  : eq_decoder y (eq_encoder y x_eq_y) = x_eq_y.
Proof.
  unfold eq_decoder. destruct x_eq_y. rewrite eq_round_trip. reflexivity.
Defined.

Hypothesis indistinguishable : forall y : A, forall H_eq1 : x = y, forall H_eq2 : x = y, eq_encoder y H_eq1 = eq_encoder y H_eq2.

Lemma eq_pirrel_from_eq_em (y : A)
  (H_eq1 : x = y)
  (H_eq2 : x = y)
  : H_eq1 = H_eq2.
Proof.
  rewrite <- eq_decoder_correct with (x_eq_y := H_eq1).
  rewrite <- eq_decoder_correct with (x_eq_y := H_eq2).
  eapply f_equal. eapply indistinguishable.
Defined.

End ABSTRACT_FORM.

Hypothesis eq_em : forall y : A, x = y \/ x <> y.

Let eq_encoder (y : A) (x_eq_y : x = y) : x = y :=
  match eq_em y with
  | or_introl H_eq => H_eq
  | or_intror H_ne => False_ind (x = y) (H_ne x_eq_y)
  end.

Lemma eq_encoder_good
  (x_eq_x : x = x)
  : eq_encoder x x_eq_x = eq_encoder x (eq_reflexivity x).
Proof.
  unfold eq_encoder. destruct (eq_em x) as [H_eq | H_ne].
  - reflexivity.
  - contradiction (H_ne x_eq_x).
Defined.

Lemma eq_em_implies_eq_pirrel (y : A)
  (H_eq1 : x = y)
  (H_eq2 : x = y)
  : H_eq1 = H_eq2.
Proof.
  revert y H_eq1 H_eq2.
  eapply eq_pirrel_from_eq_em with (eq_encoder := eq_encoder).
  ii. destruct H_eq2. eapply eq_encoder_good.
Defined.

End EQ_EM_implies_EQ_PIRREL.

Section PROJ_T2_EQ. (* Reference: "https://coq.inria.fr/doc/v8.18/stdlib/Coq.Logic.Eqdep_dec.html" *)

Context {A : Type} {B : A -> Type} (x : A).

Hypothesis eq_pirrel : forall y : B x, forall EQ : x = x, @eq_rect A x B y x EQ = y.

Lemma projT2_eq (y1 : B x) (y2 : B x)
  (EQ : @existT A B x y1 = @existT A B x y2)
  : y1 = y2.
Proof.
  set (phi := fun pr1 : @sigT A B => fun pr2 : @sigT A B => fun projT1_eq : projT1 pr1 = projT1 pr2 => @eq_rect A (projT1 pr1) B (projT2 pr1) (projT1 pr2) projT1_eq = projT2 pr2).
  assert (claim1 : phi (@existT A B x y1) (@existT A B x y2) (@f_equal _ _ (@projT1 A B) (@existT A B x y1) (@existT A B x y2) EQ)).
  { destruct EQ. reflexivity. }
  unfold phi in claim1. rewrite eq_pirrel in claim1. exact claim1.
Defined.

End PROJ_T2_EQ.

End IDENTITY.

#[universes(polymorphic=yes)]
Definition dollar@{u v} {A : Type@{u}} {B : Type@{v}} (f : A -> B) (x : A) : B := f x.

Class isMonadIter (M : Type -> Type) `{M_isMonad : isMonad M} : Type :=
  iterM (I : Type) (R : Type) (step : I -> M (I + R)%type) : I -> M R.

#[global] Arguments iterM {M}%type_scope {M_isMonad} {isMonadIter} {I} {R} (step).

Class isAlternative (F : Type -> Type) : Type :=
  { empty {A : Type} : F A
  ; alt {A : Type} : F A -> F A -> F A
  }.

Class Similarity (A : Type) (B : Type) : Type :=
  is_similar_to (x : A) (y : B) : Prop.

#[global]
Instance forall_liftsSimilarity {I : Type} {A : I -> Type} {B : I -> Type} (SIMILARITY : forall i, Similarity (A i) (B i)) : Similarity (forall i, A i) (forall i, B i) :=
  fun f : forall i, A i => fun g : forall i, B i => forall i, is_similar_to (f i) (g i).

Theorem transfinite_induction {A : Type} {B : A -> Prop} (R : A -> A -> Prop)
  (WF : well_founded R)
  (IND : forall x : A, (forall y : A, R y x -> B y) -> B x)
  : forall x : A, B x.
Proof.
  pose (Accrec_fix :=
    fix Accrec_fix (x : A) (H_acc : @Acc A R x) {struct H_acc} : B x :=
    match H_acc with
    | @Acc_intro _ _ _ IH => IND x (fun y : A => fun H_yRx : R y x => Accrec_fix y (IH y H_yRx))
    end
  ).
  exact (fun x : A => Accrec_fix x (WF x)).
Defined.

Theorem transfinite_recursion {A : Type} {B : A -> Type} (R : A -> A -> Prop)
  (WF : well_founded R)
  (IND : forall x : A, (forall y : A, R y x -> B y) -> B x)
  : forall x : A, B x.
Proof.
  pose (Accrec_fix :=
    fix Accrec_fix (x : A) (H_acc : @Acc A R x) {struct H_acc} : B x :=
    match H_acc with
    | @Acc_intro _ _ _ IH => IND x (fun y : A => fun H_yRx : R y x => Accrec_fix y (IH y H_yRx))
    end
  ).
  exact (fun x : A => Accrec_fix x (WF x)).
Qed.

Lemma preimage_preserves_wf {A : Type} {B : Type} (R : B -> B -> Prop) (f : A -> B)
  (WF : well_founded R)
  (Rof := fun lhs : A => fun rhs : A => R (f lhs) (f rhs))
  : well_founded Rof.
Proof.
  intros x. remember (f x) as y eqn: y_eq_f_x.
  revert x y_eq_f_x. induction (WF y) as [y' _ IH].
  intros x' hyp_eq. econstructor. intros x f_x_R_f_x'.
  subst y'. eapply IH; [exact (f_x_R_f_x') | reflexivity].
Defined.

Lemma list_length_wf_ind {A: Type} (phi: list A -> Prop)
  (IND: forall s: list A, (forall s': list A, length s' < length s -> phi s') -> phi s)
  : forall s: list A, phi s.
Proof.
  pose proof (@preimage_preserves_wf) as REC.
  specialize REC with (A := list A) (B := nat) (R := Nat.lt) (f := @length A).
  exact (transfinite_induction (fun lhs : list A => fun rhs : list A => length lhs < length rhs) (REC lt_wf) IND).
Qed.

End B.

Infix "×" := B.prod (at level 40, left associativity) : type_scope.
Infix "+'" := B.sum1 (at level 50, left associativity) : type_scope.
Infix "$" := B.dollar (at level 100, right associativity).
Infix "∘" := B.compose : program_scope.
Notation isFunctor := B.isFunctor.
Notation fmap := B.fmap.
Notation isMonad := B.isMonad.
Notation pure := B.pure.
Notation bind := B.bind.
Notation isAlternative := B.isAlternative.
Notation Similarity := B.Similarity.
Notation is_similar_to := B.is_similar_to.

Section EQ_DEC.

Class hasEqDec (A : Type) : Type :=
  eq_dec (x : A) (y : A) : {x = y} + {x <> y}.

#[global]
Instance nat_hasEqDec : hasEqDec nat :=
  Nat.eq_dec.

#[global]
Instance option_hasEqDec {A : Type}
  `(EQ_DEC : hasEqDec A)
  : hasEqDec (option A).
Proof.
  exact (fun x : option A => fun y : option A =>
    match x as a, y as b return {a = b} + {a <> b} with
    | None, None => left eq_refl
    | None, Some y' => right (fun EQ : None = Some y' => B.Some_ne_None y' (B.eq_symmetry None (Some y') EQ))
    | Some x', None => right (fun EQ : Some x' = None => B.Some_ne_None x' EQ)
    | Some x', Some y' =>
      match EQ_DEC x' y' with
      | left EQ => left (f_equal (@Some A) EQ)
      | right NE => right (fun EQ : Some x' = Some y' => NE (f_equal (B.maybe x' B.id) EQ))
      end
    end
  ).
Defined.

Lemma eq_pirrel_fromEqDec {A : Type} {hasEqDec : hasEqDec A} (lhs : A) (rhs : A)
  (H_eq1 : lhs = rhs)
  (H_eq2 : lhs = rhs)
  : H_eq1 = H_eq2.
Proof.
  revert rhs H_eq1 H_eq2. eapply B.eq_em_implies_eq_pirrel.
  intros rhs. pose proof (eq_dec lhs rhs) as [H_eq | H_ne].
  - left. exact H_eq.
  - right. exact H_ne.
Defined.

Lemma projT2_eq_fromEqDec {A : Type} {B : A -> Type} {hasEqDec : hasEqDec A} (x : A) (y1 : B x) (y2 : B x)
  (EQ : @existT A B x y1 = @existT A B x y2)
  : y1 = y2.
Proof.
  eapply B.projT2_eq.
  - intros y x_eq_x.
    rewrite eq_pirrel_fromEqDec with (H_eq1 := x_eq_x) (H_eq2 := eq_refl).
    reflexivity.
  - exact EQ.
Defined.

End EQ_DEC.

Section COUNTABLE. (* Reference: "https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.countable.html" *)

Class isCountable (A : Type) : Type :=
  { encode : A -> nat
  ; decode : nat -> option A
  ; decode_encode (x : A)
    : decode (encode x) = Some x 
  }.

Section SEARCH. (* Reference: "https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.countable.html" *)

Context {A : Type} `{COUNTABLE : isCountable A}.

Inductive search_step (P : A -> Prop) (n : nat) : nat -> Prop :=
  | search_step_None
    (NONE : decode n = None)
    : search_step P n (S n)
  | search_step_Some (x : A)
    (NOT : ~ P x)
    (SOME : decode n = Some x)
    : search_step P n (S n).

Lemma Acc_flip_search_step_P_0 (P : A -> Prop)
  (BOUND : exists x : A, P x)
  : Acc (flip (search_step P)) 0.
Proof.
  destruct BOUND as [x P_x]. enough (WTS : forall i, forall p, i <= encode x -> encode x = p + i -> Acc (flip (search_step P)) p) by now ii; eapply WTS with (i := encode x); lia.
  induction i as [ | i IH]; simpl; intros p LE EQ.
  - econs. intros j SEARCH. red in SEARCH. rewrite Nat.add_0_r in EQ. subst p. inv SEARCH.
    + rewrite decode_encode in NONE. congruence.
    + rewrite decode_encode in SOME. congruence.
  - econs. intros j SEARCH. red in SEARCH. eapply IH.
    + lia.
    + inv SEARCH; lia.
Defined.

Fixpoint search_go (P : A -> Prop) (P_dec : forall x, {P x} + {~ P x}) (n : nat) (acc : Acc (flip (search_step P)) n) {struct acc} : A.
Proof.
  destruct (B.Some_dec (decode n)) as [[y SOME] | NONE].
  - destruct (P_dec y) as [EQ | NE].
    + exact y.
    + exact (search_go P P_dec (S n) (Acc_inv acc (search_step_Some P n y NE SOME))).
  - exact (search_go P P_dec (S n) (Acc_inv acc (search_step_None P n NONE))).
Defined.

Fixpoint search_go_correct (P : A -> Prop) (P_dec : forall x, {P x} + {~ P x}) (n : nat) (acc : Acc (flip (search_step P)) n) {struct acc}
  : P (search_go P P_dec n acc).
Proof.
  destruct acc; simpl. destruct (B.Some_dec (decode n)) as [[? ?] | ?] eqn: ?.
  - destruct (P_dec x).
    + assumption.
    + eapply search_go_correct.
  - eapply search_go_correct.
Qed.

Lemma search_go_pirrel (P : A -> Prop) (P_dec : forall x, {P x} + {~ P x}) (n : nat) (acc : Acc (flip (search_step P)) n) (acc' : Acc (flip (search_step P)) n)
  : search_go P P_dec n acc = search_go P P_dec n acc'.
Proof.
  revert acc acc acc'. intros acc''. induction acc'' as [? _ IH]; intros [?] [?]. simpl.
  destruct (B.Some_dec (decode x)) as [[? ?] | ?] eqn: ?.
  - destruct (P_dec x0) as [? | ?].
    + reflexivity.
    + eapply IH. eapply search_step_Some with (x := x0); trivial.
  - eapply IH. eapply search_step_None; trivial.
Qed.

Definition search (n : nat) (BOUND : exists x : A, encode x = n) : A.
Proof.
  eapply search_go with (n := 0) (P := fun x : A => encode x = n).
  - exact (fun x : A => Nat.eq_dec (encode x) n).
  - eapply Acc_flip_search_step_P_0. exact BOUND.
Defined.

Theorem enumeration_lemma
  (encode_surjective : forall n : nat, exists x : A, encode x = n)
  : { enum : nat -> A & ⟪ enumerable : forall x : A, { n : nat | enum n = x } ⟫ }.
Proof.
  exists (fun n : nat => search n (encode_surjective n)). unnw. intros x. exists (encode x).
  assert (claim : encode (search (encode x) (encode_surjective (encode x))) = encode x).
  { eapply search_go_correct with (P := fun y : A => encode y = encode x) (P_dec := fun y : A => Nat.eq_dec (encode y) (encode x)). }
  apply f_equal with (f := decode) in claim. do 2 rewrite decode_encode in claim. congruence.
Defined.

End SEARCH.

Theorem LEM_implies_MarkovPrinciple (LEM : forall P : Prop, P \/ ~ P) (f : nat -> bool) 
  (NOT_ALL_TRUE : ~ forall x : nat, f x = true)
  : { n : nat | f n = false }.
Proof.
  enough (EXISTENCE : exists n : nat, f n = false).
  - assert (COUNTABLE : isCountable nat).
    { exists B.id Some. reflexivity. }
    assert (P_dec : forall x : nat, {f x = false} + {f x <> false}).
    { intros x. now destruct (f x) as [ | ]; [right | left]. }
    pose proof (FUEL := @Acc_flip_search_step_P_0 nat COUNTABLE (fun x : nat => f x = false) EXISTENCE).
    exists (@search_go nat COUNTABLE (fun x : nat => f x = false) P_dec 0 FUEL). eapply search_go_correct.
  - pose proof (LEM (exists n : nat, f n = false)) as [YES | NO].
    + exact YES.
    + contradiction NOT_ALL_TRUE. intros x. destruct (f x) as [ | ] eqn: H_OBS; now firstorder.
Defined.

Lemma dec_find_result_if_exists (P : nat -> Prop)
  (DEC : forall n, {P n} + {~ P n})
  (EXISTENCE : exists x, P x)
  : { x : nat | P x }.
Proof.
  pose (COUNTABLE := {| encode := B.id; decode := @Some nat; decode_encode (x : nat) := @eq_refl (option nat) (Some x) |}).
  exists (@search_go nat COUNTABLE P DEC 0 (@Acc_flip_search_step_P_0 nat COUNTABLE P EXISTENCE)).
  eapply search_go_correct.
Defined.

End COUNTABLE.

Section ENUMERABLE.

Class isEnumerable (A : Type) : Type :=
  { enum : nat -> A
  ; enum_spec : forall x : A, { n : nat | enum n = x }
  }.

Lemma enum_spec_injective {A : Type} `{ENUMERABLE : isEnumerable A}
  (inj := fun x : A => proj1_sig (enum_spec x))
  : forall x1 : A, forall x2 : A, inj x1 = inj x2 -> x1 = x2.
Proof.
  unfold inj. intros x1 x2 inj_EQ.
  destruct (enum_spec x1) as [n1 EQ1], (enum_spec x2) as [n2 EQ2].
  simpl in *. congruence.
Qed.

#[global]
Instance isCountable_if_isEnumerable {A : Type} `(ENUMERABLE : isEnumerable A) : isCountable A :=
  { encode (x : A) := proj1_sig (enum_spec x)
  ; decode (n : nat) := Some (enum n)
  ; decode_encode (x : A) := f_equal (@Some A) (proj2_sig (enum_spec x))
  }.

End ENUMERABLE.

Section LIFTS.

#[local]
Instance relation_on_image_liftsEquivalence {A : Type} {B : Type} {eqProp : B -> B -> Prop}
  `(isEquivalence : @Equivalence B eqProp)
  : forall f : A -> B, Equivalence (B.binary_relation_on_image eqProp f).
Proof.
  intros f. constructor.
  - intros x1. exact (Equivalence_Reflexive (f x1)).
  - intros x1 x2 H_1EQ2. exact (Equivalence_Symmetric (f x1) (f x2) H_1EQ2).
  - intros x1 x2 x3 H_1EQ2 H_2EQ3. exact (Equivalence_Transitive (f x1) (f x2) (f x3) H_1EQ2 H_2EQ3).
Defined.

#[local]
Instance relation_on_image_liftsPreOrder {A : Type} {B : Type} {leProp : B -> B -> Prop}
  `(isPreOrder : @PreOrder B leProp)
  : forall f : A -> B, PreOrder (B.binary_relation_on_image leProp f).
Proof.
  intros f. constructor.
  - intros x1. exact (PreOrder_Reflexive (f x1)).
  - intros x1 x2 x3 H_1LE2 H_2LE3. exact (PreOrder_Transitive (f x1) (f x2) (f x3) H_1LE2 H_2LE3).
Defined.

#[local]
Instance relation_on_image_liftsPartialOrder {A : Type} {B : Type} {eqProp : B -> B -> Prop} {leProp : B -> B -> Prop}
  `{isEquivalence : @Equivalence B eqProp}
  `{isPreOrder : @PreOrder B leProp}
  `(isPartialOrder : @PartialOrder B eqProp _ leProp _)
  : forall f : A -> B, PartialOrder (B.binary_relation_on_image eqProp f) (B.binary_relation_on_image leProp f).
Proof.
  intros f x1 x2. constructor.
  - intros H_EQ. constructor.
    + exact (proj1 (proj1 (partial_order_equivalence (f x1) (f x2)) H_EQ)).
    + exact (proj2 (proj1 (partial_order_equivalence (f x1) (f x2)) H_EQ)).
  - intros H_EQ. apply (proj2 (partial_order_equivalence (f x1) (f x2))). constructor.
    + exact (proj1 H_EQ).
    + exact (proj2 H_EQ).
Defined.

End LIFTS.

Section SETOID.

Class isSetoid (A : Type) : Type :=
  { eqProp (lhs : A) (rhs : A) : Prop
  ; eqProp_Equivalence :: @Equivalence A eqProp
  }.

#[local] Infix "==" := eqProp : type_scope.

#[local] Obligation Tactic := intros.

#[program]
Definition mkSetoidFromPreOrder {A : Type} (leProp : A -> A -> Prop) `(leProp_PreOrder : @PreOrder A leProp) : isSetoid A :=
  {| eqProp (x : A) (y : A) := leProp x y /\ leProp y x |}.
Next Obligation.
  split; ii.
  - exact (conj (@PreOrder_Reflexive A leProp leProp_PreOrder x) (@PreOrder_Reflexive A leProp leProp_PreOrder x)).
  - exact (conj (proj2 H) (proj1 H)).
  - exact (conj (@PreOrder_Transitive A leProp leProp_PreOrder x y z (proj1 H) (proj1 H0)) (@PreOrder_Transitive A leProp leProp_PreOrder z y x (proj2 H0) (proj2 H))).
Defined.

Definition mkSetoidFromPreOrder_PartialOrder {A : Type} (leProp : A -> A -> Prop) `(leProp_PreOrder : @PreOrder A leProp)
  (SETOID := mkSetoidFromPreOrder leProp leProp_PreOrder)
  : PartialOrder SETOID.(eqProp) leProp.
Proof.
  cbv. intros x y. split; exact (fun H => H).
Defined.

#[global, program]
Instance arrow_isSetoid {A : Type} {B : Type} `(SETOID : isSetoid B) : isSetoid (A -> B) :=
  { eqProp (f : A -> B) (g : A -> B) := forall x : A, f x == g x }.
Next Obligation.
  split.
  - intros f1 x. exact (Equivalence_Reflexive (f1 x)).
  - intros f1 f2 EQ1 x. exact (Equivalence_Symmetric (f1 x) (f2 x) (EQ1 x)).
  - intros f1 f2 f3 EQ1 EQ2 x. exact (Equivalence_Transitive (f1 x) (f2 x) (f3 x) (EQ1 x) (EQ2 x)).
Defined.

#[global, program]
Instance pair_isSetoid {A : Type} {B : Type} `(A_isSetoid : isSetoid A) `(B_isSetoid : isSetoid B) : isSetoid (B.prod A B) :=
  { eqProp lhs rhs := lhs.(B.fst) == rhs.(B.fst) /\ lhs.(B.snd) == rhs.(B.snd) }.
Next Obligation.
  split.
  - intros x1. split; reflexivity.
  - intros x1 x2 [-> ->]. split; reflexivity.
  - intros x1 x2 x3 [-> ->] [-> ->]. split; reflexivity.
Qed.

Class isSetoid1 (F : Type -> Type) : Type :=
  liftSetoid1 (X : Type) `(SETOID : isSetoid X) :: isSetoid (F X).

Definition trivialSetoid {A : Type} : isSetoid A :=
  {| eqProp := @eq A; eqProp_Equivalence := @eq_equivalence A; |}.

#[local]
Instance fromSetoid1 {F : Type -> Type} {X : Type} `(SETOID1 : isSetoid1 F) : isSetoid (F X) :=
  liftSetoid1 X trivialSetoid.

End SETOID.

Infix "==" := eqProp : type_scope.

Section POSET.

Class isPoset (D : Type) : Type :=
  { Poset_isSetoid :: isSetoid D
  ; leProp (lhs : D) (rhs : D) : Prop
  ; leProp_PreOrder :: @PreOrder D leProp
  ; leProp_PartialOrder :: @PartialOrder D eqProp eqProp_Equivalence leProp leProp_PreOrder
  }.

#[local] Infix "=<" := leProp : type_scope.

#[local] Obligation Tactic := intros.

#[global, program]
Instance arrow_isPoset {A : Type} {B : Type} `(POSET : isPoset B) : isPoset (A -> B) :=
  { Poset_isSetoid := arrow_isSetoid Poset_isSetoid; leProp f g := forall x : A, f x =< g x }.
Next Obligation.
  split.
  - intros f1 x. exact (PreOrder_Reflexive (f1 x)).
  - intros f1 f2 f3 LE1 LE2 x. exact (PreOrder_Transitive (f1 x) (f2 x) (f3 x) (LE1 x) (LE2 x)).
Defined.
Next Obligation.
  intros f g. split; [intros f_eq_g | intros [f_le_g g_le_f] x].
  - assert (claim : forall x : A, f x =< g x /\ g x =< f x).
    { intros x. eapply leProp_PartialOrder. exact (f_eq_g x). }
    exact (conj (fun x => proj1 (claim x)) (fun x => proj2 (claim x))).
  - eapply leProp_PartialOrder. exact (conj (f_le_g x) (g_le_f x)).
Defined.

Definition Prop_isPoset : isPoset Prop :=
  let impl_PreOrder : PreOrder B.impl := {| PreOrder_Reflexive (A : Prop) := B.id (A := A); PreOrder_Transitive (A : Prop) (B : Prop) (C : Prop) := B.flip (B.compose (A := A) (B := B) (C := C)); |} in
  {|
    Poset_isSetoid := mkSetoidFromPreOrder B.impl impl_PreOrder;
    leProp := B.impl;
    leProp_PreOrder := impl_PreOrder;
    leProp_PartialOrder := mkSetoidFromPreOrder_PartialOrder B.impl impl_PreOrder;
  |}.

End POSET.

Infix "=<" := leProp : type_scope.

Module E.

#[universes(polymorphic=yes)]
Definition t@{u} (A : Type@{u}) : Type@{u} := A -> Prop.

#[universes(polymorphic=yes)]
Definition elem@{u} {A : Type@{u}} (x : A) (X : E.t@{u} A) : Prop := X x.

#[local] Infix "\in" := E.elem : type_scope.

#[universes(polymorphic=yes)]
Definition isSubsetOf@{u} {A : Type@{u}} (X1 : E.t@{u} A) (X2 : E.t@{u} A) : Prop :=
  forall x : A, @E.elem@{u} A x X1 -> @E.elem@{u} A x X2.

#[local] Infix "\subseteq" := E.isSubsetOf : type_scope.

#[global]
Instance ensemble_isPoset {A : Type} : isPoset (E.t A) :=
  arrow_isPoset Prop_isPoset.

Lemma ensemble_eq_unfold {A : Type} (X1 : E.t A) (X2 : E.t A)
  : (X1 == X2) = (forall x : A, x \in X1 <-> x \in X2).
Proof.
  exact eq_refl.
Defined.

Lemma ensemble_le_unfold {A : Type} (X1 : E.t A) (X2 : E.t A)
  : (X1 =< X2) = (X1 \subseteq X2).
Proof.
  exact eq_refl.
Defined.

Inductive empty {A : Type} : E.t A :=.

#[global] Hint Constructors empty : datatypes.

Lemma in_empty_iff {A : Type}
  : forall z : A, z \in empty <-> False.
Proof.
  intros z; split; intros [].
Qed.

#[global] Hint Rewrite @in_empty_iff : datatypes.

Inductive union {A : Type} (X1 : E.t A) (X2 : E.t A) : E.t A :=
  | In_union_l (x : A)
    (H_inl : x \in X1)
    : x \in union X1 X2 
  | In_union_r (x : A)
    (H_inr : x \in X2)
    : x \in union X1 X2.

#[global] Hint Constructors union : datatypes.

Lemma in_union_iff {A : Type} (X1 : E.t A) (X2 : E.t A)
  : forall z : A, z \in union X1 X2 <-> (z \in X1 \/ z \in X2).
Proof.
  intros z; split; intros [H_inl | H_inr]; eauto with *.
Qed.

#[global] Hint Rewrite @in_union_iff : datatypes.

Inductive intersection {A : Type} (X1 : E.t A) (X2 : E.t A) : E.t A :=
  | In_intersection (x : A)
    (H_in1 : x \in X1)
    (H_in2 : x \in X2)
    : x \in intersection X1 X2.

#[global] Hint Constructors intersection : datatypes.

Lemma in_intersection_iff {A : Type} (X1 : E.t A) (X2 : E.t A)
  : forall z : A, z \in intersection X1 X2 <-> (z \in X1 /\ z \in X2).
Proof.
  intros z; split; intros [H_in1 H_in2]; eauto with *.
Qed.

#[global] Hint Rewrite @in_intersection_iff : datatypes.

Inductive unions {A : Type} (Xs : E.t (E.t A)) : E.t A :=
  | In_unions (x : A) (X : E.t A)
    (H_in : x \in X)
    (H_IN : X \in Xs)
    : x \in unions Xs.

#[global] Hint Constructors unions : datatypes.

Lemma in_unions_iff {A : Type} (Xs : E.t (E.t A))
  : forall z : A, z \in unions Xs <-> (exists X : E.t A, z \in X /\ X \in Xs).
Proof.
  intros z; split; [intros [? ?] | intros [? [? ?]]]; eauto with *.
Qed.

#[global] Hint Rewrite @in_unions_iff : datatypes.

Inductive singleton {A : Type} (x : A) : E.t A :=
  | In_singleton
    : x \in singleton x.

#[global] Hint Constructors singleton : datatypes.

Lemma in_singleton_iff {A : Type} (x : A)
  : forall z : A, z \in singleton x <-> z = x.
Proof.
  intros z; split; [intros [ ] | intros ->]; eauto with *.
Qed.

#[global] Hint Rewrite @in_singleton_iff : datatypes.

Inductive image {A : Type} {B : Type} (f : A -> B) (X : E.t A) : E.t B :=
  | In_image (y : B) (x : A)
    (H_in : x \in X)
    (EQ : y = f x)
    : y \in image f X.

#[global] Hint Constructors image : datatypes.

Lemma in_image_iff {A : Type} {B : Type} (f : A -> B) (X : E.t A)
  : forall z : B, z \in image f X <-> exists x : A, x \in X /\ z = f x.
Proof.
  intros z; split; [intros [? ? ? ?] | intros [? [? ?]]]; eauto with *.
Qed.

#[global] Hint Rewrite @in_image_iff : datatypes.

Inductive preimage {A : Type} {B : Type} (f : A -> B) (Y : E.t B) : E.t A :=
  | In_preimage (x : A)
    (H_in : f x \in Y)
    : x \in preimage f Y.

#[global] Hint Constructors preimage : datatypes.

Lemma in_preimage_iff {A : Type} {B : Type} (f : A -> B) (Y : E.t B)
  : forall z : A, z \in preimage f Y <-> exists y : B, y \in Y /\ y = f z.
Proof.
  intros z; split; [intros [? ?] | intros [? [? ->]]]; eauto with *.
Qed.

#[global] Hint Rewrite @in_intersection_iff : datatypes.

Inductive finite {A : Type} (xs : list A) : E.t A :=
  | In_finite x
    (H_in : List.In x xs)
    : x \in finite xs.

#[global] Hint Constructors finite : datatypes.

Lemma in_finite_iff {A : Type} (xs : list A)
  : forall z : A, z \in finite xs <-> List.In z xs.
Proof.
  intros z; split; [intros [?] | intros ?]; eauto with *.
Qed.

#[global] Hint Rewrite @in_finite_iff : datatypes.

Inductive insert {A : Type} (x1 : A) (X2 : E.t A) : E.t A :=
  | In_head x
    (H_eq : x = x1)
    : x \in insert x1 X2
  | In_tail x
    (H_in : x \in X2)
    : x \in insert x1 X2.

#[global] Hint Constructors insert : datatypes.

Lemma in_insert_iff {A : Type} (x1 : A) (X2 : E.t A)
  : forall z : A, z \in insert x1 X2 <-> (z = x1 \/ z \in X2).
Proof.
  intros z; split; [intros [? | ?] | intros [? | ?]]; eauto with *.
Qed.

#[global] Hint Rewrite @in_insert_iff : datatypes.

#[global]
Instance ensemble_isMonad : isMonad E.t :=
  { pure {A} (x : A) := singleton x
  ; bind {A} {B} (m : E.t A) (k : A -> E.t B) := unions (image k m)
  }.

Lemma ensemble_liftM2_spec {A : Type} {B : Type} {C : Type} (f : A -> B -> C) (X : E.t A) (Y : E.t B)
  : forall z : C, z \in B.liftM2 f X Y <-> exists x, x \in X /\ exists y, y \in Y /\ z = f x y.
Proof with autorewrite with datatypes in *; trivial.
  intros z. unfold B.liftM2. unfold bind, pure. simpl...
  split; [intros (?&?&?) | intros (?&?&?&?&?)].
  - des... des... subst... des... des... subst... subst... now firstorder.
  - subst. exists (unions (image (fun y : B => singleton (f x y)) Y)). split...
    + exists (singleton (f x x0)). split... now firstorder.
    + exists x... now firstorder.
Qed.

#[global] Hint Rewrite @ensemble_liftM2_spec : datatypes.

#[global]
Instance ensemble_isFunctor : isFunctor E.t :=
  B.mkFunctorFromMonad ensemble_isMonad.

Lemma ensemble_fmap_spec {A : Type} {B : Type} (f : A -> B) (X : E.t A)
  : forall z : B, z \in fmap f X <-> z \in image f X.
Proof with autorewrite with datatypes in *; trivial.
  intros z. unfold fmap; simpl. unfold ensemble_isFunctor; simpl.
  split; intros ?...
  - des... des... subst... subst... now firstorder.
  - des... subst... exists (singleton (f x)). split... now firstorder.
Qed.

#[global] Hint Rewrite @ensemble_fmap_spec : datatypes.

Definition full {A : Type} : E.t A :=
  fun z : A => True.

#[global] Hint Unfold full : datatypes.

Lemma in_full_iff {A : Type}
  : forall z : A, z \in full <-> True.
Proof.
  reflexivity.
Qed.

#[global] Hint Rewrite @in_full_iff : datatypes.

Definition difference {A : Type} (X1 : E.t A) (X2 : E.t A) : E.t A :=
  fun z : A => z \in X1 /\ ~ z \in X2.

#[global] Hint Unfold difference : datatypes.

Lemma in_difference_iff {A : Type} (X1 : E.t A) (X2 : E.t A)
  : forall z : A, z \in difference X1 X2 <-> (z \in X1 /\ ~ z \in X2).
Proof.
  reflexivity.
Qed.

#[global] Hint Rewrite @in_difference_iff : datatypes.

End E.

Notation ensemble := E.t.

#[global] Hint Resolve E.in_empty_iff : datatypes.
#[global] Hint Resolve E.in_union_iff : datatypes.
#[global] Hint Resolve E.in_intersection_iff : datatypes.
#[global] Hint Resolve E.in_unions_iff : datatypes.
#[global] Hint Resolve E.in_singleton_iff : datatypes.
#[global] Hint Resolve E.in_image_iff : datatypes.
#[global] Hint Resolve E.in_preimage_iff : datatypes.
#[global] Hint Resolve E.in_finite_iff : datatypes.
#[global] Hint Resolve E.in_insert_iff : datatypes.
#[global] Hint Resolve E.ensemble_liftM2_spec : datatypes.
#[global] Hint Resolve E.ensemble_fmap_spec : datatypes.
#[global] Hint Resolve E.in_full_iff : datatypes.
#[global] Hint Resolve E.in_difference_iff : datatypes.

Module CAT.

#[universes(polymorphic=yes)]
Class Category@{u v} : Type :=
  { ob : Type@{u}
  ; hom (dom : ob) (cod : ob) : Type@{v}
  ; compose {A : ob} {B : ob} {C : ob} (g : hom B C) (f : hom A B) : hom A C
  ; id {A : ob} : hom A A
  }.

#[global] Coercion ob : Category >-> Sortclass.
#[global] Coercion hom : Category >-> Funclass.

Universe u_HASK.

#[local]
Instance HASK : Category :=
  { ob := Type@{u_HASK}
  ; hom A B := A -> B
  ; compose {A} {B} {C} (g : B -> C) (f : A -> B) := fun x : A => g (f x)
  ; id {A} := fun x : A => x
  }.

End CAT.

Notation Category := CAT.Category.

Section MONAD.

#[local] Open Scope program_scope.
#[local] Open Scope type_scope.
#[local] Obligation Tactic := intros.

#[local] Notation f_eqProp := (eqProp (isSetoid := arrow_isSetoid _)).
#[local] Infix "=~=" := f_eqProp : type_scope.
#[local] Infix ">>=" := bind.
#[local] Existing Instance fromSetoid1.

Class isNiceMonad (M : Type -> Type) `{M_isMonad : isMonad M} `{M_isSetoid1 : isSetoid1 M} : Prop :=
  { bind_m_compatWith_eqProp {A : Type} {B : Type} (m1 : M A) (m2 : M A) (k : A -> M B)
    (m1_eq_m2 : m1 == m2)
    : (m1 >>= k) == (m2 >>= k)
  ; k_bind_compatWith_eqProp {A : Type} {B : Type} (k1 : A -> M B) (k2 : A -> M B) (m : M A)
    (k1_eq_k2 : k1 =~= k2)
    : (m >>= k1) == (m >>= k2)
  ; bind_assoc {A : Type} {B : Type} {C : Type} (m : M A) (k : A -> M B) (k' : B -> M C)
    : (m >>= k >>= k') == (m >>= fun x => k x >>= k')
  ; bind_pure_l {A : Type} {B : Type} (k : A -> M B) (x : A)
    : (pure x >>= k) == k x
  ; bind_pure_r {A : Type} (m : M A)
    : (m >>= pure) == m
  }.

#[global]
Add Parametric Morphism {M : Type -> Type} `{M_isMonad : isMonad M} `{M_isSetoid1 : isSetoid1 M} {A: Type} {B: Type}
  (M_isNiceMonad : isNiceMonad M (M_isMonad := M_isMonad) (M_isSetoid1 := M_isSetoid1))
  : (@bind M M_isMonad A B) with signature (eqProp ==> f_eqProp ==> eqProp)
  as bind_compatWith_eqProp.
Proof.
  intros m1 m2 m1_eq_m2 k1 k2 k1_eq_k2.
  rewrite bind_m_compatWith_eqProp with (m1 := m1) (m2 := m2) (m1_eq_m2 := m1_eq_m2).
  rewrite k_bind_compatWith_eqProp with (k1 := k1) (k2 := k2) (k1_eq_k2 := k1_eq_k2).
  reflexivity.
Qed.

#[global]
Instance stateT_isMonad {S : Type} {M : Type -> Type} `(M_isMonad : isMonad M) : isMonad (B.stateT S M) :=
  { pure {A} (x : A) := B.StateT $ fun s => pure (B.pair x s)
  ; bind {A} {B} (m : B.stateT S M A) (k : A -> B.stateT S M B) := B.StateT $ fun s => B.runStateT m s >>= fun p => B.runStateT (k p.(B.fst)) p.(B.snd)
  }.

Definition stateT_isSetoid {S : Type} {M : Type -> Type} `{M_isSetoid1 : isSetoid1 M} (X : Type) : isSetoid (B.stateT S M X) :=
  {|
    eqProp lhs rhs := forall s, B.runStateT lhs s == B.runStateT rhs s;
    eqProp_Equivalence := relation_on_image_liftsEquivalence (arrow_isSetoid (fromSetoid1 M_isSetoid1)).(eqProp_Equivalence) B.runStateT;
  |}.

#[local]
Instance stateT_isSetoid1 {S : Type} {M : Type -> Type} `{M_isSetoid1 : isSetoid1 M} : isSetoid1 (B.stateT S M) :=
  fun X : Type => fun _ : isSetoid X => @stateT_isSetoid S M M_isSetoid1 X.

#[local]
Instance stateT_isNiceMonad {S : Type} {M : Type -> Type} `{M_isMonad : isMonad M} `{M_isSetoid1 : isSetoid1 M}
  `(M_isNiceMonad : @isNiceMonad M M_isMonad M_isSetoid1)
  : isNiceMonad (B.stateT S M).
Proof.
  split; i.
  - destruct m1 as [m1], m2 as [m2]; simpl in *. intros s. eapply bind_m_compatWith_eqProp. exact (m1_eq_m2 s).
  - destruct m as [m]; simpl in *. intros s. eapply k_bind_compatWith_eqProp. intros p. exact (k1_eq_k2 (p.(B.fst)) (p.(B.snd))).
  - destruct m as [m]; simpl in *. intros s. eapply bind_assoc.
  - destruct (k x) as [m] eqn: H_OBS. simpl in *. intros s. rewrite bind_pure_l. simpl. rewrite H_OBS. reflexivity.
  - destruct m as [m]; simpl in *. intros s. rewrite bind_pure_r. reflexivity.
Qed.

#[global]
Instance stateT_isMonadIter {S : Type} {M : Type -> Type} `{M_isMonad : isMonad M} `(M_isMonadIter : @B.isMonadIter M M_isMonad) : B.isMonadIter (B.stateT S M) :=
  fun I : Type => fun R : Type => fun step : I -> B.stateT S M (I + R) =>
  let DISTR (A : Type) (B : Type) (C : Type) (it : (A + B) × C) : (A × C) + (B × C) := B.either (fun x => inl (B.pair x (B.snd it))) (fun y => inr (B.pair y (B.snd it))) (B.fst it) in
  B.StateT ∘ B.curry (B.iterM (fmap (isFunctor := B.mkFunctorFromMonad M_isMonad) (DISTR I R S) ∘ B.uncurry (B.runStateT ∘ step))).

End MONAD.

Module RETRACT. (* Reference: "https://coq.inria.fr/doc/v8.18/stdlib/Coq.Logic.Berardi.html" *)

#[universes(template)]
Record t (X : Type) (A : Type) : Type :=
  { retraction : X -> A
  ; incl : A -> X
  ; id : forall x, incl (retraction x) = x
  }.

#[global] Arguments RETRACT.retraction {X} {A}.
#[global] Arguments RETRACT.incl {X} {A}.
#[global] Arguments RETRACT.id {X} {A}.

#[universes(polymorphic=yes)]
Definition RETRACT_REFL@{u} (X : Type@{u}) : RETRACT.t X X :=
  {| retraction := @B.id X; incl := @B.id X; id := @eq_refl X |}.

End RETRACT.

Lemma eqProp_refl {A : Type} `(A_isSetoid : isSetoid A)
  : forall x : A, x == x.
Proof.
  eapply Equivalence_Reflexive.
Defined.

Lemma eqProp_sym {A : Type} `(A_isSetoid : isSetoid A)
  : forall x : A, forall y : A, x == y -> y == x.
Proof.
  eapply Equivalence_Symmetric.
Defined.

Lemma eqProp_trans {A : Type} `(A_isSetoid : isSetoid A)
  : forall x : A, forall y : A, forall z : A, x == y -> y == z -> x == z.
Proof.
  eapply Equivalence_Transitive.
Defined.

Lemma leProp_refl {A : Type} `(A_isPoset : isPoset A)
  : forall x : A, x =< x.
Proof.
  eapply PreOrder_Reflexive.
Defined.

Lemma leProp_trans {A : Type} `(A_isPoset : isPoset A)
  : forall x : A, forall y : A, forall z : A, x =< y -> y =< z -> x =< z.
Proof.
  eapply PreOrder_Transitive.
Defined.

Lemma leProp_antisymmetry {A : Type} `(A_isPoset : isPoset A)
  : forall x : A, forall y : A, x =< y -> y =< x -> x == y.
Proof.
  intros x y x_le_y y_le_x. exact (proj2 (leProp_PartialOrder x y) (conj x_le_y y_le_x)).
Defined.

Lemma eqProp_implies_leProp {A : Type} `(A_isPoset : isPoset A)
  : forall x : A, forall y : A, x == y -> x =< y.
Proof.
  intros x y x_eq_y. exact (proj1 (proj1 (leProp_PartialOrder x y) x_eq_y)).
Defined.

Create HintDb mathhints.

#[global] Hint Resolve eqProp_refl : mathhints.
#[global] Hint Resolve eqProp_sym : mathhints.
#[global] Hint Resolve eqProp_trans : mathhints.
#[global] Hint Resolve leProp_refl : mathhints.
#[global] Hint Resolve leProp_trans : mathhints.
#[global] Hint Resolve leProp_antisymmetry : mathhints.
#[global] Hint Resolve eqProp_implies_leProp : mathhints.

Class MapSetoid1 {A : Type} {B : Type} `{A_isSetoid : isSetoid A} `{B_isSetoid : isSetoid B} (f : A -> B) : Prop :=
  map_eqProp1 (x1 : A) (x2 : A) (x_EQ : x1 == x2) : f x1 == f x2.

#[global]
Add Parametric Morphism {A : Type} {B : Type} `{A_isSetoid : isSetoid A} `{B_isSetoid : isSetoid B} (f : A -> B)
  `(MAP_SETOID : @MapSetoid1 A B A_isSetoid B_isSetoid f)
  : f with signature (eqProp ==> eqProp)
  as congruence_unary.
Proof.
  intros x1 x2 x_EQ. exact (map_eqProp1 x1 x2 x_EQ).
Defined.

Class MapSetoid2 {A : Type} {B : Type} {C : Type} `{A_isSetoid : isSetoid A} `{B_isSetoid : isSetoid B} `{C_isSetoid : isSetoid C} (f : A -> B -> C) : Prop :=
  map_eqProp2 (x1 : A) (x2 : A) (y1 : B) (y2 : B) (x_EQ : x1 == x2) (y_EQ : y1 == y2) : f x1 y1 == f x2 y2.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isSetoid : isSetoid A} `{B_isSetoid : isSetoid B} `{C_isSetoid : isSetoid C} (f : A -> B -> C)
  `(MAP_SETOID : @MapSetoid2 A B C A_isSetoid B_isSetoid C_isSetoid f)
  : f with signature (eqProp ==> eqProp ==> eqProp)
  as congruence_binary.
Proof.
  intros x1 x2 x_EQ y1 y2 y_EQ. exact (map_eqProp2 x1 x2 y1 y2 x_EQ y_EQ).
Defined.

Class MapPoset1 {A : Type} {B : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} (f : A -> B) : Prop :=
  map_leProp1 (x1 : A) (x2 : A) (x_LE : x1 =< x2) : f x1 =< f x2.

#[global]
Add Parametric Morphism {A : Type} {B : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} (f : A -> B)
  `(MAP_POSET : @MapPoset1 A B A_isPoset B_isPoset f)
  : f with signature (leProp ==> leProp)
  as monotonic_unary.
Proof.
  intros x1 x2 x_LE. exact (map_leProp1 x1 x2 x_LE).
Defined.

Class MapPoset2 {A : Type} {B : Type} {C : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} `{C_isPoset : isPoset C} (f : A -> B -> C) : Prop :=
  map_leProp2 (x1 : A) (x2 : A) (y1 : B) (y2 : B) (x_LE : x1 =< x2) (y_LE : y1 =< y2) : f x1 y1 =< f x2 y2.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} `{C_isPoset : isPoset C} (f : A -> B -> C)
  `(MAP_POSET : @MapPoset2 A B C A_isPoset B_isPoset C_isPoset f)
  : f with signature (leProp ==> leProp ==> leProp)
  as monotonic_binary.
Proof.
  intros x1 x2 x_LE y1 y2 y_LE. exact (map_leProp2 x1 x2 y1 y2 x_LE y_LE).
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} `{C_isPoset : isPoset C} (f : A -> B -> C)
  `(MAP_POSET : @MapPoset2 A B C A_isPoset B_isPoset C_isPoset f)
  : f with signature (eqProp ==> leProp ==> leProp)
  as monotonic_binary_eqProp_l.
Proof.
  intros x1 x2 x_EQ y1 y2 y_LE. exact (map_leProp2 x1 x2 y1 y2 (eqProp_implies_leProp A_isPoset x1 x2 x_EQ) y_LE).
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} `{C_isPoset : isPoset C} (f : A -> B -> C)
  `(MAP_POSET : @MapPoset2 A B C A_isPoset B_isPoset C_isPoset f)
  : f with signature (leProp ==> eqProp ==> leProp)
  as monotonic_binary_eqProp_r.
Proof.
  intros x1 x2 x_LE y1 y2 y_EQ. exact (map_leProp2 x1 x2 y1 y2 x_LE (eqProp_implies_leProp B_isPoset y1 y2 y_EQ)).
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} `{C_isPoset : isPoset C} (f : A -> B -> C)
  `(MAP_POSET : @MapPoset2 A B C A_isPoset B_isPoset C_isPoset f)
  : f with signature (eqProp ==> eqProp ==> leProp)
  as monotonic_binary_eqProp_lr.
Proof.
  intros x1 x2 x_EQ y1 y2 y_EQ. exact (map_leProp2 x1 x2 y1 y2 (eqProp_implies_leProp A_isPoset x1 x2 x_EQ) (eqProp_implies_leProp B_isPoset y1 y2 y_EQ)).
Defined.

Module L.

Include Coq.Lists.List.

Lemma in_remove_iff {A : Type} `(EQ_DEC : hasEqDec A) (x1 : A) (xs2 : list A)
  : forall z, In z (remove Prelude.eq_dec x1 xs2) <-> (In z xs2 /\ z <> x1).
Proof.
  i; split.
  { intros H_IN. eapply in_remove. exact H_IN. }
  { intros [H_IN H_NE]. eapply in_in_remove; [exact H_NE | exact H_IN]. }
Qed.

Lemma rev_inj {A : Type} (xs1 : list A) (xs2 : list A)
  (rev_EQ : rev xs1 = rev xs2)
  : xs1 = xs2.
Proof.
  rewrite <- rev_involutive with (l := xs1).
  rewrite <- rev_involutive with (l := xs2).
  now f_equal.
Qed.

Lemma list_rev_dual {A : Type} (phi : list A -> Prop)
  (H_rev : forall n, phi (List.rev n))
  : forall n, phi n.
Proof.
  intros n. induction n as [ | d n _] using @List.rev_ind.
  - eapply H_rev with (n := []%list).
  - rewrite <- List.rev_involutive with (l := n).
    eapply H_rev with (n := (d :: List.rev n)%list).
Qed.

Lemma list_rev_rect {A : Type} (P : list A -> Type)
  (NIL : P [])
  (TAIL : forall x, forall xs, P xs -> P (xs ++ [x]))
  : forall xs, P xs.
Proof.
  intros xs'. rewrite <- rev_involutive with (l := xs').
  generalize (rev xs') as xs. clear xs'.
  induction xs as [ | x xs IH]; simpl.
  - exact NIL.
  - eapply TAIL. exact IH.
Qed.

Lemma last_cons {A : Type} (x0 : A) (x1 : A) (xs : list A)
  : last (x0 :: xs) x1 = last xs x0.
Proof.
  symmetry. revert x0 x1. induction xs as [ | x xs IH]; simpl; i.
  - reflexivity.
  - destruct xs as [ | x' xs'].
    + reflexivity.
    + erewrite IH with (x1 := x1). reflexivity.
Qed.

Fixpoint mk_edge_seq {V : Type} (v : V) (vs : list V) : list (V * V) :=
  match vs with
  | [] => []
  | v' :: vs' => (v, v') :: mk_edge_seq v' vs'
  end.

Lemma mk_edge_seq_last {V : Type} (v0 : V) (v' : V) (vs : list V)
  : mk_edge_seq v0 (vs ++ [v']) = mk_edge_seq v0 vs ++ [(last vs v0, v')].
Proof.
  revert v0 v'. induction vs as [ | v vs IH]; i.
  - simpl. reflexivity.
  - erewrite -> last_cons. simpl. f_equal. eauto.
Qed.

Lemma in_mk_edge_seq_inv {V : Type} (v0 : V) (v1 : V) (vs : list V)
  (IN : In (v0, v1) (mk_edge_seq v1 vs))
  : In v1 vs.
Proof.
  revert v0 v1 IN. induction vs as [ | v vs IH] using List.rev_ind; simpl; i.
  - exact IN.
  - rewrite in_app_iff. rewrite mk_edge_seq_last in IN.
    rewrite in_app_iff in IN. destruct IN as [IN | [EQ | []]].
    + left. eapply IH; exact IN.
    + inv EQ. right. repeat constructor.
Qed.

Lemma no_dup_mk_edge_seq {V : Type} (v : V) (vs : list V)
  (NO_DUP : NoDup vs)
  : NoDup (mk_edge_seq v vs).
Proof.
  revert v. induction NO_DUP as [ | v vs NOT_IN NO_DUP IH].
  - econstructor 1.
  - simpl. econstructor 2.
    + intros CONTRA. apply in_mk_edge_seq_inv in CONTRA. contradiction.
    + eapply IH.
Qed.

End L.
