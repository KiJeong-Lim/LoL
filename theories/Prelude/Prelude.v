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
Require Export LoL.Prelude.SfLib.

Notation " '⟪' x ':' t '⟫' " := (NW (fun x : unit => match x with tt => t end)) (x name, t at level 200, at level 0, no associativity) : type_scope.

Reserved Infix "==" (no associativity, at level 70).
Reserved Infix "=<" (no associativity, at level 70).
Reserved Infix "\in" (no associativity, at level 70).
Reserved Infix "\subseteq" (no associativity, at level 70).

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
Record pair (A : Type) (B : Type) : Type :=
  { fst : A; snd : B }.

#[global] Arguments fst {A} {B} _.
#[global] Arguments snd {A} {B} _.

Inductive sum1 (F : Type -> Type) (G : Type -> Type) (X : Type) : Type :=
  | inl1 (FX : F X) : sum1 F G X
  | inr1 (GX : G X) : sum1 F G X.

#[global] Arguments inl1 {F}%type_scope {G}%type_scope {X}%type_scope FX.
#[global] Arguments inr1 {F}%type_scope {G}%type_scope {X}%type_scope GX.

Definition maybe {A : Type} {B : Type} (d : B) (f : A -> B) (m : option A) : B :=
  match m with
  | None => d
  | Some x => f x
  end.

Lemma Some_ne_None {A : Type} (x : A)
  : Some x <> None.
Proof.
  assert (TRUE : option_rect (fun _ : option A => Prop) (fun _ : A => True) (False) (Some x)) by exact I.
  intros EQ. rewrite EQ in TRUE. exact TRUE.
Defined.

Class isFunctor (F : Type -> Type) : Type :=
  fmap (A : Type) (B : Type) (f : A -> B) : F A -> F B.

Class isMonad (M : Type -> Type) : Type :=
  { pure {A : Type} (x : A) : M A
  ; bind {A : Type} {B : Type} (m : M A) (k : A -> M B) : M B
  }.

Definition mkFunctorFromMonad {M : Type -> Type} `(MONAD : isMonad M) : isFunctor M :=
  fun A : Type => fun B : Type => fun f : A -> B => fun m : M A => MONAD.(bind) m (fun x : A => MONAD.(pure) (f x)).

Definition liftM2 {M : Type -> Type} {A : Type} {B : Type} {C : Type} `{MONAD : isMonad M} (f : A -> B -> C) (mx : M A) (my : M B) : M C :=
  bind mx (fun x : A => bind my (fun y : B => pure (f x y))).

End B.

Infix "×" := B.pair (at level 40, left associativity) : type_scope.
Infix "+'" := B.sum1 (at level 50, left associativity) : type_scope.
Notation isFunctor := B.isFunctor.
Notation fmap := (B.fmap _ _).
Notation isMonad := B.isMonad.
Notation pure := B.pure.
Notation bind := B.bind.

Section EQ_DEC.

Class hasEqDec (A : Type) : Type :=
  eq_dec (x : A) (y : A) : {x = y} + {x <> y}.

#[global]
Instance Some_hasEqDec {A : Type}
  `(EQ_DEC : hasEqDec A)
  : hasEqDec (option A).
Proof.
  exact (fun x : option A => fun y : option A =>
    match x, y with
    | None, None => left eq_refl
    | None, Some y' => right (fun EQ : None = Some y' => B.Some_ne_None y' (eq_equivalence.(Equivalence_Symmetric) None (Some y') EQ))
    | Some x', None => right (fun EQ : Some x' = None => B.Some_ne_None x' EQ)
    | Some x', Some y' =>
      match EQ_DEC x' y' with
      | left EQ => left (f_equal (@Some A) EQ)
      | right NE => right (fun EQ : Some x' = Some y' => NE (f_equal (B.maybe x' B.id) EQ))
      end
    end
  ).
Defined.

End EQ_DEC.

Section COUNTABLE. (* Reference: "https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.countable.html" *)

Class isCountable (A : Type) : Type :=
  { encode : A -> nat
  ; decode : nat -> option A
  ; decode_encode
    : forall x : A, decode (encode x) = Some x 
  }.

Section SEARCH. (* Reference: "https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.countable.html#choice" *)

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
Qed.

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
Qed.

End SEARCH.

End COUNTABLE.

Section ENUMERABLE.

Class isEnumerable (A : Type) : Type :=
  { enum : nat -> A
  ; enumerable : forall x : A, { n : nat | enum n = x }
  }.

#[global]
Instance isCountable_if_isEnumerable {A : Type} `(ENUMERABLE : isEnumerable A) : isCountable A :=
  { encode (x : A) := proj1_sig (enumerable x)
  ; decode (n : nat) := Some (enum n)
  ; decode_encode (x : A) := f_equal (@Some A) (proj2_sig (enumerable x))
  }.

End ENUMERABLE.

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

Class isSetoid1 (F : Type -> Type) : Type :=
  mkSetoid1 (X : Type) `(SETOID : isSetoid X) :: isSetoid (F X).

Definition trivialSetoid {A : Type} : isSetoid A :=
  {| eqProp := @eq A; eqProp_Equivalence := @eq_equivalence A; |}.

#[local]
Instance fromSetoid1 {F : Type -> Type} {X : Type} `(SETOID1 : isSetoid1 F) : isSetoid (F X) :=
  mkSetoid1 X trivialSetoid.

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
Definition In@{u} {A : Type@{u}} (x : A) (X : E.t@{u} A) := X x.

#[local] Infix "\in" := E.In : type_scope.

#[universes(polymorphic=yes)]
Definition subseteq@{u} {A : Type@{u}} (X1 : E.t@{u} A) (X2 : E.t@{u} A) : Prop :=
  forall x : A, @E.In@{u} A x X1 -> @E.In@{u} A x X2.

#[local] Infix "\subseteq" := E.subseteq : type_scope.

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
  : forall z : A, z \in difference X1 X2 <-> z \in X1 /\ ~ z \in X2.
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
