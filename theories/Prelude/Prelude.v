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

Module Basic.

Include Coq.Init.Datatypes.
Include Coq.Program.Basics.

Definition Some_dec {A : Type} (x : option A)
  : { x' : A | x = Some x' } + { x = None }.
Proof.
  destruct x as [x' | ].
  - left. exists x'. reflexivity.
  - right. reflexivity.
Defined.

End Basic.

#[universes(polymorphic)]
Class cat@{u v} : Type :=
  { ob : Type@{u}
  ; hom (dom : ob) (cod : ob) : Type@{v}
  ; compose {A : ob} {B : ob} {C : ob} (g : hom B C) (f : hom A B) : hom A C
  ; id {A : ob} : hom A A
  }.

#[global] Coercion ob : cat >-> Sortclass.
#[global] Coercion hom : cat >-> Funclass.

Section CATEGORY.

Universe u_Hask.

#[local]
Instance Hask : cat :=
  { ob := Type@{u_Hask}
  ; hom A B := A -> B
  ; compose {A} {B} {C} (g : B -> C) (f : A -> B) := fun x : A => g (f x)
  ; id {A} := fun x : A => x
  }.

End CATEGORY.

Section EQ_DEC.

Class hasEqDec (A : Type) : Type :=
  eq_dec : forall x : A, forall y : A, {x = y} + {x <> y}.

#[global]
Instance Some_hasEqDec {A : Type} `(EQ_DEC : hasEqDec A) : hasEqDec (option A) :=
  { eq_dec := ltac:(red in EQ_DEC; decide equality) }.

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
  destruct (Basic.Some_dec (decode n)) as [[y SOME] | NONE].
  - destruct (P_dec y) as [EQ | NE].
    + exact y.
    + exact (search_go P P_dec (S n) (Acc_inv acc (search_step_Some P n y NE SOME))).
  - exact (search_go P P_dec (S n) (Acc_inv acc (search_step_None P n NONE))).
Defined.

Fixpoint search_go_spec (P : A -> Prop) (P_dec : forall x, {P x} + {~ P x}) (n : nat) (acc : Acc (flip (search_step P)) n) {struct acc}
  : P (search_go P P_dec n acc).
Proof.
  destruct acc; simpl. destruct (Basic.Some_dec (decode n)) as [[? ?] | ?] eqn: ?.
  - destruct (P_dec x).
    + assumption.
    + eapply search_go_spec.
  - eapply search_go_spec.
Qed.

Lemma search_go_pirrel (P : A -> Prop) (P_dec : forall x, {P x} + {~ P x}) (n : nat) (acc : Acc (flip (search_step P)) n) (acc' : Acc (flip (search_step P)) n)
  : search_go P P_dec n acc = search_go P P_dec n acc'.
Proof.
  revert acc acc acc'. intros acc''. induction acc'' as [? _ IH]; intros [?] [?]. simpl.
  destruct (Basic.Some_dec (decode x)) as [[? ?] | ?] eqn: ?.
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
  { eapply search_go_spec with (P := fun y : A => encode y = encode x) (P_dec := fun y : A => Nat.eq_dec (encode y) (encode x)). }
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
Definition mkSetoid_fromPreOrder {A : Type} (leProp : A -> A -> Prop) `(leProp_PreOrder : @PreOrder A leProp) : isSetoid A :=
  {| eqProp (x : A) (y : A) := leProp x y /\ leProp y x |}.
Next Obligation.
  split; ii.
  - exact (conj (@PreOrder_Reflexive A leProp leProp_PreOrder x) (@PreOrder_Reflexive A leProp leProp_PreOrder x)).
  - exact (conj (proj2 H) (proj1 H)).
  - exact (conj (@PreOrder_Transitive A leProp leProp_PreOrder x y z (proj1 H) (proj1 H0)) (@PreOrder_Transitive A leProp leProp_PreOrder z y x (proj2 H0) (proj2 H))).
Defined.

Definition mkSetoid_fromPreOrder_hasPartialOrder {A : Type} (leProp : A -> A -> Prop) `(leProp_PreOrder : @PreOrder A leProp)
  : @PartialOrder A (mkSetoid_fromPreOrder leProp leProp_PreOrder).(eqProp) (mkSetoid_fromPreOrder leProp leProp_PreOrder).(eqProp_Equivalence) leProp leProp_PreOrder.
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

#[local]
Instance trivialSetoid {A : Type} : isSetoid A :=
  { eqProp (x : A) (y : A) := x = y
  ; eqProp_Equivalence := @eq_equivalence A
  }.

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
  intros f g. split.
  - intros f_eq_g.
    assert (claim : forall x : A, f x =< g x /\ g x =< f x).
    { intros x. eapply leProp_PartialOrder. exact (f_eq_g x). }
    exact (conj (fun x => proj1 (claim x)) (fun x => proj2 (claim x))).
  - intros [f_le_g g_le_f] x. eapply leProp_PartialOrder. exact (conj (f_le_g x) (g_le_f x)).
Defined.

#[global]
Instance Prop_isPoset : isPoset Prop :=
  let impl_PreOrder : PreOrder Basic.impl := {| PreOrder_Reflexive (A : Prop) := Basic.id (A := A); PreOrder_Transitive (A : Prop) (B : Prop) (C : Prop) := Basic.flip (Basic.compose (A := A) (B := B) (C := C)); |} in
  {|
    Poset_isSetoid := mkSetoid_fromPreOrder Basic.impl impl_PreOrder;
    leProp := Basic.impl;
    leProp_PreOrder := impl_PreOrder;
    leProp_PartialOrder := mkSetoid_fromPreOrder_hasPartialOrder impl impl_PreOrder;
  |}.

End POSET.

Infix "=<" := leProp : type_scope.

Section ENSEMBLE.

#[universes(polymorphic)]
Definition ensemble@{u} {A : Type@{u}} : Type@{u} :=
  A -> Prop.

End ENSEMBLE.
