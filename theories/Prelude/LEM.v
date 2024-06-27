Require Import LoL.Prelude.Prelude.
Require Import LoL.Prelude.Notations.

Module __LEM. (* Reference: "https://coq.inria.fr/doc/v8.18/stdlib/Coq.Logic.Classical_Prop.html" *)

Axiom axiom : forall P : Prop, P \/ ~ P.

Lemma NNPP (P: Prop)
  (H_NNP : ~ ~ P)
  : P.
Proof.
  pose proof (axiom P) as [H_P | H_NP].
  - exact H_P.
  - contradiction (H_NNP H_NP).
Defined.

Section PROOF_IRRELEVANCE.

Import RETRACT.

Record RETRACT2 (X : Prop) (A : Prop) : Prop :=
  { retraction2 : X -> A
  ; incl2 : A -> X
  ; id2 : RETRACT.t X A -> forall x, incl2 (retraction2 x) = x
  }.

#[local] Arguments retraction2 {X} {A}.
#[local] Arguments incl2 {X} {A}.
#[local] Arguments id2 {X} {A}.

Inductive BB : Prop :=
  | trueBB : BB
  | falseBB : BB.

Let POW (P : Prop) : Prop := P -> BB.

Lemma RETRACT2_POW_POW_INTRO (A : Prop) (B : Prop)
  : RETRACT2 (POW A) (POW B).
Proof.
  pose proof (axiom (RETRACT.t (POW A) (POW B))) as [YES | NO].
  - exists YES.(retraction) YES.(incl). ii. eapply YES.(id).
  - exists (fun _ : POW A => fun _ : B => falseBB) (fun _ : POW B => fun _ : A => falseBB).
    ii. contradiction.
Qed.

Let UNIV : Prop := forall P : Prop, POW P.

Definition BUILD (phi : UNIV -> BB) : UNIV :=
  fun P : Prop =>
  let INCL : POW UNIV -> POW P := (RETRACT2_POW_POW_INTRO P UNIV).(incl2) in
  let RETRACTION : POW UNIV -> POW UNIV := (RETRACT2_POW_POW_INTRO UNIV UNIV).(retraction2) in
  INCL (RETRACTION phi).

#[local] Notation "{ x | phi }" := (BUILD (fun x : UNIV => phi)).

Definition CONTAIN (x : UNIV) (z : UNIV) : BB :=
  x UNIV z.

#[local] Notation "z ∈ x" := (CONTAIN x z).

#[program]
Definition BUILD_SPEC : RETRACT.t (POW UNIV) UNIV :=
  {| retraction := BUILD; incl := CONTAIN; id := _ |}.
Next Obligation.
  i. unfold CONTAIN. unfold BUILD.
  destruct (RETRACT2_POW_POW_INTRO UNIV UNIV) as [RETRACTION INCL ID].
  cbn in *. eapply ID. eapply RETRACT_REFL.
Qed.

Corollary EXT_EQ (phi : UNIV -> BB)
  : forall t, (t ∈ { x | phi x }) = phi t.
Proof.
  assert (ID : CONTAIN (BUILD phi) = phi) by exact (BUILD_SPEC.(id) phi).
  exact (fun t : UNIV => @f_equal (POW UNIV) BB (fun phi : POW UNIV => phi t) (CONTAIN (BUILD phi)) phi ID).
Qed.

Let NOT (b : BB) : BB :=
  if axiom (b = trueBB) then falseBB else trueBB.

Lemma NOT_trueBB_EQ_falseBB (b : BB)
  (b_EQ_trueBB : b = trueBB)
  : NOT b = falseBB.
Proof.
  cbv. destruct (axiom (b = trueBB)); tauto.
Qed.

Lemma NOT_falseBB_EQ_trueBB (b: BB)
  (b_NE_trueBB : b <> trueBB)
  : NOT b = trueBB.
Proof.
  cbv. destruct (axiom (b = trueBB)); tauto.
Qed.

Let R : UNIV :=
  { r | NOT (r ∈ r) }.

Let RUSSEL : BB :=
  R ∈ R.

Theorem PARADOX_OF_BERARDI
  : RUSSEL = NOT RUSSEL.
Proof.
  change ((R ∈ { r | NOT (r ∈ r) }) = NOT (R ∈ R)).
  eapply EXT_EQ with (phi := fun r : UNIV => NOT (r ∈ r)).
Qed.

Corollary PROOF_IRRELEVANCE (* References: "https://coq.inria.fr/doc/v8.18/stdlib/Coq.Logic.Classical_Prop.html#proof_irrelevance" *)
  : forall P : Prop, forall p1 : P, forall p2 : P, p1 = p2.
Proof.
  assert (trueBB_EQ_falseBB: trueBB = falseBB).
  { pose proof (axiom (RUSSEL = trueBB)) as [b_EQ_trueBB | b_NE_trueBB].
    - rewrite <- b_EQ_trueBB. rewrite -> PARADOX_OF_BERARDI. now eapply NOT_trueBB_EQ_falseBB.
    - contradiction b_NE_trueBB. rewrite -> PARADOX_OF_BERARDI. now eapply NOT_falseBB_EQ_trueBB.
  }
  i. exact (@f_equal BB P (fun b => if b then p1 else p2) trueBB falseBB trueBB_EQ_falseBB).
Qed.

End PROOF_IRRELEVANCE.

Lemma projT2_eq (A : Type) (x : A) (B : A -> Type) (y1 : B x) (y2 : B x)
  (EQ : @existT A B x y1 = @existT A B x y2)
  : y1 = y2.
Proof.
  revert EQ. eapply B.projT2_eq. clear y1 y2. i.
  rewrite PROOF_IRRELEVANCE with (P := x = x) (p1 := EQ) (p2 := eq_refl).
  reflexivity.
Qed.

End __LEM.

Notation exclusive_middle := __LEM.axiom.
Notation proof_irrelevance := __LEM.PROOF_IRRELEVANCE.
Notation nnpp := __LEM.NNPP.
Tactic Notation "projT2_eq" "in" ident( H ) := apply __LEM.projT2_eq in H.
