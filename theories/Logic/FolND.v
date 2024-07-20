Require Import LoL.Prelude.Prelude.
Require Import LoL.Prelude.Notations.
Require Import LoL.Math.ThN.
Require Import LoL.Data.Vector.
Require Import LoL.Logic.FolSyntax.
Require Import LoL.Logic.FolSemantics.
Require Import LoL.Logic.FolHPS.

#[local] Infix "\in" := E.elem.
#[local] Infix "\subseteq" := E.isSubsetOf.

#[local] Infix "≡" := alpha_equiv.
#[local] Infix "\proves" := proves.

Import ListNotations.

#[local] Notation "p `[ x' := t' ]" := (subst1 x' t' p) (at level 15, no associativity, format "p `[  x'  :=  t'  ]").

Section NATURAL_DEDUCTION.

Context {L : language}.

Inductive infers (Gamma : list (frm L)) : forall C : frm L, Prop :=
  | By_hyp p
    (IN : L.In p Gamma)
    : Gamma ⊢ p
  | Eqn_I t1
    : Gamma ⊢ Eqn_frm t1 t1
  | Eqn_E x t1 t2 p1
    (INFERS1 : Gamma ⊢ Eqn_frm t1 t2)
    (INFERS2 : Gamma ⊢ subst_frm (one_subst x t1) p1)
    : Gamma ⊢ subst_frm (one_subst x t2) p1
  | All_I x y p
    (NOT_FREE1 : forall p, L.In p Gamma -> is_not_free_in_frm y p)
    (NOT_FREE2 : is_not_free_in_frm y (All_frm x p))
    (INFERS1 : Gamma ⊢ subst_frm (one_subst x (Var_trm y)) p)
    : Gamma ⊢ All_frm x p
  | All_E x t p
    (INFERS1 : Gamma ⊢ All_frm x p)
    : Gamma ⊢ subst_frm (one_subst x t) p
  | Neg_I p1 p2
    (INFERS1 : p1 :: Gamma ⊢ p2)
    (INFERS2 : p1 :: Gamma ⊢ Neg_frm p2)
    : Gamma ⊢ Neg_frm p1
  | Neg_E p1 p2
    (INFERS1 : Gamma ⊢ p1)
    (INFERS2 : Gamma ⊢ Neg_frm p1)
    : Gamma ⊢ p2
  | Imp_I p1 p2
    (INFERS1 : p1 :: Gamma ⊢ p2)
    : Gamma ⊢ Imp_frm p1 p2
  | Imp_E p1 p2
    (INFERS1 : Gamma ⊢ Imp_frm p1 p2)
    (INFERS2 : Gamma ⊢ p1)
    : Gamma ⊢ p2
  where " Gamma ⊢ C " := (infers Gamma C) : type_scope.

Section BASIC_PROPERTIES.

#[local]
Add Parametric Morphism
  : infers with signature (L.ext_eq_as_finset ==> eq ==> iff)
  as infers_congruence_on_Gamma.
Proof.
  assert (claim1 : forall ps1, forall ps2, L.ext_eq_as_finset ps1 ps2 -> forall p, ps1 ⊢ p -> ps2 ⊢ p).
  { intros ps1 ps2 EXT_EQ p INFERS. revert ps2 EXT_EQ. induction INFERS; i.
    - eapply By_hyp. rewrite <- EXT_EQ. exact IN.
    - eapply Eqn_I.
    - eapply Eqn_E with (x := x) (t1 := t1); done.
    - eapply All_I with (y := y); done.
    - eapply All_E; done.
    - eapply Neg_I with (p2 := p2); done.
    - eapply Neg_E with (p1 := p1); done.
    - eapply Imp_I with (p1 := p1); done.
    - eapply Imp_E with (p1 := p1); done.
  }
  now split; eapply claim1.
Qed.

(* Fixpoint generalized_weakening ps p (INFERS : ps ⊢ p) {struct INFERS}
  : forall eta, (exists eta' : renaming, forall z, rename_var eta' (rename_var eta z) = z) -> forall ps', (forall q, L.In q ps -> L.In q ps') -> L.map (rename_frm eta) ps' ⊢ rename_frm eta p.
Proof.
  destruct INFERS; simpl; intros eta eta_inj ps' SUBSET.
  - eapply By_hyp. eapply L.in_map_iff. done.
  - eapply Eqn_I.
  - rewrite -> rename_frm_one_subst. 2: now eapply eta_inj_upgrade_once. eapply Eqn_E with (t1 := rename_trm eta t1).
    + eapply generalized_weakening with (p := Eqn_frm t1 t2). exact INFERS1. trivial. trivial.
    + rewrite <- rename_frm_one_subst. 2: now eapply eta_inj_upgrade_once. eapply generalized_weakening. exact INFERS2. trivial. trivial.
  - eapply All_I with (y := ?[z]).
    + intros q q_in. rewrite L.in_map_iff in q_in. destruct q_in as (q'&<-&H_in).
      admit.
    + admit.
    + admit.
  - rewrite -> rename_frm_one_subst. 2: now eapply eta_inj_upgrade_once. eapply All_E.

  - eapply Neg_I with (p2 := ?[p2]).
    + change (L.map (rename_frm eta) (p1 :: ps') ⊢ ?p2). eapply generalized_weakening. exact INFERS1. trivial.
      intros q q_in. simpl in *. destruct q_in as [<- | q_in]; [left | right]; done.
    + change (L.map (rename_frm eta) (p1 :: ps') ⊢ rename_frm eta (Neg_frm p2)). eapply generalized_weakening. exact INFERS2. trivial.
      intros q q_in. simpl in *. destruct q_in as [<- | q_in]; [left | right]; done.
  - eapply Neg_E with (p1 := ?[p1]).
    + eapply generalized_weakening. eapply INFERS1. trivial. trivial.
    + change (L.map (rename_frm eta) ps' ⊢ rename_frm eta (Neg_frm p1)). eapply generalized_weakening. exact INFERS2. trivial. trivial.
  - eapply Imp_I. change (L.map (rename_frm eta) (p1 :: ps') ⊢ rename_frm eta p2). eapply generalized_weakening. exact INFERS. trivial.
    intros q q_in. simpl in *. destruct q_in as [<- | q_in]; [left | right]; done.
  - eapply Imp_E with (p1 := rename_frm eta p1).
    + change (L.map (rename_frm eta) ps' ⊢ rename_frm eta (Imp_frm p1 p2)). eapply generalized_weakening. exact INFERS1. trivial. trivial.
    + eapply generalized_weakening. exact INFERS2. trivial. trivial.
Abort.

(* Fixpoint weakening ps p (INFERS : ps ⊢ p) {struct INFERS}
  : forall ps', (forall q, L.In q ps -> L.In q ps') -> ps' ⊢ p.
Proof.
  destruct INFERS; intros ps' SUBSET.
  - eapply By_hyp. eapply SUBSET. exact IN.
  - eapply Eqn_I.
  - eapply Eqn_E with (t1 := t1).
    + eapply weakening. exact INFERS1. exact SUBSET.
    + eapply weakening. exact INFERS2. exact SUBSET.
  - eapply All_I with (y := y).
Abort. *) *)

Theorem extend_infers ps ps' p
  (SUBSET : forall q, L.In q ps -> L.In q ps')
  (INFERS : ps ⊢ p)
  : ps' ⊢ p.
Proof.
Admitted.

Lemma CP1 ps p q
  (INFERS : ps ⊢ Imp_frm p q)
  : ps ⊢ Imp_frm (Neg_frm q) (Neg_frm p).
Proof.
  eapply Imp_I. eapply Neg_I with (p2 := q). eapply Imp_E. eapply extend_infers. intros p' H_in. right. right. exact H_in.
  exact INFERS. eapply By_hyp. left. reflexivity. eapply By_hyp. right. left. reflexivity.
Qed.

#[global]
Add Parametric Morphism
  : infers with signature (L.ext_eq_as_finset ==> alpha_equiv ==> iff)
  as infers_congruence.
Proof.
  intros ps1 ps2 EXT_EQ p p' ALPHA. rewrite EXT_EQ. clear ps1 EXT_EQ. rename ps2 into ps.
  enough (WTS : [] ⊢ Imp_frm p p' /\ [] ⊢ Imp_frm p' p).
  { destruct WTS as [INFERS1 INFERS2]. split; intros INFERS.
    - eapply Imp_E. eapply extend_infers with (ps := []). done. exact INFERS1. exact INFERS.
    - eapply Imp_E. eapply extend_infers with (ps := []). done. exact INFERS2. exact INFERS.
  }
  clear ps. induction ALPHA; i.
  - rewrite EQ. split.
    + eapply Imp_I. eapply By_hyp. left. reflexivity.
    + eapply Imp_I. eapply By_hyp. left. reflexivity.
  - rewrite EQ1, EQ2. split.
    + eapply Imp_I. eapply By_hyp. left. reflexivity.
    + eapply Imp_I. eapply By_hyp. left. reflexivity.
  - destruct IHALPHA as [INFERS INFERS']. split.
    + eapply CP1. exact INFERS'.
    + eapply CP1. exact INFERS.
  - destruct IHALPHA1 as [INFERS1 INFERS1'], IHALPHA2 as [INFERS2 INFERS2']. split.
    + eapply Imp_I. eapply Imp_I. eapply Imp_E. eapply extend_infers with (ps := []). intros q []. exact INFERS2.
      eapply Imp_E. eapply By_hyp. right. left. reflexivity. eapply Imp_E. eapply extend_infers with (ps := []). intros q []. eapply INFERS1'. eapply By_hyp. left. reflexivity.
    + eapply Imp_I. eapply Imp_I. eapply Imp_E. eapply extend_infers with (ps := []). intros q []. exact INFERS2'.
      eapply Imp_E. eapply By_hyp. right. left. reflexivity. eapply Imp_E. eapply extend_infers with (ps := []). intros q []. eapply INFERS1. eapply By_hyp. left. reflexivity.
  - destruct IHALPHA as [INFERS INFERS']. split.
    + eapply Imp_I. eapply All_I with (y := z); trivial. simpl. intros q [<- | []]; trivial.
      eapply Imp_E. eapply extend_infers with (ps := []). intros q []. exact INFERS. eapply All_E. eapply By_hyp. left. reflexivity.
    + eapply Imp_I. eapply All_I with (y := z); trivial. simpl. intros q [<- | []]; trivial.
      eapply Imp_E. eapply extend_infers with (ps := []). intros q []. exact INFERS'. eapply All_E. eapply By_hyp. left. reflexivity.
Qed.

End BASIC_PROPERTIES.

Theorem infers_iff_proves ps p
  : ps ⊢ p <-> E.finite ps \proves p.
Proof.
Abort.

End NATURAL_DEDUCTION.
