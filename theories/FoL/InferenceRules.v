Require Import LoL.Prelude.Prelude.
Require Import LoL.Prelude.Notations.
Require Import LoL.Math.ThN.
Require Import LoL.Data.Vector.
Require Import LoL.FoL.Syntax.
Require Import LoL.FoL.Semantics.

#[local] Infix "\in" := E.elem.
#[local] Infix "\subseteq" := E.isSubsetOf.

#[local] Infix "≡" := alpha_equiv.

Module HPS.

Reserved Infix "\proves" (at level 70, no associativity).

Section HILBERT_PROOF_SYSTEM.

Import ListNotations.

Context {L : language}.

Definition varcouples : forall n : nat, trms L n * trms L n :=
  nat_rec (fun n => (trms L n * trms L n)%type) (O_trms, O_trms) (fun n => prod_rec _ (fun lhs => fun rhs => (S_trms n (Var_trm (n + n)) lhs, S_trms n (Var_trm (S (n + n))) rhs))).

Definition eqns_imp p : nat -> frm L :=
  nat_rec _ p (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q).

Definition Fun_eqAxm (f : L.(function_symbols)) : frm L :=
  eqns_imp (prod_rec (fun _ => frm L) (fun lhs => fun rhs => Eqn_frm (Fun_trm f lhs) (Fun_trm f rhs)) (varcouples (L.(function_arity_table) f))) (L.(function_arity_table) f).

Definition Rel_eqAxm (R : L.(relation_symbols)) : frm L :=
  eqns_imp (prod_rec (fun _ => frm L) (fun lhs => fun rhs => Imp_frm (Rel_frm R lhs) (Rel_frm R rhs)) (varcouples (L.(relation_arity_table) R))) (L.(relation_arity_table) R).

Inductive proof : list (frm L) -> frm L -> Set := (* Reference: "https://github.com/princeton-vl/CoqGym/blob/master/coq_projects/goedel/folProof.v#L68" *)
  | AXM p
    : proof [p] p
  | MP ps1 ps2 p q
    (PF1 : proof ps1 (Imp_frm p q))
    (PF2 : proof ps2 p)
    : proof (ps1 ++ ps2) q
  | GEN ps q x
    (NOT_FREE : forall p, In p ps -> is_not_free_in_frm x p)
    (PF : proof ps q)
    : proof ps (All_frm x q)
  | IMP1 p q
    : proof [] (Imp_frm p (Imp_frm q p))
  | IMP2 p q r
    : proof [] (Imp_frm (Imp_frm p (Imp_frm q r)) (Imp_frm (Imp_frm p q) (Imp_frm p r)))
  | CP p q
    : proof [] (Imp_frm (Imp_frm (Neg_frm q) (Neg_frm p)) (Imp_frm p q))
  | FA1 p x t
    : proof [] (Imp_frm (All_frm x p) (subst_frm (one_subst x t) p))
  | FA2 p x
    (NOT_FREE : is_not_free_in_frm x p)
    : proof [] (Imp_frm p (All_frm x p))
  | FA3 p q x
    : proof [] (Imp_frm (All_frm x (Imp_frm p q)) (Imp_frm (All_frm x p) (All_frm x q)))
  | EQN_REFL
    : proof [] (Eqn_frm (Var_trm 0) (Var_trm 0))
  | EQN_SYM
    : proof [] (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Eqn_frm (Var_trm 1) (Var_trm 0)))
  | EQN_TRANS
    : proof [] (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Imp_frm (Eqn_frm (Var_trm 1) (Var_trm 2)) (Eqn_frm (Var_trm 0) (Var_trm 2))))
  | EQN_FUN f
    : proof [] (Fun_eqAxm f)
  | EQN_REL R
    : proof [] (Rel_eqAxm R).

Definition proves (Gamma : ensemble (frm L)) (C : frm L) : Prop :=
  exists ps, E.finite ps \subseteq Gamma /\ inhabited (proof ps C).

#[local] Infix "\proves" := proves : type_scope.

Lemma proof_compose p q r
  : proof [] (Imp_frm (Imp_frm q r) (Imp_frm (Imp_frm p q) (Imp_frm p r))).
Proof.
  assert (PF1 : proof [] (Imp_frm (Imp_frm q r) (Imp_frm p (Imp_frm q r)))) by eapply IMP1.
  assert (PF2 : proof [] (Imp_frm (Imp_frm p (Imp_frm q r)) (Imp_frm (Imp_frm p q) (Imp_frm p r)))) by eapply IMP2.
  set (p2 := (Imp_frm (Imp_frm p (Imp_frm q r)) (Imp_frm (Imp_frm p q) (Imp_frm p r)))) in *.
  assert (PF3 : proof [] (Imp_frm p2 (Imp_frm (Imp_frm q r) p2))) by eapply IMP1.
  assert (PF4 : proof ([] ++ []) (Imp_frm (Imp_frm q r) p2)) by now eapply MP; [exact PF3 | exact PF2].
  simpl in PF4. set (p4 := Imp_frm (Imp_frm q r) p2) in *. set (p1 := Imp_frm (Imp_frm q r) (Imp_frm p (Imp_frm q r))) in *.
  assert (PF5 : proof [] (Imp_frm p4 (Imp_frm p1 (Imp_frm (Imp_frm q r) (Imp_frm (Imp_frm p q) (Imp_frm p r)))))) by eapply IMP2.
  assert (PF6 : proof ([] ++ []) (Imp_frm p1 (Imp_frm (Imp_frm q r) (Imp_frm (Imp_frm p q) (Imp_frm p r))))) by now eapply MP; [eapply PF5 | eapply PF4].
  eapply MP with (ps1 := [] ++ []) (ps2 := []); [exact PF6 | exact PF1].
Qed.

Lemma proof_id p
  : proof [] (Imp_frm p p).
Proof.
  pose proof (PF1 := @IMP1 p p).
  pose proof (PF2 := @IMP1 p (Imp_frm p p)).
  pose proof (PF3 := @IMP2 p (Imp_frm p p) p).
  pose proof (PF4 := @MP _ _ _ _ PF3 PF2).
  pose proof (PF5 := @MP _ _ _ _ PF4 PF1).
  exact PF5.
Qed.

Lemma syllogism p q r
  : proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Imp_frm q r) (Imp_frm p r))).
Proof.
  pose proof (proof_compose p q r) as PF7. set (p7 := (Imp_frm (Imp_frm q r) (Imp_frm (Imp_frm p q) (Imp_frm p r)))) in *.
  pose proof (PF8 := IMP2 (Imp_frm q r) (Imp_frm p q) (Imp_frm p r)). fold p7 in PF8.
  pose proof (PF9 := MP _ _ _ _ PF8 PF7). simpl in PF9. set (p9 := Imp_frm (Imp_frm (Imp_frm q r) (Imp_frm p q)) (Imp_frm (Imp_frm q r) (Imp_frm p r))) in *.
  pose proof (PF10 := IMP1 (Imp_frm p q) (Imp_frm q r)).
  pose proof (PF11 := IMP1 p9 (Imp_frm p q)).
  pose proof (PF12 := MP _ _ _ _ PF11 PF9). simpl in PF12.
  rewrite <- app_nil_l with (l := @nil (frm L)). eapply MP. 2: exact PF10.
  rewrite <- app_nil_l with (l := @nil (frm L)). eapply MP. 2: exact PF12.
  eapply IMP2.
Qed.

Lemma proof_flip p q r
  : proof [] (Imp_frm (Imp_frm q (Imp_frm p r)) (Imp_frm p (Imp_frm q r))).
Proof.
  pose proof (@syllogism) as PF1. specialize PF1 with (p := p) (q := Imp_frm q p) (r := Imp_frm q r).
  assert (PF2: proof [] (Imp_frm p (Imp_frm q p))) by eapply IMP1.
  pose proof (PF3 := MP _ _ _ _ PF1 PF2). simpl in PF3.
  1: rewrite <- app_nil_l with (l := @nil (frm L)); eapply MP.
  1: rewrite <- app_nil_l with (l := @nil (frm L)); eapply MP.
  1: eapply syllogism.
  2: eapply PF3.
  eapply IMP2.
Qed.

Lemma proof_rebind_All_frm (x : ivar) (z : ivar) (p : frm L)
  (FRESH : is_not_free_in_frm z (All_frm x p))
  : proof [] (Imp_frm (All_frm x p) (All_frm z (subst_frm (one_subst x (Var_trm z)) p))).
Proof.
  pose proof (@syllogism (All_frm x p) (All_frm z (All_frm x p)) (All_frm z (subst_frm (one_subst x (Var_trm z)) p))) as PF1.
  pose proof (@FA2 (All_frm x p) z FRESH) as PF2.
  pose proof (@MP _ _ _ _ PF1 PF2) as PF3. rewrite app_nil_r in PF3.
  rewrite <- app_nil_l with (l := @nil (frm L)). eapply MP. 1: exact PF3.
  pose proof (@FA3 (All_frm x p) (subst_frm (one_subst x (Var_trm z)) p) z) as PF4.
  rewrite <- app_nil_l with (l := @nil (frm L)). eapply MP. 1: exact PF4.
  eapply GEN. 1: intros ? []. eapply FA1.
Qed.

Lemma proof_ex_falso (p : frm L) (q : frm L)
  : proof [] (Imp_frm (Neg_frm p) (Imp_frm p q)).
Proof.
  pose proof (CP p q) as PF1.
  rewrite <- app_nil_l with (l := []). eapply MP with (p := Imp_frm (Neg_frm p) (Imp_frm (Neg_frm q) (Neg_frm p))). 2: exact (IMP1 (Neg_frm p) (Neg_frm q)).
  rewrite <- app_nil_l with (l := []). eapply MP. 1: eapply IMP2. rewrite <- app_nil_l with (l := []).
  eapply MP; [eapply IMP1 | exact PF1].
Qed.

Lemma proof_square (p1 : frm L) (p2 : frm L) (p3 : frm L) (p4 : frm L)
  (PROOF1 : proof [] (Imp_frm p1 p2))
  (PROOF2 : proof [] (Imp_frm p2 p3))
  (PROOF3 : proof [] (Imp_frm p3 p4))
  : proof [] (Imp_frm p1 p4).
Proof.
  1: rewrite <- app_nil_l with (l := []); eapply MP.
  1: rewrite <- app_nil_l with (l := []); eapply MP.
  1: eapply proof_compose with (q := p3).
  { exact PROOF3. }
  1: rewrite <- app_nil_l with (l := []); eapply MP.
  1: rewrite <- app_nil_l with (l := []); eapply MP.
  1: eapply proof_compose with (q := p2).
  { exact PROOF2. }
  { exact PROOF1. }
Qed.

Lemma proof_dni (p : frm L)
  : proof [] (Imp_frm p (Neg_frm (Neg_frm p))).
Proof.
  1: rewrite <- app_nil_l with (l := []); eapply MP. eapply CP.
  1: rewrite <- app_nil_l with (l := []); eapply MP.
  1: rewrite <- app_nil_l with (l := []); eapply MP.
  eapply IMP2 with (q := Imp_frm (Neg_frm (Neg_frm p)) (Neg_frm (Neg_frm (Neg_frm (Neg_frm p))))).
  - 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply proof_flip. eapply CP.
  - eapply proof_ex_falso.
Qed.

Lemma proof_dne (p : frm L)
  : proof [] (Imp_frm (Neg_frm (Neg_frm p)) p).
Proof.
  1: rewrite <- app_nil_l with (l := []); eapply MP. eapply CP. eapply proof_dni.
Qed.

Lemma proof_cp1 (p : frm L) (q : frm L)
  : proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm q) (Neg_frm p))).
Proof.
  assert (PF1: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) (Imp_frm p q)))).
  { eapply IMP1. }
  assert (PF4: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) p))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply IMP1. eapply proof_dne. }
  assert (PF7: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) (Imp_frm p q)) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) p ) (Imp_frm (Neg_frm (Neg_frm p)) q))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply IMP1. eapply IMP2. }
  assert (PF10: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) p) (Imp_frm (Neg_frm (Neg_frm p)) q)))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. 2: exact PF1. 1: rewrite <- app_nil_l with (l := []); eapply MP. 2: eapply PF7. eapply IMP2. }
  assert (PF13: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) q))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. 2: exact PF4. 1: rewrite <- app_nil_l with (l := []); eapply MP. 2: exact PF10. eapply IMP2. }
  assert (PF16: proof [] (Imp_frm (Imp_frm p q) (Imp_frm q (Neg_frm (Neg_frm q))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. 1: eapply IMP1. eapply proof_dni. }
  assert (PF19: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Imp_frm q (Neg_frm (Neg_frm q))) (Imp_frm (Neg_frm (Neg_frm p)) (Imp_frm q (Neg_frm (Neg_frm q))))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply IMP1. eapply IMP1. }
  assert (PF22: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) (Imp_frm q (Neg_frm (Neg_frm q)))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. 2: exact PF16. 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply IMP2. exact PF19. }
  assert (PF25: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) (Imp_frm q (Neg_frm (Neg_frm q)))) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) q) (Imp_frm (Neg_frm (Neg_frm p)) (Neg_frm (Neg_frm q))))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. 1: eapply IMP1. eapply IMP2. }
  pose proof (PF26 := IMP2 (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) (Imp_frm q (Neg_frm (Neg_frm q)))) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) q) (Imp_frm (Neg_frm (Neg_frm p)) (Neg_frm (Neg_frm q))))).
  pose proof (PF27 := MP _ _ _ _ PF26 PF25). simpl in PF27.
  pose proof (PF28 := MP _ _ _ _ PF27 PF22). simpl in PF28.
  pose proof (PF29 := IMP2 (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) q) (Imp_frm (Neg_frm (Neg_frm p)) (Neg_frm (Neg_frm q)))).
  pose proof (PF30 := MP _ _ _ _ PF29 PF28). simpl in PF30.
  pose proof (PF31 := MP _ _ _ _ PF30 PF13). simpl in PF31.
  assert (PF34: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) (Neg_frm (Neg_frm q))) (Imp_frm (Neg_frm q) (Neg_frm p))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply IMP1. eapply CP. }
  assert (PF36: proof [] (Imp_frm (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) (Neg_frm (Neg_frm q)))) (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm q) (Neg_frm p))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply IMP2. exact PF34. }
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. exact PF36. exact PF31. }
Qed.

Section DEDUCTION_THEOREM.

Import ListNotations.

Theorem Deduction_theorem (Gamma : ensemble (frm L)) (H : frm L) (C : frm L)
  : Gamma \proves (Imp_frm H C) <-> E.insert H Gamma \proves C.
Proof.
  revert Gamma H C.
  assert (INTERSECTION : forall X1 : ensemble (frm L), forall X2 : ensemble (frm L),
    forall z, z \in E.intersection X1 X2 <-> z \in X1 /\ z \in X2
  ).
  { eauto with *. }
  assert (FINITE : forall xs : list (frm L),
    forall z, z \in E.finite xs <-> In z xs
  ).
  { eauto with *. }
  assert (EASY_CASE : forall Gamma, forall A, forall B,
    forall PF : proof [] B,
    E.intersection (E.finite []) Gamma \proves Imp_frm A B
  ).
  { i. exists []. split. done. econstructor.
    change (proof ([] ++ []) (Imp_frm A B)). eapply MP with (p := B).
    eapply IMP1. exact PF.
  }
  assert (BWD : forall Gamma, forall H, forall C,
    forall PF: E.insert H Gamma \proves C,
    Gamma \proves Imp_frm H C
  ).
  { intros Gamma A B (ps&INCL&(PF)).
    assert (claim1 : E.intersection (E.finite ps) Gamma \proves Imp_frm A B).
    { induction PF.
      - assert (H_IN : p \in E.insert A Gamma).
        { eapply INCL. eauto with *. }
        rewrite E.in_insert_iff in H_IN; unnw. destruct H_IN as [<- | H_IN].
        + clear INCL. exists []. split. done. econstructor.
          pose proof (PF1 := IMP1 p p).
          pose proof (PF2 := IMP1 p (Imp_frm p p)).
          pose proof (PF3 := IMP2 p (Imp_frm p p) p).
          pose proof (PF4 := MP _ _ _ _ PF3 PF2). simpl in PF4.
          pose proof (PF5 := MP _ _ _ _ PF4 PF1). simpl in PF5.
          exact PF5.
        + exists [p]. split.
          { intros z z_in. econstructor; eauto. rewrite E.in_finite_iff in z_in. simpl in z_in.
            destruct z_in as [z_in | []]. subst z. exact H_IN.
          }
          econstructor.
          pose proof (PF1 := IMP1 p A).
          pose proof (PF2 := AXM p).
          pose proof (PF3 := MP _ _ _ _ PF1 PF2). simpl in PF3.
          exact PF3.
      - exploit IHPF1.
        { ii. eapply INCL. rewrite E.in_finite_iff. rewrite in_app_iff. done. }
        i. exploit IHPF2.
        { ii. eapply INCL. rewrite E.in_finite_iff. rewrite in_app_iff. done. }
        i. destruct x0 as (ps1'&INCL1&(PF1')). destruct x1 as (ps2'&INCL2&(PF2')).
        exists (ps1' ++ ps2'). split.
        { intros z z_in. pose proof (@in_app_iff (frm L)). rewrite INTERSECTION, FINITE, H.
          rewrite E.in_finite_iff in z_in. rewrite H in z_in. destruct z_in as [z_in | z_in].
          - rewrite <- E.in_finite_iff in z_in. apply INCL1 in z_in. rewrite INTERSECTION in z_in. rewrite FINITE in z_in. done.
          - rewrite <- E.in_finite_iff in z_in. apply INCL2 in z_in. rewrite INTERSECTION in z_in. rewrite FINITE in z_in. done.
        }
        econstructor. eapply MP with (p := Imp_frm A p); trivial.
        pose proof (RET := IMP2 A p q). change (proof ([] ++ ps1') (Imp_frm (Imp_frm A p) (Imp_frm A q))).
        eapply MP. exact RET. exact PF1'.
      - exploit IHPF. done. i. destruct x1 as (ps'&INCL'&(PF')).
        assert (claim : In A ps \/ E.finite ps \subseteq Gamma).
        { clear ps' q x NOT_FREE PF PF' IHPF INCL'. revert A INCL. induction ps as [ | p ps IH]; i.
          - right. done.
          - assert (H_in : In p (p :: ps)) by done.
            rewrite <- E.in_finite_iff in H_in. apply INCL in H_in. rewrite E.in_insert_iff in H_in; unnw; destruct H_in as [-> | H_in].
            + left. done.
            + assert (IH_supply : E.finite ps \subseteq E.insert A Gamma).
              { ii. eapply INCL. revert H. do 2 rewrite E.in_finite_iff. simpl. eauto with *. }
              apply IH in IH_supply. destruct IH_supply as [IN | IN].
              * simpl. left. done.
              * right. intros q q_in. rewrite E.in_finite_iff in q_in. simpl in q_in. destruct q_in as [<- | q_in]; done.
        }
        do 2 red in INCL'. destruct claim as [claim | claim].
        + pose proof (NOT_FREE A claim) as x_NOT_FREE_A.
          assert (NOT_FREE' : forall p : frm L, In p ps' -> is_not_free_in_frm x p).
          { i. rewrite <- E.in_finite_iff in H. apply INCL' in H. eapply NOT_FREE. rewrite <- E.in_finite_iff. now firstorder. }
          exists ps'. split. done. econstructor. rewrite <- app_nil_r with (l := ps').
          pose proof (GEN _ _ _ NOT_FREE' PF') as PF_1.
          pose proof (FA3 A q x) as PF_2.
          pose proof (MP _ _ _ _ PF_2 PF_1) as PF_3.
          pose proof (FA2 A x x_NOT_FREE_A) as PF_4.
          pose proof (IMP2 A (All_frm x A) (All_frm x q)) as PF_5.
          pose proof (IMP1 (Imp_frm (All_frm x A) (All_frm x q)) A) as PF_6.
          pose proof (MP _ _ _ _ PF_6 PF_3) as PF_7. simpl in *.
          pose proof (MP _ _ _ _ PF_5 PF_7) as PF_8. simpl in *.
          pose proof (MP _ _ _ _ PF_8 PF_4) as PF_9.
          exact PF_9.
        + exists ps. split. done. econstructor.
          pose proof (GEN _ _ _ NOT_FREE PF) as PF_1.
          pose proof (IMP1 (All_frm x q) A) as PF_2.
          pose proof (MP _ _ _ _ PF_2 PF_1) as PF_3.
          exact PF_3.
      - eapply EASY_CASE. eapply IMP1.
      - eapply EASY_CASE. eapply IMP2.
      - eapply EASY_CASE. eapply CP.
      - eapply EASY_CASE. eapply FA1.
      - eapply EASY_CASE. eapply FA2. done.
      - eapply EASY_CASE. eapply FA3.
      - eapply EASY_CASE. eapply EQN_REFL.
      - eapply EASY_CASE. eapply EQN_SYM.
      - eapply EASY_CASE. eapply EQN_TRANS.
      - eapply EASY_CASE. eapply EQN_FUN.
      - eapply EASY_CASE. eapply EQN_REL. 
    }
    destruct claim1 as (ps'&INCL'&(PF')).
    exists ps'. split.
    - ii. eapply INCL' in H. now firstorder.
    - eauto.
  }
  intros Gamma A B; split; intros PROVE.
  - destruct PROVE as (ps&INCL&(PF)). exists (ps ++ [A]). split.
    + red. simpl. intros p p_in. rewrite E.in_finite_iff in p_in. rewrite in_app_iff in p_in. destruct p_in as [p_in | [-> | []]]; eauto with *.
    + econstructor. pose proof (PF_1 := AXM A). pose proof (PF_2 := MP _ _ _ _ PF PF_1). exact PF_2.
  - exact (BWD Gamma A B PROVE).
Qed.

End DEDUCTION_THEOREM.

Lemma MP_preseves_truth (p : frm L) (q : frm L) (ps1 : list (frm L)) (ps2 : list (frm L)) (Gamma : ensemble (frm L))
  (ENTAILS1 : forall Gamma, E.finite ps1 \subseteq Gamma -> Gamma ⊧ Imp_frm p q)
  (ENTAILS2 : forall Gamma, E.finite ps2 \subseteq Gamma -> Gamma ⊧ p)
  (INCL : E.finite (ps1 ++ ps2) \subseteq Gamma)
  : Gamma ⊧ q.
Proof.
  assert (claim1 : E.finite ps1 \subseteq Gamma).
  { ii. eapply INCL. rewrite E.in_finite_iff in *. rewrite in_app_iff. done. }
  assert (claim2 : E.finite ps2 \subseteq Gamma).
  { ii. eapply INCL. rewrite E.in_finite_iff in *. rewrite in_app_iff. done. }
  specialize (ENTAILS1 Gamma claim1). specialize (ENTAILS2 Gamma claim2).
  red in ENTAILS1, ENTAILS2. ii. specialize (ENTAILS1 STRUCTURE env SATISFY). specialize (ENTAILS2 STRUCTURE env SATISFY).
  simpl in ENTAILS1. done.
Qed.

Lemma Gen_preserves_truth (x : ivar) (q : frm L) (ps : list (frm L)) (Gamma : ensemble (frm L))
  (NOT_FREE : forall p, In p ps -> is_not_free_in_frm x p)
  (ENTAILS1 : forall Gamma, E.finite ps \subseteq Gamma -> Gamma ⊧ q)
  (INCL : E.finite ps \subseteq Gamma)
  : Gamma ⊧ All_frm x q.
Proof.
  red in ENTAILS1. ii.
  assert (claim1 : is_free_in_frm x q = true \/ is_free_in_frm x q = false).
  { destruct (is_free_in_frm x q) as [ | ]; done. }
  destruct claim1 as [claim1 | claim1].
  - assert (claim2 : ~ In q ps).
    { intros H_contra. red in NOT_FREE. pose proof (NOT_FREE q H_contra). done. }
    red in SATISFY. eapply ENTAILS1 with (Gamma := E.delete q (E.finite ps)).
    { ii. autorewrite with datatypes in *. split. intros H_contra. subst q. done. done. }
    ii. rewrite E.in_delete_iff in H_IN; unnw. destruct H_IN as [NE H_IN]. rewrite E.in_finite_iff in H_IN; unnw.
    rewrite <- not_free_no_effect_on_interpret_frm.
    { eapply SATISFY. eapply INCL. rewrite E.in_finite_iff. exact H_IN. }
    { eapply NOT_FREE. exact H_IN. }
  - rewrite <- not_free_no_effect_on_interpret_frm; trivial.
    eapply ENTAILS1 with (Gamma := Gamma); done.
Qed.

#[local] Existing Instance V.vec_isSetoid.

Lemma Func_eqAxm_preserves_truth (f : L.(function_symbols)) (STRUCTURE : structureOf L) (env : ivar -> domain_of_discourse)
  : interpret_frm STRUCTURE env (Fun_eqAxm f).
Proof.
  enough (HACK : forall phi,
    forall phi_a_b : forall a, forall b, forall EQNS : interpret_trms STRUCTURE env a == interpret_trms STRUCTURE env b, interpret_frm STRUCTURE env (phi a b),
    interpret_frm STRUCTURE env (nat_rec (fun _ => frm L) (prod_rec (fun _ => frm L) phi (varcouples (function_arity_table L f))) (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q) (L.(function_arity_table) f))
  ).
  { unfold Fun_eqAxm. eapply HACK. ii. simpl. do 2 rewrite interpret_trm_unfold. eapply function_interpret_preserves_eqProp. exact EQNS. }
  simpl. induction (function_arity_table L f) as [ | n IH].
  - ii. eapply phi_a_b. reflexivity.
  - ii. specialize IH with (phi := fun ts => fun ts' => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts')).
    destruct (varcouples n) as [lhs rhs] eqn: OBS. simpl in *. rewrite OBS. simpl. eapply IH. ii. eapply phi_a_b. Fin.caseS i.
    + simpl. done.
    + rewrite interpret_trms_unfold. symmetry. rewrite interpret_trms_unfold. rewrite V.nth_unfold. symmetry. rewrite V.nth_unfold.
      do 2 rewrite V.tail_unfold. done.
Qed.

Lemma Rel_eqAxm_preserves_truth (R : L.(relation_symbols)) (STRUCTURE : structureOf L) (env : ivar -> domain_of_discourse)
  : interpret_frm STRUCTURE env (Rel_eqAxm R).
Proof.
  enough (HACK : forall phi,
    forall phi_a_b : forall a, forall b, forall EQNS : interpret_trms STRUCTURE env a == interpret_trms STRUCTURE env b, interpret_frm STRUCTURE env (phi a b),
    interpret_frm STRUCTURE env (nat_rec (fun _ => frm L) (prod_rec (fun _ => frm L) phi (varcouples (relation_arity_table L R))) (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q) (L.(relation_arity_table) R))
  ).
  { unfold Rel_eqAxm. eapply HACK. ii. simpl. pose proof (@relation_interpret_preserves_eqProp L STRUCTURE R _ _ EQNS). done. }
  simpl. induction (relation_arity_table L R) as [ | n IH].
  - ii. eapply phi_a_b. reflexivity.
  - ii. specialize IH with (phi := fun ts => fun ts' => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts')).
    destruct (varcouples n) as [lhs rhs] eqn: OBS. simpl in *. rewrite OBS. simpl. eapply IH. ii. eapply phi_a_b. Fin.caseS i.
    + simpl. done.
    + rewrite interpret_trms_unfold. symmetry. rewrite interpret_trms_unfold. rewrite V.nth_unfold. symmetry. rewrite V.nth_unfold.
      do 2 rewrite V.tail_unfold. done.
Qed.

Lemma for_ByHyp (Gamma : ensemble (frm L)) (p : frm L)
  (H_IN : p \in Gamma)
  : Gamma \proves p.
Proof.
  exists [p]. split.
  - intros ?. rewrite E.in_finite_iff. intros [<- | []]; done.
  - econstructor. eapply AXM.
Qed.

Lemma for_Imp_I (Gamma : ensemble (frm L)) (p : frm L) (q : frm L)
  (PROVE1 : E.insert p Gamma \proves q)
  : Gamma \proves Imp_frm p q.
Proof.
  rewrite Deduction_theorem. done.
Qed.

Lemma for_Imp_E (Gamma : ensemble (frm L)) (p : frm L) (q : frm L)
  (PROVE1 : Gamma \proves Imp_frm p q)
  (PROVE2 : Gamma \proves p)
  : Gamma \proves q.
Proof.
  destruct PROVE1 as (ps1&INCL1&(PF1)).
  destruct PROVE2 as (ps2&INCL2&(PF2)).
  exists (ps1 ++ ps2). split.
  - ii. rewrite E.in_finite_iff in H. rewrite in_app_iff in H. destruct H as [H | H].
    + eapply INCL1. now rewrite E.in_finite_iff.
    + eapply INCL2. now rewrite E.in_finite_iff.
  - econstructor. eapply MP; [exact PF1 | exact PF2].
Qed.

Lemma for_compose Gamma p q r
  (PROVE1 : Gamma \proves Imp_frm q r)
  (PROVE2 : Gamma \proves Imp_frm p q)
  : Gamma \proves Imp_frm p r.
Proof.
  destruct PROVE1 as (ps1&INCL1&(PF1)).
  destruct PROVE2 as (ps2&INCL2&(PF2)).
  exists (ps1 ++ ps2). split.
  - ii. rewrite E.in_finite_iff in H. rewrite in_app_iff in H. destruct H as [H | H].
    + eapply INCL1. done.
    + eapply INCL2. done.
  - econstructor. eapply MP.
    + rewrite <- app_nil_l with (l := ps1). eapply MP.
      * eapply proof_compose.
      * exact PF1.
    + exact PF2.
Qed.

Lemma for_CP1 Gamma p q
  (PROVE : Gamma \proves Imp_frm p q)
  : Gamma \proves Imp_frm (Neg_frm q) (Neg_frm p).
Proof.
  destruct PROVE as (ps1&INCL1&(PF1)).
  exists ps1. split; trivial. econstructor.
  rewrite <- app_nil_l with (l := ps1). eapply MP. eapply proof_cp1. exact PF1.
Qed.

Lemma for_MP (Gamma : ensemble (frm L)) (Gamma' : ensemble (frm L)) (p : frm L) (q : frm L)
  (PROVE1 : Gamma \proves Imp_frm p q)
  (PROVE2 : Gamma' \proves p)
  : E.union Gamma Gamma' \proves q.
Proof.
  destruct PROVE1 as (ps1&INCL1&(PF1)).
  destruct PROVE2 as (ps2&INCL2&(PF2)).
  exists (ps1 ++ ps2). split.
  - ii. rewrite E.in_finite_iff in H. rewrite in_app_iff in H. destruct H as [H | H].
    + left. now eapply INCL1.
    + right. now eapply INCL2.
  - econstructor. eapply MP; [exact PF1 | exact PF2].
Qed.

Lemma for_All_I (x : ivar) (p : frm L) (Gamma : ensemble (frm L))
  (FRESH : is_not_free_in_frms x Gamma)
  (PROVE : Gamma \proves p)
  : Gamma \proves All_frm x p.
Proof.
  destruct PROVE as (ps&INCL&(PF)). exists ps. split; trivial. econstructor. eapply GEN.
  - intros q q_in. rewrite <- E.in_finite_iff in q_in. pose proof (INCL q q_in) as claim. apply FRESH in claim. exact claim.
  - exact PF.
Qed.

Lemma proves_alpha_comm_lemma (p : frm L) (q : frm L)
  (ALPHA : p ≡ q)
  : E.singleton p \proves q /\ E.singleton q \proves p.
Proof.
  revert q ALPHA. pattern p. revert p. eapply @frm_depth_lt_ind; ii. destruct ALPHA.
  - rewrite <- EQ. split; eapply for_ByHyp; done.
  - rewrite <- EQ1, <- EQ2. split; eapply for_ByHyp; done.
  - assert (rank_LT1: frm_depth p1 < frm_depth (Neg_frm p1)) by now simpl; lia.
    pose proof (IH p1 rank_LT1 _ ALPHA) as [PROVE1 PROVE2].
    split.
    + eapply for_Imp_E. 2:{ eapply for_ByHyp. rewrite E.in_singleton_iff. reflexivity. }
      eapply for_CP1. eapply for_Imp_I. destruct PROVE2 as (ps&INCL&(PF)).
      exists ps. split. { intros z z_in. rewrite E.in_insert_iff; unnw. pose proof (INCL z z_in) as H_IN. rewrite E.in_singleton_iff in H_IN. done. } { econstructor. exact PF. }
    + eapply for_Imp_E. 2:{ eapply for_ByHyp. rewrite E.in_singleton_iff. reflexivity. }
      eapply for_CP1. eapply for_Imp_I. destruct PROVE1 as (ps&INCL&(PF)).
      exists ps. split. { intros z z_in. rewrite E.in_insert_iff; unnw. pose proof (INCL z z_in) as H_IN. rewrite E.in_singleton_iff in H_IN. done. } { econstructor. exact PF. }
  - assert (rank_LT1 : frm_depth p1 < frm_depth (Imp_frm p1 p2)) by now simpl; lia.
    pose proof (IH p1 rank_LT1 _ ALPHA1) as [PROVE1 PROVE2].
    assert (rank_LT2 : frm_depth p2 < frm_depth (Imp_frm p1 p2)) by now simpl; lia.
    pose proof (IH p2 rank_LT2 _ ALPHA2) as [PROVE3 PROVE4].
    split.
    + eapply for_Imp_I.
      assert (PROVE5 : E.insert p1' (E.singleton (Imp_frm p1 p2)) \proves p1).
      { destruct PROVE2 as (ps&INCL&(PF)). exists ps. split.
        - intros z z_in. pose proof (INCL z z_in) as H_IN. rewrite E.in_singleton_iff in H_IN; unnw. subst z. eauto with *.
        - econstructor. exact PF.
      }
      assert (PROVE6 : E.insert p1' (E.singleton (Imp_frm p1 p2)) \proves p2).
      { eapply for_Imp_E.
        - eapply for_ByHyp. right. rewrite E.in_singleton_iff; unnw. reflexivity.
        - exact PROVE5.
      }
      eapply for_Imp_E. 2: exact PROVE6. eapply for_Imp_I.
      destruct PROVE3 as (ps&INCL&(PF)). exists ps. split.
      * intros z z_in. pose proof (INCL z z_in) as H_IN. rewrite E.in_singleton_iff in H_IN; unnw. subst z. eauto with *.
      * econstructor. exact PF.
    + eapply for_Imp_I.
      assert (PROVE5 : E.insert p1 (E.singleton (Imp_frm p1' p2')) \proves p1').
      { destruct PROVE1 as (ps&INCL&(PF)). exists ps. split.
        - intros z z_in. pose proof (INCL z z_in) as H_IN. rewrite E.in_singleton_iff in H_IN; unnw. subst z. eauto with *.
        - econstructor. exact PF.
      }
      assert (PROVE6 : E.insert p1 (E.singleton (Imp_frm p1' p2')) \proves p2').
      { eapply for_Imp_E.
        - eapply for_ByHyp. right. rewrite E.in_singleton_iff; unnw. reflexivity.
        - exact PROVE5.
      }
      eapply for_Imp_E. 2: exact PROVE6. eapply for_Imp_I.
      destruct PROVE4 as (ps&INCL&(PF)). exists ps. split.
      * intros z z_in. pose proof (INCL z z_in) as H_IN. rewrite E.in_singleton_iff in H_IN; unnw. subst z. eauto with *.
      * econstructor. exact PF.
  - rename p1 into p, p1' into q. rename y into x, y' into y.
    assert (rank_EQ1 : frm_depth p = frm_depth (subst_frm (one_subst x (Var_trm z)) p)).
    { rewrite subst_preserves_rank. reflexivity. }
    assert (rank_EQ2 : frm_depth q = frm_depth (subst_frm (one_subst y (Var_trm z)) q)).
    { rewrite subst_preserves_rank. reflexivity. }
    assert (rank_EQ3 : frm_depth (subst_frm (one_subst x (Var_trm z)) p) = frm_depth (subst_frm (one_subst y (Var_trm z)) q)).
    { eapply alpha_equiv_compath_rank. exact ALPHA. }
    assert (rank_LT1 : frm_depth p < frm_depth (All_frm x p)) by now simpl; lia.
    assert (rank_LT2 : frm_depth q < frm_depth (All_frm x p)) by now simpl; lia.
    set (p' := subst_frm (one_subst x (Var_trm z)) p) in *. set (q' := subst_frm (one_subst y (Var_trm z)) q) in *.
    assert (rank_LT3 : frm_depth p' < frm_depth (All_frm x p)) by now simpl; lia.
    assert (rank_LT4 : frm_depth (subst_frm (one_subst y (Var_trm y)) q) < frm_depth (All_frm x p)) by now rewrite subst_preserves_rank; simpl; lia.
    assert (rank_LT5 : frm_depth (subst_frm (one_subst x (Var_trm x)) p) < frm_depth (All_frm x p)) by now rewrite subst_preserves_rank; simpl; lia.
    assert (ALPHA1 : subst_frm (one_subst y (Var_trm y)) q ≡ q).
    { eapply subst_nil_frm; intros w w_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec w y) as [ | ]; done. }
    assert (ALPHA2: subst_frm (one_subst x (Var_trm x)) p ≡ p).
    { eapply subst_nil_frm; intros w w_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec w x) as [ | ]; done. }
    pose proof (IH p' rank_LT3 q' ALPHA) as [PROVE1 PROVE2].
    pose proof (IH _ rank_LT4 q ALPHA1) as [PROVE3 PROVE4].
    pose proof (IH _ rank_LT5 p ALPHA2) as [PROVE5 PROVE6].
    assert (claim1 : E.empty \proves q' -> E.empty \proves All_frm z q').
    { intros (ps&INCL&(PF)). exists []. split. intros ? H_in. rewrite E.in_finite_iff in H_in. inv H_in. econstructor. eapply GEN. intros ? []. replace ps with (@nil (frm L)) in PF. exact PF. destruct ps as [ | p'' ps']; trivial.
      assert (IN : p'' \in E.finite (p'' :: ps')) by now rewrite E.in_finite_iff; simpl; tauto.
      apply INCL in IN. inv IN.
    }
    assert (claim2 : E.empty \proves p' -> E.empty \proves All_frm z p').
    { intros (ps&INCL&(PF)). exists []. split. intros ? H_in. rewrite E.in_finite_iff in H_in. inv H_in. econstructor. eapply GEN. intros ? []. replace ps with (@nil (frm L)) in PF. exact PF. destruct ps as [ | p'' ps']; trivial.
      assert (IN : p'' \in E.finite (p'' :: ps')) by now rewrite E.in_finite_iff; simpl; tauto.
      apply INCL in IN. inv IN.
    }
    clear rank_EQ1 rank_EQ2 rank_EQ3 rank_LT1 rank_LT2 rank_LT3 rank_LT4 rank_LT5.
    assert (EQ1 : subst_frm (one_subst z (Var_trm y)) q' = subst_frm (one_subst y (Var_trm y)) q).
    { unfold q'. rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same.
      intros w FREE. unfold subst_compose, one_subst, cons_subst, nil_subst. destruct (eq_dec w y) as [EQ | NE].
      - rewrite subst_trm_unfold. destruct (eq_dec z z) as [EQ' | NE']; done.
      - rewrite subst_trm_unfold. destruct (eq_dec w z) as [EQ' | NE'].
        + subst w. simpl in RFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in RFRESH. destruct RFRESH as [? | ?]; done.
        + done.
    }
    assert (EQ2 : subst_frm (one_subst z (Var_trm x)) p' = subst_frm (one_subst x (Var_trm x)) p).
    { unfold p'. rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same.
      intros w FREE. unfold subst_compose, one_subst, cons_subst, nil_subst. destruct (eq_dec w x) as [EQ | NE].
      - rewrite subst_trm_unfold. destruct (eq_dec z z) as [EQ' | NE']; done.
      - rewrite subst_trm_unfold. destruct (eq_dec w z) as [EQ' | NE'].
        + subst w. simpl in LFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in LFRESH. destruct LFRESH as [? | ?]; done.
        + done.
    }
    split.
    + assert (PROVE7 : E.singleton (All_frm x p) \proves All_frm z p').
      { eapply for_Imp_E.
        - exists []. split. intros ? H. rewrite E.in_finite_iff in H. inv H. econstructor. eapply proof_rebind_All_frm. exact LFRESH.
        - eapply for_ByHyp. done.
      }
      assert (PROVE8 : E.singleton (All_frm x p) \proves (Imp_frm (All_frm z p') (All_frm z q'))).
      { enough (PROVE : E.empty \proves Imp_frm p' q').
        - destruct PROVE as (ps&INCL&(PF)). assert (EQ: ps = []). destruct ps as [ | p'' ps'']; trivial.
          + assert (IN : p'' \in E.finite (p'' :: ps'')) by now rewrite E.in_finite_iff; simpl; tauto. apply INCL in IN. inv IN.
          + subst ps. exists []. split. intros ? []. inv H_in. econstructor. rewrite <- app_nil_l with (l := []). eapply MP.
            * eapply FA3.
            * eapply GEN. intros ? []. exact PF.
        - destruct PROVE1 as (ps&INCL&(PF)). eapply for_Imp_I. exists ps. split.
          + intros w w_in. pose proof (INCL w w_in) as H_IN. rewrite E.in_singleton_iff in H_IN; unnw. subst w. eauto with *.
          + econstructor. exact PF.
      }
      pose proof (PROVE9 := for_Imp_E _ _ _ PROVE8 PROVE7).
      assert (PROVE10 : E.singleton (All_frm x p) \proves Imp_frm (All_frm z q') (All_frm y q)).
      { assert (PROVE : E.insert (All_frm z q') (E.singleton (All_frm x p)) \proves (All_frm y (subst_frm (one_subst y (Var_trm y)) q))).
        { rewrite <- EQ1. rewrite <- Deduction_theorem. exists []. split. intros ? []. inv H_in. econstructor. eapply proof_rebind_All_frm.
          red. simpl. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. simpl in RFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in RFRESH. unfold q'.
          destruct (eq_dec y z) as [EQ | NE]; [done | destruct RFRESH as [FRESH' | <-]; [left | done]].
          eapply frm_is_fresh_in_subst_iff. unfold frm_is_fresh_in_subst. eapply forallb_forall. intros w w_free. rewrite fv_is_free_in_frm in w_free. unfold "∘"%prg.
          rewrite negb_true_iff. unfold one_subst, cons_subst, nil_subst.
          destruct (eq_dec w y) as [w_eq_y | w_ne_y].
          - rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
          - rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
        }
        assert (PROVE' : E.empty \proves (Imp_frm (subst_frm (one_subst y (Var_trm y)) q) q)).
        { eapply for_Imp_I. destruct PROVE3 as (ps&INCL&(PF)). exists ps. split. intros w w_in. pose proof (INCL w w_in) as H_IN. rewrite E.in_singleton_iff in H_IN; unnw. subst w. eauto with *. econstructor. exact PF. }
        destruct PROVE' as (ps&INCL&(PF)).
        assert (EQ: ps = []).
        { destruct ps as [ | p'' ps'']. reflexivity. assert (IN : p'' \in E.finite (p'' :: ps'')) by now rewrite E.in_finite_iff; simpl; tauto. apply INCL in IN. inv IN. }
        subst ps. clear INCL. eapply for_Imp_I. destruct PROVE as (ps&INCL&(PF')). exists ps. split. exact INCL. econstructor.
        rewrite <- app_nil_l with (l := ps). eapply MP. 2: exact PF'. rewrite <- app_nil_l with (l := []). eapply MP. eapply FA3.
        eapply GEN. intros ? []. exact PF.
      }
      eapply for_Imp_E. exact PROVE10. exact PROVE9.
    + assert (PROVE7 : E.singleton (All_frm y q) \proves All_frm z q').
      { eapply for_Imp_E.
        - exists []. split. intros ? []. inv H_in. econstructor. eapply proof_rebind_All_frm. exact RFRESH.
        - eapply for_ByHyp. done.
      }
      assert (PROVE8 : E.singleton (All_frm y q) \proves (Imp_frm (All_frm z q') (All_frm z p'))).
      { enough (PROVE: E.empty \proves Imp_frm q' p').
        - destruct PROVE as (ps&INCL&(PF)).
          assert (EQ : ps = []).
          { destruct ps as [ | p'' ps'']; trivial. assert (IN : p'' \in E.finite (p'' :: ps'')) by now rewrite E.in_finite_iff; simpl; tauto. apply INCL in IN. inv IN. }
          subst ps. exists []. split. intros ? []. inv H_in. econstructor. rewrite <- app_nil_l with (l := []). eapply MP.
          + eapply FA3.
          + eapply GEN. intros ? []. exact PF.
        - destruct PROVE2 as (ps&INCL&(PF)). eapply for_Imp_I. exists ps. split.
          + intros w w_in. pose proof (INCL w w_in) as H_IN. rewrite E.in_singleton_iff in H_IN; unnw. subst w. eauto with *.
          + econstructor. exact PF.
      }
      pose proof (PROVE9 := for_Imp_E _ _ _ PROVE8 PROVE7).
      assert (PROVE10 : E.singleton (All_frm y q) \proves Imp_frm (All_frm z p') (All_frm x p)).
      { assert (PROVE : E.insert (All_frm z p') (E.singleton (All_frm y q)) \proves (All_frm x (subst_frm (one_subst x (Var_trm x)) p))).
        { rewrite <- EQ2. rewrite <- Deduction_theorem. exists []. split. intros ? []. inv H_in. econstructor. eapply proof_rebind_All_frm.
          red. simpl. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. simpl in LFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in LFRESH. unfold p'.
          destruct (eq_dec x z) as [EQ | NE]; [done | destruct LFRESH as [LFRESH | <-]; [left | done]].
          eapply frm_is_fresh_in_subst_iff. unfold frm_is_fresh_in_subst. eapply forallb_forall. intros w w_free. rewrite fv_is_free_in_frm in w_free. unfold "∘"%prg.
          rewrite negb_true_iff. unfold one_subst, cons_subst, nil_subst.
          destruct (eq_dec w x) as [w_eq_x | w_ne_x].
          - rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
          - rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
        }
        assert (PROVE' : E.empty \proves (Imp_frm (subst_frm (one_subst x (Var_trm x)) p) p)).
        { eapply for_Imp_I. destruct PROVE5 as (ps&INCL&(PF)). exists ps. split. intros w w_in. pose proof (INCL w w_in) as H_IN. rewrite E.in_singleton_iff in H_IN; unnw. subst w. eauto with *. econstructor. exact PF. }
        destruct PROVE' as (ps&INCL&(PF)).
        assert (EQ: ps = []).
        { destruct ps as [ | p'' ps'']. reflexivity. assert (IN : p'' \in E.finite (p'' :: ps'')) by now rewrite E.in_finite_iff; simpl; tauto. apply INCL in IN. inv IN. }
        subst ps. clear INCL. eapply for_Imp_I. destruct PROVE as (ps&INCL&(PF')). exists ps. split. exact INCL. econstructor.
        rewrite <- app_nil_l with (l := ps). eapply MP. 2: exact PF'. rewrite <- app_nil_l with (l := []). eapply MP. eapply FA3.
        eapply GEN. intros ? []. exact PF.
      }
      eapply for_Imp_E. exact PROVE10. exact PROVE9.
Qed.

Lemma proves_alpha_proves (Gamma : ensemble (frm L)) (p : frm L) (q : frm L)
  (PROVE : Gamma \proves p)
  (ALPHA : p ≡ q)
  : Gamma \proves q.
Proof.
  apply proves_alpha_comm_lemma in ALPHA. destruct ALPHA as [PROVE' _].
  eapply for_Imp_E. 2: exact PROVE. eapply for_Imp_I. destruct PROVE' as (ps&INCL&(PF)).
  exists ps. split. intros w w_in. pose proof (INCL w w_in) as H_IN. rewrite E.in_singleton_iff in H_IN; unnw.
  subst w. eauto with *. constructor. exact PF.
Qed.

#[global]
Add Parametric Morphism
  : proves with signature (eqProp ==> alpha_equiv ==> iff) as proves_alpha_comm.
Proof.
  intros Gamma Gamma' Gamma_eq_Gamma' p p' ALPHA. split; intros PROVE.
  - eapply proves_alpha_proves. 2: exact ALPHA. destruct PROVE as (ps&INCL&(PF)). exists ps. split.
    + ii. rewrite <- Gamma_eq_Gamma'. eapply INCL. assumption.
    + econstructor. exact PF.
  - symmetry in ALPHA. eapply proves_alpha_proves. 2: exact ALPHA. destruct PROVE as (ps&INCL&(PF)). exists ps. split.
    + ii. rewrite -> Gamma_eq_Gamma'. eapply INCL. assumption.
    + econstructor. exact PF.
Qed.

Lemma extend_proves Gamma Gamma' A
  (SUBSET : Gamma \subseteq Gamma')
  (PROVES : Gamma \proves A)
  : Gamma' \proves A.
Proof.
  destruct PROVES as (ps&INCL&(PF)). exists ps. split. done. econstructor; exact PF.
Qed.

Lemma cut_one A B Gamma
  (PROVE1 : E.singleton A \proves B)
  (PROVE2 : Gamma \proves A)
  : Gamma \proves B.
Proof.
  assert (claim1 : E.singleton A == E.insert A E.empty).
  { change (forall x, x \in E.singleton A <-> x \in E.insert A E.empty). intros x. rewrite E.in_singleton_iff; unnw. rewrite E.in_insert_iff; unnw. rewrite E.in_empty_iff; unnw. done. }
  rewrite claim1 in PROVE1. rewrite <- Deduction_theorem in PROVE1.
  destruct PROVE1 as (ps1&INCL1&(PF1)), PROVE2 as (ps2&INCL2&(PF2)).
  exists ps2. split. done. econstructor. rewrite <- app_nil_l with (l := ps2).
  assert (claim2: ps1 = []).
  { destruct ps1 as [ | p' ps']. reflexivity. assert (IN : p' \in E.finite (p' :: ps')) by now rewrite E.in_finite_iff; simpl; tauto. apply INCL1 in IN. inv IN. }
  subst ps1. eapply MP; [exact PF1 | exact PF2].
Qed.

Lemma cut_one' A B Gamma
  (PROVE1 : E.insert A E.empty \proves B)
  (PROVE2 : Gamma \proves A)
  : Gamma \proves B.
Proof.
  assert (claim1 : E.singleton A == E.insert A E.empty).
  { change (forall x, x \in E.singleton A <-> x \in E.insert A E.empty). intros x. rewrite E.in_singleton_iff; unnw. rewrite E.in_insert_iff; unnw. rewrite E.in_empty_iff; unnw. done. }
  rewrite <- claim1 in PROVE1.  eapply cut_one; eauto.
Qed.

Lemma cut A B Gamma
  (PROVE1 : E.insert A  Gamma \proves B)
  (PROVE2 : Gamma \proves A)
  : Gamma \proves B.
Proof.
  rewrite <- Deduction_theorem in PROVE1. destruct PROVE1 as (ps1&INCL1&(PF1)), PROVE2 as (ps2&INCL2&(PF2)).
  exists (ps1 ++ ps2). split.
  - intros q q_in. rewrite E.in_finite_iff in q_in. rewrite in_app_iff in q_in. destruct q_in as [q_in | q_in]; [eapply INCL1 | eapply INCL2]; now rewrite E.in_finite_iff.
  - econstructor. eapply MP with (p := A); trivial.
Qed.

Lemma for_All_E (x : ivar) (t : trm L) (p : frm L) (Gamma : ensemble (frm L))
  (PROVE : Gamma \proves All_frm x p)
  : Gamma \proves subst_frm (one_subst x t) p.
Proof.
  eapply cut_one' with (A := All_frm x p).
  - rewrite <- Deduction_theorem. exists []. split. ii. rewrite E.in_finite_iff in H. inv H. econstructor. eapply FA1.
  - done.
Qed.

Lemma rebind_All_frm_fwd (Gamma : ensemble (frm L)) (x : ivar) (x' : ivar) (p : frm L)
  (FRESH : is_not_free_in_frm x' (All_frm x p))
  : Gamma \proves Imp_frm (All_frm x p) (All_frm x' (subst_frm (one_subst x (Var_trm x')) p)).
Proof.
  exists []. split. intros ? H. rewrite E.in_finite_iff in H. inv H. econstructor. eapply proof_rebind_All_frm. exact FRESH.
Qed.

Lemma rebind_All_frm_bwd (Gamma : ensemble (frm L)) (x : ivar) (x' : ivar) (p : frm L)
  (FRESH : is_not_free_in_frm x' (All_frm x p))
  : Gamma \proves Imp_frm (All_frm x' (subst_frm (one_subst x (Var_trm x')) p)) (All_frm x p).
Proof.
  eapply extend_proves with (Gamma := E.empty). done.
  eapply for_Imp_I. eapply for_All_I.
  { intros q q_in. rewrite E.in_insert_iff in q_in; unnw. destruct q_in as [-> | []].
    red in FRESH. simpl in *. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in FRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. destruct (eq_dec x x') as [EQ | NE].
    - subst. right. done.
    - destruct FRESH as [FRESH | H_contra]. 2: done. left.
      rewrite <- frm_is_fresh_in_subst_iff. unfold frm_is_fresh_in_subst. rewrite forallb_forall.
      intros u u_free. unfold "∘"%prg. rewrite negb_true_iff. unfold one_subst, cons_subst, nil_subst.
      rewrite fv_is_free_in_frm in u_free. destruct (eq_dec u x) as [EQ' | NE'].
      + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
      + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
  }
  eapply proves_alpha_proves with (p := subst_frm (one_subst x' (Var_trm x)) (subst_frm (one_subst x (Var_trm x')) p)).
  - eapply for_All_E. eapply for_ByHyp. eauto with *.
  - rewrite <- subst_compose_frm_spec. rewrite <- subst_nil_frm with (p := p) (s := nil_subst) at 2. 2: done.
    eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
    ii. unfold subst_compose. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec z x) as [EQ1 | NE1].
    + rewrite subst_trm_unfold. destruct (eq_dec x' x') as [EQ2 | NE2]; done.
    + rewrite subst_trm_unfold. destruct (eq_dec z x') as [EQ2 | NE2]. 2: done.
      subst z. red in FRESH. simpl in FRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in FRESH. destruct FRESH as [FRESH | <-]; done.
Qed.

Lemma for_All_I' (x : ivar) (y : ivar) (p : frm L) (Gamma : ensemble (frm L))
  (NOT_FREE1 : is_not_free_in_frms y Gamma)
  (NOT_FREE2 : is_not_free_in_frm y (All_frm x p))
  (PROVE1: Gamma \proves subst_frm (one_subst x (Var_trm y)) p)
  : Gamma \proves All_frm x p.
Proof.
  eapply cut_one' with (A := (All_frm y (subst_frm (one_subst x (Var_trm y)) p))).
  - rewrite <- Deduction_theorem. eapply rebind_All_frm_bwd. exact NOT_FREE2.
  - eapply for_All_I. exact NOT_FREE1. exact PROVE1.
Qed.

Lemma rebind_All_frm (Gamma : ensemble (frm L)) (x : ivar) (x' : ivar) (p : frm L)
  (FRESH : is_not_free_in_frm x' (All_frm x p))
  : Gamma \proves (All_frm x p) <-> Gamma \proves (All_frm x' (subst_frm (one_subst x (Var_trm x')) p)).
Proof.
  split.
  - intros PROVE. eapply cut_one'. 2: exact PROVE.
    rewrite <- Deduction_theorem. eapply rebind_All_frm_fwd. exact FRESH.
  - intros PROVE. eapply cut_one'. 2: exact PROVE.
    rewrite <- Deduction_theorem. eapply rebind_All_frm_bwd. exact FRESH.
Qed.

Lemma open_closed_frm (Gamma : ensemble (frm L)) (p : frm L)
  (PROVE : Gamma \proves closed_frm p)
  : Gamma \proves p.
Proof.
  revert PROVE. unfold closed_frm. revert Gamma. induction (nodup eq_dec (fvs_frm p)) as [ | x xs IH]; simpl; ii.
  - exact PROVE.
  - eapply IH. eapply proves_alpha_proves with (p := subst_frm (one_subst x (Var_trm x)) (close_ivars p xs)).
    + eapply for_All_E. exact PROVE.
    + eapply subst_nil_frm. intros u u_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec u x) as [? | ?]; done.
Qed.

Definition equiv_deductible (p1 : frm L) (p2 : frm L) : Prop :=
  E.singleton p1 \proves p2 /\ E.singleton p2 \proves p1.

#[local] Instance equiv_deductible_reflexive
  : Reflexive equiv_deductible.
Proof.
  intros p1. split; eapply for_ByHyp; done.
Qed.

#[local] Instance equiv_deductible_symmetric
  : Symmetric equiv_deductible.
Proof.
  intros p1 p2 [? ?]; split; done.
Qed.

#[local] Instance equiv_deductible_transitive
  : Transitive equiv_deductible.
Proof.
  intros p1 p2 p3 [PROVE1 PROVE2] [PROVE3 PROVE4]. split.
  - eapply cut with (A := p2). 2: done. eapply extend_proves with (Gamma := E.singleton p2). 2: done. intros q q_in. rewrite E.in_singleton_iff in q_in; unnw. subst q. eauto with *.
  - eapply cut with (A := p2). 2: done. eapply extend_proves with (Gamma := E.singleton p2). 2: done. intros q q_in. rewrite E.in_singleton_iff in q_in; unnw. subst q. eauto with *.
Qed.

#[local] Instance equiv_deductible_Equivalence : Equivalence equiv_deductible :=
  { Equivalence_Reflexive := equiv_deductible_reflexive
  ; Equivalence_Symmetric := equiv_deductible_symmetric
  ; Equivalence_Transitive := equiv_deductible_transitive
  }.

#[local] Instance upto_equiv_deductible : isSetoid (frm L) :=
  { eqProp := equiv_deductible
  ; eqProp_Equivalence := equiv_deductible_Equivalence
  }.

#[local]
Add Parametric Morphism
  : proves with signature (eqProp ==> eqProp ==> iff) as proves_equiv_deductible.
Proof.
  intros Gamma Gamma' Gamma_eq_Gamma' p1 p2 [PROVE1 PROVE2]. pose proof (@proves_alpha_comm Gamma Gamma' Gamma_eq_Gamma' p2 p2 (alpha_equiv_Reflexive p2)) as claim1. rewrite <- claim1. clear claim1.
  split; intros PROVE.
  - eapply cut with (A := p1). 2: done. eapply extend_proves. 2: exact PROVE1. intros q q_in. rewrite E.in_singleton_iff in q_in; unnw. subst q; eauto with *.
  - eapply cut with (A := p2). 2: done. eapply extend_proves. 2: exact PROVE2. intros q q_in. rewrite E.in_singleton_iff in q_in; unnw. subst q; eauto with *.
Qed.

End HILBERT_PROOF_SYSTEM.

End HPS.

Module ND.

Inductive infers {L : language} (Gamma : ensemble (frm L)) : forall C : frm L, Prop :=
  | By_hyp p
    (IN : p \in Gamma)
    : Gamma ⊢ p
  | Eqn_I t1
    : Gamma ⊢ Eqn_frm t1 t1
  | Eqn_E x t1 t2 p1
    (INFERS1 : Gamma ⊢ Eqn_frm t1 t2)
    (INFERS2 : Gamma ⊢ subst_frm (one_subst x t1) p1)
    : Gamma ⊢ subst_frm (one_subst x t2) p1
  | All_I x y p
    (NOT_FREE1 : is_not_free_in_frms y Gamma)
    (NOT_FREE2 : is_not_free_in_frm y (All_frm x p))
    (INFERS1: Gamma ⊢ subst_frm (one_subst x (Var_trm y)) p)
    : Gamma ⊢ All_frm x p
  | All_E x t p
    (INFERS1 : Gamma ⊢ All_frm x p)
    : Gamma ⊢ subst_frm (one_subst x t) p
  | Exs_I x t p
    (INFERS1 : Gamma ⊢ subst_frm (one_subst x t) p)
    : Gamma ⊢ Exs_frm x p
  | Exs_E x y p1 p2
    (NOT_FREE1 : is_not_free_in_frms y Gamma)
    (NOT_FREE2 : is_not_free_in_frm y (Exs_frm x p1))
    (NOT_FREE3 : is_not_free_in_frm y p2)
    (INFERS1: Gamma ⊢ Exs_frm x p1)
    (INFERS2: E.insert (subst_frm (one_subst x (Var_trm y)) p1) Gamma ⊢ p2)
    : Gamma ⊢ p2
  | Bot_I p1
    (INFERS1 : Gamma ⊢ p1)
    (INFERS2 : Gamma ⊢ Neg_frm p1)
    : Gamma ⊢ Bot_frm
  | Bot_E p1
    (INFERS1 : Gamma ⊢ Bot_frm)
    : Gamma ⊢ p1
  | Neg_I p1
    (INFERS1: E.insert p1 Gamma ⊢ Bot_frm)
    : Gamma ⊢ Neg_frm p1
  | Neg_E p1
    (INFERS1 : E.insert (Neg_frm p1) Gamma ⊢ Bot_frm)
    : Gamma ⊢ p1
  | Con_I p1 p2
    (INFERS1 : Gamma ⊢ p1)
    (INFERS2 : Gamma ⊢ p2)
    : Gamma ⊢ Con_frm p1 p2
  | Con_E1 p1 p2
    (INFERS1 : Gamma ⊢ Con_frm p1 p2)
    : Gamma ⊢ p1
  | Con_E2 p1 p2
    (INFERS1 : Gamma ⊢ Con_frm p1 p2)
    : Gamma ⊢ p2
  | Dis_I1 p1 p2
    (INFERS1 : Gamma ⊢ p1)
    : Gamma ⊢ Dis_frm p1 p2
  | Dis_I2 p1 p2
    (INFERS1 : Gamma ⊢ p2)
    : Gamma ⊢ Dis_frm p1 p2
  | Dis_E p1 p2 p3
    (INFERS1 : Gamma ⊢ Dis_frm p1 p2)
    (INFERS2 : E.insert p1 Gamma ⊢ p3)
    (INFERS3 : E.insert p2 Gamma ⊢ p3)
    : Gamma ⊢ p3
  | Imp_I p1 p2
    (INFERS1 : E.insert p1 Gamma ⊢ p2)
    : Gamma ⊢ Imp_frm p1 p2
  | Imp_E p1 p2
    (INFERS1 : Gamma ⊢ Imp_frm p1 p2)
    (INFERS2 : Gamma ⊢ p1)
    : Gamma ⊢ p2
  | Iff_I p1 p2
    (INFERS1 : E.insert p1 Gamma ⊢ p2)
    (INFERS2 : E.insert p2 Gamma ⊢ p1)
    : Gamma ⊢ Iff_frm p1 p2
  | Iff_E1 p1 p2
    (INFERS1 : Gamma ⊢ Iff_frm p1 p2)
    (INFERS2 : Gamma ⊢ p1)
    : Gamma ⊢ p2
  | Iff_E2 p1 p2
    (INFERS1 : Gamma ⊢ Iff_frm p1 p2)
    (INFERS2 : Gamma ⊢ p2)
    : Gamma ⊢ p1
  where " Gamma ⊢ C " := (infers Gamma C) : type_scope.

End ND.
