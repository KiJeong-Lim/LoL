Require Import LoL.Prelude.Prelude.
Require Import LoL.Prelude.Notations.
Require Import LoL.Math.ThN.
Require Import LoL.Data.Vector.
Require Import LoL.FoL.Syntax.

#[local] Infix "\in" := E.elem.
#[local] Infix "\subseteq" := E.isSubsetOf.

#[local] Infix "≡" := alpha_equiv.

#[local] Close Scope list_scope.
#[local] Open Scope vector_scope.

#[local] Existing Instance V.vec_isSetoid.

Class structureOf (L : language) : Type :=
  { domain_of_discourse : Type
  ; equation_interpret :: isSetoid domain_of_discourse
  ; function_interpret (f : L.(function_symbols)) (vs : Vector.t domain_of_discourse (L.(function_arity_table) f)) : domain_of_discourse
  ; constant_interpret (c : L.(constant_symbols)) : domain_of_discourse
  ; relation_interpret (R : L.(relation_symbols)) (vs : Vector.t domain_of_discourse (L.(relation_arity_table) R)) : Prop
  ; domain_is_nonempty : inhabited domain_of_discourse
  ; function_interpret_preserves_eqProp (f : L.(function_symbols)) (vs1 : Vector.t domain_of_discourse (L.(function_arity_table) f)) (vs2 : Vector.t domain_of_discourse (L.(function_arity_table) f))
    (EQ : vs1 == vs2)
    : function_interpret f vs1 == function_interpret f vs2
  ; relation_interpret_preserves_eqProp (R : L.(relation_symbols)) (vs1 : Vector.t domain_of_discourse (L.(relation_arity_table) R)) (vs2 : Vector.t domain_of_discourse (L.(relation_arity_table) R))
    (EQ : vs1 == vs2)
    : relation_interpret R vs1 <-> relation_interpret R vs2
  }.

Section SEMANTICS.

#[local] Open Scope program_scope.

Context {L : language}.

Definition upd_env {STRUCTURE : structureOf L} (y : ivar) (y_value : domain_of_discourse) (env : ivar -> domain_of_discourse) : ivar -> domain_of_discourse :=
  fun z : ivar => if eq_dec z y then y_value else env z.

Variable STRUCTURE : structureOf L.

Fixpoint interpret_trm (env : ivar -> domain_of_discourse) (t : trm L) {struct t} : domain_of_discourse :=
  match t with
  | Var_trm x => env x
  | Fun_trm f ts => function_interpret f (interpret_trms env ts)
  | Con_trm c => constant_interpret c
  end
with interpret_trms {n : nat} (env : ivar -> domain_of_discourse) (ts : trms L n) {struct ts} : Vector.t domain_of_discourse n :=
  match ts with
  | O_trms => []
  | S_trms n t ts => interpret_trm env t :: interpret_trms env ts 
  end.

Fixpoint interpret_frm (env : ivar -> domain_of_discourse) (p : frm L) {struct p} : Prop :=
  match p with
  | Eqn_frm t1 t2 => interpret_trm env t1 == interpret_trm env t2
  | Rel_frm R ts => relation_interpret R (interpret_trms env ts)
  | Neg_frm p1 => ~ interpret_frm env p1
  | Imp_frm p1 p2 => interpret_frm env p1 -> interpret_frm env p2
  | All_frm y p1 => forall y_value : domain_of_discourse, interpret_frm (upd_env y y_value env) p1
  end.

Lemma interpret_trm_unfold (env : ivar -> domain_of_discourse) (t : trm L) :
  interpret_trm env t =
  match t with
  | Var_trm x => env x
  | Fun_trm f ts => function_interpret f (interpret_trms env ts)
  | Con_trm c => constant_interpret c
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma interpret_trms_unfold n (env : ivar -> domain_of_discourse) (ts : trms L n) :
  interpret_trms env ts =
  match ts with
  | O_trms => VNil
  | S_trms n' t ts' => VCons n' (interpret_trm env t) (interpret_trms env ts')
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Lemma interpret_frm_unfold (env : ivar -> domain_of_discourse) (p : frm L) :
  interpret_frm env p =
  match p with
  | Eqn_frm t1 t2 => interpret_trm env t1 == interpret_trm env t2
  | Rel_frm R ts => relation_interpret R (interpret_trms env ts)
  | Neg_frm p1 => ~ interpret_frm env p1
  | Imp_frm p1 p2 => interpret_frm env p1 -> interpret_frm env p2
  | All_frm y p1 => forall y_value : domain_of_discourse, interpret_frm (upd_env y y_value env) p1
  end.
Proof.
  destruct p; reflexivity.
Defined.

Lemma interpret_trm_ext (env : ivar -> domain_of_discourse) (env' : ivar -> domain_of_discourse) (t : trm L)
  (EQUIV : forall z : ivar, forall FREE : is_free_in_trm z t = true, env z = env' z)
  : interpret_trm env t = interpret_trm env' t
with interpret_trms_ext n (env : ivar -> domain_of_discourse) (env' : ivar -> domain_of_discourse) (ts : trms L n)
  (EQUIV: forall z : ivar, forall FREE : is_free_in_trms z ts = true, env z = env' z)
  : interpret_trms env ts = interpret_trms env' ts.
Proof.
  - induction t as [x | f ts | c]; simpl.
    + eapply EQUIV. unfold is_free_in_trm. rewrite Nat.eqb_eq. done.
    + f_equal. eapply interpret_trms_ext. ii. eapply EQUIV. done.
    + done.
  - induction ts as [ | n t ts IH]; simpl.
    + done.
    + erewrite interpret_trm_ext. erewrite IH. reflexivity.
      * ii. eapply EQUIV. rewrite is_free_in_trms_unfold. rewrite orb_true_iff. done.
      * ii. eapply EQUIV. rewrite is_free_in_trms_unfold. rewrite orb_true_iff. done. 
Qed.

Lemma interpret_frm_ext (env : ivar -> domain_of_discourse) (env' : ivar -> domain_of_discourse) (p : frm L)
  (EQUIV : forall z : ivar, forall FREE : is_free_in_frm z p = true, env z = env' z)
  : interpret_frm env p <-> interpret_frm env' p.
Proof.
  revert env env' EQUIV. frm_ind p; simpl; i.
  - erewrite interpret_trms_ext. reflexivity. ii. eapply EQUIV. done.
  - rewrite interpret_trm_ext with (env := env) (env' := env'). rewrite interpret_trm_ext with (env := env) (env' := env'). reflexivity.
    + ii. eapply EQUIV. rewrite orb_true_iff. done.
    + ii. eapply EQUIV. rewrite orb_true_iff. done.
  - done.
  - rewrite IH1. rewrite IH2. reflexivity.
    + ii. eapply EQUIV. rewrite orb_true_iff. done.
    + ii. eapply EQUIV. rewrite orb_true_iff. done.
  - unfold upd_env. split; i.
    + rewrite IH1 with (env' := fun z : ivar => if eq_dec z y then y_value else env z). done.
      intros z FREE. destruct (eq_dec z y) as [z_eq_y | z_ne_y]. done.
      symmetry. eapply EQUIV. rewrite andb_true_iff. rewrite negb_true_iff. rewrite Nat.eqb_neq. done.
    + rewrite IH1 with (env' := fun z : ivar => if eq_dec z y then y_value else env' z). done.
      intros z FREE. destruct (eq_dec z y) as [z_eq_y | z_ne_y]. done.
      eapply EQUIV. rewrite andb_true_iff. rewrite negb_true_iff. rewrite Nat.eqb_neq. done.
Qed.

Theorem substitution_lemma_trm (env : ivar -> domain_of_discourse) (s : subst L) (t : trm L)
  : interpret_trm (interpret_trm env ∘ s) t = interpret_trm env (subst_trm s t)
with substitution_lemma_trms n (env : ivar -> domain_of_discourse) (s : subst L) (ts : trms L n)
  : interpret_trms (interpret_trm env ∘ s) ts = interpret_trms env (subst_trms s ts).
Proof.
  - unfold "∘" in *. revert env s. induction t as [x | f ts | c]; i.
    + done.
    + rewrite interpret_trm_unfold. rewrite substitution_lemma_trms. done.
    + done.
  - unfold "∘" in *. revert env s. induction ts as [ | n t ts IH]; i.
    + done.
    + rewrite interpret_trms_unfold. rewrite IH. rewrite substitution_lemma_trm. done.
Qed.

Theorem substitution_lemma_frm (env : ivar -> domain_of_discourse) (s : subst L) (p : frm L)
  : interpret_frm (interpret_trm env ∘ s) p <-> interpret_frm env (subst_frm s p).
Proof.
  revert env s. frm_ind p; simpl; i.
  - f_equal. rewrite substitution_lemma_trms. done.
  - f_equal. do 2 rewrite substitution_lemma_trm. done.
  - done.
  - rewrite IH1. rewrite IH2. done.
  - unfold "∘" in *.
    enough (ENOUGH : forall v : domain_of_discourse, interpret_frm (fun z : ivar => if eq_dec z y then v else interpret_trm env (s z)) p1 <-> interpret_frm (fun z : ivar => if eq_dec z (chi_frm s (All_frm y p1)) then v else env z) (subst_frm (cons_subst y (Var_trm (chi_frm s (All_frm y p1))) s) p1)) by done. i.
    assert (claim1 : forall z : ivar, is_free_in_frm z p1 = true -> interpret_trm (fun x : ivar => if eq_dec x (chi_frm s (All_frm y p1)) then v else env x) (cons_subst y (Var_trm (chi_frm s (All_frm y p1))) s z) = (if eq_dec z y then v else interpret_trm env (s z))).
    { intros z FREE. unfold cons_subst. destruct (eq_dec z y) as [z_eq_y | z_ne_y].
      - transitivity ((fun x : ivar => if eq_dec x (chi_frm s (All_frm y p1)) then v else env x) (chi_frm s (All_frm y p1))); try reflexivity.
        destruct (eq_dec (chi_frm s (All_frm y p1)) (chi_frm s (All_frm y p1))); done.
      - eapply interpret_trm_ext. intros z' FREE'. destruct (eq_dec z' (chi_frm s (All_frm y p1))) as [EQ | NE]; try done. subst z'.
        enough (CONTRA: is_free_in_trm (chi_frm s (All_frm y p1)) (s z) = false) by done.
        assert (BUT := chi_frm_is_fresh_in_subst (All_frm y p1) s).
        unfold frm_is_fresh_in_subst in BUT. rewrite forallb_forall in BUT.
        specialize BUT with (x := z). simpl in BUT. rewrite L.in_remove_iff in BUT.
        rewrite fv_is_free_in_frm in BUT. specialize (BUT (conj FREE z_ne_y)).
        unfold "∘" in BUT. rewrite negb_true_iff in BUT. done.
    }
    symmetry. transitivity (interpret_frm (fun z : ivar => interpret_trm (fun w : ivar => if eq_dec w (chi_frm s (All_frm y p1)) then v else env w) (cons_subst y (Var_trm (chi_frm s (All_frm y p1))) s z)) p1). done. 
    symmetry. eapply interpret_frm_ext. done.
Qed.

Lemma interpret_trm_ext_upto (env : ivar -> domain_of_discourse) (env' : ivar -> domain_of_discourse) (t : trm L)
  (EQUIV : forall z : ivar, forall FREE : is_free_in_trm z t = true, env z == env' z)
  : interpret_trm env t == interpret_trm env' t
with interpret_trms_ext_upto n (env : ivar -> domain_of_discourse) (env' : ivar -> domain_of_discourse) (ts : trms L n)
  (EQUIV: forall z: ivar, forall FREE: is_free_in_trms z ts = true, env z == env' z)
  : interpret_trms env ts == interpret_trms env' ts.
Proof.
  - revert env env' EQUIV. induction t as [x | f ts | c]; simpl; i.
    + eapply EQUIV. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_eq. done.
    + eapply function_interpret_preserves_eqProp. eapply interpret_trms_ext_upto.
      ii. eapply EQUIV. done.
    + reflexivity.
  - revert env env' EQUIV. simpl. induction ts as [ | n t ts IH].
    + intros env env' EQUIV. Fin.case0.
    + intros env env' EQUIV. Fin.caseS i.
      * simpl. eapply interpret_trm_ext_upto.
        ii. eapply EQUIV. rewrite is_free_in_trms_unfold. rewrite orb_true_iff. done.
      * simpl. eapply IH. ii. eapply EQUIV. rewrite is_free_in_trms_unfold. rewrite orb_true_iff. done.
Qed.

Lemma interpret_frm_ext_upto (env : ivar -> domain_of_discourse) (env' : ivar -> domain_of_discourse) (p : frm L)
  (EQUIV : forall z : ivar, forall FREE : is_free_in_frm z p = true, env z == env' z)
  : interpret_frm env p <-> interpret_frm env' p.
Proof.
  revert env env' EQUIV. frm_ind p; simpl; i.
  - eapply relation_interpret_preserves_eqProp. eapply interpret_trms_ext_upto. done.
  - split; intros EQ.
    + rewrite interpret_trm_ext_upto. symmetry. rewrite interpret_trm_ext_upto. symmetry. exact EQ.
      * ii. symmetry. eapply EQUIV. rewrite orb_true_iff. done.
      * ii. symmetry. eapply EQUIV. rewrite orb_true_iff. done.
    + rewrite interpret_trm_ext_upto. symmetry. rewrite interpret_trm_ext_upto. symmetry. exact EQ.
      * ii. eapply EQUIV. rewrite orb_true_iff. done.
      * ii. eapply EQUIV. rewrite orb_true_iff. done.
  - done.
  - rewrite IH1. rewrite IH2. reflexivity.
    + ii. eapply EQUIV. rewrite orb_true_iff. done.
    + ii. eapply EQUIV. rewrite orb_true_iff. done.
  - unfold upd_env in *. split; intros H y_value.
    + rewrite IH1. exact (H y_value). simpl. ii.
      destruct (eq_dec z y) as [z_eq_y | z_ne_y].
      * done.
      * symmetry. eapply EQUIV. rewrite andb_true_iff. rewrite negb_true_iff. rewrite Nat.eqb_neq. done.
    + rewrite IH1. exact (H y_value). simpl. ii.
      destruct (eq_dec z y) as [z_eq_y | z_ne_y].
      * done.
      * eapply EQUIV. rewrite andb_true_iff. rewrite negb_true_iff. rewrite Nat.eqb_neq. done.
Qed.

Lemma not_free_no_effect_on_interpret_trm (env : ivar -> domain_of_discourse) (t : trm L) (y : ivar) (y_value : domain_of_discourse)
  (NOT_FREE : is_free_in_trm y t = false)
  : interpret_trm env t == interpret_trm (upd_env y y_value env) t
with not_free_no_effect_on_interpret_trms n (env : ivar -> domain_of_discourse) (ts: trms L n) (y: ivar) (y_value: domain_of_discourse)
  (NOT_FREE: is_free_in_trms y ts = false)
  : interpret_trms env ts == interpret_trms (upd_env y y_value env) ts.
Proof.
  - unfold upd_env. revert env y y_value NOT_FREE. induction t as [x | f ts | c]; simpl; i.
    + destruct (eq_dec x y) as [EQ | NE].
      * subst y. rewrite is_free_in_trm_unfold in NOT_FREE. rewrite Nat.eqb_neq in NOT_FREE. done.
      * reflexivity.
    + eapply function_interpret_preserves_eqProp. eapply not_free_no_effect_on_interpret_trms. done.
    + done.
  - unfold upd_env. revert env y y_value NOT_FREE. induction ts as [ | n t ts IH]; intros ? ? ? ?; [Fin.case0 | Fin.caseS i].
    * symmetry. rewrite interpret_trms_unfold. symmetry. simpl. eapply not_free_no_effect_on_interpret_trm. rewrite is_free_in_trms_unfold in NOT_FREE. rewrite orb_false_iff in NOT_FREE. done.
    * revert i. eapply IH. rewrite is_free_in_trms_unfold in NOT_FREE. rewrite orb_false_iff in NOT_FREE. done.
Qed.

Lemma not_free_no_effect_on_interpret_frm (env : ivar -> domain_of_discourse) (p : frm L) (y : ivar) (y_value : domain_of_discourse)
  (NOT_FREE : is_free_in_frm y p = false)
  : interpret_frm env p <-> interpret_frm (upd_env y y_value env) p.
Proof.
  unfold upd_env. revert env y y_value NOT_FREE. frm_ind p; simpl; i.
  - eapply relation_interpret_preserves_eqProp. eapply interpret_trms_ext_upto.
    ii. destruct (eq_dec z y) as [EQ | NE]. subst z. done. done.
  - enough (ENOUGH : interpret_trm env t1 == interpret_trm (fun z : ivar => if eq_dec z y then y_value else env z) t1 /\ interpret_trm env t2 == interpret_trm (fun z : ivar => if eq_dec z y then y_value else env z) t2).
    { destruct ENOUGH as [ENOUGH1 ENOUGH2]; rewrite ENOUGH1, ENOUGH2; done. }
    rewrite orb_false_iff in NOT_FREE. destruct NOT_FREE as [NOT_FREE1 NOT_FREE2]. split.
    + eapply interpret_trm_ext_upto. ii. destruct (eq_dec z y) as [EQ | NE]. subst z. done. done.
    + eapply interpret_trm_ext_upto. ii. destruct (eq_dec z y) as [EQ | NE]. subst z. done. done.
  - done.
  - rewrite orb_false_iff in NOT_FREE. rewrite IH1. rewrite IH2. reflexivity. done. done.
  - unfold upd_env in *. rename y0 into x, y_value into x_value. rewrite andb_false_iff in NOT_FREE. rewrite negb_false_iff in NOT_FREE. rewrite Nat.eqb_eq in NOT_FREE. destruct NOT_FREE as [NOT_FREE | x_eq_y].
    + specialize (IH1 env x x_value NOT_FREE). split; intros INTERPRET y_value.
      * rewrite interpret_frm_ext_upto. eapply INTERPRET. ii. simpl. destruct (eq_dec z y) as [EQ | NE].
        { reflexivity. }
        { destruct (eq_dec z x) as [z_eq_x | z_ne_x]; done. }
      * rewrite interpret_frm_ext_upto. eapply INTERPRET. ii. simpl. destruct (eq_dec z y) as [EQ | NE].
        { reflexivity. }
        { destruct (eq_dec z x) as [z_eq_x | z_ne_x]; done. }
    + subst y. split; intros INTERPRET y_value.
      * rewrite interpret_frm_ext_upto. eapply INTERPRET. simpl. ii. destruct (eq_dec z x) as [z_eq_x | z_ne_x].
        { reflexivity. }
        { destruct (eq_dec z x) as [EQ | NE]; done. }
      * rewrite interpret_frm_ext_upto. eapply INTERPRET. simpl. ii. destruct (eq_dec z x) as [z_eq_x | z_ne_x].
        { reflexivity. }
        { destruct (eq_dec z x) as [EQ | NE]; done. }
Qed.

Lemma rotate_witness (x : ivar) (y : ivar) (c : domain_of_discourse) (env : ivar -> domain_of_discourse) (p : frm L)
  (NOT_FREE : is_not_free_in_frm y p \/ y = x)
  : interpret_frm (upd_env x c env) p <-> interpret_frm (upd_env y c env) (subst_frm (one_subst x (Var_trm y)) p).
Proof.
  destruct NOT_FREE as [NOT_FREE | ->].
  - split.
    + intros INTERPRET. rewrite <- substitution_lemma_frm. eapply interpret_frm_ext_upto. 2: exact INTERPRET.
      ii. simpl. unfold one_subst, cons_subst, nil_subst, "∘", upd_env. destruct (eq_dec z x) as [z_eq_x | z_ne_x].
      * subst z. rewrite interpret_trm_unfold. destruct (eq_dec y y); try done.
      * rewrite interpret_trm_unfold. destruct (eq_dec z y) as [EQ | NE]; try done.
    + intros INTERPRET. rewrite <- substitution_lemma_frm in INTERPRET. eapply interpret_frm_ext_upto. 2: exact INTERPRET.
      ii. unfold one_subst, cons_subst, nil_subst, "∘", upd_env in *. destruct (eq_dec z x) as [z_eq_x | z_ne_x].
      * subst z. rewrite interpret_trm_unfold. destruct (eq_dec y y); try done.
      * rewrite interpret_trm_unfold. destruct (eq_dec z y) as [EQ | NE]; try done.
  - rewrite -> trivial_subst. rewrite <- substitution_lemma_frm. unfold nil_subst. split.
    + intros INTERPRET. eapply interpret_frm_ext_upto. 2: exact INTERPRET. simpl. ii. done.
    + intros INTERPRET. eapply interpret_frm_ext_upto. 2: exact INTERPRET. simpl. ii. done.
Qed.

Theorem alpha_equiv_compat_interpret_frm (p : frm L) (p' : frm L) (env : ivar -> domain_of_discourse)
  (ALPHA : p ≡ p')
  : interpret_frm env p <-> interpret_frm env p'.
Proof.
  revert env. induction ALPHA; simpl; i.
  - subst ts'. done.
  - subst t1' t2'. done.
  - done.
  - done.
  - split.
    { intros INTERPRET y_value. erewrite rotate_witness with (y := z).
      2:{ simpl in RFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in RFRESH. done. }
      rewrite <- IHALPHA. erewrite <- rotate_witness.
      + eapply INTERPRET.
      + simpl in LFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in LFRESH. done.
    }
    { intros INTERPRET y_value. erewrite rotate_witness with (y := z).
      2:{ simpl in LFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in LFRESH. done. }
      rewrite -> IHALPHA. erewrite <- rotate_witness.
      + eapply INTERPRET.
      + simpl in RFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in RFRESH. done.
    }
Qed.

End SEMANTICS.

Definition satisfies_frm {L : language} (STRUCTURE : structureOf L) (env : ivar -> domain_of_discourse) (p : frm L) : Prop :=
  interpret_frm STRUCTURE env p.

Definition satisfies_frms {L : language} (STRUCTURE : structureOf L) (env : ivar -> domain_of_discourse) (ps : ensemble (frm L)) : Prop :=
  forall p : frm L, forall H_IN : p \in ps, satisfies_frm STRUCTURE env p.

Definition entails {L : language} (Gamma : ensemble (frm L)) (C : frm L) : Prop :=
  forall STRUCTURE : structureOf L, forall env : ivar -> domain_of_discourse, forall SATISFY : satisfies_frms STRUCTURE env Gamma, satisfies_frm STRUCTURE env C.

Infix "⊧" := entails : type_scope.

#[global]
Add Parametric Morphism {L : language}
  : (@entails L) with signature (eqProp ==> eq ==> iff) as entails_upto.
Proof.
  intros Gamma1 Gamma2 EQ C. split.
  - ii. eapply H. done.
  - ii. eapply H. done.
Qed.

Lemma extend_entails {L : language} (Gamma: ensemble (@frm L)) (Gamma': ensemble (@frm L)) (C: frm L)
  (ENTAILS: Gamma ⊧ C)
  (SUBSET: Gamma \subseteq Gamma')
  : Gamma' ⊧ C.
Proof.
  ii. eapply ENTAILS. done.
Qed.
