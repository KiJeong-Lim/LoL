Require Import LoL.Prelude.Prelude.
Require Import LoL.Math.ThN.
Require Import LoL.Data.Vector.

Section SYNTAX.

Definition ivar : Set := nat.

Let arity : Set := nat.

#[projections(primitive)]
Record language : Type :=
  { function_symbols : Set
  ; constant_symbols : Set
  ; relation_symbols : Set
  ; function_arity_table : function_symbols -> arity
  ; relation_arity_table : relation_symbols -> arity
  }.

Context {L : language}.

Inductive trm : Set :=
  | Var_trm (x : ivar) : trm
  | Fun_trm (f : L.(function_symbols)) (ts : trms (L.(function_arity_table) f)) : trm
  | Con_trm (c : L.(constant_symbols)) : trm
with trms : arity -> Set :=
  | O_trms : trms O
  | S_trms (n : arity) (t : trm) (ts : trms n) : trms (S n).

Inductive frm : Set :=
  | Rel_frm (r : L.(relation_symbols)) (ts : trms (L.(relation_arity_table) r)) : frm
  | Eqn_frm (t1 : trm) (t2 : trm) : frm
  | Neg_frm (p1 : frm) : frm
  | Imp_frm (p1 : frm) (p2 : frm) : frm
  | All_frm (y : ivar) (p1 : frm) : frm.

Section trms_case.

Let cast (n : nat) (m : nat) (EQ : n = m) : trms n -> trms m :=
  match EQ with
  | eq_refl => fun xs => xs
  end.

Lemma trms_case0 (phi : trms O -> Type)
  (phi_nil : phi O_trms)
  : forall ts, phi ts.
Proof.
  refine (
    let claim1 (xs : trms O) : forall H_eq : O = O, phi (cast O O H_eq xs) :=
      match xs in trms m return forall H_eq : m = O, phi (cast m O H_eq xs) with
      | O_trms => fun H_eq : O = O => _
      | S_trms n x' xs' => fun H_eq : S n = O => _
      end
    in _
  ).
  { intros xs. exact (claim1 xs eq_refl). }
  Unshelve.
  - rewrite eq_pirrel_fromEqDec with (H_eq1 := H_eq) (H_eq2 := eq_refl).
    exact (phi_nil).
  - inversion H_eq.
Qed.

Lemma trms_caseS {n' : nat} (phi : trms (S n') -> Type)
  (phi_cons: forall t', forall ts', phi (S_trms n' t' ts'))
  : forall ts, phi ts.
Proof.
  refine (
    let claim1 (xs : trms (S n')) : forall H_eq : S n' = S n', phi (cast (S n') (S n') H_eq xs) :=
      match xs in trms m return forall H_eq : m = S n', phi (cast m (S n') H_eq xs) with
      | O_trms => fun H_eq: O = S n' => _
      | S_trms n x' xs' => fun H_eq: S n = S n' => _
      end
    in _
  ).
  { intros xs. exact (claim1 xs eq_refl). }
  Unshelve.
  - inversion H_eq.
  - pose proof (f_equal Nat.pred H_eq) as n_eq_n'. simpl in n_eq_n'. subst n'.
    rewrite eq_pirrel_fromEqDec with (H_eq1 := H_eq) (H_eq2 := eq_refl).
    exact (phi_cons x' xs').
Qed.

End trms_case.

Lemma trms_rec2 (phi : forall n : nat, trms n -> trms n -> Type)
  (phi_O: phi O O_trms O_trms)
  (phi_S: forall n, forall t, forall t', forall ts, forall ts', phi n ts ts' -> phi (S n) (S_trms n t ts) (S_trms n t' ts'))
  : forall n, forall ts, forall ts', phi n ts ts'.
Proof.
  refine (
    fix trms_rec2_fix (n : nat) (ts : trms n) {struct ts} : forall ts', phi n ts ts' :=
    match ts with
    | O_trms => fun ts' : trms O => trms_case0 _ phi_O ts'
    | S_trms n t ts => _
    end
  ).
  eapply trms_caseS. intros t' ts'. eapply phi_S. exact (trms_rec2_fix n ts ts').
Qed.

Fixpoint trms_to_vec {n : nat} (ts : trms n) : Vector.t trm n :=
  match ts with
  | O_trms => Vector.VNil
  | S_trms n' t ts => Vector.VCons n' t (trms_to_vec ts)
  end.

Lemma trms_to_vec_eq_iff n (ts : trms n) (ts' : trms n)
  : trms_to_vec ts = trms_to_vec ts' <-> ts = ts'.
Proof.
  split; intros EQ.
  - revert EQ. pattern n, ts, ts'. revert n ts ts'.
    eapply trms_rec2 with (phi := fun n => fun ts => fun ts' => @trms_to_vec n ts = @trms_to_vec n ts' -> ts = ts'); ii.
    + reflexivity.
    + simpl in H0. f_equal.
      * apply f_equal with (f := Vector.head) in H0. do 2 rewrite head_unfold in H0; eauto.
      * apply f_equal with (f := tail) in H0. do 2 rewrite tail_unfold in H0; eauto.
  - f_equal; eauto.
Qed.

Let uncons' (n : nat) (xs : trms (S n)) : S n = S n -> trm * trms n :=
  match xs in trms m return S n = m -> trm * trms (pred m) with
  | O_trms => fun H_eq: S n = O => S_eq_O_elim H_eq
  | S_trms n' x xs' => fun H_eq: S n = S n' => (x, xs')
  end.

Definition head {n : nat} (xs: trms (S n)) : trm :=
  fst (uncons' n xs eq_refl).

Definition tail {n : nat} (xs: trms (S n)) : trms n :=
  snd (uncons' n xs eq_refl).

Section ENUMERATION.

Fixpoint trm_depth (t : trm) : nat :=
  match t with
  | Var_trm x => 0
  | Fun_trm f ts => 1 + trms_depth ts
  | Con_trm c => 1
  end
with trms_depth {n : arity} (ts : trms n) : nat :=
  match ts with
  | O_trms => 0
  | S_trms _ t ts => 1 + max (trm_depth t) (trms_depth ts)
  end.

Fixpoint frm_depth (p: frm) : nat :=
  match p with
  | Rel_frm R ts => 0
  | Eqn_frm t1 t2 => 0
  | Neg_frm p1 => 1 + frm_depth p1
  | Imp_frm p1 p2 => 1 + max (frm_depth p1) (frm_depth p2)
  | All_frm y p1 => 1 + frm_depth p1
  end.

Variable enum_function_symbols : nat -> L.(function_symbols).

Variable enum_constant_symbols : nat -> L.(constant_symbols).

Fixpoint gen_trm (seed : nat) (d : nat) {struct d} : trm :=
  match d with
  | O => Var_trm seed
  | S d' =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Con_trm (enum_constant_symbols seed')
    | 1 => Fun_trm (enum_function_symbols seed2) (gen_trms seed3 d')
    | S (S i) => (Var_trm i)
    end
  end
with gen_trms {n : arity} (seed : nat) (d : nat) {struct d} : trms n :=
  match n with
  | O => O_trms
  | S n' =>
    match d with
    | O => nat_rec trms O_trms (fun m : nat => S_trms m (Var_trm seed)) (S n')
    | S d' =>
      let '(seed1, seed2) := cp seed in
      S_trms n' (gen_trm seed1 d') (gen_trms seed2 d')
    end
  end.

Definition enum_trm (seed : nat) : trm :=
  let d := fst (cp seed) in
  let seed' := snd (cp seed) in
  gen_trm seed' d.

Definition enum_trms {n : arity} (seed : nat) : trms n :=
  let d := fst (cp seed) in
  let seed' := snd (cp seed) in
  gen_trms seed' d.

Section PROOF1.

Lemma gen_trm_unfold (seed : nat) (d : nat) :
  gen_trm seed d =
  match d with
  | O => Var_trm seed
  | S d' =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Con_trm (enum_constant_symbols seed')
    | 1 => Fun_trm (enum_function_symbols seed2) (gen_trms seed3 d')
    | S (S i) => (Var_trm i)
    end
  end.
Proof. destruct d; reflexivity. Defined.

Lemma gen_trms_unfold (n : arity) (seed : nat) (d : nat) :
  gen_trms seed d =
  match n with
  | O => O_trms
  | S n' =>
    match d with
    | O => nat_rec trms O_trms (fun m : nat => S_trms m (Var_trm seed)) (S n')
    | S d' =>
      let '(seed1, seed2) := cp seed in
      S_trms n' (gen_trm seed1 d') (gen_trms seed2 d')
    end
  end.
Proof. destruct d, n; reflexivity. Defined.

Hypothesis enum_function_symbols_onto : forall f : L.(function_symbols), { n : nat | enum_function_symbols n = f }.
Hypothesis enum_constant_symbols_onto : forall c : L.(constant_symbols), { n : nat | enum_constant_symbols n = c }.

Lemma gen_trm_spec (t : trm) (d : nat)
  (LE : trm_depth t <= d)
  : { seed : nat | gen_trm seed d = t }
with gen_trms_spec (n : arity) (ts : trms n) (d : nat)
  (LE : trms_depth ts <= d)
  : { seed : nat | gen_trms seed d = ts }.
Proof.
  - revert d LE. induction t as [x | f ts | c]; simpl; i.
    + destruct d as [ | d'].
      * exists x. reflexivity.
      * simpl. exists (cpInv (2 + x) 0).
        destruct (cp (cpInv (2 + x) 0)) as [x1 x2] eqn: H_OBS.
        rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
        simpl. reflexivity.
    + destruct d as [ | d']; [lia | assert (LE' : trms_depth ts <= d') by lia].
      pose proof (gen_trms_spec _ ts d' LE') as [seed2 H_OBS].
      exists (cpInv 1 (cpInv (proj1_sig (enum_function_symbols_onto f)) seed2)). rewrite gen_trm_unfold.
      destruct (cp (cpInv 1 (cpInv (proj1_sig (enum_function_symbols_onto f)) seed2))) as [x1 x2] eqn: H_OBS'.
      rewrite cp_spec in H_OBS'. apply cpInv_inj in H_OBS'. destruct H_OBS' as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_function_symbols_onto f)) seed2)) as [x2 y2] eqn: H_OBS''.
      rewrite cp_spec in H_OBS''. apply cpInv_inj in H_OBS''. destruct H_OBS'' as [<- <-].
      assert (claim : enum_function_symbols (proj1_sig (enum_function_symbols_onto f)) = f) by now destruct (enum_function_symbols_onto f).
      rewrite claim. rewrite H_OBS. reflexivity.
    + destruct d as [ | d']; [lia | assert (LE' : 0 <= d') by lia].
      exists (cpInv 0 (proj1_sig (enum_constant_symbols_onto c))). rewrite gen_trm_unfold.
      destruct (cp (cpInv 0 (proj1_sig (enum_constant_symbols_onto c)))) as [x1 x2] eqn: H_OBS'.
      assert (claim: enum_constant_symbols (proj1_sig (enum_constant_symbols_onto c)) = c) by now destruct (enum_constant_symbols_onto c).
      rewrite cp_spec in H_OBS'. apply cpInv_inj in H_OBS'. destruct H_OBS' as [<- <-]. rewrite claim.
      destruct (cp (proj1_sig (enum_constant_symbols_onto c))) as [x1 x2] eqn: H_OBS'. reflexivity.
  - revert d LE. induction ts as [ | n t ts IH]; simpl; i.
    + simpl. exists 0. rewrite gen_trms_unfold. reflexivity.
    + destruct d as [ | d'].
      * lia.
      * assert (claim1 : trm_depth t <= d') by lia.
        assert (claim2 : trms_depth ts <= d') by lia.
        apply gen_trm_spec in claim1. apply IH in claim2.
        destruct claim1 as [seed1 P_t'], claim2 as [seed2 P_ts'].
        exists (cpInv seed1 seed2). rewrite <- P_t' at 1; rewrite <- P_ts' at 1. rewrite gen_trms_unfold.
        destruct (cp (cpInv seed1 seed2)) as [x y] eqn: H_OBS. rewrite cp_spec in H_OBS.
        apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. reflexivity.
Qed.

Theorem enum_trm_spec (t : trm)
  : { seed : nat | enum_trm seed = t }.
Proof.
  epose proof (gen_trm_spec t (trm_depth t) _) as [seed H_EQ].
  exists (cpInv (trm_depth t) seed). unfold enum_trm. destruct (cp (cpInv (trm_depth t) seed)) as [x y] eqn: H_OBS.
  rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. simpl. done.
  Unshelve. reflexivity.
Qed.

Theorem enum_trms_spec (n : arity) (ts : trms n)
  : { seed : nat | enum_trms seed = ts }.
Proof.
  epose proof (gen_trms_spec n ts (trms_depth ts) _) as [seed H_EQ].
  exists (cpInv (trms_depth ts) seed). unfold enum_trms. destruct (cp (cpInv (trms_depth ts) seed)) as [x y] eqn: H_OBS.
  rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. simpl. done.
  Unshelve. reflexivity.
Qed.

End PROOF1.

Variable enum_relation_symbols : nat -> L.(relation_symbols).

Fixpoint gen_frm (seed : nat) (d : nat) {struct d} : frm :=
  match d with
  | O =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Eqn_frm (enum_trm seed2) (enum_trm seed3)
    | _ => Rel_frm (enum_relation_symbols seed2) (enum_trms seed3)
    end
  | S d' =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Neg_frm (gen_frm seed' d')
    | 1 => Imp_frm (gen_frm seed2 d') (gen_frm seed3 d')
    | 2 => All_frm seed2 (gen_frm seed3 d')
    | S (S (S i)) =>
      match i with
      | 0 => Eqn_frm (enum_trm seed2) (enum_trm seed3)
      | _ => Rel_frm (enum_relation_symbols seed2) (enum_trms seed3)
      end
    end
  end.

Definition enum_frm (seed : nat) : frm :=
  let d := fst (cp seed) in
  let seed' := snd (cp seed) in
  gen_frm seed' d.

Section PROOF2.

Lemma gen_frm_unfold (seed : nat) (d : nat) :
  gen_frm seed d =
  match d with
  | O =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Eqn_frm (enum_trm seed2) (enum_trm seed3)
    | _ => Rel_frm (enum_relation_symbols seed2) (enum_trms seed3)
    end
  | S d' =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Neg_frm (gen_frm seed' d')
    | 1 => Imp_frm (gen_frm seed2 d') (gen_frm seed3 d')
    | 2 => All_frm seed2 (gen_frm seed3 d')
    | S (S (S i)) =>
      match i with
      | 0 => Eqn_frm (enum_trm seed2) (enum_trm seed3)
      | _ => Rel_frm (enum_relation_symbols seed2) (enum_trms seed3)
      end
    end
  end.
Proof. destruct d; reflexivity. Defined.

Hypothesis enum_function_symbols_onto : forall f : L.(function_symbols), { n : nat | enum_function_symbols n = f }.
Hypothesis enum_constant_symbols_onto : forall c : L.(constant_symbols), { n : nat | enum_constant_symbols n = c }.
Hypothesis enum_relation_symbols_onto : forall R : L.(relation_symbols), { n : nat | enum_relation_symbols n = R }.

Lemma gen_frm_spec (p : frm) (d : nat)
  (LE : frm_depth p <= d)
  : { seed : nat | gen_frm seed d = p }.
Proof.
  revert d LE. induction p as [r ts | t1 t2 | p1 IH1 | p1 IH1 p2 IH2 | y p1 IH1]; simpl; i.
  - destruct d as [ | d'].
    + exists (cpInv 1 (cpInv (proj1_sig (enum_relation_symbols_onto r)) (proj1_sig (enum_trms_spec enum_function_symbols_onto enum_constant_symbols_onto _ ts)))).
      rewrite gen_frm_unfold. destruct (cp (cpInv 1 (cpInv (proj1_sig (enum_relation_symbols_onto r)) (proj1_sig (enum_trms_spec enum_function_symbols_onto enum_constant_symbols_onto (L.(relation_arity_table) r) ts))))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_relation_symbols_onto r)) (proj1_sig (enum_trms_spec enum_function_symbols_onto enum_constant_symbols_onto (L.(relation_arity_table) r) ts)))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (enum_relation_symbols_onto r) as [r_n H_r], (enum_trms_spec enum_function_symbols_onto enum_constant_symbols_onto (L.(relation_arity_table) r) ts) as [ts_n H_ts]; subst r ts. reflexivity.
    + exists (cpInv 4 (cpInv (proj1_sig (enum_relation_symbols_onto r)) (proj1_sig (enum_trms_spec enum_function_symbols_onto enum_constant_symbols_onto _ ts)))).
      rewrite gen_frm_unfold. destruct (cp (cpInv 4 (cpInv (proj1_sig (enum_relation_symbols_onto r)) (proj1_sig (enum_trms_spec enum_function_symbols_onto enum_constant_symbols_onto (L.(relation_arity_table) r) ts))))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_relation_symbols_onto r)) (proj1_sig (enum_trms_spec enum_function_symbols_onto enum_constant_symbols_onto (L.(relation_arity_table) r) ts)))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (enum_relation_symbols_onto r) as [r_n H_r], (enum_trms_spec enum_function_symbols_onto enum_constant_symbols_onto (L.(relation_arity_table) r) ts) as [ts_n H_ts]; subst r ts. reflexivity.
  - destruct d as [ | d'].
    + exists (cpInv 0 (cpInv (proj1_sig (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t1)) (proj1_sig (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t2)))).
      rewrite gen_frm_unfold. destruct (cp (cpInv 0 (cpInv (proj1_sig (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t1)) (proj1_sig (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t2))))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t1)) (proj1_sig (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t2)))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t1) as [t1_n H_t1], (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t2) as [t2_n H_t2]; subst t1 t2. reflexivity.
    + exists (cpInv 3 (cpInv (proj1_sig (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t1)) (proj1_sig (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t2)))).
      rewrite gen_frm_unfold. destruct (cp (cpInv 3 (cpInv (proj1_sig (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t1)) (proj1_sig (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t2))))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t1)) (proj1_sig (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t2)))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t1) as [t1_n H_t1], (enum_trm_spec enum_function_symbols_onto enum_constant_symbols_onto t2) as [t2_n H_t2]; subst t1 t2. reflexivity.
  - destruct d as [ | d'].
    + lia.
    + assert (claim1 : frm_depth p1 <= d') by lia.
      apply IH1 in claim1. destruct claim1 as [seed1 H_seed1]. exists (cpInv 0 seed1).
      rewrite gen_frm_unfold. destruct (cp (cpInv 0 seed1)) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp seed1) as [x y]. congruence.
  - destruct d as [ | d'].
    + lia.
    + assert (claim1 : frm_depth p1 <= d') by lia.
      assert (claim2 : frm_depth p2 <= d') by lia.
      apply IH1 in claim1. apply IH2 in claim2. destruct claim1 as [seed1 H_seed1]. destruct claim2 as [seed2 H_seed2]. exists (cpInv 1 (cpInv seed1 seed2)).
      rewrite gen_frm_unfold. destruct (cp (cpInv 1 (cpInv seed1 seed2))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv seed1 seed2)) as [x y] eqn: H_OBS. rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. congruence.
  - destruct d as [ | d'].
    + lia.
    + assert (claim1 : frm_depth p1 <= d') by lia.
      apply IH1 in claim1. destruct claim1 as [seed1 H_seed1]. exists (cpInv 2 (cpInv y seed1)).
      rewrite gen_frm_unfold. destruct (cp (cpInv 2 (cpInv y seed1))) as [x z] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv y seed1)) as [x z] eqn: H_OBS. rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. congruence.
Qed.

Theorem enum_frm_spec (p : frm)
  : { x : nat | enum_frm x = p }.
Proof.
  epose proof (gen_frm_spec p (frm_depth p) _) as [seed H_EQ].
  exists (cpInv (frm_depth p) seed). unfold enum_frm. destruct (cp (cpInv (frm_depth p) seed)) as [x y] eqn: H_OBS.
  rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. simpl. done.
  Unshelve. reflexivity.
Qed.

End PROOF2.

End ENUMERATION.

Section INSTANCES.

#[local]
Instance trm_isEnumerable `(function_symbols_isEnumerable : isEnumerable L.(function_symbols)) `(constant_symbols_isEnumerable : isEnumerable L.(constant_symbols)) : isEnumerable trm :=
  { enum := enum_trm function_symbols_isEnumerable.(enum) constant_symbols_isEnumerable.(enum)
  ; enum_spec := enum_trm_spec function_symbols_isEnumerable.(enum) constant_symbols_isEnumerable.(enum) function_symbols_isEnumerable.(enum_spec) constant_symbols_isEnumerable.(enum_spec)
  }.

#[local]
Instance trms_isEnumerable `(function_symbols_isEnumerable : isEnumerable L.(function_symbols)) `(constant_symbols_isEnumerable : isEnumerable L.(constant_symbols)) (n : arity) : isEnumerable (trms n) :=
  { enum := enum_trms function_symbols_isEnumerable.(enum) constant_symbols_isEnumerable.(enum)
  ; enum_spec := enum_trms_spec function_symbols_isEnumerable.(enum) constant_symbols_isEnumerable.(enum) function_symbols_isEnumerable.(enum_spec) constant_symbols_isEnumerable.(enum_spec) n
  }.

#[local]
Instance frms_isEnumerable `(function_symbols_isEnumerable : isEnumerable L.(function_symbols)) `(constant_symbols_isEnumerable : isEnumerable L.(constant_symbols)) `(relation_symbols_isEnumerable : isEnumerable L.(relation_symbols)) : isEnumerable frm :=
  { enum := enum_frm function_symbols_isEnumerable.(enum) constant_symbols_isEnumerable.(enum) relation_symbols_isEnumerable.(enum)
  ; enum_spec := enum_frm_spec function_symbols_isEnumerable.(enum) constant_symbols_isEnumerable.(enum) relation_symbols_isEnumerable.(enum) function_symbols_isEnumerable.(enum_spec) constant_symbols_isEnumerable.(enum_spec) relation_symbols_isEnumerable.(enum_spec)
  }.

End INSTANCES.

End SYNTAX.

#[global] Arguments trm : clear implicits.
#[global] Arguments trms : clear implicits.
#[global] Arguments frm : clear implicits.

Tactic Notation "trm_ind" ident( t ) :=
  induction t as [x | f ts | c].

Tactic Notation "trms_ind" ident( ts ) :=
  induction ts as [ | n t ts IH].

Tactic Notation "frm_ind" ident( p ) :=
  induction p as [r ts | t1 t2 | p1 IH1 | p1 IH1 p2 IH2 | y p1 IH1].

Tactic Notation "trm_ind2" ident( t ) ident( t' ) :=
  revert t'; induction t as [x | f ts | c]; intros [x' | f' ts' | c'].

Tactic Notation "trms_ind2" ident( ts ) ident( ts' ) :=
  revert ts'; induction ts as [ | n t ts IH]; [intros ts'; pattern ts'; revert ts'; apply trms_case0 | intros ts'; pattern ts'; revert ts'; apply trms_caseS; intros t' ts'].

Tactic Notation "frm_ind2" ident( p ) ident( p' ) :=
  revert p';
  induction p as [r ts | t1 t2 | p1 IH1 | p1 IH1 p2 IH2 | y p1 IH1];
  intros [r' ts' | t1' t2' | p1' | p1' p2' | y' p1'].

Section EQ_DEC.

Context {L : language}.

Hypothesis function_symbols_hasEqDec : hasEqDec L.(function_symbols).

Hypothesis constant_symbols_hasEqDec : hasEqDec L.(constant_symbols).

Lemma trm_eq_dec (t1 : trm L) (t2 : trm L)
  : {t1 = t2} + {t1 <> t2}
with trms_eq_dec n (ts1 : trms L n) (ts2 : trms L n)
  : {ts1 = ts2} + {ts1 <> ts2}.
Proof with try first [now right; congruence | now left; congruence].
  - pose proof nat_hasEqDec as ivar_hasEqDec.
    red in ivar_hasEqDec, function_symbols_hasEqDec, constant_symbols_hasEqDec.
    clear trm_eq_dec. trm_ind2 t1 t2...
    + pose proof (ivar_hasEqDec x x') as [? | ?]...
    + pose proof (function_symbols_hasEqDec f f') as [f_eq_f' | f_ne_f']...
      subst f'. pose proof (trms_eq_dec (L.(function_arity_table) f) ts ts') as [EQ | NE]...
      right. intros CONTRA. eapply NE. inv CONTRA.
      apply @projT2_eq_fromEqDec with (B := fun f : function_symbols L => trms L (L.(function_arity_table) f)) in H0.
      * exact H0.
      * exact function_symbols_hasEqDec.
    + pose proof (constant_symbols_hasEqDec c c') as [? | ?]...
  - clear trms_eq_dec. trms_ind2 ts1 ts2...
    pose proof (trm_eq_dec t t') as [? | ?]; pose proof (IH ts2) as [EQ | NE]...
    right. intros CONTRA. eapply NE. inv CONTRA.
    apply @projT2_eq_fromEqDec with (B := fun n: nat => trms L n) in H1.
    + exact H1.
    + exact nat_hasEqDec.
Defined.

#[global] Instance trm_hasEqDec : hasEqDec (trm L) := trm_eq_dec.
#[global] Instance trms_hasEqDec (n : nat) : hasEqDec (trms L n) := trms_eq_dec n.

Hypothesis relation_symbols_hasEqDec : hasEqDec L.(relation_symbols).

Lemma frm_eq_dec (p : frm L) (p' : frm L)
  : {p = p'} + {p <> p'}.
Proof with try first [now right; congruence | now left; congruence].
  pose proof nat_hasEqDec as ivar_hasEqDec. red in ivar_hasEqDec. frm_ind2 p p'...
  - pose proof (relation_symbols_hasEqDec r r') as [r_eq_r' | r_ne_r']...
    subst r'. pose proof (trms_eq_dec (L.(relation_arity_table) r) ts ts') as [EQ | NE]...
    right. intros CONTRA. eapply NE. inv CONTRA.
    apply @projT2_eq_fromEqDec with (B := fun r : relation_symbols L => trms L (L.(relation_arity_table) r)) in H0.
    + exact H0.
    + exact relation_symbols_hasEqDec.
  - pose proof (trm_eq_dec t1 t1') as [? | ?]; pose proof (trm_eq_dec t2 t2') as [? | ?]...
  - pose proof (IH1 p1') as [? | ?]...
  - pose proof (IH1 p1') as [? | ?]; pose proof (IH2 p2') as [? | ?]...
  - pose proof (ivar_hasEqDec y y') as [? | ?]; pose proof (IH1 p1') as [? | ?]...
Defined.

#[global] Instance frm_hasEqDec : hasEqDec (frm L) := frm_eq_dec.

End EQ_DEC.
