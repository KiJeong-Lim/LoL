Require Import LoL.Prelude.Prelude.
Require Import LoL.Math.ThN.
Require Import LoL.Data.Vector.

Section SYNTAX.

#[local] Infix "\in" := E.elem.
#[local] Infix "\subseteq" := E.isSubsetOf.

Definition ivar : Set := nat.

Definition rename : Set := ivar -> ivar.

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
    fix trms_rec2_fix (n : nat) (ts : trms n) {struct ts} : forall ts' : trms n, phi n ts ts' :=
    match ts with
    | O_trms => fun ts' : trms O => trms_case0 _ phi_O ts'
    | S_trms n t ts => _
    end
  ).
  eapply trms_caseS. intros t' ts'. eapply phi_S. exact (trms_rec2_fix n ts ts').
Qed.

Fixpoint trms_to_vec {n : nat} (ts : trms n) : Vector.t trm n :=
  match ts with
  | O_trms => VNil
  | S_trms n' t ts => VCons n' t (trms_to_vec ts)
  end.

Lemma trms_to_vec_eq_iff n (ts : trms n) (ts' : trms n)
  : trms_to_vec ts = trms_to_vec ts' <-> ts = ts'.
Proof.
  split; intros EQ.
  - revert EQ. pattern n, ts, ts'. revert n ts ts'.
    eapply trms_rec2 with (phi := fun n => fun ts => fun ts' => @trms_to_vec n ts = @trms_to_vec n ts' -> ts = ts'); ii.
    + reflexivity.
    + simpl in H0. f_equal.
      * apply f_equal with (f := V.head) in H0. do 2 rewrite V.head_unfold in H0; eauto.
      * apply f_equal with (f := V.tail) in H0. do 2 rewrite V.tail_unfold in H0; eauto.
  - f_equal; eauto.
Qed.

Let uncons' (n : nat) (xs : trms (S n)) : S n = S n -> trm * trms n :=
  match xs in trms m return S n = m -> trm * trms (pred m) with
  | O_trms => fun H_eq : S n = O => S_eq_O_elim H_eq
  | S_trms n' x xs' => fun H_eq : S n = S n' => (x, xs')
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

Context `{function_symbols_isEnumerable : isEnumerable L.(function_symbols)} `{constant_symbols_isEnumerable : isEnumerable L.(constant_symbols)}.

Fixpoint gen_trm (seed : nat) (d : nat) {struct d} : trm :=
  match d with
  | O => Var_trm seed
  | S d' =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Con_trm (enum seed')
    | 1 => Fun_trm (enum seed2) (gen_trms seed3 d')
    | S (S i) => Var_trm i
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

Lemma gen_trm_unfold (seed : nat) (d : nat) :
  gen_trm seed d =
  match d with
  | O => Var_trm seed
  | S d' =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Con_trm (enum seed')
    | 1 => Fun_trm (enum seed2) (gen_trms seed3 d')
    | S (S i) => (Var_trm i)
    end
  end.
Proof.
  destruct d; reflexivity.
Defined.

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
Proof.
  destruct n, d; reflexivity.
Defined.

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
      exists (cpInv 1 (cpInv (proj1_sig (enum_spec f)) seed2)). rewrite gen_trm_unfold.
      destruct (cp (cpInv 1 (cpInv (proj1_sig (enum_spec f)) seed2))) as [x1 x2] eqn: H_OBS'.
      rewrite cp_spec in H_OBS'. apply cpInv_inj in H_OBS'. destruct H_OBS' as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_spec f)) seed2)) as [x2 y2] eqn: H_OBS''.
      rewrite cp_spec in H_OBS''. apply cpInv_inj in H_OBS''. destruct H_OBS'' as [<- <-].
      assert (claim : enum (proj1_sig (enum_spec f)) = f) by now destruct (enum_spec f).
      rewrite claim. rewrite H_OBS. reflexivity.
    + destruct d as [ | d']; [lia | assert (LE' : 0 <= d') by lia].
      exists (cpInv 0 (proj1_sig (enum_spec c))). rewrite gen_trm_unfold.
      destruct (cp (cpInv 0 (proj1_sig (enum_spec c)))) as [x1 x2] eqn: H_OBS'.
      assert (claim : enum (proj1_sig (enum_spec c)) = c) by now destruct (enum_spec c).
      rewrite cp_spec in H_OBS'. apply cpInv_inj in H_OBS'. destruct H_OBS' as [<- <-]. rewrite claim.
      destruct (cp (proj1_sig (enum_spec c))) as [x1 x2] eqn: H_OBS'. reflexivity.
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

#[local]
Instance trm_isEnumerable : isEnumerable trm :=
  { enum := enum_trm
  ; enum_spec := enum_trm_spec
  }.

#[local]
Instance trms_isEnumerable (n : arity) : isEnumerable (trms n) :=
  { enum := enum_trms
  ; enum_spec := enum_trms_spec n
  }.

Context `{relation_symbols_isEnumerable : isEnumerable L.(relation_symbols)}.

Fixpoint gen_frm (seed : nat) (d : nat) {struct d} : frm :=
  match d with
  | O =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Eqn_frm (enum seed2) (enum seed3)
    | _ => Rel_frm (enum seed2) (enum seed3)
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
      | 0 => Eqn_frm (enum seed2) (enum seed3)
      | _ => Rel_frm (enum seed2) (enum seed3)
      end
    end
  end.

Definition enum_frm (seed : nat) : frm :=
  let d := fst (cp seed) in
  let seed' := snd (cp seed) in
  gen_frm seed' d.

Lemma gen_frm_unfold (seed : nat) (d : nat) :
  gen_frm seed d =
  match d with
  | O =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Eqn_frm (enum seed2) (enum seed3)
    | _ => Rel_frm (enum seed2) (enum seed3)
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
      | 0 => Eqn_frm (enum seed2) (enum seed3)
      | _ => Rel_frm (enum seed2) (enum seed3)
      end
    end
  end.
Proof.
  destruct d; reflexivity.
Defined.

Lemma gen_frm_spec (p : frm) (d : nat)
  (LE : frm_depth p <= d)
  : { seed : nat | gen_frm seed d = p }.
Proof.
  revert d LE. induction p as [r ts | t1 t2 | p1 IH1 | p1 IH1 p2 IH2 | y p1 IH1]; simpl; i.
  - destruct d as [ | d'].
    + exists (cpInv 1 (cpInv (proj1_sig (enum_spec r)) (proj1_sig (enum_spec ts)))).
      rewrite gen_frm_unfold. destruct (cp (cpInv 1 (cpInv (proj1_sig (enum_spec r)) (proj1_sig (enum_spec ts))))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_spec r)) (proj1_sig (enum_spec ts)))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (enum_spec r) as [r_n H_r], (enum_spec ts) as [ts_n H_ts]; subst r ts. reflexivity.
    + exists (cpInv 4 (cpInv (proj1_sig (enum_spec r)) (proj1_sig (enum_spec ts)))).
      rewrite gen_frm_unfold. destruct (cp (cpInv 4 (cpInv (proj1_sig (enum_spec r)) (proj1_sig (enum_spec ts))))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_spec r)) (proj1_sig (enum_spec ts)))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (enum_spec r) as [r_n H_r], (enum_spec ts) as [ts_n H_ts]; subst r ts. reflexivity.
  - destruct d as [ | d'].
    + exists (cpInv 0 (cpInv (proj1_sig (enum_spec t1)) (proj1_sig (enum_spec t2)))).
      rewrite gen_frm_unfold. destruct (cp (cpInv 0 (cpInv (proj1_sig (enum_spec t1)) (proj1_sig (enum_spec t2))))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_spec t1)) (proj1_sig (enum_spec t2)))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (enum_spec t1) as [t1_n H_t1], (enum_spec t2) as [t2_n H_t2]; subst t1 t2. reflexivity.
    + exists (cpInv 3 (cpInv (proj1_sig (enum_spec t1)) (proj1_sig (enum_spec t2)))).
      rewrite gen_frm_unfold. destruct (cp (cpInv 3 (cpInv (proj1_sig (enum_spec t1)) (proj1_sig (enum_spec t2))))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_spec t1)) (proj1_sig (enum_spec t2)))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (enum_spec t1) as [t1_n H_t1], (enum_spec t2) as [t2_n H_t2]; subst t1 t2. reflexivity.
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

#[local]
Instance frms_isEnumerable : isEnumerable frm :=
  { enum := enum_frm
  ; enum_spec := enum_frm_spec
  }.

End ENUMERATION.

#[local] Open Scope program_scope.

Section FREE_VARIABLES.

Import ListNotations.

Fixpoint fvs_trm (t : trm) : list ivar :=
  match t with
  | Var_trm x => [x]
  | Fun_trm f ts => fvs_trms ts
  | Con_trm c => []
  end
with fvs_trms {n : nat} (ts : trms n) : list ivar :=
  match ts with
  | O_trms => []
  | S_trms n t ts => fvs_trm t ++ fvs_trms ts
  end.

Fixpoint fvs_frm (p : frm) : list ivar :=
  match p with
  | Rel_frm r ts => fvs_trms ts
  | Eqn_frm t1 t2 => fvs_trm t1 ++ fvs_trm t2
  | Neg_frm p1 => fvs_frm p1
  | Imp_frm p1 p2 => fvs_frm p1 ++ fvs_frm p2
  | All_frm y p1 => List.remove Nat.eq_dec y (fvs_frm p1)
  end.

Fixpoint is_free_in_trm (z : ivar) (t : trm) : bool :=
  match t with
  | Var_trm x => Nat.eqb x z
  | Fun_trm f ts => is_free_in_trms (n := L.(function_arity_table) f) z ts
  | Con_trm c => false
  end
with is_free_in_trms {n : nat} (z : ivar) (ts : trms n) : bool :=
  match ts with
  | O_trms => false
  | S_trms n t ts => is_free_in_trm z t || is_free_in_trms (n := n) z ts
  end.

Fixpoint is_free_in_frm (z : ivar) (p : frm) : bool :=
  match p with
  | Rel_frm R ts => is_free_in_trms (n := L.(relation_arity_table) R) z ts
  | Eqn_frm t1 t2 => is_free_in_trm z t1 || is_free_in_trm z t2
  | Neg_frm p1 => is_free_in_frm z p1
  | Imp_frm p1 p2 => is_free_in_frm z p1 || is_free_in_frm z p2
  | All_frm y p1 => is_free_in_frm z p1 && negb (Nat.eqb z y)
  end.

Definition fvs_frms (Gamma: ensemble frm) : ensemble ivar :=
  E.unions (E.image (E.finite ∘ fvs_frm) Gamma).

Definition is_not_free_in_trm (x : ivar) (t : trm) : Prop :=
  is_free_in_trm x t = false.

Definition is_not_free_in_trms {n : arity} (x : ivar) (ts : trms n) : Prop :=
  is_free_in_trms x ts = false.

Definition is_not_free_in_frm (x : ivar) (p : frm) : Prop :=
  is_free_in_frm x p = false.

Definition is_not_free_in_frms (x : ivar) (ps : ensemble frm) : Prop :=
  forall p, p \in ps -> is_free_in_frm x p = false.

End FREE_VARIABLES.

Section SUBSTITUTION. (* Reference: "https://github.com/ernius/formalmetatheory-stoughton/blob/master/Substitution.lagda", "https://github.com/ernius/formalmetatheory-stoughton/blob/master/SubstitutionLemmas.lagda" *)

Definition last_ivar_trm (t : trm) : ivar :=
  maxs (fvs_trm t).

Fixpoint last_ivar_trms {n : nat} (ts : trms n) : ivar :=
  match ts with
  | O_trms => 0
  | S_trms n t ts => max (last_ivar_trm t) (last_ivar_trms (n := n) ts)
  end.

Definition last_ivar_frm (p: frm) : ivar :=
  maxs (fvs_frm p).

Definition subst : Set := ivar -> trm.

Definition chi_frm (s : subst) (p : frm) : ivar :=
  1 + maxs (List.map (last_ivar_trm ∘ s) (fvs_frm p)).

Definition nil_subst : subst :=
  fun z : ivar => Var_trm z.

Definition cons_subst (y : ivar) (t : trm) (s : subst) : subst :=
  fun z : ivar => if Nat.eq_dec z y then t else s z.

Definition one_subst (x1 : ivar) (t1 : trm) : subst :=
  cons_subst x1 t1 nil_subst.

Fixpoint subst_trm (s : subst) (t : trm) : trm :=
  match t with
  | Var_trm x => s x
  | Fun_trm f ts => Fun_trm f (subst_trms s ts)
  | Con_trm c => Con_trm c
  end
with subst_trms {n: nat} (s : subst) (ts : trms n) : trms n :=
  match ts with
  | O_trms => O_trms
  | S_trms n t ts => S_trms n (subst_trm s t) (subst_trms (n := n) s ts) 
  end.

Fixpoint subst_frm (s : subst) (p : frm) : frm :=
  let chi : ivar := chi_frm s p in
  match p with
  | Rel_frm R ts => Rel_frm R (subst_trms s ts)
  | Eqn_frm t1 t2 => Eqn_frm (subst_trm s t1) (subst_trm s t2)
  | Neg_frm p1 => Neg_frm (subst_frm s p1)
  | Imp_frm p1 p2 => Imp_frm (subst_frm s p1) (subst_frm s p2)
  | All_frm y p1 => All_frm chi (subst_frm (cons_subst y (Var_trm chi) s) p1)
  end.

End SUBSTITUTION.

Section SINGLE_SUBSTITUTION.

End SINGLE_SUBSTITUTION.

Section ALPHA. (* Reference: "https://github.com/ernius/formalmetatheory-stoughton/blob/master/Alpha.lagda" *)

Inductive alpha_equiv : frm -> frm -> Prop :=
  | alpha_Rel_frm R ts ts'
    (EQ : ts = ts')
    : Rel_frm R ts ≡ Rel_frm R ts'
  | alpha_Eqn_frm t1 t2 t1' t2'
    (EQ1 : t1 = t1')
    (EQ2 : t2 = t2')
    : Eqn_frm t1 t2 ≡ Eqn_frm t1' t2'
  | alpha_Neg_frm p1 p1'
    (ALPHA1 : p1 ≡ p1')
    : Neg_frm p1 ≡ Neg_frm p1'
  | alpha_Imp_frm p1 p2 p1' p2'
    (ALPHA1 : p1 ≡ p1')
    (ALPHA2 : p2 ≡ p2')
    : Imp_frm p1 p2 ≡ Imp_frm p1' p2'
  | alpha_All_frm z y y' p1 p1'
    (ALPHA1 : subst_frm (one_subst y (Var_trm z)) p1 ≡ subst_frm (one_subst y' (Var_trm z)) p1')
    (LFRESH : is_free_in_frm z (All_frm y p1) = false)
    (RFRESH : is_free_in_frm z (All_frm y' p1') = false)
    : All_frm y p1 ≡ All_frm y' p1'
  where " p ≡ p' " := (alpha_equiv p p') : type_scope.

End ALPHA.

End SYNTAX.

#[global] Arguments trm : clear implicits.
#[global] Arguments trms : clear implicits.
#[global] Arguments frm : clear implicits.
#[global] Arguments subst : clear implicits.

#[global]
Tactic Notation "trm_ind" ident( t ) :=
  induction t as [x | f ts | c].

#[global]
Tactic Notation "trms_ind" ident( ts ) :=
  induction ts as [ | n t ts IH].

#[global]
Tactic Notation "frm_ind" ident( p ) :=
  induction p as [r ts | t1 t2 | p1 IH1 | p1 IH1 p2 IH2 | y p1 IH1].

#[global]
Tactic Notation "trm_ind2" ident( t ) ident( t' ) :=
  revert t'; induction t as [x | f ts | c]; intros [x' | f' ts' | c'].

#[global]
Tactic Notation "trms_ind2" ident( ts ) ident( ts' ) :=
  revert ts'; induction ts as [ | n t ts IH]; [intros ts'; pattern ts'; revert ts'; apply trms_case0 | intros ts'; pattern ts'; revert ts'; apply trms_caseS; intros t' ts'].

#[global]
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
  - pose proof Nat.eq_dec as ivar_hasEqDec.
    red in function_symbols_hasEqDec, constant_symbols_hasEqDec.
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
  pose proof Nat.eq_dec as ivar_hasEqDec. frm_ind2 p p'...
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
