Require Import LoL.Prelude.Prelude.
Require Import LoL.Prelude.Notations.
Require Import LoL.Math.ThN.
Require Import LoL.Data.Vector.

#[local] Infix "\in" := E.elem.
#[local] Infix "\subseteq" := E.isSubsetOf.

Section SYNTAX.

Definition ivar : Set := nat.

Definition renaming : Set := list (ivar * ivar).

Fixpoint rename_var (eta : renaming) (x : ivar) : ivar := 
  match eta with
  | [] => x
  | (x', y) :: eta' => if eq_dec x x' then y else rename_var eta' x
  end.

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
  | Rel_frm (R : L.(relation_symbols)) (ts : trms (L.(relation_arity_table) R)) : frm
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
Unshelve.
  reflexivity.
Qed.

Theorem enum_trms_spec (n : arity) (ts : trms n)
  : { seed : nat | enum_trms seed = ts }.
Proof.
  epose proof (gen_trms_spec n ts (trms_depth ts) _) as [seed H_EQ].
  exists (cpInv (trms_depth ts) seed). unfold enum_trms. destruct (cp (cpInv (trms_depth ts) seed)) as [x y] eqn: H_OBS.
  rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. simpl. done.
Unshelve.
  reflexivity.
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
Unshelve.
  reflexivity.
Qed.

#[local]
Instance frms_isEnumerable : isEnumerable frm :=
  { enum := enum_frm
  ; enum_spec := enum_frm_spec
  }.

End ENUMERATION.

Lemma frm_depth_lt_ind (P : frm -> Prop)
  (IND: forall p : frm, forall IH : forall p' : frm, forall RANK_LT : frm_depth p' < frm_depth p, P p', P p)
  : forall p : frm, P p.
Proof.
  eapply @B.transfinite_induction with (R := fun p' : frm => fun p : frm => frm_depth p' < frm_depth p).
  - eapply B.preimage_preserves_wf. exact lt_wf.
  - exact IND.
Defined.

#[local]
Tactic Notation "trm_ind" ident( t ) :=
  induction t as [x | f ts | c].

#[local]
Tactic Notation "trms_ind" ident( ts ) :=
  induction ts as [ | n t ts IH].

#[local]
Tactic Notation "frm_ind" ident( p ) :=
  induction p as [R ts | t1 t2 | p1 IH1 | p1 IH1 p2 IH2 | y p1 IH1].

#[local]
Tactic Notation "trm_ind2" ident( t ) ident( t' ) :=
  revert t'; induction t as [x | f ts | c]; intros [x' | f' ts' | c'].

#[local]
Tactic Notation "trms_ind2" ident( ts ) ident( ts' ) :=
  revert ts'; induction ts as [ | n t ts IH]; [intros ts'; pattern ts'; revert ts'; apply trms_case0 | intros ts'; pattern ts'; revert ts'; apply trms_caseS; intros t' ts'].

#[local]
Tactic Notation "frm_ind2" ident( p ) ident( p' ) :=
  revert p';
  induction p as [R ts | t1 t2 | p1 IH1 | p1 IH1 p2 IH2 | y p1 IH1];
  intros [R' ts' | t1' t2' | p1' | p1' p2' | y' p1'].

#[local] Open Scope program_scope.

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
  | All_frm y p1 => List.remove eq_dec y (fvs_frm p1)
  end.

Lemma fvs_trm_unfold (t : trm) :
  fvs_trm t =
  match t with
  | Var_trm x => [x]
  | Fun_trm f ts => fvs_trms ts
  | Con_trm c => []
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma fvs_trms_unfold (n : arity) (ts : trms n) :
  fvs_trms ts =
  match ts with
  | O_trms => []
  | S_trms n t ts => fvs_trm t ++ fvs_trms (n := n) ts
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Lemma fvs_frm_unfold (p : frm) :
  fvs_frm p =
  match p with
  | Rel_frm r ts => fvs_trms ts
  | Eqn_frm t1 t2 => fvs_trm t1 ++ fvs_trm t2
  | Neg_frm p1 => fvs_frm p1
  | Imp_frm p1 p2 => fvs_frm p1 ++ fvs_frm p2
  | All_frm y p1 => List.remove eq_dec y (fvs_frm p1)
  end.
Proof.
  destruct p; reflexivity.
Defined.

#[local] Hint Rewrite fvs_trm_unfold : core.
#[local] Hint Rewrite fvs_trms_unfold : core.
#[local] Hint Rewrite fvs_frm_unfold : core.

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

Lemma is_free_in_trm_unfold (z : ivar) (t : trm) :
  is_free_in_trm z t =
  match t with
  | Var_trm x => Nat.eqb x z
  | Fun_trm f ts => is_free_in_trms z ts
  | Con_trm c => false
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma is_free_in_trms_unfold (n : arity) (z : ivar) (ts : trms n) :
  is_free_in_trms z ts =
  match ts with
  | O_trms => false
  | S_trms _ t ts => is_free_in_trm z t || is_free_in_trms z ts
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Lemma is_free_in_frm_unfold (z : ivar) (p : frm) :
  is_free_in_frm z p =
  match p with
  | Rel_frm R ts => is_free_in_trms z ts
  | Eqn_frm t1 t2 => is_free_in_trm z t1 || is_free_in_trm z t2
  | Neg_frm p1 => is_free_in_frm z p1
  | Imp_frm p1 p2 => is_free_in_frm z p1 || is_free_in_frm z p2
  | All_frm y p1 => is_free_in_frm z p1 && negb (Nat.eqb z y)
  end.
Proof.
  destruct p; reflexivity.
Defined.

#[local] Hint Rewrite is_free_in_trm_unfold : core.
#[local] Hint Rewrite is_free_in_trms_unfold : core.
#[local] Hint Rewrite is_free_in_frm_unfold : core.

Lemma fv_is_free_in_trm (t : trm)
  : forall z, In z (fvs_trm t) <-> is_free_in_trm z t = true
with fv_is_free_in_trms n (ts : trms n)
  : forall z, In z (fvs_trms ts) <-> is_free_in_trms z ts = true.
Proof.
  - trm_ind t. simpl; i.
    + rewrite Nat.eqb_eq. done.
    + split.
      * intros H_IN. eapply fv_is_free_in_trms. done.
      * intros FREE. eapply fv_is_free_in_trms. done.
    + done.
  - trms_ind ts; simpl; i.
    + done.
    + rewrite in_app_iff. rewrite orb_true_iff. rewrite IH. done.
Qed.

Lemma fv_is_free_in_frm (p : frm)
  : forall z, In z (fvs_frm p) <-> is_free_in_frm z p = true.
Proof.
  frm_ind p; simpl; i; (try rewrite in_app_iff); (try rewrite orb_true_iff); try now firstorder.
  - rewrite fv_is_free_in_trms; done.
  - do 2 rewrite fv_is_free_in_trm; done.
  - rewrite andb_true_iff. rewrite negb_true_iff. rewrite Nat.eqb_neq. rewrite L.in_remove_iff. done.
Qed.

Definition is_not_free_in_trm (x : ivar) (t : trm) : Prop :=
  is_free_in_trm x t = false.

Definition is_not_free_in_trms {n : arity} (x : ivar) (ts : trms n) : Prop :=
  is_free_in_trms x ts = false.

Definition is_not_free_in_frm (x : ivar) (p : frm) : Prop :=
  is_free_in_frm x p = false.

Definition is_not_free_in_frms (x : ivar) (ps : ensemble frm) : Prop :=
  forall p, p \in ps -> is_free_in_frm x p = false.

Definition fvs_frms (Gamma : ensemble frm) : ensemble ivar :=
  E.unions (E.image (E.finite ∘ fvs_frm) Gamma).

Section SUBSTITUTION. (* Reference: "https://github.com/ernius/formalmetatheory-stoughton/blob/master/Substitution.lagda", "https://github.com/ernius/formalmetatheory-stoughton/blob/master/SubstitutionLemmas.lagda" *)

Definition last_ivar_trm (t : trm) : ivar :=
  maxs (fvs_trm t).

Fixpoint last_ivar_trms {n : nat} (ts : trms n) : ivar :=
  match ts with
  | O_trms => 0
  | S_trms n t ts => max (last_ivar_trm t) (last_ivar_trms (n := n) ts)
  end.

Definition last_ivar_frm (p : frm) : ivar :=
  maxs (fvs_frm p).

Definition subst : Set :=
  ivar -> trm.

Definition chi_frm (s : subst) (p : frm) : ivar :=
  1 + maxs (List.map (last_ivar_trm ∘ s) (fvs_frm p)).

Definition nil_subst : subst :=
  fun z : ivar => Var_trm z.

Definition cons_subst (y : ivar) (t : trm) (s : subst) : subst :=
  fun z : ivar => if eq_dec z y then t else s z.

Definition one_subst (x1 : ivar) (t1 : trm) : subst :=
  cons_subst x1 t1 nil_subst.

Fixpoint subst_trm (s : subst) (t : trm) : trm :=
  match t with
  | Var_trm x => s x
  | Fun_trm f ts => Fun_trm f (subst_trms s ts)
  | Con_trm c => Con_trm c
  end
with subst_trms {n : arity} (s : subst) (ts : trms n) : trms n :=
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

Definition subst_compose (s : subst) (s' : subst) : subst :=
  fun z : ivar => subst_trm s' (s z).

Lemma subst_trm_unfold (s : subst) (t : trm) :
  subst_trm s t =
  match t with
  | Var_trm x => s x
  | Fun_trm f ts => Fun_trm f (subst_trms s ts)
  | Con_trm c => Con_trm c
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma subst_trms_unfold n (s : subst) (ts : trms n) :
  subst_trms s ts =
  match ts with
  | O_trms => O_trms
  | S_trms n t ts => S_trms n (subst_trm s t) (subst_trms s ts) 
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Lemma subst_frm_unfold (s : subst) (p : frm) :
  subst_frm s p =
  match p with
  | Rel_frm R ts => Rel_frm R (subst_trms s ts)
  | Eqn_frm t1 t2 => Eqn_frm (subst_trm s t1) (subst_trm s t2)
  | Neg_frm p1 => Neg_frm (subst_frm s p1)
  | Imp_frm p1 p2 => Imp_frm (subst_frm s p1) (subst_frm s p2)
  | All_frm y p1 =>
    let z : ivar := chi_frm s p in
    All_frm z (subst_frm (cons_subst y (Var_trm z) s) p1)
  end.
Proof.
  destruct p; reflexivity.
Defined.

Lemma last_ivar_trms_eq_maxs_fvs n (ts : trms n)
  : last_ivar_trms ts = maxs (fvs_trms ts).
Proof.
  trms_ind ts; simpl.
  - done.
  - rewrite maxs_app. done.
Qed.

Lemma last_ivar_trm_gt (t : trm) (z : ivar)
  (GT : z > last_ivar_trm t)
  : is_free_in_trm z t = false
with last_ivar_trms_gt n (ts : trms n) (z : ivar)
  (GT : z > last_ivar_trms ts)
  : is_free_in_trms z ts = false.
Proof.
  - revert z GT. unfold last_ivar_trm. trm_ind t; simpl; i.
    + rewrite Nat.eqb_neq. done.
    + eapply last_ivar_trms_gt. rewrite last_ivar_trms_eq_maxs_fvs. done.
    + done.
  - revert z GT. induction ts as [ | n t ts IH]; simpl; i.
    + done.
    + rewrite orb_false_iff. split.
      * eapply last_ivar_trm_gt. done.
      * eapply IH. done.
Qed.

Lemma last_ivar_frm_gt (p : frm) (z: ivar)
  (GT : z > last_ivar_frm p)
  : is_free_in_frm z p = false.
Proof.
  enough (ENOUGH : ~ In z (fvs_frm p)).
  { rewrite fv_is_free_in_frm in ENOUGH. rewrite not_true_iff_false in ENOUGH. done. }
  pose proof (in_maxs_ge (fvs_frm p)) as claim1. intros CONTRA.
  apply claim1 in CONTRA. unfold last_ivar_frm in GT. done.
Qed.

Lemma chi_frm_not_free (s : subst) (p : frm) (x : ivar)
  (FREE : is_free_in_frm x p = true)
  : is_free_in_trm (chi_frm s p) (s x) = false.
Proof.
  enough (ENOUGH : last_ivar_trm (s x) < chi_frm s p) by now eapply last_ivar_trm_gt.
  unfold chi_frm. simpl. unfold "<". apply fv_is_free_in_frm in FREE.
  enough (TO_SHOW : last_ivar_trm (s x) <= maxs (List.map (last_ivar_trm ∘ s) (fvs_frm p))) by done.
  eapply in_maxs_ge. unfold "∘". eapply in_map_iff. done.
Qed.

Definition frm_is_fresh_in_subst (x : ivar) (s : subst) (p : frm) : bool :=
  L.forallb (negb ∘ is_free_in_trm x ∘ s) (fvs_frm p).

Theorem chi_frm_is_fresh_in_subst (p : frm) (s : subst)
  : frm_is_fresh_in_subst (chi_frm s p) s p = true.
Proof.
  unfold frm_is_fresh_in_subst. rewrite forallb_forall. ii.
  unfold "∘". rewrite negb_true_iff. eapply chi_frm_not_free.
  rewrite <- fv_is_free_in_frm. done.
Qed.

Lemma chi_frm_nil (p : frm)
  : is_free_in_frm (chi_frm nil_subst p) p = false.
Proof.
  pose proof (chi_frm_is_fresh_in_subst p nil_subst) as claim1.
  unfold frm_is_fresh_in_subst in claim1.
  eapply not_true_iff_false. intros CONTRA. 
  rewrite forallb_forall in claim1. unfold "∘" in claim1. simpl in claim1.
  rewrite <- fv_is_free_in_frm in CONTRA. apply claim1 in CONTRA.
  rewrite negb_true_iff, Nat.eqb_neq in CONTRA. contradiction.
Qed.

Definition trm_is_fresh_in_subst (x : ivar) (s : subst) (t : trm) : bool :=
  L.forallb (negb ∘ is_free_in_trm x ∘ s) (fvs_trm t).

Definition trms_is_fresh_in_subst {n : arity} (x : ivar) (s : subst) (ts : trms n) : bool :=
  L.forallb (negb ∘ is_free_in_trm x ∘ s) (fvs_trms ts).

Theorem trm_is_fresh_in_subst_iff (t : trm) (z : ivar) (s : subst)
  : trm_is_fresh_in_subst z s t = true <-> is_free_in_trm z (subst_trm s t) = false
with trms_is_fresh_in_subst_iff n (ts : trms n) (z : ivar) (s : subst)
  : trms_is_fresh_in_subst z s ts = true <-> is_free_in_trms z (subst_trms s ts) = false.
Proof.
  - unfold trm_is_fresh_in_subst. unfold "∘". revert z s. trm_ind t; simpl; i.
    + split; intros H; [rewrite andb_true_iff in H; destruct H as [H _]; rewrite negb_true_iff in H; done| rewrite andb_true_iff; split; [rewrite negb_true_iff; done | done]].
    + eapply trms_is_fresh_in_subst_iff.
    + done.
  - unfold trms_is_fresh_in_subst. revert z s. trms_ind ts; simpl; i.
    + done.
    + rewrite forallb_app. rewrite orb_false_iff. rewrite andb_true_iff. done. 
Qed.

Theorem frm_is_fresh_in_subst_iff (p : frm) (z : ivar) (s : subst)
  : frm_is_fresh_in_subst z s p = true <-> is_free_in_frm z (subst_frm s p) = false.
Proof.
  revert z s. unfold frm_is_fresh_in_subst. frm_ind p; simpl; ii.
  - eapply trms_is_fresh_in_subst_iff.
  - rewrite orb_false_iff. do 2 rewrite <- trm_is_fresh_in_subst_iff.
    unfold frm_is_fresh_in_subst. simpl. rewrite forallb_app. rewrite andb_true_iff. done.
  - done.
  - rewrite forallb_app. rewrite orb_false_iff. rewrite andb_true_iff. done.
  - split.
    + intros H_forallb. rewrite andb_false_iff.
      destruct (z =? chi_frm s (All_frm y p1))%nat as [ | ] eqn: OBS.
      { simpl. right. done. }
      { left. rewrite Nat.eqb_neq in OBS. eapply IH1. rewrite forallb_forall.
        intros x x_in. unfold "∘". rewrite negb_true_iff. unfold cons_subst.
        destruct (eq_dec x y) as [H_eq | H_ne].
        - destruct (is_free_in_trm z (Var_trm (chi_frm s (All_frm y p1)))) as [ | ] eqn: EQ.
          + contradiction OBS. symmetry. subst y. rewrite <- fv_is_free_in_trm in EQ.
            simpl in EQ. done.
          + done.
        - rewrite forallb_forall in H_forallb. unfold "∘" in H_forallb.
          rewrite <- negb_true_iff. eapply H_forallb. eapply L.in_remove_iff. done.
      }
    + rewrite andb_false_iff. rewrite negb_false_iff. rewrite Nat.eqb_eq. unfold "∘" in *. intros [NOT_FREE | ->].
      { eapply IH1 in NOT_FREE. rewrite forallb_forall in NOT_FREE. rewrite forallb_forall.
        intros x x_in. rewrite negb_true_iff. rewrite L.in_remove_iff in x_in. destruct x_in as [x_in x_ne_y].
        apply NOT_FREE in x_in. rewrite negb_true_iff in x_in. unfold cons_subst in x_in.
        destruct (eq_dec x y) as [H_eq | H_ne]; try done.
      }
      { rewrite forallb_forall. intros x x_in. apply L.in_remove_iff in x_in. destruct x_in as [x_in x_ne_y].
        rewrite negb_true_iff. eapply chi_frm_not_free. simpl. rewrite andb_true_iff.
        split; [rewrite fv_is_free_in_frm in x_in | rewrite negb_true_iff, Nat.eqb_neq]; done.
      }
Qed.

Definition equiv_subst_in_frm (s1 : subst) (s2 : subst) (p : frm) : Prop :=
  forall z : ivar, forall FREE : is_free_in_frm z p = true, s1 z = s2 z.

Lemma chi_frm_compat_equiv_subst (s1 : subst) (s2 : subst) (p : frm)
  (EQUIV : equiv_subst_in_frm s1 s2 p)
  : chi_frm s1 p = chi_frm s2 p.
Proof.
  unfold chi_frm. f_equal. eapply maxs_ext. intros n. unfold "∘".
  split; intros H_in; eapply in_map_iff; apply in_map_iff in H_in; destruct H_in as [x [<- H_in]].
  - exists x. rewrite -> EQUIV; try done.
    rewrite fv_is_free_in_frm in H_in. done.
  - exists x. rewrite <- EQUIV; try done.
    rewrite fv_is_free_in_frm in H_in. done.
Qed.

Lemma equiv_subst_in_trm_implies_subst_trm_same (s1 : subst) (s2 : subst) (t : trm)
  (EQUIV : forall z : ivar, forall FREE : is_free_in_trm z t = true, s1 z = s2 z)
  : subst_trm s1 t = subst_trm s2 t
with equiv_subst_in_trms_implies_subst_trms_same n (s1 : subst) (s2 : subst) (ts : trms n)
  (EQUIV : forall z : ivar, forall FREE : is_free_in_trms z ts = true, s1 z = s2 z)
  : subst_trms s1 ts = subst_trms s2 ts.
Proof.
  - revert s1 s2 EQUIV. trm_ind t; simpl; ii.
    + eapply EQUIV. eapply Nat.eqb_eq. reflexivity.
    + f_equal. eapply equiv_subst_in_trms_implies_subst_trms_same. exact EQUIV.
    + reflexivity.
  - revert s1 s2 EQUIV. trms_ind ts; simpl; ii.
    + reflexivity.
    + f_equal.
      * eapply equiv_subst_in_trm_implies_subst_trm_same. ii. eapply EQUIV. rewrite orb_true_iff. left. exact FREE.
      * eapply IH. ii. eapply EQUIV. rewrite orb_true_iff. right. exact FREE.
Qed.

Lemma equiv_subst_in_frm_implies_subst_frm_same (s1 : subst) (s2 : subst) (p : frm)
  (EQUIV : equiv_subst_in_frm s1 s2 p)
  : subst_frm s1 p = subst_frm s2 p.
Proof.
  revert s1 s2 EQUIV. unfold equiv_subst_in_frm. frm_ind p; simpl; ii.
  - simpl in EQUIV. f_equal.
    eapply equiv_subst_in_trms_implies_subst_trms_same. done.
  - simpl in EQUIV. f_equal.
    + eapply equiv_subst_in_trm_implies_subst_trm_same. ii.
      eapply EQUIV. rewrite orb_true_iff. done.
    + eapply equiv_subst_in_trm_implies_subst_trm_same. ii.
      eapply EQUIV. rewrite orb_true_iff. done.
  - f_equal. eapply IH1. done.
  - f_equal.
    + eapply IH1. ii. eapply EQUIV. rewrite orb_true_iff. done.
    + eapply IH2. ii. eapply EQUIV. rewrite orb_true_iff. done.
  - f_equal.
    + eapply chi_frm_compat_equiv_subst. unfold equiv_subst_in_frm. simpl. done.
    + eapply IH1. ii. unfold cons_subst. destruct (eq_dec z y) as [H_yes | H_no].
      { f_equal. subst z. eapply chi_frm_compat_equiv_subst. unfold equiv_subst_in_frm. simpl. done. }
      { eapply EQUIV. rewrite andb_true_iff. split; try done. eapply negb_true_iff. eapply Nat.eqb_neq. done. }
Qed.

Lemma distr_compose_one (s1 : subst) (s2 : subst) (x : ivar) (x' : ivar) (t : trm) (z : ivar) (p : frm)
  (FRESH : forallb (negb ∘ is_free_in_trm x ∘ s1) (remove eq_dec x' (fvs_frm p)) = true)
  (FREE : is_free_in_frm z p = true)
  : cons_subst x' t (subst_compose s1 s2) z = subst_compose (cons_subst x' (Var_trm x) s1) (cons_subst x t s2) z.
Proof.
  unfold subst_compose, cons_subst. simpl. destruct (eq_dec z x') as [H_eq | H_ne].
  - subst z. simpl. destruct (eq_dec x x); done.
  - rewrite forallb_forall in FRESH. unfold "∘" in FRESH.
    assert (NOT_FREE : is_free_in_trm x (s1 z) = false).
    { rewrite <- negb_true_iff. eapply FRESH. rewrite L.in_remove_iff. rewrite fv_is_free_in_frm. done. }
    eapply equiv_subst_in_trm_implies_subst_trm_same. intros z' FREE'. destruct (eq_dec z' x) as [EQ | NE]; try done.
Qed.

Definition free_in_trm_wrt (x : ivar) (s : subst) (t : trm) : Prop :=
  exists y : ivar, is_free_in_trm y t = true /\ is_free_in_trm x (s y) = true.

Definition free_in_trms_wrt {n : arity} (x : ivar) (s : subst) (ts : trms n) : Prop :=
  exists y : ivar, is_free_in_trms y ts = true /\ is_free_in_trm x (s y) = true.

Lemma free_in_trm_wrt_iff (t : trm) (z : ivar) (s : subst)
  : free_in_trm_wrt z s t <-> is_free_in_trm z (subst_trm s t) = true
with free_in_trms_wrt_iff n (ts : trms n) (z : ivar) (s : subst)
  : free_in_trms_wrt z s ts <-> is_free_in_trms z (subst_trms s ts) = true.
Proof.
  - revert z s. unfold free_in_trm_wrt. trm_ind t; simpl; i.
    + split.
      * intros [y [FREE FREE']]. apply Nat.eqb_eq in FREE. subst y. done.
      * intros FREE. exists x. rewrite Nat.eqb_eq. done.
    + split.
      * intros [y [FREE FREE']]. eapply free_in_trms_wrt_iff. done.
      * intros FREE. eapply free_in_trms_wrt_iff. done.
    + done.
  - revert z s. unfold free_in_trms_wrt. trms_ind ts; simpl; i.
    + done.
    + split.
      * intros [y [FREE FREE']]. rewrite orb_true_iff in FREE. rewrite orb_true_iff. destruct FREE as [FREE | FREE].
        { left. eapply free_in_trm_wrt_iff. done. }
        { right. eapply IH. exists y. done. }
      * rewrite orb_true_iff. intros [FREE | FREE].
        { apply free_in_trm_wrt_iff in FREE. unfold free_in_trm_wrt in FREE.
          destruct FREE as [y [FREE FREE']]. exists y. rewrite orb_true_iff. done.
        }
        { apply IH in FREE. destruct FREE as [y [FREE FREE']].
          exists y. rewrite orb_true_iff. done.
        }
Qed.

Definition free_in_frm_wrt (x : ivar) (s : subst) (p : frm) : Prop :=
  exists y : ivar, is_free_in_frm y p = true /\ is_free_in_trm x (s y) = true.

Theorem free_in_frm_wrt_iff (p : frm) (z : ivar) (s : subst)
  : free_in_frm_wrt z s p <-> is_free_in_frm z (subst_frm s p) = true.
Proof.
  revert z s. unfold free_in_frm_wrt. frm_ind p; simpl; i.
  - split.
    + intros [y [FREE FREE']]. eapply free_in_trms_wrt_iff. done.
    + intros FREE. apply free_in_trms_wrt_iff in FREE. done.
  - split.
    + intros [y [FREE FREE']]. rewrite orb_true_iff in FREE. rewrite orb_true_iff. destruct FREE as [FREE | FREE].
      * left. eapply free_in_trm_wrt_iff. done.
      * right. eapply free_in_trm_wrt_iff. done.
    + intros FREE. rewrite orb_true_iff in FREE. destruct FREE as [FREE | FREE].
      * apply free_in_trm_wrt_iff in FREE. destruct FREE as [y [FREE FREE']].
        exists y. rewrite orb_true_iff. done.
      * apply free_in_trm_wrt_iff in FREE. destruct FREE as [y [FREE FREE']].
        exists y. rewrite orb_true_iff. done.
  - done.
  - split.
    + intros [y [FREE FREE']]. rewrite orb_true_iff in FREE. rewrite orb_true_iff. destruct FREE as [FREE | FREE].
      * left. eapply IH1. done.
      * right. eapply IH2. done.
    + intros FREE. rewrite orb_true_iff in FREE. destruct FREE as [FREE | FREE].
      * apply IH1 in FREE. destruct FREE as [y [FREE FREE']].
        exists y. rewrite orb_true_iff. done.
      * apply IH2 in FREE. destruct FREE as [y [FREE FREE']].
        exists y. rewrite orb_true_iff. done.
  - split.
    + intros [w [FREE FREE']]. rewrite andb_true_iff in FREE. rewrite negb_true_iff in FREE. rewrite Nat.eqb_neq in FREE.
      destruct FREE as [FREE w_ne_y]. rewrite andb_true_iff. rewrite negb_true_iff. split.
      * eapply IH1. exists w. split; trivial. unfold cons_subst.
        destruct (eq_dec w y) as [EQ | NE]; done.
      * rewrite Nat.eqb_neq. intros CONTRA.
        assert (claim1 : frm_is_fresh_in_subst (chi_frm s (All_frm y p1)) s (All_frm y p1) = true).
        { exact (chi_frm_is_fresh_in_subst (All_frm y p1) s). }
        unfold frm_is_fresh_in_subst in claim1. rewrite forallb_forall in claim1.
        assert (claim2 : In w (fvs_frm (All_frm y p1))).
        { eapply fv_is_free_in_frm. simpl. rewrite andb_true_iff. rewrite negb_true_iff. rewrite Nat.eqb_neq. done. }
        apply claim1 in claim2. unfold "∘" in claim2. rewrite negb_true_iff in claim2.
        subst z. done.
    + rewrite andb_true_iff. rewrite negb_true_iff. rewrite Nat.eqb_neq.
      set (w := chi_frm s (All_frm y p1)). intros [FREE NE].
      apply IH1 in FREE. destruct FREE as [x [FREE FREE']].
      unfold cons_subst in FREE'. destruct (eq_dec x y) as [x_eq_y | x_ne_y].
      * subst x. contradiction NE. apply fv_is_free_in_trm in FREE'. simpl in FREE'. done.
      * exists x. rewrite andb_true_iff. rewrite negb_true_iff. rewrite Nat.eqb_neq. done.
Qed.

Lemma chi_frm_ext (s1 : subst) (s2 : subst) (p1 : frm) (p2 : frm)
  (EQUIV : forall z : ivar, free_in_frm_wrt z s1 p1 <-> free_in_frm_wrt z s2 p2)
  : chi_frm s1 p1 = chi_frm s2 p2.
Proof.
  assert (claim : forall z : ivar, In z (flat_map (fvs_trm ∘ s1) (fvs_frm p1)) <-> In z (flat_map (fvs_trm ∘ s2) (fvs_frm p2))).
  { unfold free_in_frm_wrt in EQUIV. intros z. do 2 rewrite in_flat_map.
    split; intros [x [H_IN1 H_IN2]]; rewrite fv_is_free_in_frm in H_IN1; apply fv_is_free_in_trm in H_IN2; unfold "∘" in *. 
    - assert (claim1 : exists y : ivar, is_free_in_frm y p1 = true /\ is_free_in_trm z (s1 y) = true) by done.
      apply EQUIV in claim1. destruct claim1 as [y [FREE FREE']]. apply fv_is_free_in_frm in FREE. apply fv_is_free_in_trm in FREE'. done.
    - assert (claim2 : exists y : ivar, is_free_in_frm y p2 = true /\ is_free_in_trm z (s2 y) = true) by done.
      apply EQUIV in claim2. destruct claim2 as [y [FREE FREE']]. apply fv_is_free_in_frm in FREE. apply fv_is_free_in_trm in FREE'. done.
  }
  apply maxs_ext in claim. unfold chi_frm. f_equal. unfold last_ivar_trm.
  assert (ENOUGH: forall xs: list ivar, forall f: ivar -> list ivar, maxs (List.map (maxs ∘ f) xs) = maxs (List.flat_map f xs)).
  { induction xs; simpl; i; eauto. rewrite maxs_app. done. }
  do 2 rewrite <- ENOUGH in claim. done.
Qed.

Theorem subst_compose_trm_spec (t : trm) (s : subst) (s' : subst)
  : subst_trm (subst_compose s s') t = subst_trm s' (subst_trm s t)
with subst_compose_trms_spec n (ts : trms n) (s : subst) (s' : subst)
  : subst_trms (subst_compose s s') ts = subst_trms s' (subst_trms s ts).
Proof.
  - revert s s'. trm_ind t; simpl; i.
    + done.
    + f_equal. eapply subst_compose_trms_spec.
    + done.
  - revert s s'. trms_ind ts; simpl; i.
    + done.
    + f_equal.
      * eapply subst_compose_trm_spec.
      * eapply IH.
Qed.

Theorem subst_compose_frm_spec (p : frm) (s : subst) (s' : subst)
  : subst_frm (subst_compose s s') p = subst_frm s' (subst_frm s p).
Proof.
  revert s s'. frm_ind p; simpl; i.
  - f_equal; eapply subst_compose_trms_spec.
  - f_equal; eapply subst_compose_trm_spec.
  - done.
  - done.
  - enough (ENOUGH : chi_frm s' (subst_frm s (All_frm y p1)) = chi_frm (subst_compose s s') (All_frm y p1)).
    { revert ENOUGH.
      set (x := chi_frm s (All_frm y p1)).
      set (z := chi_frm (subst_compose s s') (All_frm y p1)).
      set (w := chi_frm s' (All_frm x (subst_frm (cons_subst y (Var_trm x) s) p1))).
      i. rewrite <- IH1. assert (EQ : z = w) by done. subst z. f_equal; trivial.
      eapply equiv_subst_in_frm_implies_subst_frm_same.
      unfold equiv_subst_in_frm. ii.
      rewrite <- distr_compose_one with (p := p1).
      - done.
      - change (frm_is_fresh_in_subst x s (All_frm y p1) = true).
        eapply chi_frm_is_fresh_in_subst.
      - done.
    }
    eapply chi_frm_ext. intros z. split.
    + simpl. unfold free_in_frm_wrt. intros [x [FREE FREE']]. simpl in FREE.
      rewrite andb_true_iff in FREE. rewrite negb_true_iff in FREE. rewrite Nat.eqb_neq in FREE.
      destruct FREE as [FREE NE]. apply free_in_frm_wrt_iff in FREE. unfold free_in_frm_wrt in FREE.
      destruct FREE as [w [FREE1 FREE2]]. unfold cons_subst in FREE2. destruct (eq_dec w y) as [w_eq_y | w_ne_y].
      * unfold is_free_in_trm in FREE2. rewrite Nat.eqb_eq in FREE2. subst x y. done.
      * exists w. simpl. rewrite andb_true_iff. rewrite negb_true_iff. rewrite Nat.eqb_neq. split; try tauto.
        eapply free_in_trm_wrt_iff. done.
    + intros [x [FREE FREE']]. simpl in FREE. rewrite andb_true_iff in FREE. rewrite negb_true_iff in FREE. rewrite Nat.eqb_neq in FREE. destruct FREE as [FREE NE].
      apply free_in_trm_wrt_iff in FREE'. destruct FREE' as [u [FREE' FREE'']]. exists u. split.
      * eapply free_in_frm_wrt_iff. exists x. simpl. rewrite andb_true_iff. rewrite negb_true_iff. rewrite Nat.eqb_neq. done.
      * done.
Qed.

Lemma trivial_subst (x : ivar) (p : frm)
  : subst_frm (one_subst x (Var_trm x)) p = subst_frm nil_subst p.
Proof.
  unfold one_subst, cons_subst, nil_subst. eapply equiv_subst_in_frm_implies_subst_frm_same.
  unfold equiv_subst_in_frm. ii. destruct (eq_dec z x) as [H_yes | H_no]; done.
Qed.

Lemma compose_one_subst_frm (x1 : ivar) (t1 : trm) (s : subst) (p : frm)
  : subst_frm s (subst_frm (one_subst x1 t1) p) = subst_frm (cons_subst x1 (subst_trm s t1) s) p.
Proof.
  unfold one_subst. rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same. ii.
  unfold cons_subst, nil_subst, subst_compose. destruct (eq_dec z x1) as [z_eq_x1 | z_ne_x1]; try done.
Qed.

Lemma cons_subst_subst_frm (x1 : ivar) (t1 : trm) (y : ivar) (p : frm) (s : subst)
  (NOT_FREE: is_free_in_frm y p = false \/ y = x1)
  : subst_frm (cons_subst x1 t1 s) p = subst_frm (cons_subst y t1 s) (subst_frm (one_subst x1 (Var_trm y)) p).
Proof.
  unfold one_subst. rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same.
  ii. unfold cons_subst, subst_compose, nil_subst. destruct (eq_dec z x1) as [z_eq_x1 | z_ne_x1].
  - subst z. simpl. destruct (eq_dec y y); try done.
  - simpl. destruct (eq_dec z y) as [z_eq_y | z_ne_y]; try done.
Qed.

Lemma subst_preserves_rank (p : frm) (s : subst)
  : frm_depth (subst_frm s p) = frm_depth p.
Proof.
  revert s. frm_ind p; simpl; i; try done.
Qed.

Lemma quick_draw_one (p : frm) (x : ivar) (y : ivar) (z : ivar) (s : subst)
  (FRESH : is_free_in_frm x p = false \/ x = y)
  : subst_frm (one_subst x (Var_trm z)) (subst_frm (cons_subst y (Var_trm z) s) p) = subst_frm (cons_subst y (Var_trm z) (subst_compose s (one_subst x (Var_trm z)))) (subst_frm (one_subst x (Var_trm y)) p).
Proof.
  symmetry. do 2 rewrite <- subst_compose_frm_spec.
  eapply equiv_subst_in_frm_implies_subst_frm_same. 
  intros w FREE. unfold subst_compose at 1 3. unfold one_subst. unfold cons_subst at 3 5.
  destruct (eq_dec w x) as [w_eq_x | w_ne_x], (eq_dec w y) as [w_eq_y | w_ne_y].
  - subst w. subst y. rewrite subst_trm_unfold. symmetry. rewrite subst_trm_unfold. symmetry.
    unfold subst_compose. unfold cons_subst. destruct (eq_dec x x) as [_ | CONTRA]. 2: done.
    destruct (eq_dec z x); try done.
  - subst w. simpl in FRESH. destruct FRESH; done.
  - subst w. unfold nil_subst at 2. do 2 rewrite subst_trm_unfold; symmetry.
    unfold cons_subst. unfold subst_compose. destruct (eq_dec y y) as [_ | CONTRA]. 2: done.
    destruct (eq_dec z x); try done.
  - unfold nil_subst at 2. rewrite subst_trm_unfold. unfold subst_compose.
    unfold cons_subst. destruct (eq_dec w y); try done.
Qed.

Lemma one_subst_free_assoc_lemma1 (x : ivar) (t : trm) (z : ivar) (p : frm)
  (NE : x <> z)
  (FREE : is_free_in_frm z p = true)
  : is_free_in_frm z (subst_frm (one_subst x t) p) = true.
Proof.
  enough (ENOUGH : is_free_in_frm z (subst_frm (one_subst x t) p) <> false).
  { destruct (is_free_in_frm z (subst_frm (one_subst x t) p)); done. }
  intros CONTRA. rewrite <- frm_is_fresh_in_subst_iff in CONTRA.
  unfold frm_is_fresh_in_subst in CONTRA. rewrite forallb_forall in CONTRA.
  rewrite <- fv_is_free_in_frm in FREE. specialize (CONTRA z FREE).
  unfold "∘" in CONTRA. unfold negb in CONTRA. unfold one_subst, cons_subst, nil_subst in CONTRA.
  destruct (eq_dec z x); rewrite is_free_in_trm_unfold in CONTRA.
  - done. - destruct (Nat.eqb z z) as [ | ] eqn: H_OBS. + done. + rewrite Nat.eqb_neq in H_OBS. done.
Qed.

Lemma one_subst_free_assoc_lemma2 (x : ivar) (x' : ivar) (y : ivar) (z : ivar) (p : frm) (p' : frm)
  (FRESH : is_free_in_frm y p = false \/ y = x)
  (NE : z <> x)
  (FREE : is_free_in_frm z p = true)
  (FREE' : is_free_in_frm z (subst_frm (one_subst x' (Var_trm y)) p') = true)
  : z <> x'.
Proof.
  intros CONTRA. enough (ENOUGH : is_free_in_frm z (subst_frm (one_subst x' (Var_trm y)) p') = false) by done.
  rewrite <- frm_is_fresh_in_subst_iff. subst x'. unfold frm_is_fresh_in_subst.
  rewrite forallb_forall. intros w FREE''. rewrite fv_is_free_in_frm in FREE''.
  unfold "∘"%prg. rewrite negb_true_iff. unfold one_subst, cons_subst, nil_subst.
  destruct FRESH as [FRESH | NE']; destruct (eq_dec w z) as [w_eq_z | w_ne_z]; rewrite is_free_in_trm_unfold; rewrite Nat.eqb_neq; try done.
Qed.

Lemma one_subst_free_assoc_lemma3 (x : ivar) (y : ivar) (z : ivar) (p : frm)
  (NE : z <> y)
  (FREE : is_free_in_frm z (subst_frm (one_subst x (Var_trm y)) p) = true)
  : is_free_in_frm z p = true.
Proof.
  enough (ENOUGH : is_free_in_frm z p <> false) by now destruct (is_free_in_frm z p).
  intros CONTRA. enough (ENOUGH : is_free_in_frm z (subst_frm (one_subst x (Var_trm y)) p) = false) by done.
  rewrite <- frm_is_fresh_in_subst_iff. unfold frm_is_fresh_in_subst.
  rewrite forallb_forall. intros w FREE'. rewrite fv_is_free_in_frm in FREE'.
  unfold "∘"%prg. rewrite negb_true_iff. unfold one_subst, cons_subst, nil_subst.
  destruct (eq_dec w x) as [w_eq_x | w_ne_x]; rewrite is_free_in_trm_unfold; rewrite Nat.eqb_neq; done.
Qed.

Lemma one_subst_free_assoc_lemma3' (x : ivar) (y : ivar) (z : ivar) (p : frm)
  (NE : z <> y)
  (FRESH : is_free_in_frm z p = false)
  : is_free_in_frm z (subst_frm (one_subst x (Var_trm y)) p) = false.
Proof.
  pose proof (one_subst_free_assoc_lemma3 x y z p NE).
  destruct (is_free_in_frm z (subst_frm (one_subst x (Var_trm y)) p)) as [ | ], (is_free_in_frm z p) as [ | ]; done.
Qed.

Lemma one_subst_free_assoc_lemma4 (x : ivar) (y : ivar) (z : ivar) (p : frm)
  (NE : z <> x)
  (FREE : is_free_in_frm z p = true)
  (FRESH : is_free_in_frm y p = false \/ y = x)
  : z <> y.
Proof.
  intros CONTRA.
  subst z.
  destruct FRESH as [FRESH | NE']; done.
Qed.

Definition fvs_eq_trm (t1 : trm) (t2 : trm) : Prop :=
  forall x : ivar, is_free_in_trm x t1 = true <-> is_free_in_trm x t2 = true.

Definition fvs_eq_frm (p1 : frm) (p2 : frm) : Prop :=
  forall x : ivar, is_free_in_frm x p1 = true <-> is_free_in_frm x p2 = true.

Lemma chi_frm_ext' (s : subst) (s' : subst) (p : frm) (p' : frm)
  (FvEq1 : forall x : ivar, is_free_in_frm x p = true -> fvs_eq_trm (s x) (s' x))
  (FvEq2 : fvs_eq_frm p p')
  : chi_frm s p = chi_frm s' p'.
Proof.
  eapply chi_frm_ext. intros z. split; intros (u&FREE&FREE').
  - exists u. split.
    + eapply FvEq2. exact FREE.
    + eapply FvEq1.
      * eapply FvEq2. done.
      * exact FREE'.
  - exists u. split.
    + eapply FvEq2. exact FREE.
    + eapply FvEq1.
      * eapply FvEq2. done.
      * exact FREE'.
Qed.

End SUBSTITUTION.

Section RENAMING.

Fixpoint rename_trm (eta : renaming) (t : trm) : trm :=
  match t with
  | Var_trm x => Var_trm (rename_var eta x)
  | Fun_trm f ts => Fun_trm f (rename_trms eta ts)
  | Con_trm c => Con_trm c
  end
with rename_trms {n : nat} (eta : renaming) (ts : trms n) : trms n :=
  match ts with
  | O_trms => O_trms
  | S_trms _ t ts => S_trms _ (rename_trm eta t) (rename_trms eta ts)
  end.

Fixpoint rename_frm (eta : renaming) (p : frm) : frm :=
  match p with
  | Rel_frm R ts => Rel_frm R (rename_trms eta ts)
  | Eqn_frm t1 t2 => Eqn_frm (rename_trm eta t1) (rename_trm eta t2)
  | Neg_frm p1 => Neg_frm (rename_frm eta p1)
  | Imp_frm p1 p2 => Imp_frm (rename_frm eta p1) (rename_frm eta p2)
  | All_frm y p1 => All_frm y (rename_frm ((y, y) :: eta) p1)
  end.

Lemma rename_trm_nil (t : trm) eta
  (eta_trivial : forall x, forall y, L.In (x, y) eta -> x = y)
  : rename_trm eta t = t
with rename_trms_nil n (ts : trms n) eta
  (eta_trivial : forall x, forall y, L.In (x, y) eta -> x = y)
  : rename_trms eta ts = ts.
Proof.
  - trm_ind t.
    + simpl. f_equal. induction eta as [ | [x' y] eta IH]; simpl; i.
      * reflexivity.
      * destruct (eq_dec x x') as [EQ | NE].
        { symmetry. eapply eta_trivial. subst x'. left. reflexivity. }
        { eapply IH. intros x'' y' H_in. eapply eta_trivial. right. exact H_in. }
    + simpl. f_equal. eapply rename_trms_nil; trivial.
    + reflexivity.
  - trms_ind ts.
    + reflexivity.
    + simpl. f_equal.
      * eapply rename_trm_nil; trivial.
      * exact IH; trivial.
Qed.

Lemma rename_frm_nil (p : frm) eta
  (eta_trivial : forall x, forall y, L.In (x, y) eta -> x = y)
  : rename_frm eta p = p.
Proof.
  revert eta eta_trivial. frm_ind p; simpl; i.
  - f_equal. eapply rename_trms_nil; trivial.
  - f_equal; eapply rename_trm_nil; trivial.
  - f_equal. eapply IH1; trivial.
  - f_equal; [eapply IH1 | eapply IH2]; trivial.
  - f_equal. eapply IH1. intros x' y'. simpl. intros [EQ | H_in]; done.
Qed.

End RENAMING.

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

#[local] Hint Constructors alpha_equiv : core.

Lemma is_free_in_frm_compat_alpha_equiv (p : frm) (p' : frm) (x : ivar)
  (ALPHA : p ≡ p')
  (FREE : is_free_in_frm x p = true)
  : is_free_in_frm x p' = true.
Proof.
  revert x FREE. induction ALPHA; simpl in *; i.
  - done.
  - done.
  - done.
  - rewrite orb_true_iff in *. done.
  - rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in *. destruct FREE as [FREE NE].
    simpl in LFRESH, RFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in *.
    assert (claim1 : x <> y').
    { intros CONTRA. subst y'.
      eapply one_subst_free_assoc_lemma2 with (p := p1) (p' := p1').
      - exact LFRESH.
      - exact NE.
      - exact FREE.
      - eapply IHALPHA. eapply one_subst_free_assoc_lemma1; done.
      - done.
    }
    split; trivial. eapply one_subst_free_assoc_lemma3.
    + eapply one_subst_free_assoc_lemma4.
      * exact NE.
      * exact FREE.
      * exact LFRESH.
    + eapply IHALPHA.
      * eapply one_subst_free_assoc_lemma1; done.
Qed.

#[global]
Instance alpha_equiv_Reflexive
  : Reflexive alpha_equiv.
Proof.
  intros p. pattern p. revert p. apply frm_depth_lt_ind. simpl in *; i.
  destruct p as [R ts | t1 t2 | p1 | p1 p2 | y p1]; simpl.
  - econs; done.
  - econs; done.
  - econs; eapply IH; simpl; done.
  - econs; eapply IH; simpl; done.
  - eapply alpha_All_frm with (z := y).
    + eapply IH. rewrite subst_preserves_rank. simpl; done.
    + simpl. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. done.
    + simpl. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. done.
Qed.

#[global]
Instance alpha_equiv_Symmetric
  : Symmetric alpha_equiv.
Proof.
  intros p1 p2 EQ1. induction EQ1; simpl; econs; done.
Qed.

Lemma alpha_equiv_compat_fresh (p : frm) (p' : frm) (x : ivar)
  (ALPHA : p ≡ p')
  : is_free_in_frm x p = false <-> is_free_in_frm x p' = false.
Proof.
  split.
  - symmetry in ALPHA.
    pose proof (is_free_in_frm_compat_alpha_equiv p' p x ALPHA).
    destruct (is_free_in_frm x p'), (is_free_in_frm x p); done.
  - pose proof (is_free_in_frm_compat_alpha_equiv p p' x ALPHA).
    destruct (is_free_in_frm x p), (is_free_in_frm x p'); done.
Qed.

Lemma subst_frm_compat_alpha_equiv (p : frm) (p' : frm) (s : subst)
  (ALPHA : p ≡ p')
  : subst_frm s p = subst_frm s p'.
Proof.
  revert s. induction ALPHA; simpl; i.
  - done.
  - done.
  - done.
  - done.
  - assert (claim1 : chi_frm s (All_frm y p1) = chi_frm s (All_frm y' p1')).
    { eapply chi_frm_ext'.
      - ii; reflexivity.
      - red. intros x; split; intros FREE.
        + eapply is_free_in_frm_compat_alpha_equiv.
          * eapply alpha_All_frm with (z := z); done.
          * exact FREE.
        + eapply is_free_in_frm_compat_alpha_equiv.
          * symmetry. eapply alpha_All_frm with (z := z); done.
          * exact FREE.
    }
    f_equal; trivial. rename y into x, y' into x'.
    rewrite <- claim1. clear claim1. set (y := chi_frm s (All_frm x p1)).
    erewrite cons_subst_subst_frm with (p := p1) (y := z).
    erewrite cons_subst_subst_frm with (p := p1') (y := z).
    + eapply IHALPHA.
    + simpl in RFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in RFRESH. done.
    + simpl in LFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in LFRESH. done.
Qed.

#[global]
Instance alpha_equiv_Transitive
  : Transitive alpha_equiv.
Proof.
  intros p1 p2 p3 EQ EQ'. revert p3 EQ'. induction EQ; simpl; i.
  - done.
  - done.
  - inv EQ'; econs; done.
  - inv EQ'; econs; done.
  - inv EQ'. rename y'0 into y'', z0 into z', LFRESH0 into LFRESH', RFRESH0 into RFRESH', p1'0 into p1''.
    assert (claim : subst_frm (one_subst y (Var_trm z)) p1 ≡ subst_frm (one_subst y'' (Var_trm z)) p1'').
    { eapply IHEQ.
      unfold one_subst. erewrite cons_subst_subst_frm. 2:{ simpl in LFRESH'. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in LFRESH'. exact LFRESH'. }
      symmetry. erewrite cons_subst_subst_frm. 2:{ simpl in RFRESH'. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in RFRESH'. exact RFRESH'. }
      symmetry. pose proof (subst_frm_compat_alpha_equiv _ _ (cons_subst z' (Var_trm z) nil_subst) ALPHA1) as claim1.
      rewrite claim1. reflexivity.
    }
    eapply alpha_All_frm with (z := z); trivial. erewrite <- alpha_equiv_compat_fresh.
    + exact RFRESH.
    + econstructor; eauto.
Qed.

#[global]
Instance alpha_equiv_Equivalence : Equivalence alpha_equiv :=
  { Equivalence_Reflexive := alpha_equiv_Reflexive
  ; Equivalence_Symmetric := alpha_equiv_Symmetric
  ; Equivalence_Transitive := alpha_equiv_Transitive
  }.

Lemma alpha_equiv_eq_intro (p1 : frm) (p2 : frm)
  (EQ : p1 = p2)
  : p1 ≡ p2.
Proof. 
  subst p2.
  reflexivity.
Qed.

Lemma subst_nil_trm (t : trm) (s : subst)
  (FRESH : forall x : ivar, is_free_in_trm x t = true -> s x = Var_trm x)
  : subst_trm s t = t
with subst_nil_trms n (ts : trms  n) (s : subst)
  (FRESH: forall x : ivar, is_free_in_trms x ts = true -> s x = Var_trm x)
  : subst_trms s ts = ts.
Proof.
  -  clear subst_nil_trm. revert s FRESH. trm_ind t; simpl; i.
    + eapply FRESH. rewrite Nat.eqb_eq. reflexivity.
    + f_equal. eapply subst_nil_trms with (s := s). done.
    + done.
  - clear subst_nil_trms. revert s FRESH. trms_ind ts; simpl; i.
    + done.
    + f_equal.
      * eapply subst_nil_trm. ii. eapply FRESH. rewrite orb_true_iff. done.
      * eapply IH. ii. eapply FRESH. rewrite orb_true_iff. done.
Qed.

Lemma subst_nil_frm (p : frm) (s : subst)
  (FRESH : forall x : ivar, is_free_in_frm x p = true -> s x = Var_trm x)
  : subst_frm s p ≡ p.
Proof.
  revert s FRESH. pattern p; revert p; eapply frm_depth_lt_ind; i. destruct p; simpl in *.
  - econstructor. eapply subst_nil_trms. done.
  - econstructor; eapply subst_nil_trm; ii; eapply FRESH; rewrite orb_true_iff; done.
  - econstructor. eapply IH; done.
  - econstructor; eapply IH; first [done | eauto with *].
  - assert (chi_fresh : is_free_in_frm (chi_frm s (All_frm y p)) (All_frm y p) = false).
    { pose proof (@chi_frm_is_fresh_in_subst (All_frm y p) s) as claim.
      unfold frm_is_fresh_in_subst in claim. rewrite forallb_forall in claim.
      unfold "∘"%prg in claim. enough (ENOUGH: is_free_in_frm (chi_frm s (All_frm y p)) (All_frm y p) <> true) by now destruct (is_free_in_frm (chi_frm s (All_frm y p)) (All_frm y p)).
      intros CONTRA. rewrite <- fv_is_free_in_frm in CONTRA. specialize (claim (chi_frm s (All_frm y p)) CONTRA).
      rewrite negb_true_iff in claim. rewrite FRESH in claim.
      * rewrite is_free_in_trm_unfold in claim. rewrite Nat.eqb_neq in claim. done.
      * rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. rewrite fv_is_free_in_frm in CONTRA.
        rewrite is_free_in_frm_unfold in CONTRA. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in CONTRA. done.
    }
    eapply alpha_All_frm with (z := chi_frm s (All_frm y p)).
    { transitivity (subst_frm (cons_subst y (Var_trm (chi_frm s (All_frm y p))) s) p).
      - eapply IH.
        + rewrite subst_preserves_rank. done.
        + intros x FREE. unfold one_subst, cons_subst, nil_subst.
          destruct (eq_dec x (chi_frm s (All_frm y p))); try done.
      - eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
        ii. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec z y) as [EQ | NE].
        + done.
        + eapply FRESH. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. done.
    }
    { rewrite is_free_in_frm_unfold, andb_false_iff, negb_false_iff, Nat.eqb_eq. done. }
    { exact chi_fresh. }
Qed.

Lemma alpha_equiv_if_subst_nil_eq (p1 : frm) (p2 : frm)
  (EQ : subst_frm nil_subst p1 = subst_frm nil_subst p2)
  : p1 ≡ p2.
Proof.
  revert p2 EQ. pattern p1. revert p1. eapply frm_depth_lt_ind; i. destruct p; simpl in *.
  - rewrite subst_nil_trms in EQ. rewrite <- subst_nil_frm with (p := p2) (s := nil_subst). eapply alpha_equiv_eq_intro. done.
    { ii. reflexivity. }
    { ii. reflexivity. }
  - rewrite subst_nil_trm in EQ. rewrite subst_nil_trm in EQ. rewrite <- subst_nil_frm with (p := p2) (s := nil_subst). eapply alpha_equiv_eq_intro. done.
    { ii. reflexivity. }
    { ii. reflexivity. }
    { ii. reflexivity. }
  - transitivity (subst_frm nil_subst p2).
    { rewrite <- EQ. econstructor. symmetry. eapply subst_nil_frm. ii. reflexivity. }
    { eapply subst_nil_frm. ii. reflexivity. }
  - transitivity (subst_frm nil_subst p2).
    { rewrite <- EQ. econstructor; symmetry; eapply subst_nil_frm; ii; reflexivity. }
    { eapply subst_nil_frm. ii. reflexivity. }
  - transitivity (subst_frm nil_subst p2).
    { rewrite <- EQ. econstructor.
      - symmetry. eapply subst_nil_frm. ii. unfold one_subst, cons_subst. destruct (eq_dec x (chi_frm nil_subst (All_frm y p))); try done.
      - enough (ENOUGH : is_free_in_frm (chi_frm nil_subst (All_frm y p)) (All_frm y p) <> true) by now destruct (is_free_in_frm (chi_frm nil_subst (All_frm y p)) (All_frm y p)).
        intros CONTRA. pose proof (@chi_frm_not_free nil_subst (All_frm y p) (chi_frm nil_subst (All_frm y p)) CONTRA) as claim.
        unfold nil_subst at 2 in claim. rewrite is_free_in_trm_unfold in claim. rewrite Nat.eqb_neq in claim. done.
      - rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. done.
    }
    { eapply subst_nil_frm. ii. reflexivity. }
Qed.

Lemma alpha_equiv_compath_rank (p : frm) (p' : frm)
  (ALPHA : p ≡ p')
  : frm_depth p = frm_depth p'.
Proof.
  erewrite <- subst_preserves_rank with (s := nil_subst). symmetry.
  erewrite <- subst_preserves_rank with (s := nil_subst). symmetry.
  f_equal. eapply subst_frm_compat_alpha_equiv. exact ALPHA.
Qed.

Lemma alpha_equiv_inv_subst (s : subst) (p : frm) (p' : frm)
  (ALPHA : subst_frm s p ≡ p')
  : subst_frm s p = subst_frm nil_subst p'.
Proof.
  apply subst_frm_compat_alpha_equiv with (s := nil_subst) in ALPHA.
  rewrite <- subst_compose_frm_spec in ALPHA. rewrite <- ALPHA.
  eapply equiv_subst_in_frm_implies_subst_frm_same. ii.
  unfold subst_compose. rewrite subst_nil_trm; done.
Qed.

Lemma alpha_equiv_iff_subst_nil_eq (p : frm) (p' : frm)
  : p ≡ p' <-> subst_frm nil_subst p = subst_frm nil_subst p'.
Proof.
  split; [intros EQUIV | intros EQ].
  - eapply alpha_equiv_inv_subst. rewrite <- EQUIV. eapply subst_nil_frm. done.
  - eapply alpha_equiv_if_subst_nil_eq; done.
Qed.

Definition alpha_equiv_closure (ps : ensemble frm) : ensemble frm :=
  fun p' : frm => exists p : frm, p' ≡ p /\ p \in ps.

Lemma alpha_equiv_closure_postfixedpoint (ps : ensemble frm)
  : ps \subseteq alpha_equiv_closure ps.
Proof.
  intros p p_IN. red. red. exists p. split; done.
Qed.

Lemma alpha_equiv_closure_idemponent (ps : ensemble frm)
  : alpha_equiv_closure (alpha_equiv_closure ps) == alpha_equiv_closure ps.
Proof.
  intros p; split.
  - intros (p'&ALPHA1&p''&ALPHA2&IN). exists p''. split; eauto with *. transitivity p'; trivial.
  - intros (p'&ALPHA&IN). exists p'. split; trivial. exists p'. split; trivial. reflexivity.
Qed.

Lemma alpha_equiv_closure_monotonic (ps : ensemble frm) (ps' : ensemble frm)
  (LE : ps \subseteq ps')
  : alpha_equiv_closure ps \subseteq alpha_equiv_closure ps'.
Proof.
  intros p (p'&ALPHA&IN). exists p'. split; done.
Qed.

#[global]
Add Parametric Morphism
  : subst_frm with signature (eq ==> alpha_equiv ==> eq) as subst_frm_alpha_equiv_returns_eq.
Proof.
  intros s. intros p1 p2 ALPHA. etransitivity.
  - eapply subst_frm_compat_alpha_equiv. exact ALPHA.
  - eapply equiv_subst_in_frm_implies_subst_frm_same.
    ii. reflexivity.
Qed.

#[global]
Add Parametric Morphism
  : subst_frm with signature (eq ==> alpha_equiv ==> alpha_equiv) as subst_frm_alpha_equiv_returns_alpha_equiv.
Proof.
  intros s. intros p1 p2 ALPHA.
  eapply alpha_equiv_eq_intro. eapply subst_frm_alpha_equiv_returns_eq; eauto with *.
Qed.

Lemma alpha_equiv_All_frm_intro (y : ivar) (p1 : frm) (p2 : frm)
  (ALPHA : p1 ≡ p2)
  : All_frm y p1 ≡ All_frm y p2.
Proof.
  eapply alpha_All_frm with (z := y).
  - rewrite ALPHA. reflexivity.
  - simpl; rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. done.
  - simpl; rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. done.
Qed.

#[global]
Add Parametric Morphism
  : Neg_frm with signature (alpha_equiv ==> alpha_equiv)
  as Neg_frm_alpha_equiv_alpha_equiv.
Proof.
  ii. eapply alpha_Neg_frm; done.
Qed.

#[global]
Add Parametric Morphism
  : Imp_frm with signature (alpha_equiv ==> alpha_equiv ==> alpha_equiv)
  as Neg_frm_alpha_equiv_alpha_equiv_alpha_equiv.
Proof.
  ii. eapply alpha_Imp_frm; done.
Qed.

#[global]
Add Parametric Morphism
  : All_frm with signature (eq ==> alpha_equiv ==> alpha_equiv)
  as All_frm_eq_alpha_equiv_alpha_equiv.
Proof.
  intros y p1 p2 ALPHA. eapply alpha_equiv_All_frm_intro. exact ALPHA.
Qed.

Lemma subst_subst_alpha (p : frm) (x1 : ivar) (x2 : ivar) (t1 : trm) (t2 : trm)
  (NE : x1 <> x2)
  (FRESH : is_not_free_in_trm x1 t2)
  : subst_frm (one_subst x2 t2) (subst_frm (one_subst x1 t1) p) ≡ subst_frm (one_subst x1 (subst_trm (one_subst x2 t2) t1)) (subst_frm (one_subst x2 t2) p).
Proof.
  rewrite <- subst_compose_frm_spec. rewrite <- subst_compose_frm_spec.
  eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
  unfold subst_compose. ii. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec z x1) as [EQ1 | NE1].
  - subst z. destruct (eq_dec x1 x2) as [EQ2 | NE2].
    + done.
    + symmetry. rewrite subst_trm_unfold. symmetry. destruct (eq_dec x1 x1) as [EQ3 | NE3].
      * reflexivity.
      * done.
  - rewrite subst_trm_unfold. destruct (eq_dec z x2) as [EQ2 | NE2].
    + subst z. symmetry. eapply subst_nil_trm. intros u u_free. destruct (eq_dec u x1) as [EQ3 | NE3].
      * subst u. red in FRESH. rewrite FRESH in u_free. done.
      * reflexivity.
    + symmetry. rewrite subst_trm_unfold. symmetry. destruct (eq_dec z x1) as [EQ3 | NE3].
      * done.
      * reflexivity.
Qed.

Lemma alpha_is_not_free_in_frm (p : frm) (p' : frm) (x : ivar)
  (ALPHA : p ≡ p')
  (NOT_FREE : is_not_free_in_frm x p)
  : is_not_free_in_frm x p'.
Proof.
  red. red in NOT_FREE. symmetry in ALPHA. pose proof (is_free_in_frm_compat_alpha_equiv p' p x ALPHA). destruct (is_free_in_frm x p') as [ | ]; done.
Qed.

End ALPHA.

Infix "≡" := alpha_equiv : type_scope.

Definition close_ivars (p : frm) : list ivar -> frm :=
  @list_rec _ (fun _ => frm) p (fun x => fun _ => fun q => All_frm x q).

Definition closed_frm (p : frm) : frm :=
  close_ivars p (nodup eq_dec (fvs_frm p)).

Section SINGLE_SUBSTITUTION.

Definition fresh_var (x : ivar) (t : trm) (p : frm) : ivar :=
  1 + maxs ([x] ++ fvs_trm t ++ fvs_frm p).

Lemma fresh_var_ne_x (x : ivar) (t : trm) (p : frm)
  : fresh_var x t p <> x.
Proof.
  unfold fresh_var. simpl. lia.
Qed.

Lemma fresh_var_is_not_free_in_trm (x : ivar) (t : trm) (p : frm)
  : is_free_in_trm (fresh_var x t p) t = false.
Proof.
  eapply last_ivar_trm_gt.
  unfold fresh_var. unfold last_ivar_trm.
  rewrite maxs_app. rewrite maxs_app. lia.
Qed.

Lemma fresh_var_is_not_free_in_frm (x : ivar) (t : trm) (p : frm)
  : is_free_in_frm (fresh_var x t p) p = false.
Proof.
  eapply last_ivar_frm_gt.
  unfold fresh_var. unfold last_ivar_frm.
  rewrite maxs_app. rewrite maxs_app. lia.
Qed.

Inductive subst1_spec (x : ivar) (t : trm) : frm -> frm -> Prop :=
  | subst1_All_EQ y p
    (EQ : x = y)
    : subst1_spec x t (All_frm y p) (All_frm y p)
  | subst1_All_FRESH y p1 p1'
    (NE : x <> y)
    (NOT_OCCUR : is_free_in_trm y t = false)
    (SUBST1 : subst1_spec x t p1 p1')
    : subst1_spec x t (All_frm y p1) (All_frm y p1')
  | subst1_All_RENAME y z p1 p1' p1''
    (NEW_IVAR : z = fresh_var x t p1)
    (NE : x <> y)
    (NOT_OCCUR : is_free_in_trm y t = true)
    (SUBST1 : subst1_spec y (Var_trm z) p1 p1')
    (SUBST2 : subst1_spec x t p1' p1'')
    : subst1_spec x t (All_frm y p1) (All_frm z p1'')
  | subst1_Atomic p p'
    (RANK_ZERO : frm_depth p = 0)
    (EQ : p' = subst_frm (one_subst x t) p)
    : subst1_spec x t p p'
  | subst1_Neg p1 p1'
    (SUBST1 : subst1_spec x t p1 p1')
    : subst1_spec x t (Neg_frm p1) (Neg_frm p1')
  | subst1_Imp p1 p2 p1' p2'
    (SUBST1 : subst1_spec x t p1 p1')
    (SUBST2 : subst1_spec x t p2 p2')
    : subst1_spec x t (Imp_frm p1 p2) (Imp_frm p1' p2').

Lemma subst1_uniquely_exists x t
  : forall p : frm, { p' : frm | subst1_spec x t p p' /\ frm_depth p = frm_depth p' /\ (forall q' : frm, forall SUBST : subst1_spec x t p q', q' = p') }.
Proof.
  intros p. revert x t. pattern p. revert p. eapply @B.transfinite_recursion with (R := fun p => fun p' => frm_depth p < frm_depth p').
  { eapply B.preimage_preserves_wf. exact lt_wf. }
  intros p IH x t. change (forall q, frm_depth q < frm_depth p -> forall x, forall t, { p' : frm | subst1_spec x t q p'/\ frm_depth q = frm_depth p' /\ (forall q' : frm, forall SUBST : subst1_spec x t q q', q' = p') }) in IH.
  destruct p.
  - exists (Rel_frm R (subst_trms (one_subst x t) ts)).
    split. { eapply subst1_Atomic; reflexivity. }
    split. { simpl; reflexivity. }
    ii. inv SUBST. { reflexivity. }
  - exists (Eqn_frm (subst_trm (one_subst x t) t1) (subst_trm (one_subst x t) t2)).
    split. { eapply subst1_Atomic; reflexivity. }
    split. { simpl; reflexivity. }
    ii. inv SUBST. { reflexivity. }
  - assert (rank_LT1 : frm_depth p < frm_depth (Neg_frm p)) by now simpl; lia.
    pose proof (IH p rank_LT1 x t) as [p' [SUBST1 [RANK_EQ1 UNIQUE1]]].
    exists (Neg_frm p').
    split. { eapply subst1_Neg; trivial. }
    split. { simpl; lia. }
    ii. inv SUBST. { inv RANK_ZERO. } { f_equal. eapply UNIQUE1. trivial. }
  - assert (rank_LT1 : frm_depth p1 < frm_depth (Imp_frm p1 p2)) by now simpl; lia.
    assert (rank_LT2 : frm_depth p2 < frm_depth (Imp_frm p1 p2)) by now simpl; lia.
    pose proof (IH p1 rank_LT1 x t) as [p1' [SUBST1 [RANK_EQ1 UNIQUE1]]]. pose proof (IH p2 rank_LT2 x t) as [p2' [SUBST2 [RANK_EQ2 UNIQUE2]]].
    exists (Imp_frm p1' p2').
    split. { eapply subst1_Imp; trivial. }
    split. { simpl; lia. }
    ii. inv SUBST. { inv RANK_ZERO. } { f_equal. eapply UNIQUE1; trivial. eapply UNIQUE2; trivial. }
  - pose proof (eq_dec x y) as [EQ | NE].
    + exists (All_frm y p).
      split. { eapply subst1_All_EQ; trivial. }
      split. { simpl; lia. }
      ii. inv SUBST. { reflexivity. } { contradiction. } { contradiction. } { inv RANK_ZERO. }
    + destruct (is_free_in_trm y t) as [ | ] eqn: H_OBS.
      * set (z := fresh_var x t p).
        assert (rank_LT1 : frm_depth p < frm_depth (All_frm y p)) by now simpl; lia.
        pose proof (IH p rank_LT1 y (Var_trm z)) as [p' [SUBST1 [RANK_EQ1 UNIQUE1]]].
        assert (rank_LT2 : frm_depth p' < frm_depth (All_frm y p)) by now simpl; lia.
        pose proof (IH p' rank_LT2 x t) as [p'' [SUBST2 [RANK_EQ2 UNIQUE2]]].
        exists (All_frm z p'').
        split. { eapply subst1_All_RENAME with (p1' := p'); trivial. }
        split. { simpl; lia. }
        ii. inv SUBST. { contradiction. } { rewrite H_OBS in NOT_OCCUR; discriminate. } { f_equal; eapply UNIQUE2; apply UNIQUE1 in SUBST0; done. } { inv RANK_ZERO. }
      * assert (rank_LT1 : frm_depth p < frm_depth (All_frm y p)) by now simpl; lia.
        pose proof (IH p rank_LT1 x t) as [p' [SUBST1 [RANK_EQ1 UNIQUE1]]].
        exists (All_frm y p').
        split. { eapply subst1_All_FRESH; trivial. }
        split. { simpl; lia. }
        ii. inv SUBST. { contradiction. } { f_equal; eapply UNIQUE1; trivial. } { rewrite H_OBS in NOT_OCCUR; discriminate. } { inv RANK_ZERO. }
Qed.

Definition subst1 (x : ivar) (t : trm) (p : frm) : frm :=
  proj1_sig (subst1_uniquely_exists x t p).

Lemma subst1_preserves_rank (x : ivar) (t : trm) (p : frm)
  : frm_depth (subst1 x t p) = frm_depth p.
Proof.
  unfold subst1. destruct (subst1_uniquely_exists x t p) as [p' [SUBST RANK_EQ]]; simpl. lia.
Qed.

Lemma subst1_satisfies_spec (x : ivar) (t : trm) (p : frm)
  : subst1_spec x t p (subst1 x t p).
Proof.
  unfold subst1. destruct (subst1_uniquely_exists x t p) as [q' [SUBST [RANK_EQ UNIQUE]]]; simpl. done. 
Qed.

Lemma subst1_satisfies_spec_uniquely (x : ivar) (t : trm) (p : frm)
  : forall q, subst1_spec x t p q <-> q = subst1 x t p.
Proof.
  intros q. unfold subst1. destruct (subst1_uniquely_exists x t p) as [p' [SPEC [RANK_EQ UNIQUE]]]; simpl.
  split. { eapply UNIQUE. } { intros ->. exact SPEC. }
Qed.

Lemma subst1_unfold (x : ivar) (t : trm) (p : frm) :
  subst1 x t p =
  match p with
  | Rel_frm R ts => Rel_frm R (subst_trms (one_subst x t) ts)
  | Eqn_frm t1 t2 => Eqn_frm (subst_trm (one_subst x t) t1) (subst_trm (one_subst x t) t2)
  | Neg_frm p1 => Neg_frm (subst1 x t p1)
  | Imp_frm p1 p2 => Imp_frm (subst1 x t p1) (subst1 x t p2)
  | All_frm y p1 =>
    let z : ivar := fresh_var x t p1 in
    if eq_dec x y then All_frm y p1 else if is_free_in_trm y t then All_frm z (subst1 x t (subst1 y (Var_trm z) p1)) else All_frm y (subst1 x t p1)
  end.
Proof.
  unfold subst1 at 1. symmetry. destruct (subst1_uniquely_exists x t p) as [q' [SUBST [RANK_EQ UNIQUE]]]. simpl proj1_sig. destruct p.
  - eapply UNIQUE. simpl. eapply subst1_Atomic; trivial.
  - eapply UNIQUE. simpl. eapply subst1_Atomic; trivial.
  - eapply UNIQUE. eapply subst1_Neg; eapply subst1_satisfies_spec.
  - eapply UNIQUE. eapply subst1_Imp; eapply subst1_satisfies_spec.
  - destruct (eq_dec x y) as [EQ | NE].
    + eapply UNIQUE. eapply subst1_All_EQ; trivial.
    + destruct (is_free_in_trm y t) as [ | ] eqn: H_OBS.
      * eapply UNIQUE. eapply subst1_All_RENAME with (p1' := subst1 y (Var_trm (fresh_var x t p)) p); trivial; eapply subst1_satisfies_spec.
      * eapply UNIQUE. eapply subst1_All_FRESH; trivial. eapply subst1_satisfies_spec.
Qed.

Theorem subst1_nice x t p
  : subst1 x t p ≡ subst_frm (one_subst x t) p.
Proof.
  revert x t. pattern p. revert p. eapply frm_depth_lt_ind; ii. destruct p.
  - rewrite subst1_unfold. reflexivity.
  - rewrite subst1_unfold. reflexivity.
  - rewrite subst1_unfold. simpl. eapply alpha_Neg_frm; eapply IH; simpl; lia.
  - rewrite subst1_unfold. simpl. eapply alpha_Imp_frm; eapply IH; simpl; lia.
  - rewrite subst1_unfold. simpl.
    set (chi := chi_frm (one_subst x t) (All_frm y p)). set (z := fresh_var x t p).
    destruct (eq_dec x y) as [EQ | NE].
    { subst y. eapply alpha_All_frm with (z := chi).
      - eapply alpha_equiv_eq_intro. rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same. intros w w_free.
        unfold subst_compose. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec w x) as [EQ1 | NE1].
        + rewrite subst_trm_unfold. destruct (eq_dec chi chi) as [EQ2 | NE2]; done.
        + rewrite subst_trm_unfold. destruct (eq_dec w chi) as [EQ2 | NE2]; done.
      - pose proof (@chi_frm_is_fresh_in_subst) as claim1.
        specialize claim1 with (p := All_frm x p) (s := one_subst x t).
        unfold frm_is_fresh_in_subst in claim1. rewrite forallb_forall in claim1. specialize (claim1 chi).
        fold chi in claim1. unfold "∘"%prg in claim1. rewrite negb_true_iff in claim1.
        rewrite fv_is_free_in_frm in claim1. destruct (is_free_in_frm chi (All_frm x p)) as [ | ] eqn: H_OBS.
        + rewrite is_free_in_frm_unfold in H_OBS. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in H_OBS.
          specialize (claim1 eq_refl). unfold one_subst, cons_subst, nil_subst in claim1. destruct (eq_dec chi x) as [EQ | NE].
          * done.
          * rewrite is_free_in_trm_unfold in claim1. rewrite Nat.eqb_neq in claim1. done.
        + reflexivity.
      - rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. done.
    }
    destruct (is_free_in_trm y t) as [ | ] eqn: H_OBS.
    { eapply alpha_All_frm with (z := z).
      - assert (rank_LT1 : frm_depth (subst1 y (Var_trm z) p) < frm_depth (All_frm y p)).
        { rewrite subst1_preserves_rank. simpl; lia. }
        pose proof (IH _ rank_LT1 x t) as claim1.
        assert (rank_LT2 : frm_depth p < frm_depth (All_frm y p)).
        { simpl; lia. }
        pose proof (IH _ rank_LT2 y (Var_trm z)) as claim2.
        etransitivity. { eapply subst_nil_frm. intros w w_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec w z) as [EQ1 | NE1]; done. }
        etransitivity. { eapply claim1. }
        apply subst_frm_compat_alpha_equiv with (s := one_subst x t) in claim2.
        rewrite claim2.
        rewrite <- subst_compose_frm_spec. rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
        intros w w_free. unfold subst_compose. unfold one_subst, cons_subst, nil_subst.
        destruct (eq_dec w y) as [EQ1 | NE1].
        { do 2 rewrite subst_trm_unfold. destruct (eq_dec z x) as [EQ2 | NE2].
          { pose proof (fresh_var_ne_x x t p). subst z. done. }
          { destruct (eq_dec chi chi) as [EQ3 | NE3]; done. }
        }
        { rewrite subst_trm_unfold. destruct (eq_dec w x) as [EQ2 | NE2].
          { subst w. symmetry. pose proof (@chi_frm_is_fresh_in_subst (All_frm y p) (one_subst x t)) as claim3.
            unfold frm_is_fresh_in_subst in claim3. rewrite forallb_forall in claim3. specialize (claim3 x).
            unfold "∘"%prg in claim3. rewrite negb_true_iff in claim3. fold chi in claim3.
            assert (claim4 : In x (fvs_frm (All_frm y p))).
            { rewrite fv_is_free_in_frm. simpl. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. done. }
            apply claim3 in claim4. unfold one_subst, cons_subst, nil_subst in claim4. destruct (eq_dec x x) as [EQ' | NE'].
            - eapply subst_nil_trm. intros u u_free. destruct (eq_dec u chi) as [EQ'' | NE'']; done.
            - done.
          }
          { rewrite subst_trm_unfold. destruct (eq_dec w chi) as [EQ3 | NE3].
            - subst w. pose proof (@chi_frm_is_fresh_in_subst (All_frm y p) (one_subst x t)) as claim3. fold chi in claim3.
              unfold frm_is_fresh_in_subst in claim3. rewrite forallb_forall in claim3. specialize (claim3 chi).
              unfold "∘"%prg in claim3. rewrite negb_true_iff in claim3. fold chi in claim3.
              assert (claim4: In chi (fvs_frm (All_frm y p))).
              { rewrite fv_is_free_in_frm. rewrite is_free_in_frm_unfold. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. done. }
              apply claim3 in claim4. unfold one_subst, cons_subst, nil_subst in claim4.
              destruct (eq_dec chi x) as [EQ' | NE'].
              + done.
              + rewrite is_free_in_trm_unfold in claim4. rewrite Nat.eqb_neq in claim4. done.
            - done.
          }
        }
      - rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. done.
      - rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. destruct (eq_dec z chi) as [EQ' | NE'].
        + done.
        + left. pose proof (fresh_var_ne_x x t p) as claim1. pose proof (fresh_var_is_not_free_in_trm x t p) as claim2. pose proof (fresh_var_is_not_free_in_frm x t p) as claim3.
          rewrite <- frm_is_fresh_in_subst_iff. unfold frm_is_fresh_in_subst. rewrite forallb_forall.
          intros w w_free. rewrite fv_is_free_in_frm in w_free. unfold "∘"%prg. rewrite negb_true_iff.
          unfold one_subst, cons_subst, nil_subst. fold z in claim1, claim2, claim3.
          destruct (eq_dec w y) as [EQ1 | NE1].
          { rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done. }
          { destruct (eq_dec w x) as [EQ2 | NE2].
            - subst w. done.
            - rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros H_contra. done.
          }
    }
    { assert (rank_LT1 : frm_depth p < frm_depth (All_frm y p)) by now simpl; lia.
      pose proof (claim1 := IH _ rank_LT1 x t). eapply alpha_All_frm with (z := z).
      - apply subst_frm_compat_alpha_equiv with (s := one_subst y (Var_trm z)) in claim1.
        rewrite claim1. do 2 rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
        intros w w_free. unfold subst_compose. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec w x) as [EQ1 | NE1].
        { subst w. destruct (eq_dec x y) as [EQ2 | NE2].
          - done.
          - eapply equiv_subst_in_trm_implies_subst_trm_same. intros u u_free. destruct (eq_dec u y) as [EQ3 | NE3].
            + subst u. done.
            + destruct (eq_dec u chi) as [EQ4 | NE4].
              * subst u. pose proof (@chi_frm_is_fresh_in_subst (All_frm y p) (one_subst x t)) as claim2. fold chi in claim2.
                unfold frm_is_fresh_in_subst in claim2. rewrite forallb_forall in claim2. 
                assert (claim3 : In x (fvs_frm (All_frm y p))).
                { rewrite fv_is_free_in_frm. rewrite is_free_in_frm_unfold. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. split. done. done. }
                apply claim2 in claim3. unfold "∘"%prg in claim3. rewrite negb_true_iff in claim3.
                unfold one_subst, cons_subst, nil_subst in claim3. destruct (eq_dec x x) as [EQ5 | NE5]; done.
              * done.
        }
        { rewrite subst_trm_unfold. destruct (eq_dec w y) as [EQ2 | NE2].
          - rewrite subst_trm_unfold. destruct (eq_dec chi chi) as [EQ3 | NE3]; done.
          - rewrite subst_trm_unfold. rename w into u. destruct (eq_dec u chi) as [EQ4 | NE4].
            + subst u. pose proof (@chi_frm_is_fresh_in_subst (All_frm y p) (one_subst x t)) as claim2. fold chi in claim2.
              unfold frm_is_fresh_in_subst in claim2. rewrite forallb_forall in claim2.
              assert (claim3 : In chi (fvs_frm (All_frm y p))).
              { rewrite fv_is_free_in_frm. rewrite is_free_in_frm_unfold. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. split. done. done. }
              apply claim2 in claim3. unfold "∘"%prg in claim3. rewrite negb_true_iff in claim3.
              unfold one_subst, cons_subst, nil_subst in claim3. destruct (eq_dec chi x) as [EQ5 | NE5]. done. rewrite is_free_in_trm_unfold, Nat.eqb_neq in claim3. done.
            + done.
        }
      - rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. destruct (eq_dec z y) as [EQ1 | NE1].
        + right. done.
        + left. rewrite alpha_equiv_compat_fresh with (ALPHA := claim1).
          pose proof (@chi_frm_is_fresh_in_subst (All_frm y p) (one_subst x t)) as claim2. fold chi in claim2.
          unfold frm_is_fresh_in_subst in claim2. rewrite forallb_forall in claim2.
          destruct (is_free_in_frm z p) as [ | ] eqn: H_OBS1.
          * pose proof (fresh_var_is_not_free_in_frm x t p) as claim3. subst z. done.
          * destruct (is_free_in_frm z (subst_frm (one_subst x t) p)) as [ | ] eqn: H_OBS2.
            { rewrite <- free_in_frm_wrt_iff in H_OBS2. unfold free_in_frm_wrt in H_OBS2.
              destruct H_OBS2 as (u&u_free&FREE). unfold one_subst, cons_subst, nil_subst in FREE. destruct (eq_dec u x) as [EQ' | NE'].
              - subst u. pose proof (fresh_var_is_not_free_in_trm x t p) as claim3. subst z. done.
              - rewrite is_free_in_trm_unfold, Nat.eqb_eq in FREE. subst u. done.
            }
            { done. }
      - destruct (eq_dec z chi) as [EQ' | NE'].
        + rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. done.
        + assert (ALPHA : subst_frm (cons_subst y (Var_trm chi) (one_subst x t)) p ≡ subst_frm (one_subst y (Var_trm chi)) (subst1 x t p)).
          { pose proof (@subst_frm_compat_alpha_equiv (subst1 x t p) (subst_frm (one_subst x t) p) (one_subst y (Var_trm chi)) claim1) as claim2.
            rewrite claim2. rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose. unfold one_subst, cons_subst, nil_subst.
            destruct (eq_dec u x) as [EQ1 | NE1].
            - subst u. destruct (eq_dec x y) as [EQ2 | NE2].
              + subst y. done.
              + symmetry. eapply subst_nil_trm. intros w w_free. destruct (eq_dec w y) as [EQ3 | NE3].
                * subst w. done.
                * done.
            - rewrite subst_trm_unfold. destruct (eq_dec u y) as [EQ2 | NE2]; done.
          }
          rewrite is_free_in_frm_unfold. rewrite andb_false_iff. left.
          rewrite alpha_equiv_compat_fresh with (ALPHA := ALPHA).
          assert (claim2 : is_free_in_frm z (subst1 x t p) = false).
          { rewrite alpha_equiv_compat_fresh with (ALPHA := claim1).
            destruct (is_free_in_frm z (subst_frm (one_subst x t) p)) as [ | ] eqn: H_OBS1; trivial.
            rewrite <- free_in_frm_wrt_iff in H_OBS1. unfold free_in_frm_wrt in H_OBS1.
            destruct H_OBS1 as (u&u_free&FREE). unfold one_subst, cons_subst, nil_subst in FREE.
            destruct (eq_dec u x) as [EQ1 | NE1].
            - pose proof (fresh_var_is_not_free_in_trm x t p); subst z; done.
            - rewrite is_free_in_trm_unfold in FREE. rewrite Nat.eqb_eq in FREE. subst u.
              pose proof (fresh_var_is_not_free_in_frm x t p); subst z; done.
          }
          pose proof (@one_subst_free_assoc_lemma3 y chi z (subst1 x t p) NE') as claim3.
          destruct (is_free_in_frm z (subst_frm (one_subst y (Var_trm chi)) (subst1 x t p))) as [ | ] eqn: H_OBS2.
          * specialize (claim3 eq_refl). done.
          * done.
    }
Qed.

Lemma subst1_id x p
  : subst1 x (Var_trm x) p = p.
Proof.
  revert x. pattern p. revert p. eapply frm_depth_lt_ind.
  ii. destruct p.
  - rewrite subst1_unfold. f_equal. rewrite subst_nil_trms; trivial.
    intros u u_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec u x) as [EQ | NE]; done.
  - rewrite subst1_unfold. f_equal. rewrite subst_nil_trm; trivial.
    { intros u u_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec u x) as [EQ | NE]; done. }
    rewrite subst_nil_trm; trivial.
    { intros u u_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec u x) as [EQ | NE]; done. }
  - rewrite subst1_unfold. f_equal. eapply IH. simpl; done.
  - rewrite subst1_unfold. f_equal; eapply IH; simpl; done.
  - rewrite subst1_unfold. destruct (eq_dec x y) as [EQ | NE].
    + simpl. reflexivity.
    + simpl. cbn zeta. destruct (Nat.eqb x y) as [ | ] eqn: H_OBS.
      * rewrite Nat.eqb_eq in H_OBS. done.
      * f_equal. eapply IH. simpl; lia.
Qed.

End SINGLE_SUBSTITUTION.

Definition Bot_frm : frm :=
  All_frm 0 (Neg_frm (Eqn_frm (Var_trm 0) (Var_trm 0))).

Definition Con_frm (p1 : frm) (p2 : frm) : frm :=
  Neg_frm (Imp_frm p1 (Neg_frm p2)).

Definition Dis_frm (p1 : frm) (p2 : frm) : frm :=
  Neg_frm (Con_frm (Neg_frm p1) (Neg_frm p2)).

Definition Iff_frm (p1 : frm) (p2 : frm) : frm :=
  Con_frm (Imp_frm p1 p2) (Imp_frm p2 p1).

Definition Exs_frm (y : ivar) (p1 : frm) : frm :=
  Neg_frm (All_frm y (Neg_frm p1)).

Definition is_sentence (p : frm) : Prop :=
  forall z : ivar, is_not_free_in_frm z p.

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
  induction p as [R ts | t1 t2 | p1 IH1 | p1 IH1 p2 IH2 | y p1 IH1].

#[global]
Tactic Notation "trm_ind2" ident( t ) ident( t' ) :=
  revert t'; induction t as [x | f ts | c]; intros [x' | f' ts' | c'].

#[global]
Tactic Notation "trms_ind2" ident( ts ) ident( ts' ) :=
  revert ts'; induction ts as [ | n t ts IH]; [intros ts'; pattern ts'; revert ts'; apply trms_case0 | intros ts'; pattern ts'; revert ts'; apply trms_caseS; intros t' ts'].

#[global]
Tactic Notation "frm_ind2" ident( p ) ident( p' ) :=
  revert p';
  induction p as [R ts | t1 t2 | p1 IH1 | p1 IH1 p2 IH2 | y p1 IH1];
  intros [R' ts' | t1' t2' | p1' | p1' p2' | y' p1'].

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
  - pose proof (relation_symbols_hasEqDec R R') as [R_eq_R' | R_ne_R']...
    subst R'. pose proof (trms_eq_dec (L.(relation_arity_table) R) ts ts') as [EQ | NE]...
    right. intros CONTRA. eapply NE. inv CONTRA.
    apply @projT2_eq_fromEqDec with (B := fun R : relation_symbols L => trms L (L.(relation_arity_table) R)) in H0.
    + exact H0.
    + exact relation_symbols_hasEqDec.
  - pose proof (trm_eq_dec t1 t1') as [? | ?]; pose proof (trm_eq_dec t2 t2') as [? | ?]...
  - pose proof (IH1 p1') as [? | ?]...
  - pose proof (IH1 p1') as [? | ?]; pose proof (IH2 p2') as [? | ?]...
  - pose proof (ivar_hasEqDec y y') as [? | ?]; pose proof (IH1 p1') as [? | ?]...
Defined.

#[global] Instance frm_hasEqDec : hasEqDec (frm L) := frm_eq_dec.

End EQ_DEC.

Section EXTEND_LANGUAGE_BY_ADDING_CONSTANTS.

#[local] Infix "=~=" := is_similar_to : type_scope.

Section SIMILARITY.

Let arity : Set := nat.

Context (_function_symbols : Set) (_relation_symbols : Set) (_function_arity_table : _function_symbols -> arity) (_relation_arity_table : _relation_symbols -> arity).

Definition mkL_with_constant_symbols (_constant_symbols : Set) : language :=
  {|
    function_symbols := _function_symbols;
    constant_symbols := _constant_symbols;
    relation_symbols := _relation_symbols;
    function_arity_table := _function_arity_table;
    relation_arity_table := _relation_arity_table;
  |}.

Context (_constant_symbols : Set) (L := mkL_with_constant_symbols _constant_symbols).

Section GENERAL_CASE.

Context (_constant_symbols' : Set) (L' := mkL_with_constant_symbols _constant_symbols').

Hypothesis constant_symbols_similarity : Similarity _constant_symbols _constant_symbols'.

Inductive trm_similarity : Similarity (trm L) (trm L') :=
  | Var_sim (x : ivar)
    : @Var_trm L x =~= @Var_trm L' x
  | Fun_sim (f : _function_symbols) (ts : trms L (L.(function_arity_table) f)) (ts' : trms L' (L'.(function_arity_table) f))
    (ts_SIM : ts =~= ts')
    : @Fun_trm L f ts =~= @Fun_trm L' f ts'
  | Con_sim (c : _constant_symbols) (c' : _constant_symbols')
    (c_SIM : c =~= c')
    : @Con_trm L c =~= @Con_trm L' c'
with trms_similarity : forall n : arity, Similarity (trms L n) (trms L' n) :=
  | O_trms_sim
    : @O_trms L =~= @O_trms L'
  | S_trms_sim (n : arity) (t : trm L) (t' : trm L') (ts : trms L n) (ts' : trms L' n)
    (t_SIM : t =~= t')
    (ts_SIM : ts =~= ts')
    : @S_trms L n t ts =~= @S_trms L' n t' ts'.

#[local] Instance trm_similarity_instance : Similarity (trm L) (trm L') :=
  trm_similarity.

#[local] Instance trms_similarity_instance (n : arity) : Similarity (trms L n) (trms L' n) :=
  trms_similarity n.

Inductive frm_similarity : Similarity (frm L) (frm L') :=
  | Rel_sim (R : _relation_symbols) (ts : trms L (L.(relation_arity_table) R)) (ts' : trms L' (L'.(relation_arity_table) R))
    (ts_SIM : ts =~= ts')
    : @Rel_frm L R ts =~= @Rel_frm L' R ts'
  | Eqn_sim (t1 : trm L) (t1' : trm L') (t2 : trm L) (t2' : trm L')
    (t1_SIM : t1 =~= t1')
    (t2_SIM : t2 =~= t2')
    : @Eqn_frm L t1 t2 =~= @Eqn_frm L' t1' t2'
  | Neg_sim (p1 : frm L) (p1' : frm L')
    (p1_SIM : p1 =~= p1')
    : @Neg_frm L p1 =~= @Neg_frm L' p1'
  | Imp_sim (p1 : frm L) (p1' : frm L') (p2 : frm L) (p2' : frm L')
    (p1_SIM : p1 =~= p1')
    (p2_SIM : p2 =~= p2')
    : @Imp_frm L p1 p2 =~= @Imp_frm L' p1' p2'
  | All_sim (y : ivar) (p1 : frm L) (p1' : frm L')
    (p1_SIM : p1 =~= p1')
    : @All_frm L y p1 =~= @All_frm L' y p1'.

#[local] Instance frm_similarity_instance : Similarity (frm L) (frm L') :=
  frm_similarity.

Variant frms_similarity (ps : ensemble (frm L)) (ps' : ensemble (frm L')) : Prop :=
  | is_extend_sig_frms_of_intro
    (BSIM : forall p' : frm L', forall IN : p' \in ps', exists p : frm L, p \in ps /\ p =~= p')
    (FSIM : forall p : frm L, forall IN : p \in ps, exists p' : frm L', p' \in ps' /\ p =~= p')
    : frms_similarity ps ps'.

#[local] Instance frms_similarity_instance : Similarity (ensemble (frm L)) (ensemble (frm L')) :=
  frms_similarity.

#[local] Instance subst_similarity_instance : Similarity (subst L) (subst L') :=
  fun s : subst L => fun s' : subst L' => forall z : ivar, s z =~= s' z.

Lemma fvs_trm_compat_similarity (t : trm L) (t' : trm L')
  (t_SIM : t =~= t')
  : fvs_trm t = fvs_trm t'
with fvs_trms_compat_similarity n (ts : trms L n) (ts' : trms L' n)
  (ts_SIM : ts =~= ts')
  : fvs_trms ts = fvs_trms ts'.
Proof with eauto with *.
  - induction t_SIM.
    + reflexivity.
    + change (fvs_trms ts = fvs_trms ts'). eapply fvs_trms_compat_similarity. exact ts_SIM.
    + reflexivity.
  - induction ts_SIM.
    + reflexivity.
    + change (fvs_trm t ++ fvs_trms ts = fvs_trm t' ++ fvs_trms ts'). f_equal...
Qed.

Lemma fvs_frm_compat_similarity (p : frm L) (p' : frm L')
  (p_SIM : p =~= p')
  : fvs_frm p = fvs_frm p'.
Proof with try done.
  induction p_SIM; simpl...
  - eapply fvs_trms_compat_similarity...
  - f_equal; eapply fvs_trm_compat_similarity...
Qed.

Lemma subst_trm_compat_similarity (s : subst L) (s' : subst L') (t : trm L) (t' : trm L')
  (s_SIM : s =~= s')
  (t_SIM : t =~= t')
  : subst_trm s t =~= subst_trm s' t'
with subst_trms_compat_similarity n (s : subst L) (s' : subst L') (ts : trms L n) (ts' : trms L' n)
  (s_SIM : s =~= s')
  (ts_SIM : ts =~= ts')
  : subst_trms s ts =~= subst_trms s' ts'.
Proof with eauto with *.
  - red in t_SIM. induction t_SIM.
    + cbn. eapply s_SIM.
    + do 2 rewrite subst_trm_unfold. econstructor 2.
      eapply subst_trms_compat_similarity. exact s_SIM. exact ts_SIM.
    + econstructor 3. exact c_SIM.
  - revert s s' s_SIM. induction ts_SIM; simpl; ii.
    + econstructor 1.
    + rewrite subst_trms_unfold.
      replace (subst_trms s (S_trms n t ts)) with (@S_trms L n (subst_trm s t) (subst_trms s ts)) by reflexivity.
      econstructor 2.
      * eapply subst_trm_compat_similarity. exact s_SIM. exact t_SIM.
      * eapply IHts_SIM. exact s_SIM.
Qed.

Lemma chi_frm_compat_similarity (s : subst L) (s' : subst L') (p : frm L) (p' : frm L')
  (s_SIM : s =~= s')
  (p_SIM : p =~= p')
  : chi_frm s p = chi_frm s' p'.
Proof with eauto with *.
  unfold chi_frm. simpl. f_equal. eapply maxs_ext. intros n. unfold "∘".
  split; intros H_in; eapply in_map_iff; apply in_map_iff in H_in; destruct H_in as [x [<- H_in]].
  - exists x. split.
    + unfold last_ivar_trm. eapply maxs_ext.
      pose proof (s_SIM x) as SIM. i.
      enough (ENOUGH : fvs_trm (s x) = fvs_trm (s' x)) by now rewrite ENOUGH.
      eapply fvs_trm_compat_similarity...
    + replace (fvs_frm p') with (fvs_frm p)...
      eapply fvs_frm_compat_similarity...
  - exists x. split.
    + unfold last_ivar_trm. eapply maxs_ext.
      pose proof (s_SIM x) as SIM. i.
      enough (ENOUGH : fvs_trm (s x) = fvs_trm (s' x)) by now rewrite ENOUGH.
      eapply fvs_trm_compat_similarity...
    + replace (fvs_frm p) with (fvs_frm p')...
      symmetry. eapply fvs_frm_compat_similarity...
Qed.

Lemma subst_frm_compat_simliarity (s : subst L) (s' : subst L') (p : frm L) (p' : frm L')
  (s_SIM : s =~= s')
  (p_SIM : p =~= p')
  : @subst_frm L s p =~= @subst_frm L' s' p'.
Proof with try done.
  revert s' s s_SIM. induction p_SIM; simpl; i.
  - econstructor 1. eapply subst_trms_compat_similarity...
  - econstructor 2; eapply subst_trm_compat_similarity...
  - econstructor 3...
  - econstructor 4...
  - assert (claim1 : chi_frm s (All_frm y p1) = chi_frm s' (All_frm y p1')).
    { eapply chi_frm_compat_similarity... eapply All_sim... }
    rewrite claim1. eapply All_sim. eapply IHp_SIM.
    ii. unfold cons_subst. pose proof (s_SIM z) as claim2.
    destruct (eq_dec z y)... subst z. econstructor.
Qed.

End GENERAL_CASE.

End SIMILARITY.

Section AUGMENTED_LANGUAGE.

Definition augmented_language (L : language) (constant_symbols' : Set) : language :=
  {|
    function_symbols := L.(function_symbols);
    constant_symbols := L.(constant_symbols) + constant_symbols';
    relation_symbols := L.(relation_symbols);
    function_arity_table := L.(function_arity_table);
    relation_arity_table := L.(relation_arity_table);
  |}.

Context {L : language} {constant_symbols' : Set}.

#[local] Notation L' := (augmented_language L constant_symbols').

#[local] Instance constant_symbols_similarity_instance_in_section_augmented_language : Similarity L.(constant_symbols) L'.(constant_symbols) :=
  fun c : L.(constant_symbols) => fun c' : L.(constant_symbols) + constant_symbols' => inl c = c'.

#[local] Instance trm_similarity_instance_in_section_augmented_language : Similarity (trm L) (trm L') :=
  trm_similarity_instance L.(function_symbols) L.(relation_symbols) L.(function_arity_table) L.(relation_arity_table) L.(constant_symbols) L'.(constant_symbols) constant_symbols_similarity_instance_in_section_augmented_language.

#[local] Instance trms_similarity_instance_in_section_augmented_language n : Similarity (trms L n) (trms L' n) :=
  trms_similarity_instance L.(function_symbols) L.(relation_symbols) L.(function_arity_table) L.(relation_arity_table) L.(constant_symbols) L'.(constant_symbols) constant_symbols_similarity_instance_in_section_augmented_language n.

#[local] Instance frm_similarity_instance_in_section_augmented_language : Similarity (frm L) (frm L') :=
  frm_similarity_instance L.(function_symbols) L.(relation_symbols) L.(function_arity_table) L.(relation_arity_table) L.(constant_symbols) L'.(constant_symbols) constant_symbols_similarity_instance_in_section_augmented_language.

#[local] Instance frms_similarity_instance_in_section_augmented_language : Similarity (ensemble (frm L)) (ensemble (frm L')) :=
  frms_similarity_instance L.(function_symbols) L.(relation_symbols) L.(function_arity_table) L.(relation_arity_table) L.(constant_symbols) L'.(constant_symbols) constant_symbols_similarity_instance_in_section_augmented_language.

#[local] Instance subst_similarity_instance_in_section_augmented_language : Similarity (subst L) (subst L') :=
  subst_similarity_instance L.(function_symbols) L.(relation_symbols) L.(function_arity_table) L.(relation_arity_table) L.(constant_symbols) L'.(constant_symbols) constant_symbols_similarity_instance_in_section_augmented_language.

End AUGMENTED_LANGUAGE.

End EXTEND_LANGUAGE_BY_ADDING_CONSTANTS.

#[global] Bind Scope lang_scope with frm.
#[global] Declare Custom Entry fol_frm_viewer.

Declare Scope subst_scope.
Delimit Scope subst_scope with subst.

Module FolNotations.

Notation " R '@@' ts " := (Rel_frm R ts) (R constr, ts constr, in custom fol_frm_viewer at level 0). 
Notation " t1 '=' t2 " := (Eqn_frm t1 t2) (t1 constr, t2 constr, in custom fol_frm_viewer at level 0).
Notation " 'False' " := (Bot_frm) (in custom fol_frm_viewer at level 0, no associativity).
Notation " '~' p1 " := (Neg_frm p1) (in custom fol_frm_viewer at level 2, right associativity).
Notation " p1 '/\' p2 " := (Con_frm p1 p2) (in custom fol_frm_viewer at level 2, right associativity).
Notation " p1 '\/' p2 " := (Dis_frm p1 p2) (in custom fol_frm_viewer at level 3, right associativity).
Notation " p1 '->' p2 " := (Imp_frm p1 p2) (in custom fol_frm_viewer at level 4, right associativity).
Notation " p1 '<->' p2 " := (Iff_frm p1 p2) (in custom fol_frm_viewer at level 4, no associativity).
Notation " 'forall' y ',' p1 " := (All_frm y p1) (y constr, in custom fol_frm_viewer at level 4, p1 constr).
Notation " 'exists' y ',' p1 " := (Exs_frm y p1) (y constr, in custom fol_frm_viewer at level 4, p1 constr).
Notation " p " := p (in custom fol_frm_viewer at level 0, p ident).
Notation " '(' p ')' " := p (in custom fol_frm_viewer at level 0, p at level 10).
Notation " '$' p '$' " := p (p custom fol_frm_viewer at level 10, at level 0, format "'$' p '$'", no associativity) : lang_scope.

Notation " '⟦' s '⟧' p " := (subst_frm s p) (only printing, in custom fol_frm_viewer at level 0, right associativity, format "'⟦'  s  '⟧' p").
Notation " '⟦' s '⟧' t " := (subst_trm s t) (only printing, in custom fol_frm_viewer at level 0, right associativity).
Notation " '⟦' s '⟧' ts " := (subst_trms s ts) (only printing, in custom fol_frm_viewer at level 0, right associativity).
Notation " '⟦' s '⟧' p " := (subst_frm s p) : lang_scope.

Notation " x '↦' t ';' s " := (cons_subst x t s) : subst_scope.
Notation " 'ι' " := (nil_subst) : subst_scope.
Notation " x '↦' t " := (one_subst x t) : subst_scope.
Notation " s2 '∘' s1 " := (subst_compose s1 s2) : subst_scope.

End FolNotations.
