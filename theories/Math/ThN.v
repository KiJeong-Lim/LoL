Require Import LoL.Prelude.Prelude.

Lemma S_eq_O_elim {A : Type} {n : nat}
  (S_eq_O : S n = O)
  : A.
Proof.
  set (f := fun n : nat => match n with O => True | S n' => False end).
  apply f_equal with (f := f) in S_eq_O. simpl in S_eq_O.
  enough (H_contra : False) by contradiction H_contra.
  rewrite S_eq_O. econstructor.
Defined.

Lemma le_case_eq {n : nat} (phi : n <= n -> Prop)
  (phi_eq : phi (@le_n n))
  : forall H_le : n <= n, phi H_le.
Proof.
  intros H_le.
  refine (
    let claim :=
      match H_le in le _ m return forall H_obs : m = n, phi (@eq_ind _ _ (fun m' : nat => n <= m') H_le _ H_obs) with
      | @le_n _ => fun H_obs: n = n => _
      | @le_S _ m' H_le' => fun H_obs: S m' = n => _
      end
    in _
  ).
  { eapply claim with (H_obs := eq_refl). }
  Unshelve.
  - rewrite eq_pirrel_fromEqDec with (H_eq1 := H_obs) (H_eq2 := eq_refl). exact (phi_eq).
  - lia.
Qed.

Lemma le_case_lt {n : nat} {m : nat} (H_le : m <= n) (phi : m <= S n -> Prop)
  (phi_lt: forall H_le' : m <= n, phi (@le_S m n H_le'))
  : forall H_lt : m <= S n, phi H_lt.
Proof.
  intros H_lt.
  refine (
    let claim :=
      match H_lt in le _ n' return forall H_obs : n' = S n, phi (@eq_ind _ _ (fun n' => m <= n') H_lt _ H_obs) with
      | @le_n _ => _
      | @le_S _ m' H_le' => _
      end
    in _
  ).
  { eapply claim with (H_obs := eq_refl). }
  Unshelve.
  - lia. 
  - intros H_obs. assert (m' = n) as H_eq by now apply f_equal with (f := pred) in H_obs. subst m'.
    rewrite eq_pirrel_fromEqDec with (H_eq1 := H_obs) (H_eq2 := eq_refl). exact (phi_lt H_le').
Qed.

Theorem le_pirrel (n : nat) (m : nat)
  (H_le1 : n <= m)
  (H_le2 : n <= m)
  : H_le1 = H_le2.
Proof.
  assert (m = (m - n) + n)%nat as claim by lia.
  remember (m - n)%nat as k eqn: H_eq in claim.
  clear H_eq. revert n m H_le1 H_le2 claim.
  induction k as [ | k IH]; simpl.
  - i. subst m.
    induction H_le1 using le_case_eq.
    induction H_le2 using le_case_eq.
    reflexivity.
  - i. subst m.
    assert (n <= k + n) as LE by lia.
    induction H_le1 using (le_case_lt LE).
    induction H_le2 using (le_case_lt LE).
    eapply f_equal. eapply IH. reflexivity.
Qed.

Lemma greater_than_iff (x : nat) (y : nat)
  : x > y <-> (exists z : nat, x = S (y + z)).
Proof with try (lia || eauto).
  split.
  - intros Hgt. induction Hgt as [ | m Hgt [z x_eq]]; [exists 0 | rewrite x_eq]...
  - intros [z Heq]...
Qed.

Section CANTOR_PAIRING.

Import Nat.

Fixpoint sum_from_0_to (n : nat) {struct n} : nat :=
  match n with
  | O => 0
  | S n' => n + sum_from_0_to n'
  end.

Lemma sum_from_0_to_spec (n : nat)
  : 2 * sum_from_0_to n = n * (S n).
Proof.
  induction n; simpl in *; lia.
Qed.

Fixpoint cp (n : nat) {struct n} : nat * nat :=
  match n with
  | O => (O, O)
  | S n' =>
    match cp n' with
    | (O, y) => (S y, O)
    | (S x, y) => (x, S y)
    end
  end.

Definition cpInv (x : nat) (y : nat) : nat :=
  sum_from_0_to (x + y) + y.

Lemma cpInv_leftInv (n : nat)
  : cpInv (fst (cp n)) (snd (cp n)) = n.
Proof with lia || eauto.
  induction n as [ | n IH]; simpl...
  destruct (cp n) as [x y] eqn: H_OBS. simpl in *. destruct x as [ | x']; subst n; cbn.
  - repeat rewrite add_0_r...
  - rewrite add_comm with (n := x'). simpl. rewrite add_comm with (m := x')... 
Qed.

Lemma cpInv_rightInv (x : nat) (y : nat)
  : cp (cpInv x y) = (x, y).
Proof with lia || eauto.
  unfold cpInv. remember (x + y) as z eqn: z_eq. revert y x z_eq. induction z as [ | z IH].
  - simpl; ii. destruct x as [ | x'], y as [ | y']...
  - induction y as [ | y IHy]; ii.
    + rewrite z_eq. rewrite add_0_r with (n := x). rewrite add_0_r with (n := x) in z_eq. subst x.
      rewrite add_0_r with (n := sum_from_0_to (S z)). simpl. rewrite <- add_comm. erewrite -> IH with (x := 0)...
    + assert (claim1 : z = x + y) by lia. subst z. clear z_eq. rename x into n, y into m. rewrite add_comm with (m := S m).
      assert (claim2 : S (n + m) = (S n) + m) by lia. apply IHy in claim2.
      simpl in *. rewrite add_comm. simpl. destruct (cp (n + m + sum_from_0_to (n + m) + m)) as [x y] eqn: H_OBS.
      destruct x as [ | x']; inv claim2...
Qed.

Theorem cp_spec (n : nat) (x : nat) (y : nat)
  : cp n = (x, y) <-> n = cpInv x y.
Proof.
  split; intros EQ.
  - rewrite <- cpInv_leftInv with (n := n). rewrite EQ. reflexivity.
  - subst n. rewrite <- cpInv_rightInv with (x := x) (y := y). reflexivity.
Qed.

Lemma fst_cp_le (n : nat)
  : fst (cp n) <= n.
Proof.
  destruct (cp n) as [x y] eqn: H_OBS. rewrite cp_spec in H_OBS.
  subst n. unfold cpInv. simpl. enough (ENOUGH : x + y <= sum_from_0_to (x + y)) by lia.
  induction (x + y) as [ | z IH]; simpl; lia.
Qed.

Lemma snd_cp_le (n : nat)
  : snd (cp n) <= n.
Proof.
  destruct (cp n) as [x y] eqn: H_OBS. rewrite cp_spec in H_OBS.
  subst n. unfold cpInv. simpl. enough (ENOUGH : x + y <= sum_from_0_to (x + y)) by lia.
  induction (x + y) as [ | z IH]; simpl; lia.
Qed.

Lemma cpInv_inj (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat)
  (EQ : cpInv x1 y1 = cpInv x2 y2)
  : x1 = x2 /\ y1 = y2.
Proof.
  enough (ENOUGH : (x1, y1) = (x2, y2)) by now inv ENOUGH.
  rewrite <- cp_spec in EQ. rewrite <- EQ. symmetry. eapply cp_spec. reflexivity.
Qed.

Corollary cpInv_inj1 {x1 : nat} {x2 : nat} {y1 : nat} {y2 : nat}
  (EQ : cpInv x1 y1 = cpInv x2 y2)
  : x1 = x2.
Proof.
  now apply cpInv_inj in EQ.
Qed.

Corollary cpInv_inj2 {x1 : nat} {x2 : nat} {y1 : nat} {y2 : nat}
  (EQ : cpInv x1 y1 = cpInv x2 y2)
  : y1 = y2.
Proof.
  now apply cpInv_inj in EQ.
Qed.

End CANTOR_PAIRING.
