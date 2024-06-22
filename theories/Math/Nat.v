Require Import LoL.Prelude.Prelude.

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
