Require Import LoL.Prelude.Prelude.
Require Import LoL.Prelude.Notations.

Module GRAPH.

#[projections(primitive)]
Record t : Type :=
  { vertices : Type
  ; edges : ensemble (vertices * vertices)
  }.

End GRAPH.

Notation vertices := GRAPH.vertices.
Notation edges := GRAPH.edges.

Section GraphTheory_basic1.

Context {G : GRAPH.t}.

#[local] Notation V := G.(vertices).
#[local] Notation E := G.(edges).

#[local] Notation In := L.In.
#[local] Infix "\in" := E.elem : type_scope.

Inductive walk (v : V) : V -> list V -> Prop :=
  | walk_refl
    : v ~~~[ [] ]~~> v
  | walk_step (v0 : V) (v1 : V) (w : list V)
    (H_edge : (v0, v1) \in E)
    (H_walk : v1 ~~~[ w ]~~> v)
    : v0 ~~~[ v1 :: w ]~~> v
  where " src ~~~[ w ]~~> tgt " := (walk tgt src w) : type_scope.

#[local] Hint Constructors walk : core.

Lemma walk_last (v0 : V) (v : V) (w : list V)
  (WALK : v0 ~~~[ w ]~~> v)
  : v = last w v0.
Proof.
  induction WALK as [ | v0 v1 w H_edge WALK IH].
  - reflexivity.
  - rewrite -> L.last_cons. exact IH.
Qed.

Theorem walk_iff (v0 : V) (vs : list V)
  : v0 ~~~[ vs ]~~> last vs v0 <-> Forall E (L.mk_edge_seq v0 vs).
Proof.
  split.
  - intros WALK. revert v0 WALK. induction vs as [ | v1 vs IH]; i.
    + econstructor 1.
    + simpl. rewrite -> L.last_cons in WALK. inv WALK.
      econstructor 2; eauto.
  - intros H_Forall. revert v0 H_Forall. induction vs as [ | v1 vs IH]; i.
    + simpl. econstructor 1.
    + rewrite -> L.last_cons. simpl in H_Forall. inv H_Forall.
      econstructor 2; eauto.
Qed.

Lemma walk_app (v1 : V) (v2 : V) (v : V) (vs1 : list V) (vs2 : list V)
  (PATH1 : v1 ~~~[ vs1 ]~~> v2)
  (PATH2 : v2 ~~~[ vs2 ]~~> v)
  : v1 ~~~[ vs1 ++ vs2 ]~~> v.
Proof.
  revert v1 v2 v vs2 PATH1 PATH2. induction vs1 as [ | v vs1 IH]; simpl; i; inv PATH1; eauto.
Qed.

Theorem walk_app_iff (v0 : V) (v' : V) (vs1 : list V) (vs2 : list V)
  : v0 ~~~[ vs1 ++ vs2 ]~~> v' <-> (exists v, v0 ~~~[ vs1 ]~~> v /\ v ~~~[ vs2 ]~~> v').
Proof.
  split.
  - intros WALK. revert v0 v' vs2 WALK. induction vs1 as [ | v1 vs1 IH]; simpl; i; eauto.
    inv WALK. apply IH in H_walk. des; eauto.
  - intros VIA. des. eapply walk_app; eauto.
Qed.

Inductive path (v : V) : V -> list V -> Prop :=
  | path_refl
    : v ---[ [] ]--> v
  | path_step (v0 : V) (v1 : V) (p : list V)
    (H_edge : (v0, v1) \in E)
    (H_path : v1 ---[ p ]--> v)
    (NOT_IN : ~ In v1 p)
    : v0 ---[ v1 :: p ]--> v
  where " src ---[ p ]--> tgt " := (path tgt src p) : type_scope.

#[local] Hint Constructors path : core.

Lemma path_vertices_no_dup (v0 : V) (v : V) (p : list V)
  (H_path : v0 ---[ p ]--> v)
  : NoDup p.
Proof.
  induction H_path as [ | v0 v1 p H_edge H_path IH NOT_IN]; econstructor; eauto.
Qed.

Lemma no_dup_walk_is_path (v0 : V) (v : V) (w : list V)
  (NO_DUP : NoDup w)
  (H_walk : v0 ~~~[ w ]~~> v)
  : v0 ---[ w ]--> v.
Proof.
  induction H_walk as [ | v0 v1 w H_edge H_walk IH]; i.
  - econstructor 1.
  - econstructor 2.
    + exact H_edge.
    + eapply IH. now inv NO_DUP.
    + now inv NO_DUP.
Qed.

Theorem path_iff_no_dup_walk (v0 : V) (v : V) (vs : list V)
  : v0 ---[ vs ]--> v <-> (v0 ~~~[ vs ]~~> v /\ NoDup vs).
Proof with eauto.
  split.
  - intros H_path. split.
    + induction H_path; simpl...
    + eapply path_vertices_no_dup...
  - intros [H_walk NO_DUP].
    eapply no_dup_walk_is_path...
Qed.

Lemma path_app_inv (v0 : V) (v' : V) (vs1 : list V) (vs2 : list V)
  (PATH : v0 ---[ vs1 ++ vs2 ]--> v')
  : exists v, v0 ---[ vs1 ]--> v /\ v ---[ vs2 ]--> v'.
Proof.
  rewrite -> path_iff_no_dup_walk in PATH. destruct PATH as [WALK NO_DUP].
  rewrite -> walk_app_iff in WALK. destruct WALK as (v&WALK1&WALK2).
  exists v. split; rewrite -> path_iff_no_dup_walk.
  - split; trivial. eapply NoDup_app_remove_r; eauto.
  - split; trivial. eapply NoDup_app_remove_l; eauto.
Qed.

Section Walk_finds_Path.

Lemma mk_subpath (v0 : V) (v1 : V) (v : V) (p : list V)
  (PATH : v0 ---[ p ]--> v)
  (ELEM : In v1 p)
  : exists p', v0 ---[ p' ]--> v1 /\ (exists p'', p = p' ++ p'' /\ v1 ---[ p'' ]--> v).
Proof.
  revert v1 ELEM. induction PATH as [ | v0 v1 p H_edge PATH IH NOT_IN]; i; inv ELEM.
  - exists [v2]. split; eauto. exists p. split; eauto.
  - rename H into ELEM. pose proof (IH v2 ELEM) as (p'&PATH1&p''&EQ&PATH2).
    exists (v1 :: p'). split.
    + econstructor 2; eauto. subst p. rewrite in_app_iff in NOT_IN. tauto.
    + exists p''. split; [now rewrite EQ | exact PATH2].
Qed.

Hypothesis In_dec : forall v : V, forall vs : list V, In v vs \/ ~ In v vs.

Theorem walk_finds_path (v0 : V) (v : V) (w : list V)
  (WALK : v0 ~~~[ w ]~~> v)
  : exists p, v0 ---[ p ]--> v.
Proof.
  revert v0 v WALK. induction w as [ | v' w IH] using List.rev_ind; i.
  - inv WALK. exists []. econstructor 1.
  - rewrite -> walk_app_iff in WALK. destruct WALK as (v1&WALK1&WALK2).
    inv WALK2. inv H_walk. pose proof (IH v0 v1 WALK1) as [p PATH].
    pose proof (In_dec v' p) as [ELEM | NOT_IN].
    + pose proof (mk_subpath v0 v' v1 p PATH ELEM) as (p'&PATH'&_).
      exists p'. exact PATH'.
    + exists (p ++ [v']). rewrite -> path_iff_no_dup_walk. split.
      * rewrite -> walk_app_iff. exists v1. split.
        { now eapply path_iff_no_dup_walk. }
        { econstructor 2; eauto. }
      * rewrite <- rev_involutive. eapply NoDup_rev.
        rewrite -> rev_unit. econstructor 2.
        { now rewrite <- In_rev. }
        { eapply NoDup_rev. eapply path_iff_no_dup_walk. exact PATH. }
Qed.

End Walk_finds_Path.

Definition trail (v' : V) (v : V) (vs : list V) : Prop :=
  v ~~~[ vs ]~~> v' /\ NoDup (L.mk_edge_seq v vs).

#[local] Notation " src ===[ t ]==> tgt " := (trail tgt src t) : type_scope.

Lemma path_implies_trail (v0 : V) (v : V) (p : list V)
  (PATH : v0 ---[ p ]--> v)
  : v0 ===[ p ]==> v.
Proof.
  rewrite path_iff_no_dup_walk in PATH.
  destruct PATH as [WALK NO_DUP]. split.
  - exact WALK.
  - eapply L.no_dup_mk_edge_seq. exact NO_DUP.
Qed.

End GraphTheory_basic1.

Module GraphNotations.

#[global] Notation " src ~~~[ w ]~~> tgt " := (walk tgt src w) : type_scope.
#[global] Notation " src ---[ p ]--> tgt " := (path tgt src p) : type_scope.
#[global] Notation " src ===[ t ]==> tgt " := (trail tgt src t) : type_scope.

End GraphNotations.
