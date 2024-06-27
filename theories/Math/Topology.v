Require Import LoL.Prelude.Prelude.

#[local] Infix "\in" := E.elem : type_scope.
#[local] Infix "\subseteq" := E.isSubsetOf : type_scope.

Class hasTopology (A : Type) : Type :=
  { isOpen (X : ensemble A) : Prop
  ; full_isOpen
    : isOpen E.full
  ; intersection_isOpen (X1 : ensemble A) (X2 : ensemble A)
    (OPEN1 : isOpen X1)
    (OPEN2 : isOpen X2)
    : isOpen (E.intersection X1 X2)
  ; unions_isOpen (Xs : ensemble (ensemble A))
    (OPENs : forall X, X \in Xs -> isOpen X)
    : isOpen (E.unions Xs)
  ; isOpen_ext (X1 : ensemble A) (X2 : ensemble A)
    (OPEN : isOpen X1)
    (EXT_EQ : X1 == X2)
    : isOpen X2
  }.

#[global]
Add Parametric Morphism {A : Type} `{TOPOLOGY : hasTopology A}
  : (@isOpen A TOPOLOGY) with signature (eqProp ==> iff)
  as isOpen_compatWith_eqProp.
Proof.
  intros X1 X2 EXT_EQ. split; intros OPEN.
  - eapply isOpen_ext with (X1 := X1). exact OPEN. exact EXT_EQ.
  - eapply isOpen_ext with (X1 := X2). exact OPEN. symmetry. exact EXT_EQ.
Qed.

Lemma empty_isOpen {A : Type} `{TOPOLOGY : hasTopology A}
  : isOpen (@E.empty A).
Proof.
  assert (EQ : (@E.empty A) == E.unions E.empty).
  { rewrite E.ensemble_eq_unfold. intros x. autorewrite with datatypes. now firstorder. }
  rewrite EQ. eapply unions_isOpen. now firstorder.
Qed.

#[global] Hint Resolve full_isOpen : mathhints.
#[global] Hint Resolve intersection_isOpen : mathhints.
#[global] Hint Resolve unions_isOpen : mathhints.
#[global] Hint Resolve empty_isOpen : mathhints.
