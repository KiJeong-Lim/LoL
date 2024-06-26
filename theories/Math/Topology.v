Require Import LoL.Prelude.Prelude.

#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "\subseteq" := E.isSubsetOf : type_scope.

Class Topology (A : Type) : Type :=
  { isOpen (X : ensemble A) : Prop
  ; isOpen_full
    : isOpen E.full
  ; isOpen_empty
    : isOpen E.empty
  ; isOpen_unions (Xs : ensemble (ensemble A))
    (OPENs : forall X, X \in Xs -> isOpen X)
    : isOpen (E.unions Xs)
  ; isOpen_intersection (X1 : ensemble A) (X2 : ensemble A)
    (OPEN1 : isOpen X1)
    (OPEN2 : isOpen X2)
    : isOpen (E.intersection X1 X2)
  ; isOpen_ext (X1 : ensemble A) (X2 : ensemble A)
    (OPEN : isOpen X1)
    (EXT_EQ : X1 == X2)
    : isOpen X2
  }.

#[global]
Add Parametric Morphism {A : Type} `{TOPOLOGY : Topology A}
  : (@isOpen A TOPOLOGY) with signature (eqProp ==> iff)
  as isOpen_compatWith_eqProp.
Proof.
  intros X1 X2 EXT_EQ. split; intros OPEN.
  - eapply isOpen_ext with (X1 := X1). exact OPEN. exact EXT_EQ.
  - eapply isOpen_ext with (X1 := X2). exact OPEN. symmetry. exact EXT_EQ.
Qed.
