Require Import LoL.Prelude.Prelude.
Require Import LoL.Prelude.Notations.
Require Import LoL.Math.ThN.
Require Import LoL.Data.Vector.
Require Import LoL.Logic.FolSyntax.
Require Import LoL.Logic.FolSemantics.

#[local] Infix "\in" := E.elem.
#[local] Infix "\subseteq" := E.isSubsetOf.

#[local] Infix "≡" := alpha_equiv.

Import ListNotations.

#[local] Notation "p `[ x' := t' ]" := (subst1 x' t' p) (at level 15, no associativity, format "p `[  x'  :=  t'  ]").

Section NATURAL_DEDUCTION.

Inductive infers {L : language} (Gamma : list (frm L)) : forall C : frm L, Prop :=
  | By_hyp p
    (IN : L.In p Gamma)
    : Gamma ⊢ p
  | Eqn_I t1
    : Gamma ⊢ Eqn_frm t1 t1
  | Eqn_E x t1 t2 p1
    (INFERS1 : Gamma ⊢ Eqn_frm t1 t2)
    (INFERS2 : Gamma ⊢ subst_frm (one_subst x t1) p1)
    : Gamma ⊢ subst_frm (one_subst x t2) p1
  | All_I x y p
    (NOT_FREE1 : forall p, L.In p Gamma -> is_not_free_in_frm y p)
    (NOT_FREE2 : is_not_free_in_frm y (All_frm x p))
    (INFERS1 : Gamma ⊢ subst_frm (one_subst x (Var_trm y)) p)
    : Gamma ⊢ All_frm x p
  | All_E x t p
    (INFERS1 : Gamma ⊢ All_frm x p)
    : Gamma ⊢ subst_frm (one_subst x t) p
  | Neg_I p1 p2
    (INFERS1 : p1 :: Gamma ⊢ p2)
    (INFERS2 : p1 :: Gamma ⊢ Neg_frm p2)
    : Gamma ⊢ Neg_frm p1
  | Neg_E p1 p2
    (INFERS1 : Gamma ⊢ p1)
    (INFERS2 : Gamma ⊢ Neg_frm p1)
    : Gamma ⊢ p2
  | Imp_I p1 p2
    (INFERS1 : p1 :: Gamma ⊢ p2)
    : Gamma ⊢ Imp_frm p1 p2
  | Imp_E p1 p2
    (INFERS1 : Gamma ⊢ Imp_frm p1 p2)
    (INFERS2 : Gamma ⊢ p1)
    : Gamma ⊢ p2
  where " Gamma ⊢ C " := (infers Gamma C) : type_scope.

Context {L : language}.

End NATURAL_DEDUCTION.
