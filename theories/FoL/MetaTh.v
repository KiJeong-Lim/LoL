Require Import LoL.Prelude.Prelude.
Require Import LoL.Prelude.LEM.
Require Import LoL.Prelude.Notations.
Require Import LoL.Math.ThN.
Require Import LoL.Data.Vector.
Require Import LoL.FoL.Syntax.
Require Import LoL.FoL.Semantics.
Require Import LoL.FoL.InferenceRules.

#[local] Infix "\in" := E.elem.
#[local] Infix "\subseteq" := E.isSubsetOf.

#[local] Infix "≡" := alpha_equiv.

Module ND.

Inductive infers {L : language} (Gamma : ensemble (frm L)) : forall C : frm L, Prop :=
  | By_hyp p
    (IN : p \in Gamma)
    : Gamma ⊢ p
  | Eqn_I t1
    : Gamma ⊢ Eqn_frm t1 t1
  | Eqn_E x t1 t2 p1
    (INFERS1 : Gamma ⊢ Eqn_frm t1 t2)
    (INFERS2 : Gamma ⊢ subst_frm (one_subst x t1) p1)
    : Gamma ⊢ subst_frm (one_subst x t2) p1
  | All_I x y p
    (NOT_FREE1 : is_not_free_in_frms y Gamma)
    (NOT_FREE2 : is_not_free_in_frm y (All_frm x p))
    (INFERS1 : Gamma ⊢ subst_frm (one_subst x (Var_trm y)) p)
    : Gamma ⊢ All_frm x p
  | All_E x t p
    (INFERS1 : Gamma ⊢ All_frm x p)
    : Gamma ⊢ subst_frm (one_subst x t) p
  | Exs_I x t p
    (INFERS1 : Gamma ⊢ subst_frm (one_subst x t) p)
    : Gamma ⊢ Exs_frm x p
  | Exs_E x y p1 p2
    (NOT_FREE1 : is_not_free_in_frms y Gamma)
    (NOT_FREE2 : is_not_free_in_frm y (Exs_frm x p1))
    (NOT_FREE3 : is_not_free_in_frm y p2)
    (INFERS1 : Gamma ⊢ Exs_frm x p1)
    (INFERS2 : E.insert (subst_frm (one_subst x (Var_trm y)) p1) Gamma ⊢ p2)
    : Gamma ⊢ p2
  | Bot_I p1
    (INFERS1 : Gamma ⊢ p1)
    (INFERS2 : Gamma ⊢ Neg_frm p1)
    : Gamma ⊢ Bot_frm
  | Bot_E p1
    (INFERS1 : Gamma ⊢ Bot_frm)
    : Gamma ⊢ p1
  | Neg_I p1
    (INFERS1: E.insert p1 Gamma ⊢ Bot_frm)
    : Gamma ⊢ Neg_frm p1
  | Neg_E p1
    (INFERS1 : E.insert (Neg_frm p1) Gamma ⊢ Bot_frm)
    : Gamma ⊢ p1
  | Con_I p1 p2
    (INFERS1 : Gamma ⊢ p1)
    (INFERS2 : Gamma ⊢ p2)
    : Gamma ⊢ Con_frm p1 p2
  | Con_E1 p1 p2
    (INFERS1 : Gamma ⊢ Con_frm p1 p2)
    : Gamma ⊢ p1
  | Con_E2 p1 p2
    (INFERS1 : Gamma ⊢ Con_frm p1 p2)
    : Gamma ⊢ p2
  | Dis_I1 p1 p2
    (INFERS1 : Gamma ⊢ p1)
    : Gamma ⊢ Dis_frm p1 p2
  | Dis_I2 p1 p2
    (INFERS1 : Gamma ⊢ p2)
    : Gamma ⊢ Dis_frm p1 p2
  | Dis_E p1 p2 p3
    (INFERS1 : Gamma ⊢ Dis_frm p1 p2)
    (INFERS2 : E.insert p1 Gamma ⊢ p3)
    (INFERS3 : E.insert p2 Gamma ⊢ p3)
    : Gamma ⊢ p3
  | Imp_I p1 p2
    (INFERS1 : E.insert p1 Gamma ⊢ p2)
    : Gamma ⊢ Imp_frm p1 p2
  | Imp_E p1 p2
    (INFERS1 : Gamma ⊢ Imp_frm p1 p2)
    (INFERS2 : Gamma ⊢ p1)
    : Gamma ⊢ p2
  | Iff_I p1 p2
    (INFERS1 : E.insert p1 Gamma ⊢ p2)
    (INFERS2 : E.insert p2 Gamma ⊢ p1)
    : Gamma ⊢ Iff_frm p1 p2
  | Iff_E1 p1 p2
    (INFERS1 : Gamma ⊢ Iff_frm p1 p2)
    (INFERS2 : Gamma ⊢ p1)
    : Gamma ⊢ p2
  | Iff_E2 p1 p2
    (INFERS1 : Gamma ⊢ Iff_frm p1 p2)
    (INFERS2 : Gamma ⊢ p2)
    : Gamma ⊢ p1
  where " Gamma ⊢ C " := (infers Gamma C) : type_scope.

End ND.
