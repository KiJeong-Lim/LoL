Require Import LoL.Prelude.Prelude.
Require Import LoL.Prelude.Notations.
Require Import LoL.Math.ThN.
Require Import LoL.Data.Vector.
Require Import LoL.FoL.Syntax.

#[local] Infix "\in" := E.elem.
#[local] Infix "\subseteq" := E.isSubsetOf.

Module HPS.

Section HILBERT_PROOF_SYSTEM.

Import ListNotations.

Context {L : language}.

Definition varcouples : forall n : nat, trms L n * trms L n :=
  nat_rec (fun n => (trms L n * trms L n)%type) (O_trms, O_trms) (fun n => prod_rec _ (fun lhs => fun rhs => (S_trms n (Var_trm (n + n)) lhs, S_trms n (Var_trm (S (n + n))) rhs))).

Definition eqns_imp p : nat -> frm L :=
  nat_rec _ p (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q).

Definition Fun_eqAxm (f : L.(function_symbols)) : frm L :=
  eqns_imp (prod_rec (fun _ => frm L) (fun lhs => fun rhs => Eqn_frm (Fun_trm f lhs) (Fun_trm f rhs)) (varcouples (L.(function_arity_table) f))) (L.(function_arity_table) f).

Definition Rel_eqAxm (R : L.(relation_symbols)) : frm L :=
  eqns_imp (prod_rec (fun _ => frm L) (fun lhs => fun rhs => Imp_frm (Rel_frm R lhs) (Rel_frm R rhs)) (varcouples (L.(relation_arity_table) R))) (L.(relation_arity_table) R).

Inductive proof : list (frm L) -> frm L -> Set := (* Reference: "https://github.com/princeton-vl/CoqGym/blob/master/coq_projects/goedel/folProof.v#L68" *)
  | AXM p
    : proof [p] p
  | MP ps1 ps2 p q
    (PF1 : proof ps1 (Imp_frm p q))
    (PF2 : proof ps2 p)
    : proof (ps1 ++ ps2) q
  | GEN ps q x
    (NOT_FREE : forall p, In p ps -> is_not_free_in_frm x p)
    (PF : proof ps q)
    : proof ps (All_frm x q)
  | IMP1 p q
    : proof [] (Imp_frm p (Imp_frm q p))
  | IMP2 p q r
    : proof [] (Imp_frm (Imp_frm p (Imp_frm q r)) (Imp_frm (Imp_frm p q) (Imp_frm p r)))
  | CP p q
    : proof [] (Imp_frm (Imp_frm (Neg_frm q) (Neg_frm p)) (Imp_frm p q))
  | FA1 p x t
    : proof [] (Imp_frm (All_frm x p) (subst_frm (one_subst x t) p))
  | FA2 p x
    (NOT_FREE : is_not_free_in_frm x p)
    : proof [] (Imp_frm p (All_frm x p))
  | FA3 p q x
    : proof [] (Imp_frm (All_frm x (Imp_frm p q)) (Imp_frm (All_frm x p) (All_frm x q)))
  | EQN_REFL
    : proof [] (Eqn_frm (Var_trm 0) (Var_trm 0))
  | EQN_SYM
    : proof [] (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Eqn_frm (Var_trm 1) (Var_trm 0)))
  | EQN_TRANS
    : proof [] (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Imp_frm (Eqn_frm (Var_trm 1) (Var_trm 2)) (Eqn_frm (Var_trm 0) (Var_trm 2))))
  | EQN_FUN f
    : proof [] (Fun_eqAxm f)
  | EQN_REL R
    : proof [] (Rel_eqAxm R).

Definition proves (Gamma : ensemble (frm L)) (C : frm L) : Prop :=
  exists ps, E.finite ps \subseteq Gamma /\ inhabited (proof ps C).

End HILBERT_PROOF_SYSTEM.

End HPS.

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
    (INFERS1: Gamma ⊢ subst_frm (one_subst x (Var_trm y)) p)
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
    (INFERS1: Gamma ⊢ Exs_frm x p1)
    (INFERS2: E.insert (subst_frm (one_subst x (Var_trm y)) p1) Gamma ⊢ p2)
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
