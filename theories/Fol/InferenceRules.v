Require Import LoL.Prelude.Prelude.
Require Import LoL.Prelude.Notations.
Require Import LoL.Math.ThN.
Require Import LoL.Data.Vector.
Require Import LoL.Fol.Syntax.
Require Import LoL.Fol.Semantics.

#[local] Infix "\in" := E.elem.
#[local] Infix "\subseteq" := E.isSubsetOf.

Module HPS.

Section HILBERT_PROOF_SYSTEM.

Context {L: language}.

Definition varcouples : forall n, trms L n * trms L n :=
  nat_rec (fun n => (trms L n * trms L n)%type) (O_trms, O_trms) (fun n => prod_rec _ (fun lhs => fun rhs => (S_trms n (Var_trm (n + n)) lhs, S_trms n (Var_trm (S (n + n))) rhs))).

Definition eqns_imp p : nat -> frm L :=
  nat_rec _ p (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q).

Definition Func_eqAxm (f: L.(function_symbols)) : frm L :=
  eqns_imp (prod_rec (fun _ => frm L) (fun lhs => fun rhs => Eqn_frm (Fun_trm f lhs) (Fun_trm f rhs)) (varcouples (L.(function_arity_table) f))) (L.(function_arity_table) f).

Definition Rel_eqAxm (R: L.(relation_symbols)) : frm L :=
  eqns_imp (prod_rec (fun _ => frm L) (fun lhs => fun rhs => Imp_frm (Rel_frm R lhs) (Rel_frm R rhs)) (varcouples (L.(relation_arity_table) R))) (L.(relation_arity_table) R).

Inductive proof : list (frm L) -> frm L -> Set :=
  | AXM p
    : proof [p] p
  | MP ps1 ps2 p q
    (PF1: proof ps1 (Imp_frm p q))
    (PF2: proof ps2 p)
    : proof (ps1 ++ ps2) q
  | GEN ps q x
    (NOT_FREE: forall p, In p ps -> is_not_free_in_frm x p)
    (PF: proof ps q)
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
    (NOT_FREE: is_not_free_in_frm x p)
    : proof [] (Imp_frm p (All_frm x p))
  | FA3 p q x
    : proof [] (Imp_frm (All_frm x (Imp_frm p q)) (Imp_frm (All_frm x p) (All_frm x q)))
  | EQN_REFL
    : proof [] (Eqn_frm (Var_trm 1) (Var_trm 1))
  | EQN_SYM
    : proof [] (Imp_frm (Eqn_frm (Var_trm 1) (Var_trm 2)) (Eqn_frm (Var_trm 2) (Var_trm 1)))
  | EQN_TRANS
    : proof [] (Imp_frm (Eqn_frm (Var_trm 1) (Var_trm 2)) (Imp_frm (Eqn_frm (Var_trm 2) (Var_trm 3)) (Eqn_frm (Var_trm 1) (Var_trm 3))))
  | EQN_FUNC (f: L.(function_symbols))
    : proof [] (Func_eqAxm f)
  | EQN_REL (R: L.(relation_symbols))
    : proof [] (Rel_eqAxm R).

Definition proves (Gamma: ensemble (frm L)) (C: frm L) : Prop :=
  exists ps: list (frm L), E.finite ps \subseteq Gamma /\ inhabited (proof ps C).

End HILBERT_PROOF_SYSTEM.

End HPS.
