Require Import LoL.Prelude.Prelude.

Section SYNTAX.

Definition ivar : Set := nat.

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
  | Rel_frm (r : L.(relation_symbols)) (ts : trms (L.(relation_arity_table) r)) : frm
  | Eqn_frm (t1 : trm) (t2 : trm) : frm
  | Neg_frm (p1 : frm) : frm
  | Imp_frm (p1 : frm) (p2 : frm) : frm
  | All_frm (y : ivar) (p1 : frm) : frm.

End SYNTAX.
