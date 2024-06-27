Require Import LoL.Prelude.Prelude.
Require Import LoL.Math.ThN.
Require Import LoL.Data.Vector.
Require Import LoL.Fol.Syntax.

#[local] Infix "\in" := E.elem.
#[local] Infix "\subseteq" := E.isSubsetOf.

#[local] Close Scope list_scope.
#[local] Open Scope vector_scope.

#[local] Existing Instance V.vec_isSetoid.

Class structureOf (L : language) : Type :=
  { domain_of_discourse : Type
  ; equation_interpret :: isSetoid domain_of_discourse
  ; function_interpret (f : L.(function_symbols)) (vs : Vector.t domain_of_discourse (L.(function_arity_table) f)) : domain_of_discourse
  ; constant_interpret (c : L.(constant_symbols)) : domain_of_discourse
  ; relation_interpret (R : L.(relation_symbols)) (vs : Vector.t domain_of_discourse (L.(relation_arity_table) R)) : Prop
  ; domain_is_nonempty : inhabited domain_of_discourse
  ; function_interpret_preserves_eqProp (f : L.(function_symbols)) (vs1 : Vector.t domain_of_discourse (L.(function_arity_table) f)) (vs2 : Vector.t domain_of_discourse (L.(function_arity_table) f))
    (EQ : vs1 == vs2)
    : function_interpret f vs1 == function_interpret f vs2
  ; relation_interpret_preserves_eqProp (R : L.(relation_symbols)) (vs1 : Vector.t domain_of_discourse (L.(relation_arity_table) R)) (vs2 : Vector.t domain_of_discourse (L.(relation_arity_table) R))
    (EQ : vs1 == vs2)
    : relation_interpret R vs1 <-> relation_interpret R vs2
  }.

Section SEMANTICS.

Context {L : language}.

Definition upd_env {STRUCTURE : structureOf L} (y : ivar) (y_value : domain_of_discourse) (env : ivar -> domain_of_discourse) : ivar -> domain_of_discourse :=
  fun z : ivar => if Nat.eq_dec z y then y_value else env z.

Variable STRUCTURE : structureOf L.

Fixpoint interpret_trm (env : ivar -> domain_of_discourse) (t : trm L) {struct t} : domain_of_discourse :=
  match t with
  | Var_trm x => env x
  | Fun_trm f ts => function_interpret f (interpret_trms env ts)
  | Con_trm c => constant_interpret c
  end
with interpret_trms {n : nat} (env : ivar -> domain_of_discourse) (ts : trms L n) {struct ts} : Vector.t domain_of_discourse n :=
  match ts with
  | O_trms => []
  | S_trms n t ts => interpret_trm env t :: interpret_trms env ts 
  end.

Fixpoint interpret_frm (env : ivar -> domain_of_discourse) (p : frm L) {struct p} : Prop :=
  match p with
  | Eqn_frm t1 t2 => interpret_trm env t1 == interpret_trm env t2
  | Rel_frm R ts => relation_interpret R (interpret_trms env ts)
  | Neg_frm p1 => ~ interpret_frm env p1
  | Imp_frm p1 p2 => interpret_frm env p1 -> interpret_frm env p2
  | All_frm y p1 => forall y_value : domain_of_discourse, interpret_frm (upd_env y y_value env) p1
  end.

Lemma interpret_trm_unfold (env : ivar -> domain_of_discourse) (t : trm L) :
  interpret_trm env t =
  match t with
  | Var_trm x => env x
  | Fun_trm f ts => function_interpret f (interpret_trms env ts)
  | Con_trm c => constant_interpret c
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma interpret_trms_unfold n (env : ivar -> domain_of_discourse) (ts : trms L n) :
  interpret_trms env ts =
  match ts with
  | O_trms => VNil
  | S_trms n' t ts' => VCons n' (interpret_trm env t) (interpret_trms env ts')
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Lemma interpret_frm_unfold (env : ivar -> domain_of_discourse) (p : frm L) :
  interpret_frm env p =
  match p with
  | Eqn_frm t1 t2 => interpret_trm env t1 == interpret_trm env t2
  | Rel_frm R ts => relation_interpret R (interpret_trms env ts)
  | Neg_frm p1 => ~ interpret_frm env p1
  | Imp_frm p1 p2 => interpret_frm env p1 -> interpret_frm env p2
  | All_frm y p1 => forall y_value : domain_of_discourse, interpret_frm (upd_env y y_value env) p1
  end.
Proof.
  destruct p; reflexivity.
Defined.

End SEMANTICS.
