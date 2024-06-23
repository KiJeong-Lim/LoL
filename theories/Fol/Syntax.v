Require Import LoL.Prelude.Prelude.
Require Import LoL.Math.Nat.

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

Section ENUMERATION.

Fixpoint trm_depth (t : trm) : nat :=
  match t with
  | Var_trm x => 0
  | Fun_trm f ts => 1 + trms_depth ts
  | Con_trm c => 1
  end
with trms_depth {n : arity} (ts : trms n) : nat :=
  match ts with
  | O_trms => 0
  | S_trms _ t ts => 1 + max (trm_depth t) (trms_depth ts)
  end.

Fixpoint frm_depth (p: frm) : nat :=
  match p with
  | Rel_frm R ts => 0
  | Eqn_frm t1 t2 => 0
  | Neg_frm p1 => 1 + frm_depth p1
  | Imp_frm p1 p2 => 1 + max (frm_depth p1) (frm_depth p2)
  | All_frm y p1 => 1 + frm_depth p1
  end.

Variable enum_function_symbols : nat -> L.(function_symbols).

Variable enum_constant_symbols : nat -> L.(constant_symbols).

Fixpoint gen_trm (seed : nat) (d : nat) {struct d} : trm :=
  match d with
  | O => Var_trm seed
  | S d' =>
    let seed1 := fst (cp seed) in
    let seed' := snd (cp seed) in
    let seed2 := fst (cp seed') in
    let seed3 := snd (cp seed') in
    match seed1 with
    | 0 => Con_trm (enum_constant_symbols seed')
    | 1 => Fun_trm (enum_function_symbols seed2) (gen_trms seed3 d')
    | S (S i) => Var_trm i
    end
  end
with gen_trms {n : arity} (seed : nat) (d : nat) {struct d} : trms n :=
  match n with
  | O => O_trms
  | S n' =>
    match d with
    | O => nat_rec _ (O_trms) (fun x => fun acc => S_trms _ (Var_trm seed) acc) (S n')
    | S d' =>
      let seed1 := fst (cp seed) in
      let seed2 := snd (cp seed) in
      S_trms _ (gen_trm seed1 d') (gen_trms seed2 d')
    end
  end.

Definition enum_trm (seed : nat) : trm :=
  let d := fst (cp seed) in
  let seed' := snd (cp seed) in
  gen_trm seed' d.

Definition enum_trms {n : arity} (seed : nat) : trms n :=
  let d := fst (cp seed) in
  let seed' := snd (cp seed) in
  gen_trms seed' d.

Section PROOF1.

Hypothesis enum_function_symbols_onto : forall f : L.(function_symbols), { n : nat | enum_function_symbols n = f }.

Hypothesis enum_constant_symbols_onto : forall c : L.(constant_symbols), { n : nat | enum_constant_symbols n = c }.

End PROOF1.

Variable enum_relation_symbols : nat -> L.(relation_symbols).

Fixpoint gen_frm (seed: nat) (d: nat) {struct d} : frm :=
  match d with
  | O =>
    let seed1 := fst (cp seed) in
    let seed' := snd (cp seed) in
    let seed2 := fst (cp seed') in
    let seed3 := snd (cp seed') in
    match seed1 with
    | 0 => Eqn_frm (enum_trm seed2) (enum_trm seed3)
    | _ => Rel_frm (enum_relation_symbols seed2) (enum_trms seed3)
    end
  | S d' =>
    let seed1 := fst (cp seed) in
    let seed' := snd (cp seed) in
    let seed2 := fst (cp seed') in
    let seed3 := snd (cp seed') in
    match seed1 with
    | 0 => Neg_frm (gen_frm seed' d')
    | 1 => Imp_frm (gen_frm seed2 d') (gen_frm seed3 d')
    | 2 => All_frm seed2 (gen_frm seed3 d')
    | S (S (S i)) =>
      match i with
      | 0 => Eqn_frm (enum_trm seed2) (enum_trm seed3)
      | _ => Rel_frm (enum_relation_symbols seed2) (enum_trms seed3)
      end
    end
  end.

Definition enum_frm (seed : nat) : frm :=
  let d := fst (cp seed) in
  let seed' := snd (cp seed) in
  gen_frm seed' d.

Section PROOF2.

Hypothesis enum_function_symbols_onto : forall f : L.(function_symbols), { n : nat | enum_function_symbols n = f }.

Hypothesis enum_constant_symbols_onto : forall c : L.(constant_symbols), { n : nat | enum_constant_symbols n = c }.

Hypothesis enum_relation_symbols_onto : forall R : L.(relation_symbols), { n : nat | enum_relation_symbols n = R }.

End PROOF2.

End ENUMERATION.

End SYNTAX.

#[global] Arguments trm : clear implicits.
#[global] Arguments trms : clear implicits.
#[global] Arguments frm : clear implicits.
