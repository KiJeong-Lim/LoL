Require Import LoL.Prelude.Prelude.

Module __LEM.

Axiom axiom: forall P: Prop, P \/ ~ P.

Lemma NNPP (P: Prop)
  (H_NNP : ~ ~ P)
  : P.
Proof.
  pose proof (axiom P) as [H_P | H_NP].
  - exact H_P.
  - contradiction (H_NNP H_NP).
Defined.

End __LEM.

Notation exclusive_middle := __LEM.axiom.
Notation nnpp := __LEM.NNPP.
