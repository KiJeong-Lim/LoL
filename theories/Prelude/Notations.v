Require Import LoL.Prelude.Prelude.

Reserved Infix "∈" (no associativity, at level 70).
Reserved Notation "'\['  dom '→' cod  '\]'".
Reserved Infix "`compare`" (no associativity, at level 40).
Reserved Infix "⊢" (no associativity, at level 70).
Reserved Infix "⊧" (no associativity, at level 70).
Reserved Infix "⊭" (no associativity, at level 70).
Reserved Infix "!!" (left associativity, at level 25).

Module MonadNotations.

Infix ">>=" := bind.

End MonadNotations.
