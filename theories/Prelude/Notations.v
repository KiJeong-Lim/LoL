Require Import LoL.Prelude.Prelude.

Reserved Infix "∈" (no associativity, at level 70).
Reserved Notation "'\['  dom '→' cod  '\]'".
Reserved Infix "`compare`" (no associativity, at level 40).
Reserved Infix "⊢" (no associativity, at level 70).
Reserved Infix "⊧" (no associativity, at level 70).
Reserved Infix "⊭" (no associativity, at level 70).
Reserved Infix "!!" (left associativity, at level 25).
Reserved Notation " x '↦' t ';' s " (at level 55, right associativity).
Reserved Notation " x '↦' t " (at level 55, no associativity).
Reserved Notation " '∅' " (at level 0, no associativity).
Reserved Notation " 'ι' " (at level 0, no associativity).
Reserved Notation " '⟦' s '⟧' p " (at level 0, right associativity, format "'⟦'  s  '⟧' p").

Reserved Notation " base '^{'  power  '}' " (at level 15, left associativity).
Reserved Notation " src '~~~[' x ']~~>' tgt " (at level 70, no associativity).
Reserved Notation " src '---[' x ']-->' tgt " (at level 70, no associativity).
Reserved Notation " src '===[' x ']==>' tgt " (at level 70, no associativity).
Reserved Notation " src '~~~[' x ']~~>*' tgt " (at level 70, no associativity).
Reserved Notation " src '---[' x ']-->*' tgt " (at level 70, no associativity).

Module MonadNotations.

Infix ">>=" := bind.

End MonadNotations.

Declare Scope lang_scope.
