Require Import LoL.Prelude.Prelude.

Module Fin.

Inductive t : nat -> Set :=
  | FZ (n : nat) : t (S n)
  | FS (n : nat) (i : t n) : t (S n).

#[global] Arguments FZ {n}.
#[global] Arguments FS {n} (i).

End Fin.

Notation FZ := Fin.FZ.
Notation FS := Fin.FS.

#[global] Declare Scope vec_scope.

Module Vector.

#[universes(template)]
Inductive t (A : Type) : nat -> Type :=
  | VNil : t A O
  | VCons (n : nat) (x : A) (xs : t A n) : t A (S n).

#[global] Arguments VNil {A}.
#[global] Arguments VCons {A} (n) (x) (xs).

End Vector.

#[global] Bind Scope vec_scope with Vector.t.

Notation " [ ] " := (@Vector.VNil _) : vec_scope.
Notation " x :: xs " := (@Vector.VCons _ _ x xs) : vec_scope.

Notation VNil := Vector.VNil.
Notation VCons := Vector.VCons.

#[local] Open Scope vec_scope.
