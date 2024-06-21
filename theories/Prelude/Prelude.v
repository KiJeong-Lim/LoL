Require Export Coq.Arith.Compare_dec.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Arith.Wf_nat.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Lists.List.
Require Export Coq.micromega.Lia.
Require Export Coq.Program.Basics.
Require Export Coq.Program.Utils.
Require Export Coq.Program.Wf.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Relations.Relation_Operators.
Require Export Coq.Setoids.Setoid.
Require Export LoL.Prelude.SfLib.

#[universes(polymorphic)]
Class cat@{u v} : Type :=
  { ob : Type@{u}
  ; hom (dom : ob) (cod : ob) : Type@{v}
  ; compose {A} {B} {C} (g : hom B C) (f : hom A B) : hom A C
  ; id {A} : hom A A
  }.

#[global] Coercion ob : cat >-> Sortclass.
#[global] Coercion hom : cat >-> Funclass.
