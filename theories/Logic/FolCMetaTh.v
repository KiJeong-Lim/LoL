Require Import LoL.Prelude.Prelude.
Require Import LoL.Prelude.Notations.
Require Import LoL.Math.ThN.
Require Import LoL.Data.Vector.
Require Import LoL.Logic.FolSyntax.
Require Import LoL.Logic.FolSemantics.
Require Import LoL.Logic.FolHPS.
Require Import LoL.Logic.FolND.

#[local] Infix "\in" := E.elem.
#[local] Infix "\subseteq" := E.isSubsetOf.

#[local] Infix "≡" := alpha_equiv.
#[local] Infix "⊢" := infers.
#[local] Infix "\proves" := proves.
