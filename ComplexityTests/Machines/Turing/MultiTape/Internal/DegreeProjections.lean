/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreePrimitives

/-! Direct projection clients retain arbitrary encodings, growing words and empty components. -/
open Turing.MultiTapeTM
universe u

example {α β : Type u} (a : α ↪ List Bool) (b : β ↪ List Bool) :
    ComputableInDegree Prod.fst (encPair a b) a 1 1 :=
  ComputableInDegree.fst a b

example {α β : Type u} (a : α ↪ List Bool) (b : β ↪ List Bool) :
    ComputableInDegree Prod.snd (encPair a b) b 1 1 :=
  ComputableInDegree.snd a b

example : ComputableInDegree Prod.fst
    (encPair (Function.Embedding.refl (List Bool)) (Function.Embedding.refl (List Bool)))
    (Function.Embedding.refl (List Bool)) 1 1 :=
  ComputableInDegree.fst _ _

example : ComputableInDegree Prod.snd
    (encPair (Function.Embedding.refl (List Bool)) (Function.Embedding.refl (List Bool)))
    (Function.Embedding.refl (List Bool)) 1 1 :=
  ComputableInDegree.snd _ _
