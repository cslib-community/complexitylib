/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

import Complexity.Computability.GenericRAM.Native.Certificate

/-! Proof replacement at a fixed plain proposition does not change Native's selected data.

This does not assert equality of machines selected from the old and new codec class types.
The classes contain only capabilities; exposed Native data is chosen from plain implementation
proofs whose proposition remains unchanged.
-/

open Turing.MultiTapeTM Cslib.GenericRAM

variable {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}

example (h₁ h₂ : ComputableInPolyTime f encIn encOut) :
    NativeCertificate.ofPolyTime h₁ = NativeCertificate.ofPolyTime h₂ ∧
    (NativeCertificate.ofPolyTime h₁).time = (NativeCertificate.ofPolyTime h₂).time ∧
    (NativeCertificate.ofPolyTime h₁).space = (NativeCertificate.ofPolyTime h₂).space :=
  ⟨rfl, rfl, rfl⟩
