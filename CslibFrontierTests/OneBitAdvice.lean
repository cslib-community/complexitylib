/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: candidate
import CslibFrontier.Computability.Complexity.Classes.Advice.OneBit
import CslibFrontier.Computability.Circuit.Boolean.Advice

/-! # Goldreich's one-bit advice endpoint

The source statement combines one exact advice bit, polynomial circuits, native undecidability
and membership depending only on the input length. An even-length language exercises the class
at both the empty input and an odd-length input.
-/

open Cslib Cslib.Complexity Cslib.Circuits.Boolean Turing.MultiTapeTM

example : ∃ L ∈ PWithAdvice (fun _ => 1), L ∈ PPoly ∧ ¬ IsDecidable L encBits ∧
    ∀ x y : List Bool, x.length = y.length → (x ∈ L ↔ y ∈ L) := by
  obtain ⟨L, hL, hdec, hlen⟩ := exists_mem_PWithAdvice_one_not_isDecidable
  exact ⟨L, hL, PWithAdvice_subset_PPoly (by fun_prop) hL, hdec, hlen⟩

example : List.length ⁻¹' {n : ℕ | n % 2 = 0} ∈ PWithAdvice (fun _ => 1) :=
  length_preimage_mem_PWithAdvice_one _

example : [] ∈ (List.length ⁻¹' {n : ℕ | n % 2 = 0} : Set (List Bool)) := by
  change 0 % 2 = 0
  decide

example : [true] ∉ (List.length ⁻¹' {n : ℕ | n % 2 = 0} : Set (List Bool)) := by
  change ¬ 1 % 2 = 0
  decide
