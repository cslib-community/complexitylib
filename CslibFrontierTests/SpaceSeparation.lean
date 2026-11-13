/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Complexity.Classes.Space.Separation
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Classes.Padding.Space

/-! Clients of space padding and of Book's separation of linear space from `NP`. -/

open Cslib.Complexity Turing.MultiTapeTM

/-- Book's theorem, in the exact form of Arora–Barak 2007 Exercise 3.2. -/
example : DSPACE encBits (fun n => n) ≠ NP encBits := DSPACE_ne_NP

-- Quadratic space is not closed under polynomial-time reductions either, so it is not `NP`.
example : DSPACE encBits (· ^ 2) ≠ NP encBits :=
  DSPACE_pow_ne_of_polyTimeReducible_mem (by norm_num) fun _ _ h hB => h.mem_NP hB

-- Padding a cubic-space problem with exponent `3` lands in linear space, and the problem reduces
-- to its padded version.
example (A : Set (List Bool)) (hA : A ∈ DSPACE encBits fun n => (n + 1) ^ 3) :
    spacePadded A 3 ∈ DSPACE encBits (fun n => (n + 1) ^ 1) ∧
      PolyTimeReducible encBits encBits A (spacePadded A 3) :=
  ⟨spacePadded_mem_DSPACE le_rfl (by simpa using hA), polyTimeReducible_spacePadded A (by norm_num)⟩

-- If linear space were `NP`, every problem reducing to a linear-space problem would be in it.
example (h : DSPACE encBits (fun n => n) = NP encBits) : False := by
  obtain ⟨A, B, hAB, hB, hA⟩ := exists_polyTimeReducible_mem_DSPACE_pow_notMem (k := 1) le_rfl
  simp only [pow_one] at hB hA
  rw [h] at hB hA
  exact hA (hAB.mem_NP hB)
