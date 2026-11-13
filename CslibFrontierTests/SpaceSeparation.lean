/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Complexity.Classes.Space.Separation
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Classes.Padding.Language
import CslibFrontier.Computability.Complexity.Classes.Padding.Space
import CslibFrontier.Computability.Complexity.Classes.Space.Quantitative

/-! Clients of the padded language, space padding, the `DSPACE` bridges and Book's separation of
linear space from `NP`. -/

open Cslib.Complexity Turing.MultiTapeTM

/-- Book's theorem, in the exact form of Arora–Barak 2007 Exercise 3.2. -/
example : DSPACE encBits (fun n => n) ≠ NP encBits := DSPACE_ne_NP

-- Quadratic space is not closed under polynomial-time reductions either, so it is not `NP`.
example : DSPACE encBits (· ^ 2) ≠ NP encBits :=
  DSPACE_pow_ne_of_polyTimeReducible_mem (by norm_num) fun _ _ h hB => h.mem_NP hB

-- Padding a cubic-space problem with exponent `3` lands in linear space, and the problem reduces
-- to its padded version.
example (A : Set (List Bool)) (hA : A ∈ DSPACE encBits fun n => (n + 1) ^ 3) :
    polynomialPadded A 3 ∈ DSPACE encBits (fun n => (n + 1) ^ 1) ∧
      PolyTimeReducible encBits encBits A (polynomialPadded A 3) :=
  ⟨polynomialPadded_mem_DSPACE le_rfl (by simpa using hA),
    polyTimeReducible_polynomialPadded A (by norm_num)⟩

-- Membership of an arbitrary word: a framed word followed by any long enough suffix, not only
-- ones, is in the padded language exactly when the framed word is in `A`.
example (A : Set (List Bool)) (k : ℕ) (y v : List Bool)
    (hv : (y.length + 1) ^ k ≤ (frame y ++ v).length) :
    frame y ++ v ∈ polynomialPadded A k ↔ y ∈ A := by
  rw [mem_polynomialPadded_iff, unframe_frame_append]
  exact and_iff_right hv

-- A framed word without padding is too short for exponent `2`.
example (A : Set (List Bool)) : frame [true] ∉ polynomialPadded A 2 := by
  rw [mem_polynomialPadded_iff, ← List.append_nil (frame [true]), unframe_frame_append]
  simp

-- Any padding length at least `(|y| + 1) ^ k` works, as used by the unpadding direction.
example (A : Set (List Bool)) (y : List Bool) :
    frame y ++ List.replicate ((y.length + 1) ^ 2 + 5) true ∈ polynomialPadded A 2 ↔ y ∈ A :=
  frame_append_replicate_mem_polynomialPadded_iff (Nat.le_add_right _ _)

-- The `DSPACE` bridges compose: a problem in `DSPACE s` is decided in the quantitative calculus
-- within space `O(s n)`, and that decider puts it back in `DSPACE s`.
example {α : Type} (enc : α ↪ List Bool) (s : ℕ → ℕ) (A : Set α) (hA : A ∈ DSPACE enc s) :
    {a | indicator A a = true} ∈ DSPACE enc s :=
  let ⟨_, hT⟩ := computableInO_indicator_of_mem_DSPACE hA
  setOf_mem_DSPACE_of_computableInO hT fun _ => le_rfl

-- If linear space were `NP`, every problem reducing to a linear-space problem would be in it.
example (h : DSPACE encBits (fun n => n) = NP encBits) : False := by
  obtain ⟨A, B, hAB, hB, hA⟩ := exists_polyTimeReducible_mem_DSPACE_pow_notMem (k := 1) le_rfl
  simp only [pow_one] at hB hA
  rw [h] at hB hA
  exact hA (hAB.mem_NP hB)
