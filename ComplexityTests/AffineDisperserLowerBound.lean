/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.AffineDisperser

/-!
# Tests for the `3.5 n - 7 d` lower bound for affine dispersers

Non-vacuity checks for `Complexity.Computability.Circuit.Boolean.AffineDisperser` and
`Complexity.Foundations.Combinatorics.AffineDisperser.Basic`: affine dispersers exist, so the
hypothesis of Theorem 4.1 is satisfiable, and the theorem gives a concrete bound.
-/

namespace ComplexityTests.AffineDisperserLowerBound

open Cslib Cslib.Circuits Cslib.BitString Cslib.Circuits.Boolean.AffineDisperser

/-! ### Affine dispersers exist -/

/-- The first bit is an affine disperser for dimension `1` on one bit: an injective map from
`BitString 1` to itself is onto. -/
theorem isAffineDisperser_first : IsAffineDisperser (fun x : BitString 1 => x 0) 1 := by
  intro g _ hinj
  obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.1 hinj fun _ => true
  obtain ⟨v, hv⟩ := Finite.injective_iff_surjective.1 hinj fun _ => false
  exact ⟨u, v, by simp [hu, hv]⟩

/-- Affine dispersers exist for dimension `11` on `100` bits and dimension `15` on `1000` bits,
while no function is an affine disperser for dimension `0`. -/
example (f : BitString 3 → Bool) :
    (∃ g : BitString 100 → Bool, IsAffineDisperser g 11) ∧
      (∃ h : BitString 1000 → Bool, IsAffineDisperser h 15) ∧
      ¬ IsAffineDisperser f 0 :=
  ⟨exists_isAffineDisperser (by norm_num), exists_isAffineDisperser (by norm_num),
    not_isAffineDisperser_zero f⟩

/-! ### The lower bound -/

/-- Some function on `100` bits needs at least `273` gates over the full binary basis, by
Theorem 4.1 with `d = 11`: `7 · 100 ≤ 2 |C| + 14 · 11`. -/
example : ∃ f : BitString 100 → Bool, ∀ C : Circuit (fullSignature 2 Bool) 100 1,
    C.Computes fullInterpretation (single f) → 273 ≤ C.size := by
  obtain ⟨f, hf⟩ := exists_isAffineDisperser (n := 100) (d := 11) (by norm_num)
  exact ⟨f, fun C hC => by have := seven_mul_le_two_mul_size_add hf C hC; omega⟩

/-- The circuit without gates computing the first bit. -/
abbrev firstBit : Circuit (fullSignature 2 Bool) 1 1 :=
  Circuit.wiring _ fun _ => 0

/-- The circuit without gates computing the first bit starts gate elimination in a valid state
with `a = 1`, and Theorem 4.1 for `n = d = 1` asks nothing of it. -/
example :
    (initialState firstBit).Valid (fun x : BitString 1 => x 0) ∧
      (initialState firstBit).a = 1 ∧
      7 * 1 ≤ 2 * firstBit.size + 14 * 1 :=
  ⟨initialState_valid (Circuit.wiring_computes _ _), initialState_a _,
    seven_mul_le_two_mul_size_add isAffineDisperser_first _ (Circuit.wiring_computes _ _)⟩

end ComplexityTests.AffineDisperserLowerBound
