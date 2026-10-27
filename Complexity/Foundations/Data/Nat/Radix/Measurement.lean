/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.Nat.Radix
import Mathlib.Data.List.OfFn

/-!
# Fixed-width signed measurement values

`measurementValues c D j` decodes `c` little-endian digits in radix `2 * D + 1`, shifted by
`-D`. The result is runtime list data, including at `D = 0` (radix one) and `c = 0`.
This is the measurement-VALUE box, not a tuple of formal monomial exponents.
-/

@[expose] public section
namespace Cslib.Radix

/-- Decode a runtime number of signed measurement coordinates using the existing radix digits. -/
def measurementValues (c D j : ℕ) : List ℤ :=
  (List.range c).map fun i => (digit (2 * D + 1) j i : ℤ) - D

/-- The tuple keeps its full declared dimension, including zero entries. -/
@[simp] theorem length_measurementValues (c D j : ℕ) :
    (measurementValues c D j).length = c := by
  simp [measurementValues]

/-- Every coordinate is in the required signed interval, even at out-of-range indices. -/
theorem measurementValues_bounds (c D j : ℕ) :
    ∀ z ∈ measurementValues c D j, -(D : ℤ) ≤ z ∧ z ≤ D := by
  intro z hz
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
  have hd : digit (2 * D + 1) j i < 2 * D + 1 := by
    rw [digit_eq_div_pow_mod]
    exact Nat.mod_lt _ (by omega)
  omega

private theorem shifted_digit (D d : ℕ) :
    (((d : ℤ) - D + D).toNat) = d := by omega

private theorem decoded_value (c D j : ℕ) (hj : j < (2 * D + 1) ^ c) :
    Nat.ofDigits (2 * D + 1)
      ((measurementValues c D j).map fun z => (z + (D : ℤ)).toNat) = j := by
  obtain ⟨x, hx, hval⟩ := Nat.exists_ofDigits_ofFn hj
  have hwords : (measurementValues c D j).map (fun z => (z + (D : ℤ)).toNat) = List.ofFn x := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp only [measurementValues, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [shifted_digit, ← hval]
    exact (digit_ofDigits (B := 2 * D + 1) (by omega) (List.ofFn x)
      (by simpa using hx) i (by simpa using hi')).trans (List.getElem_ofFn hi')
  rw [hwords, hval]

/-- No two fitting indices encode the same signed measurement tuple, including radix one. -/
theorem measurementValues_injective (c D : ℕ) :
    Function.Injective (fun j : Fin ((2 * D + 1) ^ c) => measurementValues c D j) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg
    (fun word : List ℤ => Nat.ofDigits (2 * D + 1) (word.map fun z => (z + (D : ℤ)).toNat)) h
  simpa only [decoded_value c D i i.isLt, decoded_value c D j j.isLt] using hv

/-- Every list of the declared length with coordinates in the signed interval has exactly one
fitting index. This proves actual decoder coverage without materializing the box. -/
theorem measurementValues_coverage (c D : ℕ) (word : List ℤ) (hlen : word.length = c)
    (hword : ∀ z ∈ word, -(D : ℤ) ≤ z ∧ z ≤ D) :
    ∃! j : Fin ((2 * D + 1) ^ c), measurementValues c D j = word := by
  let digits := word.map fun z => (z + (D : ℤ)).toNat
  have hd : ∀ d ∈ digits, d < 2 * D + 1 := by
    intro d hd
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hd
    have := hword z hz
    omega
  have hv : Nat.ofDigits (2 * D + 1) digits < (2 * D + 1) ^ c := by
    simpa [digits, hlen] using Nat.ofDigits_lt_base_pow_length_of_pos (by omega) digits hd
  let j : Fin ((2 * D + 1) ^ c) := ⟨Nat.ofDigits (2 * D + 1) digits, hv⟩
  have hj : measurementValues c D j = word := by
    apply List.ext_getElem (by simp [hlen])
    intro i hi hi'
    simp only [measurementValues, List.getElem_map, List.getElem_range]
    have he := digit_ofDigits (B := 2 * D + 1) (by omega) digits hd i (by simpa [digits] using hi')
    have hz := hword word[i] (List.getElem_mem hi')
    change (digit (2 * D + 1) (Nat.ofDigits (2 * D + 1) digits) i : ℤ) - D = word[i]
    rw [he]
    simp only [digits, List.getElem_map]
    omega
  exact ⟨j, hj, fun k hk => measurementValues_injective c D (hk.trans hj.symm)⟩

end Cslib.Radix
