/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Kolmogorov.Uncomputability
import Complexity.Crypto.Computational.PRGToOneWay
import Complexity.Foundations.Data.BitString.ShortWords

/-!
Regression clients for concrete Kolmogorov complexity examples, the growth and uncomputability of
plain Kolmogorov complexity, the binary words of bounded length, and one-way functions from
pseudorandom generators.
-/

namespace ComplexityTests.KolmogorovCrypto

open Cslib Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod Cslib.Crypto Filter Finset
open scoped NNReal

/-! ### Concrete Kolmogorov complexity examples -/

-- Exact values for the literal description method on a three-bit word.
example : literal.Produces [true, false, true] [true, false, true] := literal_produces.2 rfl

example : ¬ literal.Produces [true, false] [true, false, true] := by simp [literal_produces]

example : literal.ecomplexity [true, false, true] = 3 := by simp

example : literal.complexity [true, false, true] = 3 := by simp [DescriptionMethod.complexity]

example : literal.etimeBoundedComplexity 3 [true, false, true] = 3 := by
  rw [etimeBoundedComplexity_literal (by decide)]
  rfl

example : literal.etimeBoundedComplexity 2 [true, false, true] = ⊤ :=
  etimeBoundedComplexity_literal_eq_top (by decide)

-- Mapping a description method by an involution preserves exact complexity.
example : (literal.map List.reverse).ecomplexity [true, false, false] = 3 := by
  have h : [true, false, false] = ([false, false, true] : List Bool).reverse := rfl
  rw [h, ecomplexity_map_eq_of_injective List.reverse_injective]
  simp

-- Mapping by `List.length` witnesses that `3` has description length at most `3`.
example : (literal.map List.length).ecomplexity 3 ≤ 3 := by
  have h : (3 : ℕ) = ([true, false, true] : List Bool).length := rfl
  rw [h]
  exact (ecomplexity_map_le List.length literal [true, false, true]).trans_eq (by simp)

-- Concrete finiteness, optimality, and time-bounded attainment for `universal`.
example :
    universal.ecomplexity 0 ≠ ⊤ ∧
    universal.ecomplexity 42 ≠ ⊤ ∧
    (universal.complexity 42 : ℕ∞) = universal.ecomplexity 42 ∧
    (∃ p : List Bool, universal.Produces p 42 ∧ (p.length : ℕ∞) = universal.ecomplexity 42) ∧
    (∃ t, universal.etimeBoundedComplexity t 42 = universal.ecomplexity 42) :=
  ⟨ecomplexity_universal_ne_top 0,
   ecomplexity_universal_ne_top 42,
   natCast_complexity_universal 42,
   universal.exists_length_eq_ecomplexity (ecomplexity_universal_ne_top 42),
   universal.exists_etimeBoundedComplexity_eq_ecomplexity 42⟩

/-! ### Growth and uncomputability of plain Kolmogorov complexity -/

-- Growth, composition bound, square-root separation, and uncomputability for `universal`.
example :
    (∀ᶠ x in atTop, 10 ≤ universal.complexity x) ∧
    (∃ c, ∀ x, universal.complexity (2 ^ x) ≤ x + c) ∧
    (∃ c, ∀ x, universal.complexity (x + 1) ≤ universal.complexity x + c) ∧
    (∃ᶠ x in atTop, universal.complexity x < Nat.sqrt x) ∧
    ¬ Computable universal.complexity := by
  refine ⟨tendsto_atTop.1 tendsto_complexity_universal 10, ?_,
    exists_complexity_universal_comp_le Computable.succ,
    frequently_complexity_universal_lt_of_computable Primrec.nat_sqrt.to_comp
      (fun k => ⟨k * k, (Nat.sqrt_eq k).ge⟩),
    not_computable_complexity_universal⟩
  obtain ⟨c, hc⟩ := exists_complexity_universal_le_size_add
  refine ⟨c + 1, fun x => ?_⟩
  have h := hc (2 ^ x)
  rw [Nat.size_pow] at h
  omega

/-! ### Binary words of bounded length -/

example : [true, false] ∈ BitString.shortWords 2 := by simp

example : [true, false, true] ∉ BitString.shortWords 2 := by simp

example : #(BitString.shortWords 3) = 15 := by simp [BitString.card_shortWords]

/-! ### One-way functions from pseudorandom generators -/

-- A generator stretching `n` bits to `2 n + 1` bits is one-way.
example {G : List Bool → List Bool} (hG : PseudorandomGenerator G fun n => 2 * n + 1) :
    OneWay G :=
  hG.oneWay fun n => by omega

/-- The stretch `n ↦ n + (⌊log₂ n⌋ + 1) ^ 2`, below `2 n` for large `n`. -/
private abbrev logSqStretch (n : ℕ) : ℕ := n + (Nat.log 2 n + 1) ^ 2

-- It is a valid stretch: it is strictly increasing and expands every length.
example (n : ℕ) : n < logSqStretch n := Nat.lt_add_of_pos_right (by positivity)

private theorem strictMono_logSqStretch : StrictMono logSqStretch := fun _ _ hab =>
  Nat.add_lt_add_of_lt_of_le hab
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right hab.le) 1) 2)

example : logSqStretch 64 < 2 * 64 := by decide

example {G : List Bool → List Bool} (hG : PseudorandomGenerator G logSqStretch)
    (hgap : Negligible fun n => (1 / 2 : ℝ≥0) ^ (logSqStretch n - n)) :
    OneWay G ∧
    (∃ f : List Bool → List Bool, OneWay f) ∧
    ((∃ f : List Bool → List Bool, OneWay f) ↔
      ∃ (G' : List Bool → List Bool) (ℓ : ℕ → ℕ), PseudorandomGenerator G' ℓ) :=
  ⟨hG.oneWay_of_injective strictMono_logSqStretch.injective hgap,
   hG.exists_oneWay,
   exists_oneWay_iff_exists_pseudorandomGenerator⟩

end ComplexityTests.KolmogorovCrypto
