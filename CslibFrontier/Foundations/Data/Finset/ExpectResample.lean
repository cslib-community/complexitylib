/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/{,Order/}BigOperators/Expect.lean`)

public import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Resampling a coordinate and even powers of averages

Two facts about uniform averages used by Cauchy–Schwarz arguments that double a sample.
An average raised to the power `2 ^ m` is at most the average of the `2 ^ m`-th powers
(`Finset.pow_two_pow_expect_le_expect_pow_two_pow`), by `m` applications of
`Finset.sq_expect_le_expect_sq`. Resampling one coordinate of a uniformly random dependent function
`∀ i, X i` keeps it uniformly random (`Fintype.expect_expect_update_pi`), the dependent form of
`Fintype.expect_expect_update`, with no nonemptiness assumption.

## Main results

* `Finset.pow_two_pow_expect_le_expect_pow_two_pow`: `(𝔼 f) ^ (2 ^ m) ≤ 𝔼 f ^ (2 ^ m)`.
* `Fintype.expect_expect_update_pi`: `𝔼 s, 𝔼 a, F (update s i a) = 𝔼 s, F s`.
-/

public section

open scoped BigOperators

namespace Finset

variable {ι R : Type*} [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
  [Module ℚ≥0 R] [PosSMulMono ℚ≥0 R]

/-- An average raised to the power `2 ^ m` is at most the average of the `2 ^ m`-th powers, by
repeated Cauchy–Schwarz (`Finset.sq_expect_le_expect_sq`). Over `ℝ` this is a case of the
even-power Jensen inequality `Real.pow_arith_mean_le_arith_mean_pow_of_even`; this form needs no
convexity and holds in any linearly ordered semiring averaged over `ℚ≥0`. -/
theorem pow_two_pow_expect_le_expect_pow_two_pow (s : Finset ι) (f : ι → R) (m : ℕ) :
    (𝔼 i ∈ s, f i) ^ (2 ^ m) ≤ 𝔼 i ∈ s, f i ^ (2 ^ m) := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    have hpow : ∀ x : R, x ^ (2 ^ (m + 1)) = (x ^ 2) ^ (2 ^ m) := fun x => by
      rw [pow_succ', pow_mul]
    rw [hpow, expect_congr rfl fun i _ => hpow (f i)]
    exact (pow_le_pow_left₀ (sq_nonneg _) (sq_expect_le_expect_sq s f) _).trans
      (ih fun i => f i ^ 2)

end Finset

namespace Fintype

variable {ι M : Type*} [Fintype ι] [AddCommMonoid M] [Module ℚ≥0 M]

/-- Resampling one coordinate of a uniformly random dependent function keeps it uniformly random:
the dependent form of `Fintype.expect_expect_update`, with no nonemptiness assumption. -/
theorem expect_expect_update_pi [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
    (F : (∀ i, X i) → M) (i : ι) :
    𝔼 s, 𝔼 a : X i, F (Function.update s i a) = 𝔼 s, F s := by
  let e : Equiv.Perm ((∀ j, X j) × X i) :=
    Function.Involutive.toPerm (fun p ↦ (Function.update p.1 i p.2, p.1 i)) fun p ↦ by simp
  calc 𝔼 s, 𝔼 a : X i, F (Function.update s i a) = 𝔼 p : (∀ j, X j) × X i, F (e p).1 :=
        (Fintype.expect_prod_type (fun p : (∀ j, X j) × X i ↦ F (e p).1)).symm
    _ = 𝔼 p : (∀ j, X j) × X i, F p.1 := Fintype.expect_equiv e _ _ fun _ ↦ rfl
    _ = 𝔼 s, F s := by
      rcases isEmpty_or_nonempty (X i) with h | h
      · have : IsEmpty (∀ j, X j) := ⟨fun s ↦ h.false (s i)⟩
        simp
      · exact Fintype.expect_comp_fst F

end Fintype
