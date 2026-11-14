/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.NumberTheory.PrimeCollision
public import CslibFrontier.Foundations.NumberTheory.PrimeWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Collisions in closed prime windows

This is a quantified interpretation of [Goldreich2007DraftR5], Exercise 9.7
(`r5.pdf`, PDF64/printed446). The source says only `L = poly(log M)`;
it specifies neither an error parameter nor a polynomial degree.
For every positive error tolerance, one constant works for all input bounds,
window sizes and fixed distinct pairs. This is a pairwise statement, not a
simultaneous guarantee for every pair. Uniform sampling is among the primes;
no efficient prime sampler or runtime bound is asserted.

## Main results

* `Nat.exists_closedPrimes_collision_bound`: nonempty windows and pairwise error bounds.
* `Nat.exists_ceil_closedPrimes_collision_bound`: natural sizes at the quadratic threshold.
-/

public section

namespace Nat

/-- The primes in the closed interval `[lo, hi]`. -/
@[expose] def closedPrimes (lo hi : ℕ) : Finset ℕ :=
  (Finset.Icc lo hi).filter Nat.Prime

private theorem sqrt_card {c x : ℝ} (hc : 0 < c) (hx : 4 ≤ x)
    {S : Finset ℕ} (hS : c * (x / Real.log x) ≤ (S.card : ℝ)) :
    c * Real.sqrt x / 2 ≤ (S.card : ℝ) := by
  have hs := Real.sq_sqrt (show 0 ≤ x by linarith)
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have := Real.log_le_rpow_div (show 0 ≤ x by linarith)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at this
    linarith
  have hp : 0 < Real.log x := Real.log_pos (by linarith)
  have h := (le_div_iff₀ hp).mpr
    (show Real.sqrt x / 2 * Real.log x ≤ x by
      nlinarith [Real.sqrt_nonneg x])
  nlinarith

/-- One positive density constant bounds both closed windows by a square root. -/
private theorem exists_sqrt_card_closedPrimes :
    ∃ c : ℝ, 0 < c ∧ ∀ L : ℕ, 6 ≤ L →
      c * Real.sqrt L / 2 ≤ ((closedPrimes 3 L).card : ℝ) ∧
      c * Real.sqrt L / 2 ≤ ((closedPrimes L (2 * L)).card : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := exists_forall_mul_div_log_le_card_primes
  refine ⟨c, hc, fun L hL => ?_⟩
  have hLr : (6 : ℝ) ≤ L := by exact_mod_cast hL
  constructor
  · apply sqrt_card hc (by linarith)
    apply hcount _ (by linarith)
    intro p hp hlo hhi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hp⟩
    · have : (3 : ℝ) ≤ p := by linarith
      exact_mod_cast this
    · exact_mod_cast hhi.le
  · have h := sqrt_card hc (show (4 : ℝ) ≤ 2 * L by linarith)
      (hcount (2 * L) (by linarith) (closedPrimes L (2 * L)) (by
        intro p hp hlo hhi
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hp⟩
        · exact_mod_cast (show (L : ℝ) ≤ p by linarith)
        · exact_mod_cast hhi.le))
    have hs : Real.sqrt (L : ℝ) ≤ Real.sqrt (2 * L) :=
      Real.sqrt_le_sqrt (by linarith)
    nlinarith

/-- Quantified interpretation of Exercise 9.7 for both closed prime windows.
The same `C` works for every `M`, `L` and fixed pair `a ≠ b`. -/
theorem exists_closedPrimes_collision_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M L : ℕ, 2 ≤ M →
      C * (Nat.log2 M : ℝ) ^ 2 ≤ L →
      ∀ Q ∈ [closedPrimes 3 L, closedPrimes L (2 * L)],
        Q.Nonempty ∧ ∀ a b : ℕ, a ≤ M → b ≤ M → a ≠ b →
          ((Q.filter fun p => Nat.ModEq p a b).card : ℝ) / Q.card ≤ δ := by
  obtain ⟨c, hc, hcount⟩ := exists_sqrt_card_closedPrimes
  let C : ℝ := max 6 (4 / (c ^ 2 * δ ^ 2))
  refine ⟨C, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro M L hM hL Q hQ
  have hk : (1 : ℝ) ≤ Nat.log2 M := by
    exact_mod_cast (show 1 ≤ Nat.log2 M by
      rw [Nat.log2_eq_log_two]
      exact Nat.le_log_of_pow_le (by norm_num) (by simpa using hM))
  have hC6 : 6 ≤ C := le_max_left _ _
  have hC : 4 / (c ^ 2 * δ ^ 2) ≤ C := le_max_right _ _
  have hL6 : 6 ≤ L := by exact_mod_cast (show (6 : ℝ) ≤ L by nlinarith)
  have hcards := hcount L hL6
  have hcard : c * Real.sqrt L / 2 ≤ (Q.card : ℝ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl
    · exact hcards.1
    · exact hcards.2
  have hpr : ∀ p ∈ Q, p.Prime := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl <;> exact fun p hp => (Finset.mem_filter.mp hp).2
  have hscale : 4 * (Nat.log2 M : ℝ) ^ 2 ≤ (L : ℝ) * (c ^ 2 * δ ^ 2) := by
    have hden : 0 < c ^ 2 * δ ^ 2 := by positivity
    have := (div_le_iff₀ hden).mp hC
    nlinarith
  have hs := Real.sq_sqrt (Nat.cast_nonneg L)
  have hroot := Real.sqrt_nonneg (L : ℝ)
  have hlarge : (Nat.log2 M : ℝ) ≤ δ * (Q.card : ℝ) := by
    have hpos : 0 ≤ c * δ * Real.sqrt L := by positivity
    have hsq : (2 * (Nat.log2 M : ℝ)) ^ 2 ≤ (c * δ * Real.sqrt L) ^ 2 := by
      calc
        _ = 4 * (Nat.log2 M : ℝ) ^ 2 := by ring
        _ ≤ (L : ℝ) * (c ^ 2 * δ ^ 2) := hscale
        _ = (c * δ * Real.sqrt L) ^ 2 := by rw [mul_pow, mul_pow, hs]; ring
    have : 2 * (Nat.log2 M : ℝ) ≤ c * δ * Real.sqrt L := by nlinarith
    nlinarith
  have hcardpos : 0 < (Q.card : ℝ) := by nlinarith
  refine ⟨Finset.card_pos.mp (by exact_mod_cast hcardpos), ?_⟩
  intro a b ha hb hne
  apply (div_le_iff₀ hcardpos).mpr
  have hbad : ((Q.filter fun p => Nat.ModEq p a b).card : ℝ) ≤ Nat.log2 M := by
    exact_mod_cast card_filter_modEq_le_log hpr ha hb hne
  exact hbad.trans hlarge

/-- Choosing the ceiling of the quadratic threshold gives natural window sizes. -/
theorem exists_ceil_closedPrimes_collision_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M →
      let L := ⌈C * (Nat.log2 M : ℝ) ^ 2⌉₊
      ∀ Q ∈ [closedPrimes 3 L, closedPrimes L (2 * L)],
        Q.Nonempty ∧ ∀ a b : ℕ, a ≤ M → b ≤ M → a ≠ b →
          ((Q.filter fun p => Nat.ModEq p a b).card : ℝ) / Q.card ≤ δ := by
  obtain ⟨C, hC, hbound⟩ := exists_closedPrimes_collision_bound hδ
  exact ⟨C, hC, fun M hM => hbound M _ hM (Nat.le_ceil _)⟩

end Nat
