/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Moser.Compression
public import Complexity.Probability.BitString.CoinFlips
public import Mathlib.Basic.Real.ENatENNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Moser's algorithm on fair coins

Run Moser's algorithm (`Complexity.Logics.Propositional.CNF.Moser`) on a tape of independent fair
coin flips (`Cslib.BitString.coinFlips`). Whether the run uses up a budget of `t` resamplings
depends only on the first `n + t k` bits of the tape, so its probability is the fraction of the
words of that length on which it does. If every clause of an exact `k`-CNF shares a variable with
fewer than `2 ^ (k - 3)` other clauses, the counting bound of
`Complexity.Logics.Propositional.CNF.Moser.Compression` makes this probability at most
`2 ^ (m + 1) 2⁻ᵗ` (`coinFlips_exhausts_le`).

The number of resamplings of the run without a budget (`resamplings`, `⊤` when the run does not
stop) is therefore at most `m + 2` in expectation (`lintegral_resamplings_le`) and finite almost
surely (`ae_resamplings_ne_top`). Almost surely the run stops with a satisfying assignment
(`ae_exists_eval_final`). The constant `m + 2` is the one of this encoding, whose scan of `Solve`
costs one bit per clause, under the bound `r < 2 ^ (k - 3)` reported by Fortnow [Fortnow2009]; it
is not a cited endpoint. Fortnow derives `O(m log m)` resamplings, and Moser [Moser2009] expected
polynomial time for his algorithm with restarts. An expected number of resamplings linear in `m`
is the symmetric case of the theorem of Moser and Tardos [MoserTardos2010], whose general
criterion `e p (d + 1) ≤ 1` is not covered here.

## Main definitions

* `Cslib.Logic.PL.Moser.resamplings`: the number of resamplings of the run without a budget.

## Main results

* `Cslib.Logic.PL.Moser.coinFlips_exhausts_le`: the tail bound
  `Pr[t resamplings] ≤ 2 ^ (m + 1) 2⁻ᵗ`.
* `Cslib.Logic.PL.Moser.lintegral_resamplings_le`: at most `m + 2` resamplings in expectation.
* `Cslib.Logic.PL.Moser.ae_resamplings_ne_top`: the run stops almost surely.
* `Cslib.Logic.PL.Moser.ae_exists_eval_final`: **the algorithmic Local Lemma for `k`-SAT**.

## References

* [R. A. Moser, *A constructive proof of the Lovász Local Lemma*][Moser2009]
* [L. Fortnow, *A Kolmogorov Complexity Proof of the Lovász Local Lemma*][Fortnow2009]
* [R. A. Moser and G. Tardos, *A constructive proof of the general Lovász Local
  Lemma*][MoserTardos2010]
-/

public section

namespace Cslib.Logic.PL.Moser

open Finset MeasureTheory Cslib.BitString
open scoped ENNReal

variable {n : ℕ} {φ : CNF (Fin n)}

/-! ### The probability of long runs -/

theorem measurableSet_exhausts {k : ℕ} (hφ : φ.IsExactDistinct k) (t : ℕ) :
    MeasurableSet {x | Exhausts φ k t x} :=
  measurableSet_setOf_of_prefix fun _ _ hxy => exhausts_congr hφ hxy

/-- If every clause of an exact `k`-CNF shares a variable with fewer than `2 ^ (k - 3)` other
clauses, the run on fair coins uses up a budget of `t` resamplings with probability `p` satisfying
`p 2 ^ t ≤ 2 ^ (m + 1)`. -/
theorem coinFlips_exhausts_mul_le {k : ℕ} (hk : 3 ≤ k) (hφ : φ.IsExactDistinct k)
    (hdeg : ∀ i : Fin φ.length, degree φ i < 2 ^ (k - 3)) (t : ℕ) :
    coinFlips {x | Exhausts φ k t x} * 2 ^ t ≤ 2 ^ (φ.length + 1) := by
  have h := card_exhausts_mul_two_pow_lt hk hφ hdeg t
  have hc : ((#{y : Fin (n + t * k) → Bool |
      Exhausts φ k t (Function.extend Fin.val y fun _ => false)} * 2 ^ t : ℕ) : ℝ≥0∞) ≤
      ((2 ^ (n + t * k) * 2 ^ (φ.length + 1) : ℕ) : ℝ≥0∞) := Nat.cast_le.2 h.le
  push_cast at hc
  have hN : (2 : ℝ≥0∞) ^ (n + t * k) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hN' : (2 : ℝ≥0∞) ^ (n + t * k) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [coinFlips_setOf_eq_card_mul fun _ _ hxy => exhausts_congr hφ hxy, mul_right_comm]
  calc _ ≤ (2 : ℝ≥0∞) ^ (n + t * k) * 2 ^ (φ.length + 1) * (2 ^ (n + t * k))⁻¹ := by gcongr
    _ = 2 ^ (φ.length + 1) := by
        rw [mul_right_comm, ENNReal.mul_inv_cancel hN hN', one_mul]

/-- **Moser's tail bound.** If every clause of an exact `k`-CNF shares a variable with fewer than
`2 ^ (k - 3)` other clauses, the run on fair coins uses up a budget of `t` resamplings with
probability at most `2 ^ (m + 1) 2⁻ᵗ`. -/
theorem coinFlips_exhausts_le {k : ℕ} (hk : 3 ≤ k) (hφ : φ.IsExactDistinct k)
    (hdeg : ∀ i : Fin φ.length, degree φ i < 2 ^ (k - 3)) (t : ℕ) :
    coinFlips {x | Exhausts φ k t x} ≤ 2 ^ (φ.length + 1) * 2⁻¹ ^ t := by
  have h := coinFlips_exhausts_mul_le hk hφ hdeg t
  have h2 : (2 : ℝ≥0∞) ^ t * 2⁻¹ ^ t = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  calc coinFlips {x | Exhausts φ k t x} = coinFlips {x | Exhausts φ k t x} * 2 ^ t * 2⁻¹ ^ t := by
        rw [mul_assoc, h2, mul_one]
    _ ≤ 2 ^ (φ.length + 1) * 2⁻¹ ^ t := by gcongr

/-! ### The number of resamplings -/

variable (φ) in
/-- The number of resamplings of the run without a budget, `⊤` if it does not stop. The run with a
budget of `t` follows the run without a budget until it would make a `t + 1`-st resampling, and
stops there instead; it makes the same passes and returns until then. -/
noncomputable def resamplings (k : ℕ) (x : ℕ → Bool) : ℕ∞ :=
  ⨆ t, ((final φ k t x).trace.length : ℕ∞)

/-- The run without a budget makes at least `t` resamplings exactly when the run with a budget of
`t` uses it up. -/
theorem le_resamplings_iff {k t : ℕ} {x : ℕ → Bool} :
    (t : ℕ∞) ≤ resamplings φ k x ↔ Exhausts φ k t x := by
  constructor
  · intro h
    by_contra hx
    have ht : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · exact absurd (Nat.zero_le _) hx
      · exact ht
    have hlt (t' : ℕ) : (final φ k t' x).trace.length < t := by
      rcases le_or_gt t t' with h' | h'
      · rw [final_eq_of_not_exhausts h' hx]
        exact Nat.lt_of_not_le hx
      · exact lt_of_le_of_lt (length_trace_run_le k t' x _) h'
    have hle : resamplings φ k x ≤ ((t - 1 : ℕ) : ℕ∞) :=
      iSup_le fun t' => ENat.natCast_le_natCast.2 (by have := hlt t'; omega)
    have := ENat.natCast_le_natCast.1 (h.trans hle)
    omega
  · intro h
    exact le_iSup_of_le t (ENat.natCast_le_natCast.2 h)

private theorem toENNReal_eq_tsum (r : ℕ∞) :
    (r : ℝ≥0∞) = ∑' t : ℕ, if ((t + 1 : ℕ) : ℕ∞) ≤ r then 1 else 0 := by
  induction r using ENat.recTopCoe with
  | top =>
    simp only [le_top, ite_true, ENat.toENNReal_top]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe r =>
    rw [tsum_eq_sum (s := range r) fun t ht =>
      ite_eq_right fun h => ht (mem_range.2 (ENat.natCast_le_natCast.1 h))]
    rw [sum_congr rfl fun t ht => ite_eq_left (ENat.natCast_le_natCast.2 (mem_range.1 ht)),
      ENat.toENNReal_coe, sum_const, card_range, nsmul_eq_mul, mul_one]

theorem resamplings_eq_tsum (k : ℕ) (x : ℕ → Bool) :
    (resamplings φ k x : ℝ≥0∞) = ∑' t : ℕ, {x | Exhausts φ k (t + 1) x}.indicator 1 x := by
  rw [toENNReal_eq_tsum]
  refine tsum_congr fun t => ?_
  by_cases h : Exhausts φ k (t + 1) x
  · rw [ite_eq_left (le_resamplings_iff.2 h), Set.indicator_of_mem h, Pi.one_apply]
  · rw [ite_eq_right (fun h' => h (le_resamplings_iff.1 h')), Set.indicator_of_notMem h]

/-- The expected number of resamplings is the sum of the probabilities of making `t + 1`
resamplings. -/
theorem lintegral_resamplings_eq_tsum {k : ℕ} (hφ : φ.IsExactDistinct k) :
    ∫⁻ x, (resamplings φ k x : ℝ≥0∞) ∂coinFlips =
      ∑' t : ℕ, coinFlips {x | Exhausts φ k (t + 1) x} := by
  rw [lintegral_congr fun x => resamplings_eq_tsum k x,
    lintegral_tsum fun t => (measurable_one.indicator
      (measurableSet_exhausts hφ (t + 1))).aemeasurable]
  exact tsum_congr fun t => lintegral_indicator_one (measurableSet_exhausts hφ (t + 1))

/-- **Expected number of resamplings.** If every clause of an exact `k`-CNF shares a variable with
fewer than `2 ^ (k - 3)` other clauses, the run on fair coins makes at most `m + 2` resamplings in
expectation. -/
theorem lintegral_resamplings_le {k : ℕ} (hk : 3 ≤ k) (hφ : φ.IsExactDistinct k)
    (hdeg : ∀ i : Fin φ.length, degree φ i < 2 ^ (k - 3)) :
    ∫⁻ x, (resamplings φ k x : ℝ≥0∞) ∂coinFlips ≤ φ.length + 2 := by
  rw [lintegral_resamplings_eq_tsum hφ,
    ← Summable.sum_add_tsum_nat_add' (k := φ.length + 1) CompleteLattice.summable]
  have h1 : ∑ t ∈ range (φ.length + 1), coinFlips {x | Exhausts φ k (t + 1) x} ≤ φ.length + 1 :=
    calc _ ≤ ∑ _t ∈ range (φ.length + 1), (1 : ℝ≥0∞) := sum_le_sum fun _ _ => prob_le_one
      _ = φ.length + 1 := by simp only [sum_const, card_range, nsmul_eq_mul, mul_one,
          Nat.cast_add, Nat.cast_one]
  have h2 : ∑' t : ℕ, coinFlips {x | Exhausts φ k (t + (φ.length + 1) + 1) x} ≤ 1 := by
    calc _ ≤ ∑' t : ℕ, (2⁻¹ : ℝ≥0∞) ^ (t + 1) := by
          refine tsum_le_tsum fun t => ?_
          refine (coinFlips_exhausts_le hk hφ hdeg _).trans (le_of_eq ?_)
          rw [show t + (φ.length + 1) + 1 = (φ.length + 1) + (t + 1) by omega,
            pow_add (2⁻¹ : ℝ≥0∞) (φ.length + 1) (t + 1), ← mul_assoc, ← mul_pow,
            ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
      _ = 1 := by
          rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two,
            ENNReal.mul_inv_cancel (by simp) (by simp)]
  calc _ ≤ ((φ.length : ℝ≥0∞) + 1) + 1 := add_le_add h1 h2
    _ = φ.length + 2 := by rw [add_assoc, one_add_one_eq_two]

/-- **Termination.** If every clause of an exact `k`-CNF shares a variable with fewer than
`2 ^ (k - 3)` other clauses, the run on fair coins stops almost surely. -/
theorem ae_resamplings_ne_top {k : ℕ} (hk : 3 ≤ k) (hφ : φ.IsExactDistinct k)
    (hdeg : ∀ i : Fin φ.length, degree φ i < 2 ^ (k - 3)) :
    ∀ᵐ x ∂coinFlips, resamplings φ k x ≠ ⊤ := by
  have hsum : ∑' t : ℕ, coinFlips {x | Exhausts φ k (t + 1) x} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := (φ.length + 2 : ℝ≥0∞)) (by simp) ?_
    rw [← lintegral_resamplings_eq_tsum hφ]
    exact lintegral_resamplings_le hk hφ hdeg
  have htop : {x | resamplings φ k x = ⊤} ⊆ ⋂ t : ℕ, {x | Exhausts φ k (t + 1) x} :=
    fun x hx => Set.mem_iInter.2 fun t => le_resamplings_iff.1 (by
      rw [show resamplings φ k x = ⊤ from hx]
      exact le_top)
  rw [ae_iff]
  simp only [ne_eq, not_not]
  refine measure_mono_null htop (le_antisymm ?_ zero_le)
  refine ge_of_tendsto' (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum) fun t => ?_
  exact measure_mono (Set.iInter_subset _ t)

/-- **The algorithmic Local Lemma for `k`-SAT.** If every clause of an exact `k`-CNF shares a
variable with fewer than `2 ^ (k - 3)` other clauses, then almost surely the run on fair coins
stops after some number `R` of resamplings, and the run with any budget above `R` ends with a
satisfying assignment. -/
theorem ae_exists_eval_final {k : ℕ} (hk : 3 ≤ k) (hφ : φ.IsExactDistinct k)
    (hdeg : ∀ i : Fin φ.length, degree φ i < 2 ^ (k - 3)) :
    ∀ᵐ x ∂coinFlips, ∃ R : ℕ, resamplings φ k x = R ∧
      ∀ t, R < t → φ.eval (final φ k t x).assignment = true := by
  filter_upwards [ae_resamplings_ne_top hk hφ hdeg] with x hx
  obtain ⟨R, hR⟩ := ENat.ne_top_iff_exists.1 hx
  refine ⟨R, hR.symm, fun t ht => eval_final_of_not_exhausts (hφ.ne_nil (by omega)) fun h => ?_⟩
  have := ENat.natCast_le_natCast.1 ((le_resamplings_iff.2 h).trans hR.symm.le)
  omega

end Cslib.Logic.PL.Moser
