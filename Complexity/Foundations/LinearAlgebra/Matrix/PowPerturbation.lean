/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
import Complexity.Foundations.Analysis.Normed.Ring.PowSub
import Mathlib.Analysis.Matrix.Normed

/-!
# Perturbation of powers of substochastic matrices

These are the row-sum (matrix `∞`-norm) estimates behind the Saks–Zhou iteration
[ChattopadhyayLiao2020, Appendix A.1]. They are stated with explicit row sums, so that no scoped
norm instance appears in their statements: if every row of `A` and of `B` has absolute sum at
most `1`, and every row of `A - B` has absolute sum at most `δ`, then every row of `A ^ m - B ^ m`
has absolute sum at most `m δ`. Nonnegative matrices whose rows sum to at most `1` keep this
property under powers.

## Main results

* `Matrix.sum_abs_pow_sub_pow_le`: `∑ⱼ |(A ^ m - B ^ m)ᵢⱼ| ≤ m δ`.
* `Matrix.sum_pow_apply_le_one`: powers of substochastic matrices are substochastic.

## References

* [E. Chattopadhyay and J.-J. Liao, *Optimal Error Pseudodistributions for Read-Once Branching
  Programs*][ChattopadhyayLiao2020], Appendix A.1, the matrix-norm step in the proof of
  Lemma A.4.
-/

public section

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.Operator in
private theorem linfty_opNorm_le_iff {A : Matrix ι ι ℝ} {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖A‖ ≤ δ ↔ ∀ i, ∑ j, |A i j| ≤ δ := by
  rw [linfty_opNorm_def]
  lift δ to NNReal using hδ
  rw [NNReal.coe_le_coe, Finset.sup_le_iff]
  refine forall_congr' fun i => ?_
  simp only [Finset.mem_univ, true_implies, ← NNReal.coe_le_coe, NNReal.coe_sum, coe_nnnorm,
    Real.norm_eq_abs]

open scoped Matrix.Norms.Operator in
/-- **Perturbation of powers.** If every row of `A` and of `B` has absolute sum at most `1` and
every row of `A - B` has absolute sum at most `δ`, then every row of `A ^ m - B ^ m` has absolute
sum at most `m δ`. This is `norm_pow_sub_pow_le_of_norm_le_one` for the matrix `∞`-norm. -/
theorem sum_abs_pow_sub_pow_le {A B : Matrix ι ι ℝ} {δ : ℝ}
    (hA : ∀ i, ∑ j, |A i j| ≤ 1) (hB : ∀ i, ∑ j, |B i j| ≤ 1)
    (hAB : ∀ i, ∑ j, |A i j - B i j| ≤ δ) (m : ℕ) (i : ι) :
    ∑ j, |(A ^ m) i j - (B ^ m) i j| ≤ m * δ := by
  have hδ : 0 ≤ δ := (Finset.sum_nonneg fun j _ => abs_nonneg _).trans (hAB i)
  have hA' : ‖A‖ ≤ 1 := (linfty_opNorm_le_iff zero_le_one).2 hA
  have hB' : ‖B‖ ≤ 1 := (linfty_opNorm_le_iff zero_le_one).2 hB
  have hAB' : ‖A - B‖ ≤ δ := (linfty_opNorm_le_iff hδ).2 hAB
  have h := (norm_pow_sub_pow_le_of_norm_le_one hA' hB' m).trans
    (mul_le_mul_of_nonneg_left hAB' (Nat.cast_nonneg m))
  exact (linfty_opNorm_le_iff (by positivity)).1 h i

/-- Powers of a nonnegative matrix whose rows sum to at most `1` have rows summing to at most
`1`. -/
theorem sum_pow_apply_le_one {A : Matrix ι ι ℝ} (h0 : ∀ i j, 0 ≤ A i j)
    (h1 : ∀ i, ∑ j, A i j ≤ 1) (m : ℕ) (i : ι) : ∑ j, (A ^ m) i j ≤ 1 := by
  induction m generalizing i with
  | zero =>
    simp [Matrix.one_apply]
  | succ m ih =>
    calc ∑ j, (A ^ (m + 1)) i j = ∑ k, (A ^ m) i k * ∑ j, A k j := by
          simp only [_root_.pow_succ, Matrix.mul_apply, Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ k, (A ^ m) i k * 1 := by
          gcongr with k
          · exact pow_apply_nonneg h0 m i k
          · exact h1 k
      _ ≤ 1 := by simpa using ih i

end Matrix
