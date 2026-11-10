/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.PolynomialAtomRows.RootError
public import CslibFrontier.Computability.LogSpaceDerandomization.HeavyCount
public import CslibFrontier.Computability.LogSpaceDerandomization.RootMetric
public import CslibFrontier.Computability.LogSpaceDerandomization.RowCompression.FalseOverflow
import CslibFrontier.Computability.LogSpaceDerandomization.RowCompression.FalseOverflowNorm

/-!
# Actual polynomial row errors on false first overflows

The computed and true polynomial row outputs are in `[0,1]`, and each has fewer than `K`
retained nonzero entries. Their fourth-root discrepancy therefore has summed fourth power
at most `2 * K`, independently of the row width, default, and later compression states.
At a false first overflow, the existing actual-prefix charge pays for this bounded error.

The resulting normalized bound uses the final state of the real compression recursion and
the raw prefix at `j + 1`. The environment may jointly determine the increments, initial
states, true rows, retained endpoints, and first overflow. No independence is assumed.

This is the bounded-output integration of (8.12) in the proof of
[OpenAI2026LogSpace, Section 8.4, Proposition 8.5], on the fourth-moment route of issue #1721.
It does not supply prefix mean/noise budgets, sum their geometric costs, prove post-overflow
relative stability, or assert the complete integrated compression estimate.

## Main results

* `Cslib.PolynomialAtomRow.rowNormPow_falseFirstOverflow_le`: the normalized false-overflow
  output charge at a specified group.
* `Cslib.PolynomialAtomRow.rowNormPow_falseFirstOverflowBefore_le`: the finite union over
  possible first-overflow groups, with no additional factor from their number.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, equations (8.12) on p. 48 and (8.16) on p. 49 (source labels
  `buf-false-charge` and `buf-false-sum`)
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.PolynomialAtomRow

open Finset RowCompression Probability
open scoped BigOperators

variable {Ω V : Type*} [Fintype Ω] [Fintype V] (kind : PolynomialAtomRow)

open Classical in
/-- The final actual polynomial outputs on a specified false-first-overflow event are paid
for by the raw-prefix moment at `j + 1`. Every random quantity may share the environment. -/
theorem rowNormPow_falseFirstOverflow_le {θ η N u : ℝ} (hθ : 0 < θ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (n : ℕ → ℕ) (K : ℕ) (hK : 0 < K) (m j : ℕ) (hj : j < m) (hn : 0 < n j)
    (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (a : Ω → V → State V)
    (truth : Ω → V → V → Fin 2 → ℝ)
    (ha : ∀ σ x, X σ x → (a σ x).defaultValue = 0)
    (hfirst : ∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0)
    (hsecond : ∀ σ x y, X σ x → Y σ y →
      truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 = 0) :
    let S := fun σ => ({y | Y σ y} : Finset V)
    let b := fun σ x => iterate (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) m
    let F := fun σ x => IsFirstOverflow (S σ) n (fun _ => K)
      (dyadicFloor η m) (Δ σ x) (a σ x) j ∧
        ¬ heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ
    rowNormPow 4 N u X Y (fun σ x y =>
      if F σ x then kind.stateRootError θ (S σ) K (b σ x) ⟨0, truth σ x⟩ y else 0) ≤
      (64 * (K : ℝ) / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
        rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
          (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) := by
  simpa only [mul_one] using rowNormPow_falseFirstOverflow_le_of_bound hη hη1 hNu X Y n K m j
    hj hn Δ a truth
    (fun σ x y => kind.stateRootError θ ({y | Y σ y} : Finset V) K
      (iterate ({y | Y σ y} : Finset V) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) m)
      ⟨0, truth σ x⟩ y)
    zero_le_one (fun σ x _ => (kind.sum_stateRootError_pow_four_le hθ _ hK _ _).trans_eq
      (mul_one _).symm) ha hfirst hsecond

open Classical in
/-- **The false-type contribution to actual final output error.** Taking the union of the
possible false first overflows gives the sum of their raw-prefix charges. Both sides use the
same `RootMetric` normalization, and no independence or final-output error premise is required. -/
theorem rowNormPow_falseFirstOverflowBefore_le {θ η N u : ℝ} (hθ : 0 < θ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (n : ℕ → ℕ) (K : ℕ) (hK : 0 < K) (m : ℕ) (hn : ∀ j < m, 0 < n j)
    (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (a : Ω → V → State V)
    (truth : Ω → V → V → Fin 2 → ℝ)
    (ha : ∀ σ x, X σ x → (a σ x).defaultValue = 0)
    (hfirst : ∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0)
    (hsecond : ∀ j < m, ∀ σ x y, X σ x → Y σ y →
      truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 = 0) :
    let S := fun σ => ({y | Y σ y} : Finset V)
    let b := fun σ x => iterate (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) m
    let F := fun j σ x => IsFirstOverflow (S σ) n (fun _ => K)
      (dyadicFloor η m) (Δ σ x) (a σ x) j ∧
        ¬ heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ
    rowNormPow 4 N u X Y (fun σ x y =>
      if ∃ j < m, F j σ x then kind.stateRootError θ (S σ) K (b σ x) ⟨0, truth σ x⟩ y else 0) ≤
      ∑ j ∈ range m, (64 * (K : ℝ) / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
        rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
          (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) := by
  classical
  exact (rowNormPow_ite_exists_le_sum hNu X Y m _ _).trans <| sum_le_sum fun j hj =>
    kind.rowNormPow_falseFirstOverflow_le hθ hη hη1 hNu X Y n K hK m j
      (mem_range.mp hj) (hn j (mem_range.mp hj)) Δ a truth ha hfirst
      (hsecond j (mem_range.mp hj))

end Cslib.PolynomialAtomRow
