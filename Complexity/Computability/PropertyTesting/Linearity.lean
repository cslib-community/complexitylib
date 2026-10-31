/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.AssignmentTester
public import Complexity.Computability.PCP.LocalTest.DecisionTree
import Mathlib.Tactic.Linarith

/-!
# Query bounds and amplification for linearity testing

The existing BLR local test (`PCP.HadamardTester.blrTest`) becomes a decision-tree tester through
`PCP.LocalTest.decisionTree`. Repeating it `k` times reads at most `3 * k` table entries, accepts
every parity with probability one, and accepts a function at relative Hamming distance at least
`ε` from every parity with probability at most `(1 - ε) ^ k`. The random strings are `k` pairs of
independent uniform points of the cube; the distance is under the uniform distribution.

The distance guarantee is a consequence of the existing BLR soundness theorem
[O'Donnell, Theorem 1.30 and Example 7.3][ODonnell2014]. The repetition and execution bridges are
elementary constructions. These are query bounds, with no machine running-time claim.

## Main results

* `Cslib.BitString.depth_decisionTree_repeatAll_blrTest_le`: the `3 * k` worst-case query bound.
* `Cslib.BitString.acceptProb_repeatAll_blrTest_parityOn`: one-sided completeness.
* `Cslib.BitString.acceptProb_repeatAll_blrTest_le`: soundness under an explicit distance promise.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open PCP HadamardTester

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance (r : (ι → Bool) × (ι → Bool)) (a : Fin 3 → Bool) :
    Decidable ((blrTest ι).Accepts r a) :=
  inferInstanceAs (Decidable ((a 0 ^^ a 1) = a 2))

omit [DecidableEq ι] in
/-- Every run of `k` BLR trials reads at most `3 * k` table entries, including repetitions. -/
theorem depth_decisionTree_repeatAll_blrTest_le (k : ℕ)
    (r : Fin k → (ι → Bool) × (ι → Bool)) :
    (((blrTest ι).repeatAll k).decisionTree r).depth ≤ 3 * k := by
  simpa only [FinEnum.card_fin, Nat.mul_comm] using
    (blrTest ι).depth_decisionTree_repeatAll_le k r

/-- Parities are accepted with probability one by any number of independent BLR trials. -/
theorem acceptProb_repeatAll_blrTest_parityOn (k : ℕ) (S : Finset ι) :
    ((blrTest ι).repeatAll k).acceptProb (parityOn S) = 1 := by
  rw [LocalTest.acceptProb_repeatAll, acceptProb_blrTest, blrAcceptance_parityOn, one_pow]

/-- If the relative Hamming distance from `f` to every parity is at least `ε`, then `k`
independent BLR trials accept with probability at most `(1 - ε) ^ k`. In particular, this
gives one-sided property testing at every distance threshold `0 ≤ ε ≤ 1`. -/
theorem acceptProb_repeatAll_blrTest_le {f : (ι → Bool) → Bool} {ε : ℝ}
    (hfar : ∀ S, ε ≤ (hammingDist f (parityOn S) : ℝ) / 2 ^ Fintype.card ι) (k : ℕ) :
    ((blrTest ι).repeatAll k).acceptProb f ≤ (1 - ε) ^ k := by
  obtain ⟨S, hS⟩ := exists_hammingDist_parityOn_le_of_le_blrAcceptance
    (f := f) (ε := 1 - blrAcceptance f) (by linarith)
  have ha : blrAcceptance f ≤ 1 - ε := by linarith [hfar S]
  have hnonneg : 0 ≤ blrAcceptance f := by
    rw [← acceptProb_blrTest]
    exact (blrTest ι).acceptProb_nonneg f
  rw [LocalTest.acceptProb_repeatAll, acceptProb_blrTest]
  exact pow_le_pow_left₀ hnonneg ha k

end Cslib.BitString
