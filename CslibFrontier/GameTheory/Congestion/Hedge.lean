/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Congestion.Affine
public import CslibFrontier.GameTheory.Strategic.Hedge
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Hedge dynamics in affine congestion games

Atomic congestion games with affine latencies are `(5/3, 1/3)`-smooth
(`CongestionGame.isSmooth_of_hasAffineLatencies`). So the price-of-anarchy bound for Hedge dynamics
in smooth games (`CostGame.IsSmooth.timeAverage_hedgeDist_socialCost_le`) specializes as follows.
If every player runs Hedge for `T` rounds, the expected social cost under the time average of the
outcome distributions is at most `5/2 socialCost s' + 3 M ∑ i, √(ln |S i| / T)` for every profile
`s'`, where `M` bounds the costs. This combines [Roughgarden2013CS364A], Lecture 17,
Corollary 3.3 with [Roughgarden2015], Example 2.5.

## Main results

* `Cslib.GameTheory.CongestionGame.timeAverage_hedgeDist_socialCost_le`: the `5/2` bound for Hedge
  dynamics in affine congestion games.

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [T. Roughgarden, *Intrinsic robustness of the price of anarchy*][Roughgarden2015]
-/

public section

namespace Cslib.GameTheory.CongestionGame

variable {ι : Type*} {S : ι → Type*} {E : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq E]
  [Finite E] [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)] (C : CongestionGame ι S E)

/-- **The price of anarchy of Hedge dynamics in affine congestion games**: if `C` has affine
latencies, its costs are bounded by `M > 0` and `ln |S i| ≤ T` for every player `i`, then the
expected social cost under the time average of the first `T > 0` outcome distributions of Hedge
dynamics is at most `5/2 socialCost s' + 3 M ∑ i, √(ln |S i| / T)` for every profile `s'`. -/
theorem timeAverage_hedgeDist_socialCost_le (h : C.HasAffineLatencies) {M : ℝ} (hM : 0 < M)
    (hc : ∀ i s, |C.toCostGame.cost i s| ≤ M) {T : ℕ} (hT0 : 0 < T)
    (hT : ∀ i, Real.log (Fintype.card (S i)) ≤ T) (s' : ∀ i, S i) :
    (timeAverage (C.toCostGame.hedgeDist M T) T hT0).weights.sum
        (fun s w => w * C.toCostGame.socialCost s)
      ≤ 5 / 2 * C.toCostGame.socialCost s'
        + 3 * M * ∑ i, √(Real.log (Fintype.card (S i)) / T) := by
  have h' := (C.isSmooth_of_hasAffineLatencies h).timeAverage_hedgeDist_socialCost_le
    (by norm_num) hM hc hT0 hT s'
  refine h'.trans (le_of_eq ?_)
  ring

end Cslib.GameTheory.CongestionGame
