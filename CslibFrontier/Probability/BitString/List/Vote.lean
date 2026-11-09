/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Vote
public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal

/-!
# Majority prediction and its training test

The predictor uses only the observable vote list. Its nonpositive-margin training test also
receives the true label, and bounds prediction error including ties and the empty list.
The probability laws apply to arbitrary discrete sources, including infinite ambient types.

## Main results

* `Cslib.BitString.listStrictMajority_error_le`: margin-test failure bounds prediction error.
* `Cslib.BitString.map_listNonpositiveMargin_true`: the exact law of the executable test.

## References

[Holenstein, Claim 2.16][Holenstein2005]. Adapted from
Crypto/Computational/Pseudoentropy/Boosting/Vote.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.BitString

/-- The nonpositive-margin event bounds the majority predictor's error on any source. -/
theorem listStrictMajority_error_le {α : Type*} (source : PMF α)
    (votes : α → List Bool) (truth : α → Bool) :
    (source.toOuterMeasure {x | listStrictMajority (votes x) ≠ truth x}).toReal ≤
      (source.toOuterMeasure {x | listVoteMargin (votes x) (truth x) ≤ 0}).toReal := by
  apply Probability.PMF.toOuterMeasure_toReal_mono
  intro x hwrong
  by_contra hpositive
  exact hwrong (listStrictMajority_eq_of_pos (lt_of_not_ge hpositive))

/-- Sampling the training test accepts with exactly the nonpositive-margin probability. -/
theorem map_listNonpositiveMargin_true {α : Type*} (source : PMF α)
    (votes : α → List Bool) (truth : α → Bool) :
    (source.map (fun x => listNonpositiveMargin (votes x) (truth x))) true =
      source.toOuterMeasure {x | listVoteMargin (votes x) (truth x) ≤ 0} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, listNonpositiveMargin_eq_true,
    Set.mem_ofPred_eq]

end Cslib.BitString
