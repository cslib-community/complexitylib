/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Signed margins of vote lists

The signed margin is the number of correct votes minus the number of incorrect votes.
A positive margin ensures that the existing strict-majority operation returns the supplied
label, including a precise account of empty lists and ties.

## Main definitions

* `Cslib.BitString.listVoteMargin`: the real-valued signed margin for analysis.
* `Cslib.BitString.signedVote`: one prediction's contribution to the margin.

## Main results

* `Cslib.BitString.listVoteMargin_cons`: the change produced by one prediction.
* `Cslib.BitString.listStrictMajority_eq_of_pos`: positive margin guarantees the majority label.
* `Cslib.BitString.listNonpositiveMargin_eq_true`: the count test agrees with the real margin.

## References

[Holenstein, Claim 2.16][Holenstein2005]. Adapted from
Crypto/Computational/Pseudoentropy/Boosting/Vote.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing the shared strict-majority operation.
-/

@[expose] public section

namespace Cslib.BitString

/-- Correct votes minus incorrect votes, represented as a real number for the analysis. -/
def listVoteMargin (votes : List Bool) (truth : Bool) : ℝ :=
  2 * (votes.count truth : ℝ) - votes.length

/-- A correct prediction contributes one to the margin; an incorrect prediction subtracts one. -/
def signedVote (vote truth : Bool) : ℝ := if vote = truth then 1 else -1

/-- Each vote contributes `±1` to the margin: `|signedVote vote truth| = 1`. -/
@[simp] theorem abs_signedVote (vote truth : Bool) : |signedVote vote truth| = 1 := by
  unfold signedVote
  split <;> norm_num

/-- The empty vote list has margin zero. -/
@[simp] theorem listVoteMargin_nil (truth : Bool) : listVoteMargin [] truth = 0 := by
  simp [listVoteMargin]

/-- Adding a predictor updates the margin by its signed prediction. -/
theorem listVoteMargin_cons (vote : Bool) (votes : List Bool) (truth : Bool) :
    listVoteMargin (vote :: votes) truth = listVoteMargin votes truth + signedVote vote truth := by
  by_cases h : vote = truth <;>
    simp only [listVoteMargin, signedVote, List.count_cons, List.length_cons, beq_iff_eq, h,
      ite_true, ite_false, Nat.cast_add, Nat.cast_one] <;> ring

/-- The training test agrees exactly with the real margin event used by the potential proof. -/
theorem listNonpositiveMargin_eq_true (votes : List Bool) (truth : Bool) :
    listNonpositiveMargin votes truth = true ↔ listVoteMargin votes truth ≤ 0 := by
  simp only [listNonpositiveMargin, decide_eq_true_eq, listVoteMargin, sub_nonpos]
  norm_cast

private theorem count_false_add_true (votes : List Bool) :
    votes.count false + votes.count true = votes.length := by
  simpa [List.count_eq_countP] using
    (votes.length_eq_countP_add_countP (· == false)).symm

/-- Reversing the label negates the signed margin of the same observable vote word. -/
@[simp] theorem listVoteMargin_not (votes : List Bool) (truth : Bool) :
    listVoteMargin votes (!truth) = -listVoteMargin votes truth := by
  have htotal : (votes.count false : ℝ) + votes.count true = votes.length := by
    exact_mod_cast count_false_add_true votes
  cases truth <;> simp only [Bool.not_true, Bool.not_false, listVoteMargin] <;> linarith

/-- The magnitude of the signed margin is at most the number of votes. -/
theorem abs_listVoteMargin_le (votes : List Bool) (truth : Bool) :
    |listVoteMargin votes truth| ≤ votes.length := by
  have hcount : (votes.count truth : ℝ) ≤ votes.length := by
    exact_mod_cast (show votes.count truth ≤ votes.length from List.count_le_length)
  have hnonneg : (0 : ℝ) ≤ votes.count truth := by positivity
  rw [abs_le]
  constructor <;> dsimp only [listVoteMargin] <;> linarith

/-- A positive signed margin guarantees that the executable majority predicts the label. -/
theorem listStrictMajority_eq_of_pos {votes : List Bool} {truth : Bool}
    (hmargin : 0 < listVoteMargin votes truth) :
    listStrictMajority votes = truth := by
  have hcount : votes.length < 2 * votes.count truth := by
    have h : (votes.length : ℝ) < 2 * (votes.count truth : ℝ) := by
      dsimp only [listVoteMargin] at hmargin
      linarith
    exact_mod_cast h
  have htotal := count_false_add_true votes
  cases truth <;>
    simp only [listStrictMajority_eq_decide_count, decide_eq_false_iff_not, decide_eq_true_eq] <;>
    lia

end Cslib.BitString
