/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Greedy rounds and pessimistic estimators

The method of conditional expectations makes a sequence of binary choices one round at a time.
In each round it computes an estimate of the final cost after each of the two branches and takes
the branch with the smaller estimate (`Cslib.PessimisticEstimator.greedyStep`; ties go to
`true`) [Williamson and Shmoys, Section 5.2][WilliamsonShmoys2011]. If the smaller branch
estimate is always at most the current estimate, the estimate never increases
(`Cslib.PessimisticEstimator.estimate_greedyStep_le`). This is all that is used of the estimate:
it need not be an exact conditional expectation, only a *pessimistic estimator* [Raghavan1988]
[Alon and Spencer, Chapter 16][AlonSpencer2016]. The usual way to verify the premise is
averaging: if the two branch estimates sum to at most twice the current estimate, the smaller one
is at most the current estimate (`Cslib.PessimisticEstimator.greedy_spec_of_add_le`).

The premise is usually needed only on the states that the process can reach. The general
statement (`Cslib.PessimisticEstimator.greedy_spec`) assumes an invariant indexed by the rounds
still to come, which passes from a round to the rest along both branches, and asserts the premise
only where the invariant holds. It also returns the invariant for the final state, which is how
clients identify the final estimate with the cost of the constructed object.

Estimates take values in any linear order; the averaging form needs a linearly ordered
cancellative additive monoid, such as `ℕ`, `ℚ` or `ℝ`. Maximizing an estimate is minimizing its
negation.

## Main definitions

* `Cslib.PessimisticEstimator.greedyStep`: one round, choosing the branch with the smaller
  estimate.
* `Cslib.PessimisticEstimator.greedy`: the rounds of a list, in order.

## Main results

* `Cslib.PessimisticEstimator.estimate_greedyStep`: a round attains the smaller branch estimate.
* `Cslib.PessimisticEstimator.estimate_greedyStep_le`: a round does not increase the estimate if
  the smaller branch estimate is at most the current one.
* `Cslib.PessimisticEstimator.greedy_spec`: the method of conditional expectations with a
  pessimistic estimator, under an invariant indexed by the remaining rounds.
* `Cslib.PessimisticEstimator.estimate_greedy_le`: the special case of a fixed invariant.
* `Cslib.PessimisticEstimator.greedy_spec_of_add_le`: the averaging form of `greedy_spec`.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Chapter 16][AlonSpencer2016]
* [P. Raghavan, *Probabilistic construction of deterministic algorithms: approximating packing
  integer programs*][Raghavan1988]
* [D. P. Williamson, D. B. Shmoys, *The Design of Approximation Algorithms*,
  Section 5.2][WilliamsonShmoys2011]
-/

public section

namespace Cslib.PessimisticEstimator

variable {S R M : Type*}

/-- One greedy round `r` from state `s`: take the branch `true` unless the branch `false` has a
strictly smaller estimate. -/
@[expose] def greedyStep [LE M] [DecidableRel (α := M) (· ≤ ·)]
    (branch : R → Bool → S → S) (Φ : S → M) (s : S) (r : R) : S :=
  if Φ (branch r true s) ≤ Φ (branch r false s) then branch r true s else branch r false s

/-- The greedy rounds of a list, in order. -/
@[expose] def greedy [LE M] [DecidableRel (α := M) (· ≤ ·)]
    (branch : R → Bool → S → S) (Φ : S → M) (rounds : List R) (s : S) : S :=
  rounds.foldl (greedyStep branch Φ) s

section Order

variable [LinearOrder M] (branch : R → Bool → S → S) (Φ : S → M)

/-- A greedy round takes one of the two branches. -/
theorem greedyStep_eq_or (s : S) (r : R) :
    greedyStep branch Φ s r = branch r true s ∨ greedyStep branch Φ s r = branch r false s := by
  unfold greedyStep
  split
  · exact .inl rfl
  · exact .inr rfl

/-- A greedy round attains the smaller of the two branch estimates. -/
theorem estimate_greedyStep (s : S) (r : R) :
    Φ (greedyStep branch Φ s r) = min (Φ (branch r true s)) (Φ (branch r false s)) := by
  unfold greedyStep
  split
  · exact (min_eq_left ‹_›).symm
  · exact (min_eq_right (le_of_not_ge ‹_›)).symm

/-- A greedy round whose smaller branch estimate is at most the current estimate does not
increase the estimate. -/
theorem estimate_greedyStep_le {s : S} {r : R}
    (h : min (Φ (branch r true s)) (Φ (branch r false s)) ≤ Φ s) :
    Φ (greedyStep branch Φ s r) ≤ Φ s :=
  (estimate_greedyStep branch Φ s r).trans_le h

/-- **The method of conditional expectations, with a pessimistic estimator**. Suppose an
invariant `Inv`, indexed by the rounds still to come, holds initially and passes from each round
to the remaining ones along both branches, and that wherever it holds the smaller of the two
branch estimates of the next round is at most the current estimate. Then the greedy rounds end in
a state satisfying the invariant for no remaining rounds, with an estimate at most the initial
one. -/
theorem greedy_spec (Inv : List R → S → Prop)
    (hbranch : ∀ r rs s b, Inv (r :: rs) s → Inv rs (branch r b s))
    (hmin : ∀ r rs s, Inv (r :: rs) s → min (Φ (branch r true s)) (Φ (branch r false s)) ≤ Φ s) :
    ∀ (rounds : List R) (s : S), Inv rounds s →
      Inv [] (greedy branch Φ rounds s) ∧ Φ (greedy branch Φ rounds s) ≤ Φ s
  | [], s, hs => ⟨hs, le_rfl⟩
  | r :: rs, s, hs => by
    have hInv : Inv rs (greedyStep branch Φ s r) := by
      rcases greedyStep_eq_or branch Φ s r with h | h <;> rw [h] <;> exact hbranch _ _ _ _ hs
    obtain ⟨hend, hle⟩ := greedy_spec Inv hbranch hmin rs _ hInv
    exact ⟨hend, hle.trans (estimate_greedyStep_le branch Φ (hmin r rs s hs))⟩

/-- `greedy_spec` for an invariant that does not depend on the remaining rounds. -/
theorem estimate_greedy_le (Inv : S → Prop)
    (hbranch : ∀ r s b, Inv s → Inv (branch r b s))
    (hmin : ∀ r s, Inv s → min (Φ (branch r true s)) (Φ (branch r false s)) ≤ Φ s)
    (rounds : List R) {s : S} (hs : Inv s) :
    Φ (greedy branch Φ rounds s) ≤ Φ s :=
  (greedy_spec branch Φ (fun _ => Inv) (fun r _ s b => hbranch r s b) (fun r _ s => hmin r s)
    rounds s hs).2

section Averaging

variable [AddCommMonoid M] [IsOrderedCancelAddMonoid M]

/-- **Averaging**: `greedy_spec` when the two branch estimates sum to at most twice the current
estimate, as when the estimate is a conditional expectation over a fair coin. -/
theorem greedy_spec_of_add_le (Inv : List R → S → Prop)
    (hbranch : ∀ r rs s b, Inv (r :: rs) s → Inv rs (branch r b s))
    (havg : ∀ r rs s, Inv (r :: rs) s →
      Φ (branch r true s) + Φ (branch r false s) ≤ Φ s + Φ s)
    (rounds : List R) (s : S) (hs : Inv rounds s) :
    Inv [] (greedy branch Φ rounds s) ∧ Φ (greedy branch Φ rounds s) ≤ Φ s :=
  greedy_spec branch Φ Inv hbranch
    (fun r rs s hs => min_le_of_add_le_two_nsmul ((havg r rs s hs).trans_eq (two_nsmul _).symm))
    rounds s hs

end Averaging

end Order

end Cslib.PessimisticEstimator
