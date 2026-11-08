/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.StableMatching.Incomplete.Complete
import CslibFrontier.Algorithms.Lean.StableMatching.Incomplete.RuralHospitals
import CslibFrontier.Algorithms.Lean.StableMatching.Incentives
import Mathlib.Data.Fin.VecNotation

/-!
# Stable matching with incomplete lists: checked instances

Kernel-checked (`decide`, no `native_decide`) examples for markets with incomplete preference
lists:

1. A market with three proposers and two receivers that has two stable matchings. Proposer- and
   receiver-proposing deferred acceptance differ, but both leave proposer `2` unmatched. By the
   rural hospitals theorem, proposer `2` is unmatched in every stable matching.
2. A two-by-two market in which receiver `1` lists proposer `1`, yet both stay unmatched in every
   stable matching, because proposer `1` finds receiver `1` unacceptable. A matching that pairs
   them is not individually rational.
3. A market in which nobody finds anybody acceptable: the empty matching is the only stable one.
4. Complete lists as a special case: on Roth's three-by-three market, deferred acceptance for
   incomplete lists agrees with the complete-list implementation.
-/

namespace CslibFrontierTests.StableMatchingIncomplete

open Cslib.Algorithms.Lean.StableMatching

/-! ### 1. Two stable matchings, one proposer always unmatched -/

/-- Proposers `0` and `1` both find receivers `0` and `1` acceptable, in opposite orders;
proposer `2` finds only receiver `0` acceptable, and receiver `0` ranks it last. -/
def twoStable : IncompleteInstance 3 2 where
  propPref := ![[0, 1], [1, 0], [0]]
  recvPref := ![[1, 0, 2], [0, 1]]

example : (fun p => twoStable.deferredAcceptance p) = ![some 0, some 1, none] := by decide

example : (fun p => twoStable.receiverDeferredAcceptance p) = ![some 1, some 0, none] := by
  decide

/-- The two deferred-acceptance matchings are different stable matchings. -/
example : twoStable.deferredAcceptance ≠ twoStable.receiverDeferredAcceptance := by
  intro h
  have := congrArg (fun μ : PartialMatching 3 2 => μ 0) h
  revert this
  decide

example : PartialMatching.matchedProposers twoStable.deferredAcceptance = {0, 1} ∧
    PartialMatching.matchedProposers twoStable.receiverDeferredAcceptance = {0, 1} ∧
    PartialMatching.matchedReceivers twoStable.deferredAcceptance = Finset.univ := by
  decide

/-- The empty matching is individually rational but blocked by `(0, 0)`. -/
example : twoStable.IsIndividuallyRational ⊥ ∧ twoStable.IsBlockingPair ⊥ 0 0 ∧
    ¬ twoStable.IsStable ⊥ := by
  decide

/-- Proposer `2` is unmatched in every stable matching of `twoStable`. -/
example (ν : PartialMatching 3 2) (hν : twoStable.IsStable ν) : ν 2 = none := by
  have h := (twoStable.unmatched_eq_of_isStable hν twoStable.isStable_deferredAcceptance).1
  have hda : twoStable.deferredAcceptance 2 = none := by decide
  change (2 : Fin 3) ∈ {p | ν p = none}
  rw [h]
  exact hda

/-! ### 2. An unmatched receiver that lists an unmatched proposer -/

/-- Both proposers find only receiver `0` acceptable; both receivers find both proposers
acceptable and prefer proposer `0`. -/
def rural : IncompleteInstance 2 2 where
  propPref := ![[0], [0]]
  recvPref := ![[0, 1], [0, 1]]

example : (fun p => rural.deferredAcceptance p) = ![some 0, none] ∧
    (fun p => rural.receiverDeferredAcceptance p) = ![some 0, none] := by
  decide

/-- Pairing proposer `1` with receiver `1` is not individually rational, so this perfect matching
is not stable. -/
example : ¬ rural.IsIndividuallyRational (PartialMatching.ofInjOn ![some 0, some 1] (by decide))
    ∧ ¬ rural.IsStable (PartialMatching.ofInjOn ![some 0, some 1] (by decide)) := by
  decide

/-- Proposer `1` and receiver `1` are unmatched in every stable matching of `rural`. -/
example (ν : PartialMatching 2 2) (hν : rural.IsStable ν) : ν 1 = none ∧ ν.symm 1 = none := by
  have h := rural.unmatched_eq_of_isStable hν rural.isStable_deferredAcceptance
  have hp : rural.deferredAcceptance 1 = none := by decide
  have hr : rural.deferredAcceptance.symm 1 = none := by decide
  constructor
  · change (1 : Fin 2) ∈ {p | ν p = none}
    rw [h.1]
    exact hp
  · change (1 : Fin 2) ∈ {r | ν.symm r = none}
    rw [h.2]
    exact hr

/-! ### 3. Nobody is acceptable -/

/-- A market in which every list is empty. -/
def lonely : IncompleteInstance 2 1 where
  propPref := ![[], []]
  recvPref := ![[]]

example : (fun p => lonely.deferredAcceptance p) = fun _ => none := by decide

/-- The empty matching is the only stable matching of `lonely`. -/
example (ν : PartialMatching 2 1) (hν : lonely.IsStable ν) : ν = ⊥ := by
  refine PEquiv.ext fun p => ?_
  cases hp : ν p with
  | none => rfl
  | some r =>
    have h : ∀ (p : Fin 2) (r : Fin 1), r ∉ lonely.propPref p := by decide
    exact absurd (hν.1 p r hp).1 (h p r)

/-! ### 4. Complete lists -/

/-- The library's witness market for Roth's impossibility theorem. -/
abbrev roth : Instance 3 := MatchingMechanism.rothInstance

example : (fun p => roth.toIncompleteInstance.deferredAcceptance p) =
    fun p => some (roth.deferredAcceptance p) := by
  decide

example : roth.toIncompleteInstance.receiverDeferredAcceptance =
    roth.receiverDeferredAcceptance.toPEquiv :=
  roth.receiverDeferredAcceptance_toIncompleteInstance

end CslibFrontierTests.StableMatchingIncomplete
