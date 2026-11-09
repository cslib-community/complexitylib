/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.StableMatching.Lattice
import CslibFrontier.Algorithms.Lean.StableMatching.Incentives
import Mathlib.Data.Fin.VecNotation

/-!
# Stable matching: checked instances

Kernel-checked (`decide`, no `native_decide`) examples for deferred acceptance:

1. Boundary cases `n = 0` and `n = 1`, where the proposal bound `n ^ 2 - n + 1` is respectively
   not attained and attained.
2. Roth's three-by-three market, which has exactly two stable matchings: proposer-proposing and
   receiver-proposing deferred acceptance differ, the identity matching is blocked, and the lattice
   of stable matchings has `⊥ < ⊤`; a market with three stable matchings exercises `propJoin` and
   `propMeet`.
3. A three-by-three market attaining the proposal bound `3 ^ 2 - 3 + 1 = 7`.
4. Incentives: in Roth's market a receiver gains by misreporting under proposer-proposing deferred
   acceptance and a proposer gains under receiver-proposing deferred acceptance, so neither
   mechanism is strategy-proof for the other side; no proposer gains under proposer-proposing
   deferred acceptance.
-/

namespace CslibFrontierTests.StableMatching

open Cslib.Algorithms.Lean.StableMatching

/-- A preference list over `Fin 3`, given as the vector of agents from most to least preferred. -/
abbrev pref (v : Fin 3 → Fin 3) (h : Function.Injective v := by decide) : Equiv.Perm (Fin 3) :=
  permOfInjective v h

/-! ### 1. Boundary cases -/

/-- The empty market. -/
def empty : Instance 0 := ⟨Fin.elim0, Fin.elim0⟩

example : empty.IsStable empty.deferredAcceptance ∧ empty.proposals = 0 := by decide

/-- The market with one agent on each side. -/
def single : Instance 1 := ⟨fun _ => 1, fun _ => 1⟩

example : single.deferredAcceptance = 1 ∧ single.proposals = 1 ^ 2 - 1 + 1 := by decide

/-! ### 2. Roth's market: two stable matchings -/

/-- The library's witness market for Roth's impossibility theorem. -/
abbrev roth : Instance 3 := MatchingMechanism.rothInstance

/-- The proposer-optimal stable matching of `roth`. -/
abbrev μa : Matching 3 := MatchingMechanism.rothProposerOptimal

/-- The receiver-optimal stable matching of `roth`. -/
abbrev μb : Matching 3 := MatchingMechanism.rothReceiverOptimal

example : roth.propPref 1 = pref ![0, 2, 1] ∧ roth.recvPref 2 = pref ![1, 2, 0] ∧
    μa = pref ![1, 0, 2] ∧ μb = pref ![1, 2, 0] := by decide

example : roth.deferredAcceptance = μa := by decide
example : roth.receiverDeferredAcceptance = μb := by decide
example : roth.IsStable μa ∧ roth.IsStable μb := by decide
example : ∀ μ : Matching 3, roth.IsStable μ → μ = μa ∨ μ = μb := by decide
example : ¬ roth.IsStable 1 ∧ roth.IsBlockingPair 1 1 0 := by decide
example : Fintype.card roth.Stable = 2 := by decide

/-- The join and meet of two stable matchings, computed on a market with a third stable matching
strictly between the proposer-optimal and receiver-optimal ones. -/
def latin : Instance 3 where
  propPref := ![pref ![0, 1, 2], pref ![1, 2, 0], pref ![2, 0, 1]]
  recvPref := ![pref ![1, 2, 0], pref ![2, 0, 1], pref ![0, 1, 2]]

example : latin.IsStable (pref ![0, 1, 2]) ∧ latin.IsStable (pref ![1, 2, 0]) ∧
    latin.IsStable (pref ![2, 0, 1]) ∧ Fintype.card latin.Stable = 3 := by decide

example : latin.deferredAcceptance = pref ![0, 1, 2] ∧
    latin.receiverDeferredAcceptance = pref ![2, 0, 1] := by decide

/-- Joining the middle and bottom stable matchings of `latin` gives the middle one, and meeting them
gives the bottom one. -/
example :
    latin.propJoin (μ := pref ![1, 2, 0]) (ν := pref ![2, 0, 1]) (by decide) (by decide) =
        pref ![1, 2, 0] ∧
      latin.propMeet (μ := pref ![1, 2, 0]) (ν := pref ![2, 0, 1]) (by decide) (by decide) =
        pref ![2, 0, 1] := by
  decide
example : roth.proposals = 5 := by decide

/-- The two stable matchings of `roth` are distinct, so its lattice of stable matchings is not
trivial. -/
example : (⊥ : roth.Stable) < ⊤ := by
  refine lt_of_le_of_ne bot_le fun h => ?_
  have h' := congrArg Subtype.val h
  rw [Instance.Stable.coe_top, Instance.Stable.coe_bot] at h'
  revert h'
  decide

/-! ### 3. The proposal bound is attained -/

/-- A three-by-three market in which deferred acceptance makes `3 ^ 2 - 3 + 1` proposals. -/
def tight : Instance 3 where
  propPref := ![pref ![0, 1, 2], pref ![0, 1, 2], pref ![1, 0, 2]]
  recvPref := ![pref ![2, 0, 1], pref ![0, 1, 2], pref ![0, 1, 2]]

example : tight.proposals = 3 ^ 2 - 3 + 1 := by decide

example : tight.proposals = ∑ p, ((tight.propRank p (tight.deferredAcceptance p)).val + 1) :=
  tight.proposals_eq

/-! ### 4. Incentives -/

/-- Under proposer-proposing deferred acceptance, receiver `0` of `roth` gains by reporting
`2, 0, 1`. -/
example : ¬ (MatchingMechanism.deferredAcceptance (n := 3)).IsReceiverStrategyProof := by
  intro h
  have := h roth 0 (pref ![2, 0, 1])
  revert this
  decide

/-- Under receiver-proposing deferred acceptance, proposer `1` of `roth` gains by reporting
`0, 1, 2`. -/
example : ¬ (MatchingMechanism.receiverDeferredAcceptance (n := 3)).IsProposerStrategyProof := by
  intro h
  have := h roth 1 (pref ![0, 1, 2])
  revert this
  decide

/-- Proposer `1` of `roth` gains under proposer-proposing deferred acceptance by no report. -/
example : ∀ π : Equiv.Perm (Fin 3),
    roth.propRank 1 (roth.deferredAcceptance 1) ≤
      roth.propRank 1 ((roth.updatePropPref 1 π).deferredAcceptance 1) := by
  decide

end CslibFrontierTests.StableMatching
