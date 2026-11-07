/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.StableMatching.Lattice
import Complexity.Algorithms.Lean.StableMatching.Incentives
import Mathlib.Data.Fin.VecNotation

/-!
# Stable matching: checked instances

Kernel-checked (`decide`, no `native_decide`) examples for deferred acceptance:

1. Boundary cases `n = 0` and `n = 1`, where the proposal bound `n ^ 2 - n + 1` is respectively
   not attained and attained.
2. Roth's three-by-three market, which has exactly two stable matchings: proposer-proposing and
   receiver-proposing deferred acceptance differ, the identity matching is blocked, and the lattice
   of stable matchings has `⊥ < ⊤`.
3. A three-by-three market attaining the proposal bound `3 ^ 2 - 3 + 1 = 7`.
4. Incentives: in Roth's market a receiver gains by misreporting under proposer-proposing deferred
   acceptance and a proposer gains under receiver-proposing deferred acceptance, so neither
   mechanism is strategy-proof for the other side; no proposer gains under proposer-proposing
   deferred acceptance.
-/

namespace ComplexityTests.StableMatching

open Cslib.Algorithms.Lean.StableMatching

/-- A preference list over `Fin 3`, given as the vector of agents from most to least preferred. -/
def pref (v : Fin 3 → Fin 3) (h : Function.Injective v := by decide) : Equiv.Perm (Fin 3) :=
  permOfInjective v h

/-! ### 1. Boundary cases -/

/-- The empty market. -/
def empty : Instance 0 := ⟨Fin.elim0, Fin.elim0⟩

example : empty.IsStable empty.deferredAcceptance ∧ empty.proposals = 0 := by decide

/-- The market with one agent on each side. -/
def single : Instance 1 := ⟨fun _ => 1, fun _ => 1⟩

example : single.deferredAcceptance = 1 ∧ single.proposals = 1 ^ 2 - 1 + 1 := by decide

/-! ### 2. Roth's market: two stable matchings -/

/-- Three proposers and three receivers with exactly two stable matchings. -/
def roth : Instance 3 where
  propPref := ![pref ![2, 0, 1], pref ![0, 2, 1], pref ![2, 0, 1]]
  recvPref := ![pref ![2, 1, 0], pref ![2, 1, 0], pref ![1, 2, 0]]

/-- The proposer-optimal stable matching of `roth`. -/
def μa : Matching 3 := pref ![1, 0, 2]

/-- The receiver-optimal stable matching of `roth`. -/
def μb : Matching 3 := pref ![1, 2, 0]

example : roth.deferredAcceptance = μa := by decide
example : roth.receiverDeferredAcceptance = μb := by decide
example : roth.IsStable μa ∧ roth.IsStable μb := by decide
example : ∀ μ : Matching 3, roth.IsStable μ → μ = μa ∨ μ = μb := by decide
example : ¬ roth.IsStable 1 ∧ roth.IsBlockingPair 1 1 0 := by decide
example : Fintype.card roth.Stable = 2 := by decide
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

/-! ### 4. Incentives -/

/-- Under proposer-proposing deferred acceptance, receiver `0` of `roth` gains by reporting
`2, 0, 1`. -/
example : ¬ (Mechanism.deferredAcceptance (n := 3)).IsReceiverStrategyProof := by
  intro h
  have := h roth 0 (pref ![2, 0, 1])
  revert this
  decide

/-- Under receiver-proposing deferred acceptance, proposer `1` of `roth` gains by reporting
`0, 1, 2`. -/
example : ¬ (Mechanism.receiverDeferredAcceptance (n := 3)).IsProposerStrategyProof := by
  intro h
  have := h roth 1 (pref ![0, 1, 2])
  revert this
  decide

/-- Proposer `1` of `roth` gains under proposer-proposing deferred acceptance by no report. -/
example : ∀ π : Equiv.Perm (Fin 3),
    roth.propRank 1 (roth.deferredAcceptance 1) ≤
      roth.propRank 1 ((roth.updatePropPref 1 π).deferredAcceptance 1) := by
  decide

end ComplexityTests.StableMatching
