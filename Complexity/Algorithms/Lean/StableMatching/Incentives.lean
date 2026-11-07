/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.StableMatching.Blocking
import Mathlib.Data.Fin.VecNotation

/-!
# Incentives in stable matching mechanisms

A (direct) matching mechanism maps reported preference profiles to matchings. It is stable when
its output is always stable for the reported profile, and strategy-proof for the proposers
(resp. receivers) when no proposer (resp. receiver) can obtain a partner it truly prefers by
misreporting its list, whatever the others report.

Proposer-proposing deferred acceptance is a stable mechanism that is strategy-proof for the
proposers ([DubinsFreedman1981], [Roth1982]), and symmetrically receiver-proposing deferred
acceptance is strategy-proof for the receivers. Roth's impossibility theorem [Roth1982] says that
no stable mechanism is strategy-proof for both sides. We prove it with an explicit market with
three proposers and three receivers that has exactly two stable matchings: if a stable mechanism
selects the first, a receiver gains by misreporting, and if it selects the second, a proposer gains
by misreporting. (There is no such market with two agents on each side.)

## Main definitions

* `Mechanism n`: maps an `Instance n` (the reported profile) to a `Matching n`.
* `Mechanism.IsStable`, `Mechanism.IsProposerStrategyProof`,
  `Mechanism.IsReceiverStrategyProof`.
* `Mechanism.deferredAcceptance`, `Mechanism.receiverDeferredAcceptance`.

## Main results

* `Mechanism.isProposerStrategyProof_deferredAcceptance`,
  `Mechanism.isReceiverStrategyProof_receiverDeferredAcceptance`.
* `Mechanism.not_isStable_and_strategyProof`: Roth's impossibility theorem.

## References

* [DubinsFreedman1981]
* [Roth1982]
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

/-- A direct matching mechanism: it maps a reported preference profile to a matching. -/
abbrev Mechanism (n : ℕ) := Instance n → Matching n

namespace Mechanism

variable {n : ℕ}

/-- A mechanism is stable when its output is stable for the reported profile. -/
@[expose] def IsStable (M : Mechanism n) : Prop := ∀ I : Instance n, I.IsStable (M I)

/-- A mechanism is strategy-proof for the proposers when, whatever the profile `I`, no proposer `p`
obtains, by reporting a list `π` instead of its list in `I`, a partner that it strictly prefers
according to its list in `I`. -/
@[expose] def IsProposerStrategyProof (M : Mechanism n) : Prop :=
  ∀ (I : Instance n) (p : Fin n) (π : Equiv.Perm (Fin n)),
    I.propRank p (M I p) ≤ I.propRank p (M (I.updatePropPref p π) p)

/-- A mechanism is strategy-proof for the receivers when no receiver can obtain a strictly
preferred partner by misreporting its list. -/
@[expose] def IsReceiverStrategyProof (M : Mechanism n) : Prop :=
  ∀ (I : Instance n) (r : Fin n) (π : Equiv.Perm (Fin n)),
    I.recvRank r ((M I).symm r) ≤ I.recvRank r ((M (I.updateRecvPref r π)).symm r)

/-- Proposer-proposing deferred acceptance as a mechanism. -/
@[expose] def deferredAcceptance : Mechanism n := fun I => I.deferredAcceptance

/-- Receiver-proposing deferred acceptance as a mechanism. -/
@[expose] def receiverDeferredAcceptance : Mechanism n := fun I => I.receiverDeferredAcceptance

/-- Deferred acceptance is a stable mechanism ([GaleShapley1962]). -/
theorem isStable_deferredAcceptance : (deferredAcceptance (n := n)).IsStable := by
  intro I
  exact I.isStable_deferredAcceptance

/-- Receiver-proposing deferred acceptance is a stable mechanism. -/
theorem isStable_receiverDeferredAcceptance : (receiverDeferredAcceptance (n := n)).IsStable := by
  intro I
  exact I.isStable_receiverDeferredAcceptance

/-- Deferred acceptance is strategy-proof for the proposers ([DubinsFreedman1981], [Roth1982]). -/
theorem isProposerStrategyProof_deferredAcceptance :
    (deferredAcceptance (n := n)).IsProposerStrategyProof :=
  fun I p π => I.propRank_deferredAcceptance_le_updatePropPref p π

/-- Receiver-proposing deferred acceptance is strategy-proof for the receivers. -/
theorem isReceiverStrategyProof_receiverDeferredAcceptance :
    (receiverDeferredAcceptance (n := n)).IsReceiverStrategyProof := by
  intro I r π
  -- swapping roles turns receiver `r`'s misreport into a proposer misreport, definitionally
  exact I.swap.propRank_deferredAcceptance_le_updatePropPref r π

/-! ### Roth's impossibility theorem -/

/-- The permutation of `Fin 3` listing `v 0, v 1, v 2`. -/
private def pref3 (v : Fin 3 → Fin 3) (hv : Function.Injective v := by decide) :
    Equiv.Perm (Fin 3) :=
  permOfInjective v hv

/-- Roth's market: three proposers and three receivers with exactly two stable matchings. -/
private def rothInstance : Instance 3 where
  propPref := ![pref3 ![2, 0, 1], pref3 ![0, 2, 1], pref3 ![2, 0, 1]]
  recvPref := ![pref3 ![2, 1, 0], pref3 ![2, 1, 0], pref3 ![1, 2, 0]]

private theorem rothInstance_isStable {μ : Matching 3} (hμ : rothInstance.IsStable μ) :
    μ = pref3 ![1, 0, 2] ∨ μ = pref3 ![1, 2, 0] := by
  revert μ
  decide

/-- If the mechanism picks the first stable matching, receiver `0` gains by reporting `2, 0, 1`. -/
private theorem rothInstance_receiver_gains {μ : Matching 3}
    (hμ : (rothInstance.updateRecvPref 0 (pref3 ![2, 0, 1])).IsStable μ) :
    rothInstance.recvRank 0 (μ.symm 0) < rothInstance.recvRank 0 ((pref3 ![1, 0, 2]).symm 0) := by
  revert μ
  decide

/-- If the mechanism picks the second stable matching, proposer `1` gains by reporting `0, 1, 2`. -/
private theorem rothInstance_proposer_gains {μ : Matching 3}
    (hμ : (rothInstance.updatePropPref 1 (pref3 ![0, 1, 2])).IsStable μ) :
    rothInstance.propRank 1 (μ 1) < rothInstance.propRank 1 ((pref3 ![1, 2, 0]) 1) := by
  revert μ
  decide

/-- Roth's impossibility theorem [Roth1982]: no stable matching mechanism is strategy-proof for
both the proposers and the receivers. The witness is a market with three agents on each side. -/
theorem not_isStable_and_strategyProof (M : Mechanism 3) :
    ¬ (M.IsStable ∧ M.IsProposerStrategyProof ∧ M.IsReceiverStrategyProof) := by
  rintro ⟨hs, hp, hr⟩
  rcases rothInstance_isStable (hs rothInstance) with h | h
  · have h1 := hr rothInstance 0 (pref3 ![2, 0, 1])
    have h2 := rothInstance_receiver_gains (hs (rothInstance.updateRecvPref 0 (pref3 ![2, 0, 1])))
    rw [h] at h1
    exact absurd h1 (not_le_of_gt h2)
  · have h1 := hp rothInstance 1 (pref3 ![0, 1, 2])
    have h2 := rothInstance_proposer_gains (hs (rothInstance.updatePropPref 1 (pref3 ![0, 1, 2])))
    rw [h] at h1
    exact absurd h1 (not_le_of_gt h2)

end Mechanism

end Cslib.Algorithms.Lean.StableMatching
