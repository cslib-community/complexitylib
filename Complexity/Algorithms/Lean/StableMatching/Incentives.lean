/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.StableMatching.Blocking
public import Mathlib.Data.Fin.VecNotation

/-!
# Incentives in stable matching mechanisms

A (direct) matching mechanism maps reported preference profiles to matchings. It is stable when
its output is always stable for the reported profile, and strategy-proof for the proposers
(resp. receivers) when no proposer (resp. receiver) can obtain a partner it truly prefers by
misreporting its list, whatever the others report.

Proposer-proposing deferred acceptance is a stable mechanism that is strategy-proof for the
proposers ([DubinsFreedman1981]; [Roth1982], Theorem 5), and symmetrically receiver-proposing
deferred acceptance is strategy-proof for the receivers. Roth's impossibility theorem
([Roth1982], Theorem 3) says that no stable mechanism is strategy-proof for both sides. We prove it
for three agents on each side, with an explicit market that has exactly two stable matchings: if a
stable mechanism selects the first, a receiver gains by misreporting, and if it selects the second,
a proposer gains by misreporting. This single witness establishes the impossibility; the statement
for every `n ≥ 3` (padding the witness with mutually top-ranked pairs) is not formalized. There is
no witness with two agents on each side.

## Main definitions

* `MatchingMechanism n`: maps an `Instance n` (the reported profile) to a `Matching n`.
* `MatchingMechanism.IsStable`, `MatchingMechanism.IsProposerStrategyProof`,
  `MatchingMechanism.IsReceiverStrategyProof`.
* `MatchingMechanism.deferredAcceptance`, `MatchingMechanism.receiverDeferredAcceptance`.
* `MatchingMechanism.rothInstance`: Roth's three-by-three witness market.

## Main results

* `MatchingMechanism.isStable_deferredAcceptance`,
  `MatchingMechanism.isProposerStrategyProof_deferredAcceptance`,
  `MatchingMechanism.isReceiverStrategyProof_receiverDeferredAcceptance`.
* `MatchingMechanism.rothInstance_isStable_iff`, `MatchingMechanism.rothInstance_receiver_gains`,
  `MatchingMechanism.rothInstance_proposer_gains`: the witness, checked by `decide`.
* `MatchingMechanism.not_isStable_and_strategyProof`: Roth's impossibility theorem for
  `MatchingMechanism 3`.

## References

* [DubinsFreedman1981]
* [Roth1982]
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

/-- A direct matching mechanism: it maps a reported preference profile to a matching. There are no
payments; this is unrelated to quasilinear mechanisms with transfers. -/
abbrev MatchingMechanism (n : ℕ) := Instance n → Matching n

namespace MatchingMechanism

variable {n : ℕ}

/-- A mechanism is stable when its output is stable for the reported profile. -/
@[expose] def IsStable (M : MatchingMechanism n) : Prop := ∀ I : Instance n, I.IsStable (M I)

/-- A mechanism is strategy-proof for the proposers when, whatever the profile `I`, no proposer `p`
obtains, by reporting a list `π` instead of its list in `I`, a partner that it strictly prefers
according to its list in `I`. -/
@[expose] def IsProposerStrategyProof (M : MatchingMechanism n) : Prop :=
  ∀ (I : Instance n) (p : Fin n) (π : Equiv.Perm (Fin n)),
    I.propRank p (M I p) ≤ I.propRank p (M (I.updatePropPref p π) p)

/-- A mechanism is strategy-proof for the receivers when no receiver can obtain a strictly
preferred partner by misreporting its list. -/
@[expose] def IsReceiverStrategyProof (M : MatchingMechanism n) : Prop :=
  ∀ (I : Instance n) (r : Fin n) (π : Equiv.Perm (Fin n)),
    I.recvRank r ((M I).symm r) ≤ I.recvRank r ((M (I.updateRecvPref r π)).symm r)

/-- Proposer-proposing deferred acceptance as a mechanism. -/
@[expose] def deferredAcceptance : MatchingMechanism n := fun I => I.deferredAcceptance

/-- Receiver-proposing deferred acceptance as a mechanism. -/
@[expose] def receiverDeferredAcceptance : MatchingMechanism n :=
  fun I => I.receiverDeferredAcceptance

/-- Deferred acceptance is a stable mechanism ([GaleShapley1962]). -/
theorem isStable_deferredAcceptance : (deferredAcceptance (n := n)).IsStable := by
  intro I
  exact I.isStable_deferredAcceptance

/-- Receiver-proposing deferred acceptance is a stable mechanism. -/
theorem isStable_receiverDeferredAcceptance : (receiverDeferredAcceptance (n := n)).IsStable := by
  intro I
  exact I.isStable_receiverDeferredAcceptance

/-- Deferred acceptance is strategy-proof for the proposers ([DubinsFreedman1981]; [Roth1982],
Theorem 5). -/
theorem isProposerStrategyProof_deferredAcceptance :
    (deferredAcceptance (n := n)).IsProposerStrategyProof :=
  fun I p π => I.propRank_deferredAcceptance_le_updatePropPref p π

/-- Receiver-proposing deferred acceptance is strategy-proof for the receivers. -/
theorem isReceiverStrategyProof_receiverDeferredAcceptance :
    (receiverDeferredAcceptance (n := n)).IsReceiverStrategyProof := by
  intro I r π
  have h := I.swap.propRank_deferredAcceptance_le_updatePropPref r π
  rw [← Instance.swap_updateRecvPref] at h
  exact h

/-! ### Roth's impossibility theorem -/

/-- Roth's market: three proposers and three receivers with exactly two stable matchings,
`rothProposerOptimal` and `rothReceiverOptimal`. -/
@[expose] def rothInstance : Instance 3 where
  propPref := ![permOfInjective ![2, 0, 1], permOfInjective ![0, 2, 1], permOfInjective ![2, 0, 1]]
  recvPref := ![permOfInjective ![2, 1, 0], permOfInjective ![2, 1, 0], permOfInjective ![1, 2, 0]]

/-- The proposer-optimal stable matching of `rothInstance`: `0 ↦ 1`, `1 ↦ 0`, `2 ↦ 2`. -/
@[expose] def rothProposerOptimal : Matching 3 := permOfInjective ![1, 0, 2]

/-- The receiver-optimal stable matching of `rothInstance`: `0 ↦ 1`, `1 ↦ 2`, `2 ↦ 0`. -/
@[expose] def rothReceiverOptimal : Matching 3 := permOfInjective ![1, 2, 0]

/-- `rothInstance` has exactly the two stable matchings `rothProposerOptimal` and
`rothReceiverOptimal`. -/
theorem rothInstance_isStable_iff (μ : Matching 3) :
    rothInstance.IsStable μ ↔ μ = rothProposerOptimal ∨ μ = rothReceiverOptimal := by
  revert μ
  decide

/-- If a stable mechanism picks `rothProposerOptimal`, receiver `0` gains by reporting `2, 0, 1`:
every stable matching of the reported market gives it a partner it truly prefers. -/
theorem rothInstance_receiver_gains {μ : Matching 3}
    (hμ : (rothInstance.updateRecvPref 0 (permOfInjective ![2, 0, 1])).IsStable μ) :
    rothInstance.recvRank 0 (μ.symm 0) < rothInstance.recvRank 0 (rothProposerOptimal.symm 0) := by
  revert μ
  decide

/-- If a stable mechanism picks `rothReceiverOptimal`, proposer `1` gains by reporting `0, 1, 2`:
every stable matching of the reported market gives it a partner it truly prefers. -/
theorem rothInstance_proposer_gains {μ : Matching 3}
    (hμ : (rothInstance.updatePropPref 1 (permOfInjective ![0, 1, 2])).IsStable μ) :
    rothInstance.propRank 1 (μ 1) < rothInstance.propRank 1 (rothReceiverOptimal 1) := by
  revert μ
  decide

/-- Roth's impossibility theorem ([Roth1982], Theorem 3), for three agents on each side: no stable
matching mechanism is strategy-proof for both the proposers and the receivers. Since the theorem
is an impossibility over all markets, the single witness `rothInstance` already establishes it.
The statement for every `n ≥ 3`, obtainable by padding the witness with mutually top-ranked pairs,
is not formalized here. -/
theorem not_isStable_and_strategyProof (M : MatchingMechanism 3) :
    ¬ (M.IsStable ∧ M.IsProposerStrategyProof ∧ M.IsReceiverStrategyProof) := by
  rintro ⟨hs, hp, hr⟩
  rcases (rothInstance_isStable_iff _).1 (hs rothInstance) with h | h
  · have h1 := hr rothInstance 0 (permOfInjective ![2, 0, 1])
    have h2 := rothInstance_receiver_gains
      (hs (rothInstance.updateRecvPref 0 (permOfInjective ![2, 0, 1])))
    rw [h] at h1
    exact absurd h1 (not_le_of_gt h2)
  · have h1 := hp rothInstance 1 (permOfInjective ![0, 1, 2])
    have h2 := rothInstance_proposer_gains
      (hs (rothInstance.updatePropPref 1 (permOfInjective ![0, 1, 2])))
    rw [h] at h1
    exact absurd h1 (not_le_of_gt h2)

end MatchingMechanism

end Cslib.Algorithms.Lean.StableMatching
