/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment

/-!
# Delayed-opening simulation against corrupted OT commitment receivers

A simulator runs the commit prefix without the committed bit. Only at opening does it receive
that bit and reconstruct the revealed pairs from the receiver's recorded indices and answers.
All four OT indices and adaptive receiver strategies are allowed. The joint law retains the
opening, transcript and private receiver state, rather than only the pre-opening marginal.

## Main definitions

* `OTCommitment.equivocate`: reconstruct an opening consistent with the recorded OT answers.

## Main results

* `OTCommitment.equivocation`: exact joint law for a bit-independent commit prefix followed by
  an opening to the supplied bit.
* `OTCommitment.equivocation_bind`: the same law after arbitrary randomized post-opening work.

This is a fixed-length, honest-sender execution with one later opening. It does not formalize
full ideal commitment scheduling, mid-commit abort, composition or simulator efficiency. The
simulator sees the corrupted receiver's OT indices; an honest sender does not have that access.

## References

The construction is [Cramer2000], §7.1, printed p. 21. This equivocation and exact joint-law
analysis is original; it is not an additional theorem quoted from that source.
-/

public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

open Cslib.Probability

/-- Reconstruct the honest pair from its selected value and a bit supplied only at opening.
The simulator knows the corrupted receiver's index; the actual honest sender does not. -/
@[expose] def equivocate {k : ℕ} (b : Bool) (transcript : Fin k → Fin 4 × Bool) : Opening k :=
  opening b (fun i => if (fin4ToBoolPair (transcript i).1).2 then
    (transcript i).2 ^^ b else (transcript i).2)

/-- Every reconstructed pair has the supplied parity and matches the recorded selected value,
including selections in either of the two duplicated OT slots. -/
theorem equivocate_accepts {k : ℕ} (b : Bool) (transcript : Fin k → Fin 4 × Bool) :
    Accepts (fun i => (fin4ToBoolPair (transcript i).1).2) (fun i => (transcript i).2)
      b (equivocate b transcript) := by
  intro i
  cases b <;> cases ha : (transcript i).2 <;>
    cases hc : (fin4ToBoolPair (transcript i).1).2 <;>
    simp [equivocate, opening, ha, hc]

private theorem receiverCommit_received {State : Type} (A : Receiver State) (b : Bool)
    (k : ℕ) (st : State) {masks : Fin k → Bool} {transcript : Fin k → Fin 4 × Bool}
    {final : State} (h : (masks, transcript, final) ∈ (receiverCommit A b k st).support) :
    ∀ i, (transcript i).2 = table b (masks i) (transcript i).1 := by
  induction k generalizing st with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
      simp only [receiverCommit_succ, transfer_eq, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at h
      obtain ⟨⟨j, next⟩, _, r, _, next', _, ⟨restMasks, rest, final'⟩, hrest, he⟩ := h
      cases he
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact ih next' hrest i

/-- An actual honest opening is the unique parity-correct completion of the receiver's selected
values. This support statement links the simulator's reconstruction to masks really sampled. -/
theorem opening_eq_equivocate_of_mem_support {State : Type} (A : Receiver State) (b : Bool)
    (k : ℕ) (st : State) {masks : Fin k → Bool} {transcript : Fin k → Fin 4 × Bool}
    {final : State} (h : (masks, transcript, final) ∈ (receiverCommit A b k st).support) :
    opening b masks = equivocate b transcript := by
  funext i c
  have hi := receiverCommit_received A b k st h i
  simp only [equivocate, opening]
  rw [hi]
  cases b <;> cases masks i <;> cases hc : (fin4ToBoolPair (transcript i).1).2 <;>
    cases c <;> simp [table, hc]

/-- Exact simulation of the joint opening, receiver transcript and commit-final private state.
The simulator's prefix is `receiverRun A false`, which has no committed-bit input. It receives
`b` only when applying `equivocate` after that prefix has finished. -/
theorem equivocation {State : Type} (A : Receiver State) (b : Bool) (k : ℕ) (st : State) :
    (receiverCommit A b k st).map (fun (masks, transcript, final) =>
      (transcript, final, opening b masks)) =
    (receiverRun A false k st).map (fun (transcript, final) =>
      (transcript, final, equivocate b transcript)) := by
  calc
    _ = (receiverCommit A b k st).map (fun (_, transcript, final) =>
        (transcript, final, equivocate b transcript)) := by
      apply Probability.PMF.map_congr_on_support
      rintro ⟨masks, transcript, final⟩ h
      dsimp only
      rw [opening_eq_equivocate_of_mem_support A b k st h]
    _ = (receiverRun A b k st).map (fun (transcript, final) =>
        (transcript, final, equivocate b transcript)) := by
      simp only [receiverRun, PMF.map_comp, Function.comp_def]
    _ = _ := by rw [perfectHiding A b false k st]

/-- An arbitrary randomized receiver continuation can process the revealed pairs and its entire
commit view. It runs after opening in both experiments; exact equality needs no efficiency
assumption on the continuation or finiteness assumption on its state/output. -/
theorem equivocation_bind {State Output : Type} (A : Receiver State) (b : Bool) (k : ℕ)
    (st : State) (finish : (Fin k → Fin 4 × Bool) → State → Opening k → PMF Output) :
    (do
      let (masks, transcript, final) ← receiverCommit A b k st
      finish transcript final (opening b masks)) = (do
      let (transcript, final) ← receiverRun A false k st
      finish transcript final (equivocate b transcript)) := by
  have h := congrArg (fun p => p.bind (fun (transcript, final, o) =>
    finish transcript final o)) (equivocation A b k st)
  simpa only [PMF.bind_map, Function.comp_def, Probability.PMF.monad_bind_eq_bind] using h

end Cslib.Crypto.Protocols.MPC.OTCommitment
