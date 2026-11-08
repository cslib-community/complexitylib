/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.ConcurrentBatch.Resources
public import Complexity.Computability.Probabilistic.NativeOpenExecution
import Complexity.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Guarded concurrent source-batch protocol on actual native word channels

[Wang2027], model PDF pp. 4--6. Raw requests are decoded and checked before any
joint oracle trajectory is sampled. Nonempty preformed batches, nonreuse,
remaining turn budget and absolute deadline follow from the concrete guard.
Invalid requests receive a deterministic rejection with zero oracle resources;
they are not issued source batches. No parser-validity/representation contract
is supplied by the native client.

## Main results

* `admit_sound`: actual accepted packets satisfy the source batch guards.
* `commit_wellFormed`: actual concurrent observations preserve source feasibility.
* `serve_rejected`: invalid packets do not invoke the oracle sampler.
* `serve_accepted`: the exact joint report/resource/state law of an accepted packet.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.ConcurrentBatch
open NativeOpenExecution
open scoped NNReal
variable {n : ℕ} {Private : Type}

/-- Previously consumed source opportunities. -/
@[expose] def usedHistory : List (Exchange n) → Finset (Fin n)
  | [] => ∅
  | x :: h => active x.batch.slots ∪ usedHistory h

/-- Source batches never reuse an opportunity, within or across turns. -/
@[expose] def noReuse : List (Exchange n) → Prop
  | [] => True
  | x :: h => Disjoint (active x.batch.slots) (usedHistory h) ∧ noReuse h

/-- External hidden state, accepted source history and actual resource meters. -/
structure ServerState (n : ℕ) (Private : Type) where
  /-- Arbitrary private oracle state, shared across correlated calls/batches. -/
  privateState : Private
  /-- Consumed labeled opportunities. -/
  used : Finset (Fin n)
  /-- Sum of actual concurrent batch maxima, excluding native local computation. -/
  elapsed : ℝ≥0
  /-- Complete accepted source batches, newest first; rejections are not turns. -/
  history : List (Exchange n)

/-- Initial protocol state; no source opportunity has been consumed. -/
@[expose] def initial (privateState : Private) : ServerState n Private :=
  ⟨privateState, ∅, 0, []⟩

/-- The actual source history agrees with the meters and is deadline/turn feasible. -/
@[expose] def WellFormed (limits : Limits n) (s : ServerState n Private) : Prop :=
  s.used = usedHistory s.history ∧
    s.elapsed = (s.history.map Exchange.duration).sum ∧ s.elapsed ≤ limits.deadline ∧
      s.history.length ≤ limits.turns ∧ noReuse s.history

/-- The empty actual source history satisfies every nonnegative deadline/budget. -/
theorem initial_wellFormed (limits : Limits n) (privateState : Private) :
    WellFormed limits (initial (n := n) privateState) := by
  simp [WellFormed, initial, usedHistory, noReuse]

/-- Decode and validate the whole batch before sampling any response. -/
@[expose] def admit (limits : Limits n) (s : ServerState n Private)
    (word : Word) : Option (Batch n) :=
  match decodeBatch n word with
  | none => none
  | some b => if s.elapsed < limits.deadline ∧ s.history.length < limits.turns ∧
      Disjoint (active b.slots) s.used then some b else none

/-- Concrete source validity comes from checked bytes and budget/nonreuse tests. -/
theorem admit_sound (limits : Limits n) (s : ServerState n Private) (word : Word) (b : Batch n)
    (h : admit limits s word = some b) :
    decodeBatch n word = some b ∧ encodeBatch b = word ∧ s.elapsed < limits.deadline ∧
      s.history.length < limits.turns ∧ Disjoint (active b.slots) s.used := by
  unfold admit at h
  split at h
  · cases h
  · rename_i batch hb
    split_ifs at h with hg
    cases h
    exact ⟨hb, decodeBatch_sound hb, hg.1, hg.2.1, hg.2.2⟩

/-- Update source meters only from the actual concurrently completed/canceled receipt. -/
@[expose] def commit (s : ServerState n Private) (x : Exchange n) (privateState : Private) :
    ServerState n Private :=
  ⟨privateState, active x.batch.slots ∪ s.used, s.elapsed + x.duration, x :: s.history⟩

/-- Every accepted batch preserves exactly-once, turn and deadline feasibility,
including deadline-truncated calls charged through cancellation. -/
theorem commit_wellFormed (limits : Limits n) (s : ServerState n Private)
    (hs : WellFormed limits s) (word : Word) (b : Batch n)
    (hb : admit limits s word = some b) (paths : Fin n → CallTrace) (privateState : Private) :
    WellFormed limits
      (commit s (observe limits (limits.deadline - s.elapsed) b paths) privateState) := by
  obtain ⟨hu, he, hd, ht, hn⟩ := hs
  obtain ⟨_, _, _, hturn, hdisj⟩ := admit_sound limits s word b hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [commit, usedHistory, observe, hu]
  · simp only [commit, List.map_cons, List.sum_cons, he, add_comm]
  · change s.elapsed + (observe limits (limits.deadline - s.elapsed) b paths).duration ≤ _
    calc
      _ ≤ s.elapsed + (limits.deadline - s.elapsed) :=
        by
          gcongr
          exact observe_duration_le limits _ b paths
      _ = limits.deadline := add_tsub_cancel_of_le hd
  · change (s.history.length + 1) ≤ limits.turns
    omega
  · change Disjoint (active b.slots) (usedHistory s.history) ∧ noReuse s.history
    exact ⟨hu ▸ hdisj, hn⟩

/-- The source may sample a fully correlated vector of potential call trajectories
and a new private state, conditional on all past accepted data and the preformed batch. -/
abbrev Sampler (n : ℕ) (Private : Type) :=
  ServerState n Private → Batch n → PMF ((Fin n → CallTrace) × Private)

/-- Actual raw batch reply: canonical report, summed tokens and concurrent maximum. -/
@[expose] def replyOf (x : Exchange n) : Reply :=
  ⟨encodeReport x.report, x.tokens, x.duration⟩

/-- Rejection is an explicit status packet, with no issued HSO call or charge. -/
@[expose] def rejection : Reply := ⟨[false], 0, 0⟩

/-- Concrete guarded batch handler. The sampler is not evaluated on rejection. -/
@[expose] def serve (limits : Limits n) (sample : Sampler n Private)
    (word : Word) (s : ServerState n Private) : PMF (Reply × ServerState n Private) :=
  match admit limits s word with
  | none => PMF.pure (rejection, s)
  | some b => (sample s b).map fun (paths, privateState) =>
    let x := observe limits (limits.deadline - s.elapsed) b paths
    (replyOf x, commit s x privateState)

/-- An actual rejected request performs no response/trajectory sampling. -/
theorem serve_rejected (limits : Limits n) (sample : Sampler n Private)
    (word : Word) (s : ServerState n Private) (h : admit limits s word = none) :
    serve limits sample word s = PMF.pure (rejection, s) := by simp [serve, h]

/-- Exact actual report, resources and hidden state all come from the same joint sample. -/
theorem serve_accepted (limits : Limits n) (sample : Sampler n Private)
    (word : Word) (s : ServerState n Private) (b : Batch n) (h : admit limits s word = some b) :
    serve limits sample word s = (sample s b).map (fun (paths, privateState) =>
      let x := observe limits (limits.deadline - s.elapsed) b paths
      (replyOf x, commit s x privateState)) := by simp [serve, h]

/-- Ordinary native word handler; all source checks occur before oracle sampling. -/
@[expose] def environment (limits : Limits n) (sample : Sampler n Private) :
    Environment Unit (ServerState n Private) :=
  fun q memory => serve limits sample q.2 memory.privateState

/-- Visible reports roundtrip; cancellation is distinct from an empty completed word. -/
theorem reply_decodes (x : Exchange n) : decodeReport n (replyOf x).word = some x.report :=
  decodeReport_encode _

/-- The rejection status cannot be confused with an accepted batch response. -/
theorem rejection_decodes : decodeReport n rejection.word = none := rfl

end Cslib.Probability.StochasticOracle.ConcurrentBatch
