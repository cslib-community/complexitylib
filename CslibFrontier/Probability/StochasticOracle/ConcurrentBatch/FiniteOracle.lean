/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Protocol
public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy
public import CslibFrontier.Computability.Probabilistic.NativeInterface
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Concurrent batch observations in the finite quantitative oracle API

A finite joint trajectory table is primitive oracle data, not a product law or a
supplied representation certificate. At a reached physical snapshot it constructs
the existing `SelectionPolicy.Oracle` response, proposal, token and maximum-latency
fields. Actual guarded word/native dispatch has exactly the same joint law.

This is a batch-local finite-scenario transfer. It does not assert that latent
scenario labels are visible to a machine, reconstruct an arbitrary policy from
its full history, or assume a sufficient finite abstraction of unbounded metadata.
The general guarded protocol itself allows arbitrary discrete joint laws.

## Main results

* `serve_observation_law`: actual raw reports and joint resources have the quantitative API law.
* `native_dispatch_law`: actual selected native queries execute that same constructed joint table.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.ConcurrentBatch
open NativeOpenExecution NativeInterface Cslib.Optimization.OneConstraint Turing
open scoped NNReal
variable {n m : ℕ} {B R Private Control : Type} {k : ℕ} {input : List Bool}
variable [Fintype R]

/-- General finite conditional trajectory tables; calls may be arbitrarily correlated. -/
structure FiniteProfile (n : ℕ) (B R : Type) [Fintype R] where
  /-- All query words are preformed from previous records and the selected action. -/
  request : List (SelectionPolicy.Record B R) → B → Batch n
  /-- Conditional joint trajectory law, allowed to depend on the full history. -/
  law : List (SelectionPolicy.Record B R) → B → Distribution R ℝ
  /-- Joint potential call paths from the same response scenario. -/
  paths : List (SelectionPolicy.Record B R) → B → R → Fin n → CallTrace

variable (profile : FiniteProfile n B R) (limits : Limits n)

/-- Actual concurrent receipt at a reached remaining-deadline snapshot. -/
@[expose] def profileReceipt (remaining : ℝ≥0) (h : List (SelectionPolicy.Record B R))
    (b : B) (r : R) : Exchange n :=
  observe limits remaining (profile.request h b) (profile.paths h b r)

/-- Existing quantitative oracle fields are computed from the concrete batch
codec, valid candidate masks, accrued invoices and concurrent maximum latency. -/
@[expose] def oracleAt (remaining : ℝ≥0) : SelectionPolicy.Oracle B R (Fin m) where
  respond := profile.law
  proposed h b r := proposals m (profileReceipt profile limits remaining h b r).report
  charge h b r := (profileReceipt profile limits remaining h b r).tokens
  duration h b r := (profileReceipt profile limits remaining h b r).duration
  charge_nonneg := by intros; exact Nat.cast_nonneg _
  duration_nonneg := by intros; exact NNReal.coe_nonneg _

/-- Concrete sampler used by the actual native batch handler at this selection.
New private state can retain the response scenario and all its correlations. -/
@[expose] def profileSampler (h : List (SelectionPolicy.Record B R)) (b : B)
    (nextPrivate : R → Private) : Sampler n Private := fun _ _ =>
  (profile.law h b).toPMF.map fun r => (profile.paths h b r, nextPrivate r)

/-- Runtime source guards on the actual packet; framing/nonemptiness are already proved. -/
theorem admit_profile (s : ServerState n Private) (h : List (SelectionPolicy.Record B R)) (b : B)
    (hd : s.elapsed < limits.deadline) (ht : s.history.length < limits.turns)
    (hu : Disjoint (active (profile.request h b).slots) s.used) :
    admit limits s (encodeBatch (profile.request h b)) = some (profile.request h b) := by
  simp [admit, decodeBatch_encode, hd, ht, hu]

/-- The actual raw report/cost/physical-time tuple equals the finite quantitative
oracle observation law, derived from the concrete handler and the same joint sample. -/
theorem serve_observation_law (s : ServerState n Private)
    (h : List (SelectionPolicy.Record B R)) (b : B) (nextPrivate : R → Private)
    (hd : s.elapsed < limits.deadline) (ht : s.history.length < limits.turns)
    (hu : Disjoint (active (profile.request h b).slots) s.used) :
    (serve limits (profileSampler profile h b nextPrivate)
        (encodeBatch (profile.request h b)) s).map
        (fun out => (out.1.word, (out.1.tokens : ℝ), (out.1.duration : ℝ))) =
      ((oracleAt (m := m) profile limits (limits.deadline - s.elapsed)).respond h b).toPMF.map
        (fun r => (encodeReport
          (profileReceipt profile limits (limits.deadline - s.elapsed) h b r).report,
          (oracleAt (m := m) profile limits (limits.deadline - s.elapsed)).charge h b r,
          (oracleAt (m := m) profile limits (limits.deadline - s.elapsed)).duration h b r)) := by
  rw [serve_accepted _ _ _ _ _ (admit_profile profile limits s h b hd ht hu)]
  simp only [profileSampler, PMF.map_comp]
  rfl

/-- All candidate proposals come from actually completed, well-formed raw masks,
not an arbitrary semantic proposal parser. Cancellations yield no proposal. -/
theorem profile_proposals (remaining : ℝ≥0)
    (h : List (SelectionPolicy.Record B R)) (b : B) (r : R) :
    parseProposals n m (replyOf (profileReceipt profile limits remaining h b r)).word =
      (oracleAt (m := m) profile limits remaining).proposed h b r := by
  exact parseProposals_report _

/-- Arbitrary actual native hidden configurations dispatch the encoded selected
batch into the derived joint table, retaining complete tapes and oracle state.
Only actual byte-buffer and runtime budget conditions are hypotheses. -/
theorem native_dispatch_law
    (world : World k Control Unit (ServerState n Private) input) (next : Control)
    (h : List (SelectionPolicy.Record B R)) (b : B) (nextPrivate : R → Private)
    (hw : (world.config.channels ()).queryBuffer = encodeBatch (profile.request h b))
    (hd : world.memory.privateState.elapsed < limits.deadline)
    (ht : world.memory.privateState.history.length < limits.turns)
    (hu : Disjoint (active (profile.request h b).slots) world.memory.privateState.used) :
    dispatch (environment limits (profileSampler profile h b nextPrivate))
        (.query world () next) =
      (profile.law h b).toPMF.map (fun r =>
        let x := profileReceipt profile limits
          (limits.deadline - world.memory.privateState.elapsed) h b r
        (⟨world.config.receive () next (replyOf x).word,
          world.memory.record ((), encodeBatch (profile.request h b)) (replyOf x)
            (commit world.memory.privateState x (nextPrivate r))⟩ :
          World k Control Unit (ServerState n Private) input)) := by
  simp only [dispatch, environment, hw]
  rw [serve_accepted _ _ _ _ _ (admit_profile profile limits _ h b hd ht hu)]
  simp only [profileSampler, PMF.map_comp]
  rfl

end Cslib.Probability.StochasticOracle.ConcurrentBatch
