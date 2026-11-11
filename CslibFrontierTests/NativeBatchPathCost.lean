/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Probabilistic.NativeBatch.PathCost
import CslibFrontierTests.NativeBatchMetadata
import Mathlib.Tactic

/-!
# Native infinite-path bills with unbounded invoices and silent divergent suffixes

The geometric hidden-state source has no finite invoice alphabet. The same native
program's complete expectation is its actual infinite-path expectation. A second
client continues a real charged receipt through a silent native loop: divergence
preserves an exact positive bill, rather than turning it into zero terminal cost.
-/

noncomputable section
open Cslib Cslib.Probability NativeBatch NativeOpenExecution NativeInterface
open StochasticOracle.ConcurrentBatch MeasureTheory
open scoped ENNReal NativeBatch.PathCost
namespace CslibFrontierTests.NativeBatchPathCost
open ConcurrentBatch (limits)
open NativeBatchMetadata (spin spinning chargedPrefix)
open NativeBatchPolicy (firstReceipt)

-- One ordinary blank-input native program and its actual unbounded correlated source.
example : (∫⁻ ω, PathCost.totalBill Trace.charge ω
    ∂PathCost.pathMeasure limits NativeBatchMetadata.sample NativeBatchPolicy.machine
      NativeBatchMetadata.start) =
    Quantitative.expected limits NativeBatchMetadata.sample NativeBatchPolicy.machine
      Trace.charge 3 NativeBatchMetadata.start := by
  exact PathCost.lintegral_totalBill_complete _ _ _ _ rfl _
    (initial_invariant limits 0)

private def suffixState (u : Bool) (t : ℕ) : Trace.State 3 0 Bool Unit [] :=
  ⟨none, List.replicate t none ++ [some (firstReceipt u)]⟩

private theorem suffix_law (u : Bool) (t : ℕ) :
    ObservedProcess.stateLaw (Trace.step limits ConcurrentBatch.sample spin)
      (t + 1) (chargedPrefix u) = PMF.pure (suffixState u (t + 1)) := by
  induction t with
  | zero =>
    simp [ObservedProcess.stateLaw, Trace.step, chargedPrefix, NativeBatchMetadata.spin_diverges,
      Trace.respond, respondSource, Trace.receipt, suffixState]
  | succ t ih =>
    rw [ObservedProcess.stateLaw, ih, PMF.pure_bind]
    simp [Trace.step, suffixState, seekSourceFrom, Trace.respond, respondSource, Trace.receipt,
      List.replicate_succ]

-- The suffix is genuinely divergent, yet total accrued expectation is 11 or 3.
example (u : Bool) :
    (∫⁻ ω, PathCost.totalBill Trace.charge ω
      ∂PathCost.pathMeasureFrom limits ConcurrentBatch.sample spin (chargedPrefix u)) =
      (if u then 11 else 3 : ℝ≥0∞) := by
  rw [PathCost.lintegral_totalBill_from]
  have he (t : ℕ) : (∑' state, ObservedProcess.stateLaw
      (Trace.step limits ConcurrentBatch.sample spin) t (chargedPrefix u) state *
        Trace.accrued Trace.charge state) = (if u then 11 else 3 : ℝ≥0∞) := by
    have hr := (NativeBatchPolicy.first_resources u).2
    cases t with
    | zero =>
      cases u <;> simp [ObservedProcess.stateLaw, PMF.pure_apply,
        Trace.accrued, chargedPrefix, Trace.charge, hr]
    | succ t =>
      rw [suffix_law]
      cases u <;> simp [PMF.pure_apply, Trace.accrued, suffixState, Trace.charge, hr]
  simp_rw [he]
  exact ciSup_const

-- A zero score remains zero even on these divergent trajectories.
example (u : Bool) :
    (∫⁻ ω, PathCost.totalBill (fun _ : Trace.Record 3 => 0) ω
      ∂PathCost.pathMeasureFrom limits ConcurrentBatch.sample spin (chargedPrefix u)) = 0 := by
  simp [PathCost.totalBill, Trace.accrued, Quantitative.newest]

end CslibFrontierTests.NativeBatchPathCost
