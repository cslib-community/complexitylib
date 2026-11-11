/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualRealChoice
public import CslibFrontier.Computability.Probabilistic.NativeBatch.PathCost
import Mathlib.Tactic

/-!
# Actual real-integrable total path cost of the native residual selector

[Wang2027], model p. 5 and Theorem 6 p. 13. The same compiled rational-table
cost chooser runs on original encoded input against every fixed invoice law with the
source batch means.
The invoice law is drawn independently of the residual index `J` and history.
Its actual infinite native path has a total nonnegative receipt bill. This total
is almost surely finite and its real representative is integrable, with the exact
source minimum as expectation. No integrability, total-bill or termination premise
is supplied; the proved native execution and conditional accounting are reused.

## Main definitions

* `ExecutionState`, `execution`: the original program's full infinite native execution.

## Main results

* `lintegral_totalBill`, `integrable_totalBill`: actual extended and real cost identities.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualPathCost
open Turing NativeOpenExecution NativeRetention ConcurrentBatch ResidualCover
open NativeResidualCostChoice (Prices Reflects controller encoding)
open scoped NNReal ENNReal NativeBatch.PathCost
open MeasureTheory
variable {z n m : ℕ} (T : Fin z → Block)
variable (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

/-- Full trace state of the existing price-aware native program on its original
instance/role/rational-table input, including hidden metadata and accrued receipts. -/
abbrev ExecutionState (p : Prices) :=
  NativeBatch.Trace.State (z + 1) controller.tapes Unit controller.Controls
    (encoding ⟨NativeResidualAttainment.input T points candidates, p⟩)

/-- Actual infinite path measure of the same compiled selector and source oracle. -/
@[expose] def execution (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ)) (p : Prices) :
    Measure (ℕ → ExecutionState T points candidates p) :=
  NativeBatch.PathCost.pathMeasure NativeResidualAttainment.limits
    (NativeResidualInvoice.sample T points candidates P ν) controller.program
    ⟨controller.program.initialConfig
      (encoding ⟨NativeResidualAttainment.input T points candidates, p⟩),
      NativeResidualAttainment.initialMemory⟩

/-- The actual total path bill, rather than a terminal bill that discards
nonterminating mass, has the exact source minimum as its extended expectation. -/
theorem lintegral_totalBill (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ))
    (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z) (p : Prices) (h : Reflects p P) :
    (∫⁻ ω, NativeBatch.PathCost.totalBill NativeBatch.Trace.charge ω
      ∂execution T points candidates P ν p) =
      ENNReal.ofReal (min (∑ j, P.specialistCost j)
        (P.nearCost + P.missing.mean P.specialistCost)) := by
  rw [execution, NativeBatch.PathCost.lintegral_totalBill_complete _ _ _ _ rfl _
    (NativeBatch.initial_invariant _ ())]
  exact NativeResidualRealChoice.native_expected_cost T points candidates P ν hν hz p h

/-- Real total-bill integrability and exact expectation are derived for this
same native program. The only price assumption is the primitive rational input
reflection required by the source's algorithmic-input convention. -/
theorem integrable_totalBill (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ))
    (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z) (p : Prices) (h : Reflects p P) :
    (∀ᵐ ω ∂execution T points candidates P ν p,
      NativeBatch.PathCost.totalBill NativeBatch.Trace.charge ω < ⊤) ∧
    Integrable (fun ω => (NativeBatch.PathCost.totalBill NativeBatch.Trace.charge ω).toReal)
      (execution T points candidates P ν p) ∧
    (∫ ω, (NativeBatch.PathCost.totalBill NativeBatch.Trace.charge ω).toReal
      ∂execution T points candidates P ν p) =
      min (∑ j, P.specialistCost j) (P.nearCost + P.missing.mean P.specialistCost) := by
  have he := NativeResidualRealChoice.native_expected_cost T points candidates P ν hν hz p h
  obtain ⟨hae, hint, heq⟩ := NativeBatch.PathCost.totalBill_real _ _ _ _ rfl _
    (NativeBatch.initial_invariant _ ()) (he ▸ ENNReal.ofReal_ne_top)
  refine ⟨hae, hint, ?_⟩
  rw [execution, heq]
  erw [he]
  rw [ENNReal.toReal_ofReal]
  exact le_min (Finset.sum_nonneg (fun j _ => (P.specialist_pos j).le))
    (add_nonneg P.near_pos.le (Finset.sum_nonneg
      (fun j _ => mul_nonneg (P.missing.nonneg j) (P.specialist_pos j).le)))

end Cslib.Probability.StochasticOracle.NativeResidualPathCost
