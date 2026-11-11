/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualCostChoice
public import CslibFrontier.Probability.StochasticOracle.NativeResidualRealAdaptive
import CslibFrontier.Computability.Probabilistic.NativeUnboundedExecution.OutputTransfer
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# The native cost-aware selector on fixed real-mean invoice oracles

[Wang2027], model p. 5 and Theorem 6 p. 13. The same compiled rational cost
comparison now operates on genuinely random natural token reports, drawn from any
fixed invoice PMF with the source batch means. Declared
expected costs need not equal any realized invoice. No real serializer, integer
price identity or total-cost/integrability conclusion is assumed.

## Main results

* `native_selectionOnly`, `native_certified`: actual tape admission and deadline success.
* `native_expected_cost`, `native_cost_mem`, `native_upper`: the same code realizes
  the source minimum as an actual attained feasible expected bill.
* `native_optimum`: the attained bill equals the universal native optimum on this oracle.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualRealChoice
open Turing Turing.MultiTapeTM NativeOpenExecution NativeRetention ConcurrentBatch ResidualCover
open NativeResidualAttainment
open NativeResidualCostChoice (Prices Reflects controller encoding packed adaptive)
open scoped NNReal ENNReal
variable {z n m : ℕ} (T : Fin z → Block)
variable (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

/-- Successful provenance is transferred using the derived native implementation
law and the proved real-mean source admission of both fixed strategies. -/
theorem native_selectionOnly (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ)) (hz : 3 ≤ z)
    (p : Prices)
    (accept : Finset (Fin (input T points candidates).startup.system.rows.length) → Bool) :
    NativeUnboundedExecution.SelectionOnly controller.program
      (environment limits (NativeResidualInvoice.sample T points candidates P ν))
      (NativeBatch.candidateParser (n := z + 1)
        (input T points candidates).startup.system.rows.length)
      (decodeFamily (input T points candidates).startup.system.rows.length) accept
      ⟨controller.program.initialConfig (encoding ⟨input T points candidates, p⟩),
        initialMemory⟩ := by
  have hadmit : NativeUnboundedExecution.SelectionOnly
      (NativeResidualRouting.controller (adaptive p)).program
      (environment limits (NativeResidualInvoice.sample T points candidates P ν))
      (NativeBatch.candidateParser (n := z + 1)
        (input T points candidates).startup.system.rows.length)
      (decodeFamily (input T points candidates).startup.system.rows.length) accept
      ⟨(NativeResidualRouting.controller (adaptive p)).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩ := by
    cases he : adaptive p with
    | false =>
      exact NativeResidualRealCost.native_all_selectionOnly T points candidates P ν hz 2
        (by omega) accept
    | true =>
      exact NativeResidualRealAdaptive.native_selectionOnly T points candidates P
        ν hz accept
  exact NativeUnboundedExecution.selectionOnly_of_output_memory controller.program _
    (NativeResidualRouting.controller (adaptive p)).program _ _ _ accept _ _
    (NativeResidualCostChoice.native_law _ _ ⟨input T points candidates, p⟩ initialMemory) hadmit

/-- The named cost-aware code emits a certified actual cover by the source deadline. -/
theorem native_certified (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ)) (hz : 3 ≤ z) (p : Prices) :
    ((NativeUnboundedExecution.terminal controller.program
      (environment limits (NativeResidualInvoice.sample T points candidates P ν))
      ⟨controller.program.initialConfig (encoding ⟨input T points candidates, p⟩),
        initialMemory⟩).map
      (BatchOutput.certified limits (input T points candidates).startup.system
        (valid T points candidates (by omega)))) true = 1 := by
  rw [BatchOutput.terminal_certified, NativeResidualCostChoice.native_law,
    ← BatchOutput.terminal_certified]
  cases he : adaptive p with
  | false =>
    exact NativeResidualRealCost.native_all_certified T points candidates P ν hz 2
      (by omega)
  | true => exact NativeResidualRealAdaptive.native_certified T points candidates P ν hz

private theorem fixed_terminates (P : Parameters z) (ν : PMF (Fin (z + 1) → ℕ)) (hz : 3 ≤ z)
    (b : Bool) :
    NativeUnboundedExecution.terminal (NativeResidualRouting.controller b).program
      (environment limits (NativeResidualInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller b).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩ none = 0 := by
  have hcert : ((NativeUnboundedExecution.terminal (NativeResidualRouting.controller b).program
      (environment limits (NativeResidualInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller b).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
      (BatchOutput.certified limits (input T points candidates).startup.system
        (valid T points candidates (by omega)))) true = 1 := by
    cases b with
    | false =>
      exact NativeResidualRealCost.native_all_certified T points candidates P ν hz 2 (by omega)
    | true => exact NativeResidualRealAdaptive.native_certified T points candidates P ν hz
  apply (PMF.apply_eq_zero_iff _ _).mpr
  intro hn
  have hm : false ∈ ((NativeUnboundedExecution.terminal (NativeResidualRouting.controller b).program
      (environment limits (NativeResidualInvoice.sample T points candidates P ν))
      ⟨(NativeResidualRouting.controller b).program.initialConfig
        (GuardedStartup.encoding (input T points candidates)), initialMemory⟩).map
      (BatchOutput.certified limits (input T points candidates).startup.system
        (valid T points candidates (by omega)))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨none, hn, rfl⟩
  rw [(PMF.apply_eq_one_iff _ _).mp hcert] at hm
  cases hm

/-- The actual compiled cost chooser realizes the real source formula, with no
natural-price identification: only rational algorithmic inputs reflect the
source's fixed expected prices and probabilities. -/
theorem native_expected_cost (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z) (p : Prices)
      (h : Reflects p P) :
    NativeBatch.Quantitative.expected limits (NativeResidualInvoice.sample T points candidates P ν)
      controller.program NativeBatch.Trace.charge 3
      ⟨controller.program.initialConfig (encoding ⟨input T points candidates, p⟩), initialMemory⟩ =
      ENNReal.ofReal (min (∑ j, P.specialistCost j)
        (P.nearCost + P.missing.mean P.specialistCost)) := by
  have he := NativeBatch.Quantitative.expected_charge_eq_of_output_memory limits
    (NativeResidualInvoice.sample T points candidates P ν) controller.program
    (NativeResidualRouting.controller (adaptive p)).program _ _
    (NativeBatch.initial_invariant limits ()) (NativeBatch.initial_invariant limits ()) rfl rfl
    (NativeResidualCostChoice.native_law _ _ ⟨input T points candidates, p⟩ initialMemory)
    (fixed_terminates T points candidates P ν hz (adaptive p))
  change NativeBatch.Quantitative.expected _ _ _ NativeBatch.Trace.charge 3 _ = _ at he
  rw [he]
  by_cases hb : adaptive p = true
  · rw [hb, min_eq_right ((NativeResidualCostChoice.adaptive_iff p P h).mp hb)]
    exact NativeResidualRealAdaptive.native_expected_cost T points candidates P ν hν hz
  · have hf : adaptive p = false := Bool.eq_false_iff.mpr hb
    rw [hf, min_eq_left
      (le_of_not_ge (fun hc => hb ((NativeResidualCostChoice.adaptive_iff p P h).mpr hc)))]
    exact NativeResidualRealCost.native_all_expected_cost T points candidates P ν hν hz 2 (by omega)

/-- The source minimum is attained in the existing native class by this same
single program, even for nonintegral fixed expected costs. -/
theorem native_cost_mem (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z) (p : Prices)
      (h : Reflects p P) :
    ENNReal.ofReal (min (∑ j, P.specialistCost j)
      (P.nearCost + P.missing.mean P.specialistCost)) ∈
      BatchOptimum.costs limits (NativeResidualInvoice.sample T points candidates P ν)
        (packed ⟨input T points candidates, p⟩) () (valid T points candidates (by omega)) 1 := by
  exact ⟨controller.tapes, controller.Controls, controller.finite, controller.program,
    native_selectionOnly T points candidates P ν hz p _,
    (native_certified T points candidates P ν hz p).ge,
    (native_expected_cost T points candidates P ν hν hz p h).symm⟩

/-- Feasible native upper bound, used with universal mean accounting in `native_optimum`. -/
theorem native_upper (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z) (p : Prices)
      (h : Reflects p P) :
    BatchOptimum.optimum limits (NativeResidualInvoice.sample T points candidates P ν)
      (packed ⟨input T points candidates, p⟩) () (valid T points candidates (by omega)) 1 ≤
      ENNReal.ofReal (min (∑ j, P.specialistCost j)
        (P.nearCost + P.missing.mean P.specialistCost)) :=
  sInf_le (native_cost_mem T points candidates P ν hν hz p h)

/-- The same compiled cost-aware selector attains the universal native optimum
on its priced input, with arbitrary fixed real means reflected by rational data.
All competitors use this very oracle and seed; lower accounting is derived. -/
theorem native_optimum (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z) (p : Prices)
      (h : Reflects p P) :
    BatchOptimum.optimum limits (NativeResidualInvoice.sample T points candidates P ν)
      (packed ⟨input T points candidates, p⟩) () (valid T points candidates (by omega)) 1 =
      ENNReal.ofReal (min (∑ j, P.specialistCost j)
        (P.nearCost + P.missing.mean P.specialistCost)) := by
  apply le_antisymm (native_upper T points candidates P ν hν hz p h)
  let c := (finCongr (NativeResidualEncoding.rows_length T points candidates)).trans candidates
  have hdata : (packed ⟨input T points candidates, p⟩).startup.system =
      SourceEncoding.toNative (NativeResidualEncoding.source T points c) := by
    rw [NativeResidualEncoding.source_reindex]
    rfl
  have hlower := NativeResidualOptimum.two_lower_of_mean T points
    (packed ⟨input T points candidates, p⟩) c P limits
    ν (by omega)
    (valid T points candidates (by omega)) hdata rfl hν
  dsimp only [c, packed, input] at hlower
  rwa [NativeResidualInvoice.sample_reindex T points candidates
    (NativeResidualEncoding.rows_length T points candidates)] at hlower

end Cslib.Probability.StochasticOracle.NativeResidualRealChoice
