/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeResidualRealMinima
import CslibFrontierTests.StochasticOracleResidualCover
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Actual irrational expected token costs and correlated natural invoices

The five nontrivial source blocks are covered by the same compiled all-specialist
program. Every specialist has expected price sqrt(2), with ordinary natural token
reports. No irrational number is encoded on the program's input or reply tape.
-/

noncomputable section
namespace CslibFrontierTests.StochasticOracleNativeResidualRealCost
open Cslib.Probability StochasticOracle NativeRetention ResidualCover ConcurrentBatch
open NativeResidualRealCost NativeOpenExecution Turing
open scoped NNReal ENNReal

private abbrev blocks := StochasticOracleResidualCover.blocks
private def points : Fin (Fintype.card (Point blocks)) ≃ Point blocks :=
  (Fintype.equivFin _).symm
private def candidates : Fin (Fintype.card (Candidate blocks)) ≃ Candidate blocks :=
  (Fintype.equivFin _).symm
private def parameters : Parameters 5 where
  missing := StochasticOracleResidualCover.parameters.missing
  full_support := StochasticOracleResidualCover.parameters.full_support
  nearCost := 1
  near_pos := by norm_num
  specialistCost _ := Real.sqrt 2
  specialist_pos _ := Real.sqrt_pos.mpr (by norm_num)

-- Arbitrary real means, rather than constant natural invoices identified with prices.
example : NativeBatch.Quantitative.expected (NativeResidualAll.config 1)
    (NativeResidualInvoice.sample blocks points candidates parameters (FixedMeanInvoice.law
      (NativeResidualRealCost.prices parameters))) (NativeResidualRouting.controller false).program
    NativeBatch.Trace.charge 2
    ⟨(NativeResidualRouting.controller false).program.initialConfig
      (GuardedStartup.encoding (NativeResidualAttainment.input blocks points candidates)),
      NativeResidualAttainment.initialMemory⟩ = ENNReal.ofReal (5 * Real.sqrt 2) := by
  rw [native_all_expected_cost blocks points candidates parameters (FixedMeanInvoice.law
    (NativeResidualRealCost.prices parameters)) (NativeResidualRealCost.hasMean parameters)
      (by norm_num) 1 (by norm_num)]
  norm_num [parameters]

example : ((NativeUnboundedExecution.terminal (NativeResidualRouting.controller false).program
    (environment (NativeResidualAll.config 1)
      (NativeResidualInvoice.sample blocks points candidates parameters (FixedMeanInvoice.law
        (NativeResidualRealCost.prices parameters))))
    ⟨(NativeResidualRouting.controller false).program.initialConfig
      (GuardedStartup.encoding (NativeResidualAttainment.input blocks points candidates)),
      NativeResidualAttainment.initialMemory⟩).map
      (BatchOutput.certified (NativeResidualAll.config 1)
        (NativeResidualAttainment.input blocks points candidates).startup.system
        (NativeResidualAttainment.valid blocks points candidates (by norm_num)))) true = 1 :=
  native_all_certified blocks points candidates parameters (FixedMeanInvoice.law
    (NativeResidualRealCost.prices parameters)) (by norm_num) 1 (by norm_num)

-- The original infimum still ranges over every admitted native competitor.
example : BatchOptimum.optimum (NativeResidualAll.config 1)
    (NativeResidualInvoice.sample blocks points candidates parameters (FixedMeanInvoice.law
      (NativeResidualRealCost.prices parameters))) (NativeResidualAttainment.input blocks points
      candidates)
    () (NativeResidualAttainment.valid blocks points candidates (by norm_num)) 1 ≤
      ENNReal.ofReal (5 * Real.sqrt 2) := by
  have h := native_all_upper blocks points candidates parameters (FixedMeanInvoice.law
    (NativeResidualRealCost.prices parameters)) (NativeResidualRealCost.hasMean parameters)
      (by norm_num) 1 (by norm_num)
  norm_num [parameters] at h ⊢
  exact h

-- The adaptive program also handles an irrational specialist mean, with a fresh
-- invoice draw after seeing the near residual.
example : NativeBatch.Quantitative.expected NativeResidualAttainment.limits
    (NativeResidualInvoice.sample blocks points candidates parameters (FixedMeanInvoice.law
      (NativeResidualRealCost.prices parameters))) (NativeResidualRouting.controller true).program
    NativeBatch.Trace.charge 3
    ⟨(NativeResidualRouting.controller true).program.initialConfig
      (GuardedStartup.encoding (NativeResidualAttainment.input blocks points candidates)),
      NativeResidualAttainment.initialMemory⟩ = ENNReal.ofReal (1 + Real.sqrt 2) := by
  rw [NativeResidualRealAdaptive.native_expected_cost blocks points candidates parameters
    (FixedMeanInvoice.law (NativeResidualRealCost.prices parameters))
      (NativeResidualRealCost.hasMean parameters)
    (by norm_num)]
  norm_num [parameters, StochasticOracleResidualCover.parameters,
    Cslib.Optimization.OneConstraint.Distribution.mean, Fin.sum_univ_succ]
  congr 1
  ring

-- The lower bound quantifies over all admitted native competitors on this same
-- oracle: these are equalities of the existing native infima, not only feasible bills.
example : BatchOptimum.optimum NativeResidualAttainment.limits
    (NativeResidualInvoice.sample blocks points candidates parameters (FixedMeanInvoice.law
      (NativeResidualRealCost.prices parameters)))
    (NativeResidualAttainment.input blocks points candidates)
    () (NativeResidualAttainment.valid blocks points candidates (by norm_num)) 1 =
      ENNReal.ofReal (1 + Real.sqrt 2) := by
  have hs : 1 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hmean : parameters.missing.mean parameters.specialistCost = Real.sqrt 2 := by
    norm_num [parameters, StochasticOracleResidualCover.parameters,
      Cslib.Optimization.OneConstraint.Distribution.mean, Fin.sum_univ_succ]
    ring
  have hsum : (∑ j, parameters.specialistCost j) = 5 * Real.sqrt 2 := by
    norm_num [parameters]
  rw [NativeResidualRealMinima.native_optimum blocks points candidates parameters
    (FixedMeanInvoice.law (NativeResidualRealCost.prices parameters))
      (NativeResidualRealCost.hasMean parameters) (by norm_num),
    hmean, hsum]
  change ENNReal.ofReal (min (5 * Real.sqrt 2) (1 + Real.sqrt 2)) = _
  rw [min_eq_right (by nlinarith)]

example : BatchOptimum.optimum (NativeResidualAll.config 1)
    (NativeResidualInvoice.sample blocks points candidates parameters (FixedMeanInvoice.law
      (NativeResidualRealCost.prices parameters)))
    (NativeResidualAttainment.input blocks points candidates)
    () (NativeResidualAttainment.valid blocks points candidates (by norm_num)) 1 =
      ENNReal.ofReal (5 * Real.sqrt 2) := by
  rw [NativeResidualRealMinima.native_one_optimum blocks points candidates parameters
    (FixedMeanInvoice.law (NativeResidualRealCost.prices parameters))
      (NativeResidualRealCost.hasMean parameters) (by norm_num)]
  norm_num [parameters]

private def scaled : Parameters 5 :=
  { parameters with nearCost := 2 * Real.sqrt 2, near_pos := by positivity }

-- The source's nontrivial 5/3 adaptivity ratio holds even at irrational prices.
example :
    (BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualInvoice.sample blocks points candidates scaled (FixedMeanInvoice.law
        (NativeResidualRealCost.prices scaled)))
      (NativeResidualAttainment.input blocks points candidates)
      () (NativeResidualAttainment.valid blocks points candidates (by norm_num)) 1).toReal /
    (BatchOptimum.optimum NativeResidualAttainment.limits
      (NativeResidualInvoice.sample blocks points candidates scaled (FixedMeanInvoice.law
        (NativeResidualRealCost.prices scaled)))
      (NativeResidualAttainment.input blocks points candidates)
      () (NativeResidualAttainment.valid blocks points candidates (by norm_num)) 1).toReal =
        5 / 3 := by
  have h := NativeResidualRealMinima.native_linear_ratio blocks points candidates scaled
    (FixedMeanInvoice.law (NativeResidualRealCost.prices scaled))
      (NativeResidualRealCost.hasMean scaled)
    (by norm_num) (Real.sqrt 2) 2 (Real.sqrt_pos.mpr (by norm_num))
    (fun _ => rfl) rfl (by norm_num)
  norm_num at h ⊢
  exact h

-- Nonintegral fixed costs can give correlated invoices: only one coordinate can
-- receive the positive cap in a joint draw, without any independence hypothesis.
example (choice : Option (Fin 2)) :
    FixedMeanInvoice.invoice (fun _ : Fin 2 => (1 / 2 : ℝ≥0)) choice 0 = 0 ∨
      FixedMeanInvoice.invoice (fun _ : Fin 2 => (1 / 2 : ℝ≥0)) choice 1 = 0 := by
  by_cases h : choice = some (0 : Fin 2)
  · right
    simp [FixedMeanInvoice.invoice, h]
  · left
    simp [FixedMeanInvoice.invoice, h]

example (i : Fin 2) :
    (FixedMeanInvoice.choice (fun _ : Fin 2 => (1 / 2 : ℝ≥0))).mean
      (fun j => (FixedMeanInvoice.invoice (fun _ : Fin 2 => (1 / 2 : ℝ≥0)) j i : ℝ)) = 1 / 2 := by
  simpa using FixedMeanInvoice.mean_call (fun _ : Fin 2 => (1 / 2 : ℝ≥0)) i

-- Both no opportunities and a zero mean have harmless completions.
example : (FixedMeanInvoice.choice (fun i : Fin 0 => Fin.elim0 i)).mean
    (fun j => ((∑ i : Fin 0, FixedMeanInvoice.invoice (fun i : Fin 0 => Fin.elim0 i) j i : ℕ) : ℝ))
      = 0 := by
  simp [Cslib.Optimization.OneConstraint.Distribution.mean]

example (i : Fin 1) : (FixedMeanInvoice.choice (fun _ : Fin 1 => 0)).mean
    (fun j => (FixedMeanInvoice.invoice (fun _ : Fin 1 => 0) j i : ℝ)) = 0 := by
  simpa using FixedMeanInvoice.mean_call (fun _ : Fin 1 => 0) i

/-- Unit prices, so a deterministic natural invoice also has the source means. -/
private def unit : Parameters 5 where
  missing := StochasticOracleResidualCover.parameters.missing
  full_support := StochasticOracleResidualCover.parameters.full_support
  nearCost := 1
  near_pos := by norm_num
  specialistCost _ := 1
  specialist_pos _ := by norm_num

/-- A genuinely different fee law with the same means: a fair coin chooses between
the deterministic unit invoice and the constructed random `FixedMeanInvoice` law. -/
private def coinLaw : PMF (Fin 6 → ℕ) :=
  (PMF.uniformOfFintype Bool).bind fun b =>
    if b then PMF.pure (fun _ => 1) else FixedMeanInvoice.law (prices unit)

private theorem coinLaw_hasMean : NativeResidualInvoice.HasMean unit coinLaw :=
  hasMean_bind _ _ fun b => by
    cases b
    · exact hasMean unit
    · exact NativeResidualInvoice.hasMean_pure unit _ fun i => by
        cases h : finSuccEquiv 5 i <;> simp [unit]

-- The attained native two-turn optimum holds for this mixed fee law too: min(5, 1 + 1) = 2.
example : BatchOptimum.optimum NativeResidualAttainment.limits
    (NativeResidualInvoice.sample blocks points candidates unit coinLaw)
    (NativeResidualAttainment.input blocks points candidates)
    () (NativeResidualAttainment.valid blocks points candidates (by norm_num)) 1 = 2 := by
  rw [NativeResidualRealMinima.native_optimum blocks points candidates unit coinLaw
    coinLaw_hasMean (by norm_num)]
  have hmean : unit.missing.mean unit.specialistCost = 1 :=
    Cslib.Optimization.OneConstraint.Distribution.mean_const _ _
  simp only [unit] at hmean ⊢
  rw [hmean]
  norm_num

end CslibFrontierTests.StochasticOracleNativeResidualRealCost
