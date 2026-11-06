/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of requested-iterate pilot means)
import Complexity.Foundations.Probability.HierarchyPilotMean
import all ComplexityTests.HierarchyPilotCanonicalAlignment

/-!
# Genuine nonzero pilot mean at requested input one

The actual requested left child has narrower source rate, inherited copy suffixes,
its own preparation and usage mask. Its normalized mean is positive, whereas the
unchanged actual-only dispatcher returns zero. The right child resets the source.
A second normalization index checks the current maximum at two, rather than silently
restricting the bridge to the initial normalization. These are true-child mean and
request tests, not executed-child accuracy or recursive availability certificates.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace PilotMeanRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)
private def data := PolynomialBudgetHistory.data HP
private def request := (PilotCanonicalAlignmentRegression.calls HP true).left
private lemma admissible : Admissible (request HP) := by
  exact ⟨by change (0 : Fin 3) ≠ 1; decide, rfl, rfl⟩

-- The requested input-one child is genuinely pilotNormalized zero, with nonzero E_1.
private lemma mean (x : ZMod 5) :
    rowSliceMean (fun σ v => (request HP).source.retains (channels 1) σ v)
      (fun σ v => (request HP).usage.retains (channels 1) σ v)
      (pilotChild HP 1 id (request HP) (admissible HP) (data HP).base 0) x x = HP.Q 1 := by
  have hm := pilotChild_usage_mean HP 1 id (request HP) (admissible HP)
    (by norm_num) Function.injective_id SourceRegression.horizon
    (s := 1) (k := 0) (u := 0) (by decide) (by decide) rfl rfl rfl
    (data HP).base (ProductMeanRegression.nonneg HP)
    (ProductMeanRegression.mass HP)
    (ProductMeanRegression.stage_bound HP) HP.k_pos x x
  change _ = PilotCanonicalAlignmentRegression.E HP x x / rate 0 at hm
  rw [PilotCanonicalAlignmentRegression.pilot_correction_one HP x] at hm
  simpa only [rate, pow_zero, inv_one, one_pow, div_one, id_eq] using hm

-- The normalized mean and its genuine E_1*C product are nonzero at input one.
example (x : ZMod 5) :
    0 < rowSliceMean (fun σ v => (request HP).source.retains (channels 1) σ v)
      (fun σ v => (request HP).usage.retains (channels 1) σ v)
      (pilotChild HP 1 id (request HP) (admissible HP) (data HP).base 0) x x ∧
    0 < (PilotCanonicalAlignmentRegression.E HP * (data HP).base) x x := by
  rw [mean HP x]
  have hmul : PilotCanonicalAlignmentRegression.E HP * (data HP).base =
      PilotCanonicalAlignmentRegression.E HP := Matrix.mul_one _
  rw [hmul, PilotCanonicalAlignmentRegression.pilot_correction_one HP x]
  exact ⟨CutoffRegression.Q_one_pos HP, CutoffRegression.Q_one_pos HP⟩

-- This is also an actual noninitial normalization index, not a zero-only bridge.
example (x y : ZMod 5) :
    rowSliceMean (fun σ v => (request HP).source.retains (channels 1) σ v)
      (fun σ v => (request HP).usage.retains (channels 1) σ v)
      (pilotChild HP 1 id (request HP) (admissible HP) (data HP).base 1) x y =
      PilotTask.value HP.toHierarchyParams (canonicalChannel id (rate 0))
        (canonicalChannel id (rate 0)) (rate 0) (data HP).base (.correction 2) x y := by
  have hm := pilotChild_usage_mean HP 1 id (request HP) (admissible HP)
    (by norm_num) Function.injective_id SourceRegression.horizon
    (s := 1) (k := 0) (u := 0) (by decide) (by decide) rfl rfl rfl
    (data HP).base (ProductMeanRegression.nonneg HP) (ProductMeanRegression.mass HP)
    (ProductMeanRegression.stage_bound HP) (CanonicalRangeRegression.later_iteration HP) x y
  change _ = PilotTask.value HP.toHierarchyParams (canonicalChannel id (rate 0))
    (canonicalChannel id (rate 0)) (rate 0) (data HP).base (.correction 2) x y / rate 0 at hm
  simpa only [show rate 0 = 1 by norm_num [rate], div_one, id_eq] using hm

-- Separate narrower usage retains the same canonical target and its own normalization.
example (x : ZMod 5) :
    let r := { request HP with usage := gridChannel 1 1 [] }
    rowSliceMean (fun σ v => r.source.retains (channels 1) σ v)
      (fun σ v => r.usage.retains (channels 1) σ v)
      (pilotChild HP 1 id r (admissible HP) (data HP).base 0) x x = HP.Q 1 := by
  dsimp only
  have hm := pilotChild_usage_mean HP 1 id
    { request HP with usage := gridChannel 1 1 [] } (admissible HP)
    (by norm_num) Function.injective_id SourceRegression.horizon
    (s := 1) (k := 0) (u := 1) (by decide) (by decide) rfl rfl rfl
    (data HP).base (ProductMeanRegression.nonneg HP) (ProductMeanRegression.mass HP)
    (ProductMeanRegression.stage_bound HP) HP.k_pos x x
  change _ = PilotCanonicalAlignmentRegression.E HP x x / rate 0 at hm
  rw [PilotCanonicalAlignmentRegression.pilot_correction_one HP x] at hm
  simpa only [rate, pow_zero, inv_one, one_pow, div_one, id_eq] using hm

-- Index one uses pilotInput one and maximum two, preserving the actual source PREP.
example (σ : Environment 5 3) :
    pilotChild HP 1 id (request HP) (admissible HP) (data HP).base 1 σ =
      correctionRequest 1 id (request HP) (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        (fun _ => pilotRaw HP 1 id (request HP) (admissible HP) (data HP).base 1)
        (pilotPreparation HP 1 id (request HP) (admissible HP) (data HP).base 1)
        (fun _ => PilotTask.value HP.toHierarchyParams
          (stageSource 1 id (request HP) (admissible HP)) (splitTerminal 1 id (request HP))
          (request HP).terminal.rate (data HP).base (.maximum 2)) σ := rfl

-- The source/usage mask is not replaced by the broad terminal mask.
example (σ : Environment 5 3) (x y : ZMod 5)
    (hy : ¬ splitUsage 1 id (request HP) (σ (request HP).terminal.role) y) :
    pilotChild HP 1 id (request HP) (admissible HP) (data HP).base 1 σ x y = 0 :=
  pilotChild_zero_off_usage HP 1 id (request HP) (admissible HP) (data HP).base 1 σ x y hy

end PilotMeanRegression
