/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of later actual input canonical means)
import Complexity.Foundations.Probability.HierarchyLaterInputMean
import all ComplexityTests.HierarchyCanonicalRange
import all ComplexityTests.HierarchyProductMean

/-!
The actual first later input retains a genuinely positive correction and product.
Its canonical mean is strictly larger than the signed residual, even on the identity
base where that residual simplifies to the base. The request has unequal source and
terminal rates and inherited nonempty suffixes. These are canonical finite means,
not executed later RAW accuracy or a recursive joint IH.
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
namespace LaterInputMeanRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

private def iteration : Fin HP.k := ⟨1, CanonicalRangeRegression.later_iteration HP⟩
private def data := PolynomialBudgetHistory.data HP
private def request : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  { ProductMeanRegression.request HP with task := .row 0 (.input (iteration HP)) }
private def E : Matrix (ZMod 5) (ZMod 5) ℝ :=
  HP.toHierarchyParams.correctionIter (canonicalChannel id (rate 0))
    (canonicalChannel id (rate 0)) (rate 0) (data HP).base 1

private lemma correction_one (x : ZMod 5) : E HP x x = HP.Q 1 := by
  unfold E
  rw [HP.toHierarchyParams.correctionIter_succ_apply]
  have hm := PilotTask.value_maximum_eq_zero HP.toHierarchyParams
    (canonicalChannel id (rate 0)) (canonicalChannel id (rate 0)) (rate 0) (data HP).base
    (by simpa only [ZMod.card] using ProductMeanRegression.detector_rank HP) HP.k
  erw [PilotTask.value_maximum_last] at hm
  rw [hm]
  simp only [Pi.zero_apply, HP.γ_one 0 (by norm_num), mul_one]
  norm_num [HierarchyParams.correctionInput, HierarchyParams.correctionIter,
    cutoffCorrectionIter, data, PolynomialBudgetHistory.data, PolynomialBudgetHistory.base, rate]

private lemma canonical_mean (x y : ZMod 5) :
    rowSliceMean
      (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
      (fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y)
      (fun σ x y => ∑ bin ∈ (data HP).bins,
        HierarchyTask.rawPositiveSample (channels (data HP).padding) 0 bin
          (.input (iteration HP)) (request HP).source (BudgetData.midpoint (request HP))
          (request HP).terminal ((data HP).binRate bin)
          (fun q => (data HP).residualCanonicalChild bin q σ) x y) x y =
      (data HP).canonicalPreparationInput false (iteration HP) (request HP) x y := by
  apply (data HP).canonicalLaterInput_mean 1
    (by ext bin; simp [data, PolynomialBudgetHistory.data]; omega) rfl rfl rfl
    (by change (1 : ZMod 5) ≠ 0; norm_num) SourceRegression.horizon (by decide)
    (request HP) 0 2 (by decide) 1 0 [1] [2, 3] rfl rfl (by decide) (by decide)
    (ProductMeanRegression.nonneg HP) (ProductMeanRegression.mass HP)
    (ProductMeanRegression.stage_bound HP) (iteration HP) 0 rfl x y
    (ProductMeanRegression.cover HP y)

-- This prevents replacing the later input reference by the signed residual or by C.
example (x : ZMod 5) :
    0 < E HP x x ∧ 0 < (E HP * (data HP).base) x x ∧
    (data HP).canonicalPreparationInput false (iteration HP) (request HP) x x =
      1 + HP.Q 1 ∧
    (data HP).base x x + (E HP * (data HP).base) x x - E HP x x = 1 := by
  have hE := correction_one HP x
  have hmul : E HP * (data HP).base = E HP := Matrix.mul_one _
  have hG : (data HP).canonicalPreparationInput false (iteration HP) (request HP) x x =
      1 + HP.Q 1 := by
    change (data HP).base x x + (E HP * (data HP).base) x x = _
    rw [hmul, hE]
    rw [show (data HP).base x x = 1 from Matrix.one_apply_eq x]
  refine ⟨hE ▸ CutoffRegression.Q_one_pos HP, ?_, hG, ?_⟩
  · rw [hmul, hE]; exact CutoffRegression.Q_one_pos HP
  · rw [hmul, hE]
    rw [show (data HP).base x x = 1 from Matrix.one_apply_eq x]
    ring

-- Complete finite-bin canonical consumer at the actual requested iteration.
example (x : ZMod 5) :
    rowSliceMean
      (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
      (fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y)
      (fun σ x y => ∑ bin ∈ (data HP).bins,
        HierarchyTask.rawPositiveSample (channels (data HP).padding) 0 bin
          (.input (iteration HP)) (request HP).source (BudgetData.midpoint (request HP))
          (request HP).terminal ((data HP).binRate bin)
          (fun q => (data HP).residualCanonicalChild bin q σ) x y) x x =
      1 + HP.Q 1 := by
  rw [canonical_mean HP]
  change (data HP).base x x + (E HP * (data HP).base) x x = _
  rw [show E HP * (data HP).base = E HP from Matrix.mul_one _, correction_one HP,
    show (data HP).base x x = 1 from Matrix.one_apply_eq x]

example :
    let r := request HP
    let Q := HierarchyTask.rawRequests 0 0 (.input (iteration HP)) r.source
      (BudgetData.midpoint r) r.terminal ((data HP).binRate 0)
    Q.left.task = .row 0 (.normalized ⟨0, HP.k_pos⟩) ∧ Q.negative = none ∧
      Q.right.source = BudgetData.midpoint r ∧
      Q.left.source = gridChannel 0 1 [1] ∧ Q.right.source.suffix = [] ∧
      r.terminal = gridChannel 2 0 [2, 3] := by
  dsimp only
  constructor
  · change HierarchyTask.correctionAtomTask 0 false
      (⟨1, by have := HP.k_pos; omega⟩ : Fin (HP.k + 1)) = _
    rw [show (⟨1, by have := HP.k_pos; omega⟩ : Fin (HP.k + 1)) =
      (⟨0, HP.k_pos⟩ : Fin HP.k).succ from rfl]
    simp only [HierarchyTask.correctionAtomTask, Fin.cases_succ,
      Bool.false_eq_true, ↓reduceIte]
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end LaterInputMeanRegression
