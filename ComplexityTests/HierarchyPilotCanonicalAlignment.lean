/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (regression of incomplete pilot canonical dispatch)
import all ComplexityTests.HierarchyLaterInputMean

/-!
# Requested pilot children are not actual correction children

At input one, actual and pilot requests call different normalized constructors.
The existing actual canonical dispatcher returns zero for the pilot constructor,
although the genuine requested pilot correction and its product with the base are
strictly positive. This is a regression of the missing bridge, not a new pilot
reference or an executed accuracy/payment theorem.

The P=5 fixture retains source suffix [1], terminal suffix [2,3], and the empty
right-source reset. Source and terminal rates differ. Its zero detector is proved
from the genuine rank, not supplied as a correction or maximum assumption.
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
namespace PilotCanonicalAlignmentRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

private def iteration : Fin HP.k := ⟨1, CanonicalRangeRegression.later_iteration HP⟩
private def data := PolynomialBudgetHistory.data HP
private def request : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  { ProductMeanRegression.request HP with task := .row 0 (.pilotInput (iteration HP)) }
private def calls (pilot : Bool) :=
  HierarchyTask.rawRequests 0 0
    (if pilot then .pilotInput (iteration HP) else .input (iteration HP))
    (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
    ((data HP).binRate 0)
private def E : Matrix (ZMod 5) (ZMod 5) ℝ :=
  PilotTask.value HP.toHierarchyParams (canonicalChannel id (rate 0))
    (canonicalChannel id (rate 0)) (rate 0) (data HP).base (.correction 1)

private lemma pilot_correction_one (x : ZMod 5) : E HP x x = HP.Q 1 := by
  unfold E
  rw [PilotTask.value_correction_succ]
  have hm := PilotTask.value_maximum_eq_zero HP.toHierarchyParams
    (canonicalChannel id (rate 0)) (canonicalChannel id (rate 0)) (rate 0) (data HP).base
    (by simpa only [ZMod.card] using ProductMeanRegression.detector_rank HP) 1
  rw [hm]
  simp only [Pi.zero_apply, HP.γ_one 0 (by norm_num), mul_one]
  norm_num [PilotTask.value, pilotInput, pilotCorrection_zero, data,
    PolynomialBudgetHistory.data, PolynomialBudgetHistory.base, rate]

-- The exact later call, rather than an initial-input or final-residual substitution.
example :
    (calls HP true).left.task = .row 0 (.pilotNormalized ⟨0, HP.k_pos⟩) ∧
    (calls HP false).left.task = .row 0 (.normalized ⟨0, HP.k_pos⟩) ∧
    (calls HP true).left.task ≠ (calls HP false).left.task ∧
    (calls HP true).negative = none ∧
    (calls HP true).right.source = BudgetData.midpoint (request HP) ∧
    (calls HP true).right.source.suffix = [] ∧
    (calls HP true).left.source = gridChannel 0 1 [1] ∧
    (request HP).terminal = gridChannel 2 0 [2, 3] := by
  have hi : (iteration HP).castSucc = (⟨0, HP.k_pos⟩ : Fin HP.k).succ := rfl
  simp [calls, HierarchyTask.rawRequests, hi, HierarchyTask.correctionAtomTask,
    request, ProductMeanRegression.request, PolynomialBudgetHistory.request,
    BudgetData.midpoint, gridChannel]

-- A zero fallback cannot be the genuine pilot child: its required correction is positive.
example (σ : Environment 5 3) (x : ZMod 5) :
    (data HP).residualCanonicalChild 0 (calls HP true).left σ x x = 0 ∧
    0 < E HP x x ∧ 0 < (E HP * (data HP).base) x x ∧
    (data HP).canonicalPreparationInput true (iteration HP) (request HP) x x =
      1 + HP.Q 1 := by
  have hz : (data HP).residualCanonicalChild 0 (calls HP true).left σ x x = 0 := by
    have hi : (iteration HP).castSucc = (⟨0, HP.k_pos⟩ : Fin HP.k).succ := rfl
    simp [BudgetData.residualCanonicalChild, canonicalRequestChild, calls,
      HierarchyTask.rawRequests, hi, HierarchyTask.correctionAtomTask]
  have he := pilot_correction_one HP x
  have hmul : E HP * (data HP).base = E HP := Matrix.mul_one _
  refine ⟨hz, he ▸ CutoffRegression.Q_one_pos HP, ?_, ?_⟩
  · rw [hmul, he]
    exact CutoffRegression.Q_one_pos HP
  · change (data HP).base x x + (E HP * (data HP).base) x x = _
    rw [hmul, he, show (data HP).base x x = 1 from Matrix.one_apply_eq x]

end PilotCanonicalAlignmentRegression
