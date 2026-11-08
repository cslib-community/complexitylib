/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Edge.Solver.Storage
public import Complexity.Computability.PolyTime.CSP.Edge.Solver.Step
import Complexity.Computability.PolyTime.CSP.Edge.Solver.GuardPolyTime
import Complexity.Computability.PolyTime.CSP.Edge.Solver.Initialization
import Complexity.Computability.PolyTime.CSP.Vars
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Native polynomial-time complete explicit-table edge solver

The complete framed input includes binary names and arities, all relation rows, and every list
frame. The guard supplies every model, row-validity and width check internally. The one-child
improvement stack has a list-funded unary clock, full encoded storage bounded by `stateBudget`,
and one native step machine uniform on all raw states. These certificates are original finite
representation and resource bookkeeping for the existing whole-instance algorithm.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.Program

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM

/-- Complete internal guard for one improvement input, including its actual buffer width. -/
@[expose] def inputGuard (input : EdgeForest.Input) : Bool :=
  checkModel input.body && EdgeAugmenting.valid input.body input.labels &&
    decide (input.labels.length = (CSP.occurrences input.body).length)

/-- Total guarded one-improvement program. Every row/model/width check is internal. -/
@[expose] def safeImprove (input : EdgeForest.Input) : Option (List Bool) :=
  if inputGuard input then improve input else none

/-- The internal guard supplies the actual model and valid exact-width occurrence labeling. -/
theorem inputGuard_spec (input : EdgeForest.Input) (h : inputGuard input = true) :
    EdgeInstance input.body ∧ EdgeInstance.EvenConstraints Table.sem input.body ∧
      ValidLabeling Table.sem (EdgeAugmenting.labeling input.body input.labels) ∧
        input.labels.length = (incidenceList input.body).length := by
  have hc : checkModel input.body = true ∧ EdgeAugmenting.valid input.body input.labels = true ∧
      input.labels.length = (CSP.occurrences input.body).length := by
    simpa only [inputGuard, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h
  have hm := checkModel_sound input.body hc.1
  refine ⟨hm.1, hm.2, ?_, ?_⟩
  · simpa only [EdgeAugmenting.valid_eq, decide_eq_true_eq] using hc.2.1
  · simpa only [occurrences_eq_map_incidenceList, List.length_map] using hc.2.2

/-- Every successful guarded improvement has the original actual occurrence width. This
statement covers all raw inputs, without assuming a valid model or a well-formed buffer. -/
theorem safeImprove_width (input : EdgeForest.Input) {bits : List Bool}
    (h : safeImprove input = some bits) : bits.length = (incidenceList input.body).length := by
  unfold safeImprove at h
  split at h
  next hg =>
    rw [improve_eq input (inputGuard_spec input hg).2.2.2] at h
    obtain ⟨f, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact List.length_map f
  next => contradiction

/-- The guarded wrapper agrees with the unguarded mathematical improvement on its actual
model. Validity and width are checked by the wrapper itself on raw inputs. -/
theorem safeImprove_buffer (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) (hf : ValidLabeling Table.sem f)
    (hM : EdgeInstance.EvenConstraints Table.sem F) :
    safeImprove ⟨F, buffer f⟩ = improve ⟨F, buffer f⟩ := by
  have hm : checkModel F = true := checkModel_eq_true F |>.mpr ⟨hF, hM⟩
  simp [safeImprove, inputGuard, hm, EdgeAugmenting.valid_eq,
    hf, buffer, EdgeAugmenting.labeling_map, occurrences_eq_map_incidenceList]

/-- The full stack-storage budget is itself native polynomial-time in unary on every raw CSP.
Its computation scans actual lists and complete encoded names, never an interval of labels. -/
theorem computableInPolyTime_stateBudget : ComputableInPolyTime stateBudget
    (encCSP encTable encNat) encUnary := by
  have hv := computableInPolyTime_length_vars encTable encNat
  have hl : ComputableInPolyTime (fun F : CSP Table ℕ => F.length)
      (encCSP encTable encNat) encUnary := ComputableInPolyTime.length_list _
  have he : ComputableInPolyTime (fun F : CSP Table ℕ => (encCSP encTable encNat F).length)
      (encCSP encTable encNat) encUnary := ComputableInPolyTime.length_bits.comp
    (ComputableInPolyTime.of_eq (encOut := encBits) (fun _ => rfl))
  have hget := encTable_rows_deg.computableInPolyTime
  have hr : ComputableInPolyTime
      (fun F : CSP Table ℕ => F.flatMap fun c => c.1.rows)
      (encCSP encTable encNat) (encList (encList encBool)) := by fun_prop
  have hc : ComputableInPolyTime Size.rowCount (encCSP encTable encNat) encUnary := by
    unfold Size.rowCount
    simpa only [Function.comp_def, List.length_flatMap] using
      (ComputableInPolyTime.length_list (encList encBool)).comp hr
  unfold stateBudget frameBudget inputBudget walkBudget Size.bodyBudget Size.nameBudget
    Size.rowBudget
  fun_prop

/-- Full framed stack storage is polynomial in the complete framed original input length. -/
theorem polyBounded_stateBudget : PolyBounded
    (fun F : CSP Table ℕ => (encCSP encTable encNat F).length) stateBudget := by
  simpa only [encUnary_apply, List.length_replicate] using
    computableInPolyTime_stateBudget.polyBounded_length

end Cslib.Complexity.CSP.EdgeSolver.Program
