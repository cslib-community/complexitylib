/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyBudgetEvaluator

/-!
# Structural execution of scheduled raw tasks

Every raw task has a literal zero sample at budget zero. Later pilot inputs, actual inputs
and the stage-zero residual dispatch to the existing dyadic RAW program. Availability
below is conditional on the two literal endpoint samples of each nonempty group and on
valid grid completion; equal-budget groups make no child calls. No canonical accuracy,
inactive-child availability or native workspace bound is inferred.
The existing `pairedSample_of_errors` API in `HierarchyApproximateHistory` retains any
error of the zero approximation against a coarse canonical sample.

The execution plumbing is original, over the existing shared-history implementation
inspired by [OpenAI2026LogSpace, Sections 7.4–7.5]. It does not close the paper's simultaneous
recursive invariant.

## Main results

* `sample_zero`: all raw constructors share the literal zero boundary.
* `completedGroup_available`: actual endpoint samples suffice for one common group walk.
* `raw_available`: all scheduled groups execute from those same endpoint obligations.
* `step_pilotInput`, `step_input`, `step_residual`: active raw constructor dispatch.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- The sample boundary executes no children, independently of the raw task or ray. -/
theorem sample_zero
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (t : HierarchyTask.RawTask HP.k) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (bin : Option ℕ) : B.sample history 0 t r bin = some 0 := by
  simp only [sample, ↓reduceIte]

/-- Only the two actual samples of a nonempty group require availability. The grid
request supplies completion on the original source and usage suffixes. -/
theorem completedGroup_available
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s u : Fin 3) (hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel u ku su)
    (hsamples : ∀ bin ∈ B.rays t,
      let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      fine ≠ coarse →
        (∃ A, B.sample history fine t r bin = some A) ∧
        (∃ C, B.sample history coarse t r bin = some C)) :
    ∃ A, B.completedGroup history M d t r = some A := by
  have hp (bin : Option ℕ) (hb : bin ∈ B.rays t) :
      ∃ A, B.pairedSample history M d t r bin = some A := by
    by_cases he : LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) =
        LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
    · exact ⟨0, by simp only [pairedSample, he, ↓reduceIte]⟩
    · obtain ⟨⟨A, hA⟩, ⟨C, hC⟩⟩ := hsamples bin hb he
      exact ⟨A - C, by
        simp only [pairedSample, he, ↓reduceIte, hA, hC, bind, Option.bind_some, pure]⟩
  let f := fun bin => (B.pairedSample history M d t r bin).getD 0
  have hinputs : (B.rays t).mapM (B.pairedSample history M d t r) =
      some ((B.rays t).map f) := by
    apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro bin hb
    obtain ⟨A, hA⟩ := hp bin hb
    simp only [f, hA, Option.getD_some]
  unfold completedGroup
  split_ifs
  · exact ⟨0, rfl⟩
  · simp only [hinputs, bind, Option.bind_some]
    exact ⟨_, B.complete_grid M r s u hsu ks ku ss su hs hu _ d⟩

/-- Structural availability of the literal RAW program. The hypotheses concern only
executed samples at their own budgets; canonical error bounds are separate inputs to
subsequent analytic clients. -/
theorem raw_available
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s u : Fin 3) (hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel u ku su)
    (hsamples : ∀ j < Nat.log2 M + 1, ∀ bin ∈ B.rays t,
      let d := dyadicSlack (Nat.log2 M + 1) j
      let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      fine ≠ coarse →
        (∃ A, B.sample history fine t r bin = some A) ∧
        (∃ C, B.sample history coarse t r bin = some C)) :
    ∃ A, B.raw history M t r = some A := by
  let f := fun j => (B.completedGroup history M (dyadicSlack (Nat.log2 M + 1) j) t r).getD 0
  have hgroups : (List.range (Nat.log2 M + 1)).mapM (fun j =>
      B.completedGroup history M (dyadicSlack (Nat.log2 M + 1) j) t r) =
        some ((List.range (Nat.log2 M + 1)).map f) := by
    apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro j hj
    obtain ⟨A, hA⟩ := B.completedGroup_available history M _ t r s u hsu ks ku ss su hs hu
      (hsamples j (List.mem_range.mp hj))
    simp only [f, hA, Option.getD_some]
  exact ⟨_, by rw [raw, hgroups]; rfl⟩

/-- Active pilot inputs of every iteration dispatch to the same scheduled RAW program. -/
theorem step_pilotInput
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (i : Fin HP.k)
    (hr : r.task = .row 0 (.pilotInput i)) (hp : 0 < B.requestPrecision M r) :
    B.step history M r = (B.raw history M (.pilotInput i) r).map .row := by
  simp only [step, hr, hp, ↓reduceIte, ite_self]

/-- Later actual inputs keep their actual correction route. Iteration zero deliberately
retains the established pilot-zero equality of the public evaluator. -/
theorem step_input
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (i : Fin HP.k)
    (hr : r.task = .row 0 (.input i)) (hi : i.val ≠ 0)
    (hp : 0 < B.requestPrecision M r) :
    B.step history M r = (B.raw history M (.input i) r).map .row := by
  simp only [step, hr, hi, hp, ↓reduceIte]

/-- Active residuals use the scheduled positive rays and their single negative ray. -/
theorem step_residual
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .residual 0) (hp : 0 < B.requestPrecision M r) :
    B.step history M r = (B.raw history M .residual r).map .row := by
  simp only [step, hr, hp, ↓reduceIte]

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
