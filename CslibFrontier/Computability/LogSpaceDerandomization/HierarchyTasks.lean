/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.DenseRowRecipes
import all CslibFrontier.Computability.LogSpaceDerandomization.DetectedHierarchy
import all CslibFrontier.Computability.LogSpaceDerandomization.HierarchyParams
import all CslibFrontier.Computability.LogSpaceDerandomization.CorrectionHierarchy

/-!
# Bounded cross-stage hierarchy tasks

The dependency order of [OpenAI2026LogSpace, Section 7.1], revision `7ef5c0cc`, connects
stage-local pilot and actual correction tasks to the existing hierarchy of Section 4.5.
Iteration indices here are finite: completed corrections and maxima have indices in
`Fin (k + 1)`, while inputs, preparations and normalized rows have indices in `Fin k`.
Thus a normalized pilot's newly completed maximum still belongs to the same stage block.
The block size is computed from the local constructor bound, not postulated for unbounded tasks.

The matrix output uses the actual residual and copy stage, and the reward output uses (4.31).
At positive stages, the base matrix and previous reward are calls to these earlier outputs.
The semantic equations use `DetectedHierarchy` itself; no second hierarchy is introduced.
Preparation and normalization retain their whole-function recipes. Channel roles, usage rates,
inherited suffixes and midpoint source release retain the contracts of `CorrectionRowTask`.

This is a deterministic cross-stage hierarchy/reward client, not the complete stochastic task
assembly: routed direct/residual bin tables, fixed-copy-symbol suffix extension and their
cross-stage role/rate tuples remain open. There is no error recurrence, budget-recursive
estimator, root regularity or native complexity claim for these noncomputable functions.

## Main definitions

* `Matrix.HierarchyParams.BoundedRowTask`: finite local iteration indices.
* `Matrix.HierarchyParams.HierarchyTask`: stage plus bounded row or next-matrix constructor.

## Main results

* `Matrix.HierarchyParams.HierarchyTask.rank_lt_of_dependency`: global computed decrease.
* `Matrix.hierarchyTask_base_succ`: the base matrix calls the preceding matrix output.
* `Matrix.hierarchyTask_previousReward_succ`: the reward leaf calls the preceding reward output.
-/

public section

open Finset
open scoped BigOperators

namespace Matrix.HierarchyParams

/-- Local constructors with only the iterations needed by a `k`-step hierarchy stage. -/
inductive BoundedRowTask (k : ℕ) where
  | base
  | pilotInput (i : Fin k)
  | score (i : Fin k)
  | detector (i : Fin k)
  | maximum (i : Fin (k + 1))
  | pilotCorrection (i : Fin (k + 1))
  | pilotPreparation (i : Fin k)
  | pilotNormalized (i : Fin k)
  | correction (i : Fin (k + 1))
  | input (i : Fin k)
  | preparation (i : Fin k)
  | normalized (i : Fin k)
  | previousReward
  | weights
  | reward (i : Fin (k + 1))
  | projectedReward (i : Fin (k + 1))
  deriving DecidableEq, Fintype

namespace BoundedRowTask

/-- Forget the finite index proofs into the existing unified local family. -/
abbrev localTask {k : ℕ} : BoundedRowTask k → CorrectionRowTask
  | .base => .pilot (.pilot .base)
  | .pilotInput i => .pilot (.pilot (.input i))
  | .score i => .pilot (.pilot (.score i))
  | .detector i => .pilot (.pilot (.detector i))
  | .maximum i => .pilot (.pilot (.maximum i))
  | .pilotCorrection i => .pilot (.pilot (.correction i))
  | .pilotPreparation i => .pilot (.preparation i)
  | .pilotNormalized i => .pilot (.normalized i)
  | .correction i => .correction i
  | .input i => .input i
  | .preparation i => .preparation i
  | .normalized i => .normalized i
  | .previousReward => .previousReward
  | .weights => .weights
  | .reward i => .reward i
  | .projectedReward i => .projectedReward i

/-- Every constructor really fits the stage block, including both stochastic families. -/
theorem rank_le {k : ℕ} (t : BoundedRowTask k) : t.localTask.rank k ≤ 20 * k + 26 := by
  apply CorrectionRowTask.rank_le
  cases t <;>
    simp only [CorrectionRowTask.iteration, PilotRowTask.iteration,
      PilotTask.iteration] <;> omega

/-- Complete finite child recipes. Successor maxima/corrections use the preceding finite
index; preparations and normalized rows never request an iteration beyond `k`. -/
@[expose] def children {k : ℕ} : BoundedRowTask k → List (BoundedRowTask k)
  | .base | .previousReward => []
  | .pilotInput i => [.base, .pilotCorrection i.castSucc]
  | .score i => [.pilotInput i]
  | .detector i => [.score i]
  | .maximum i => Fin.cases [] (fun j => [.maximum j.castSucc, .detector j]) i
  | .pilotCorrection i => Fin.cases []
      (fun j => [.pilotInput j, .maximum j.succ, .pilotNormalized j]) i
  | .pilotPreparation i => [.pilotInput i]
  | .pilotNormalized i => [.pilotInput i, .pilotPreparation i, .maximum i.succ]
  | .correction i => Fin.cases []
      (fun j => [.input j, .maximum (Fin.last k), .normalized j]) i
  | .input i => [.base, .correction i.castSucc]
  | .preparation i => [.input i]
  | .normalized i => [.input i, .preparation i, .maximum (Fin.last k)]
  | .weights => [.maximum (Fin.last k)]
  | .reward i => [.previousReward, .correction i]
  | .projectedReward i => Fin.cases [.weights, .reward 0]
      (fun j => [.weights, .reward j.succ, .previousReward, .normalized j]) i

/-- Forgetting finite index proofs preserves every local dependency, with no missing child. -/
theorem children_localTask {k : ℕ} (t : BoundedRowTask k) :
    t.children.map localTask = t.localTask.children k := by
  cases t with
  | maximum i | pilotCorrection i | correction i | projectedReward i =>
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [children, localTask, CorrectionRowTask.children, PilotRowTask.children,
        PilotTask.children]
  | _ => simp [children, localTask, CorrectionRowTask.children, PilotRowTask.children,
      PilotTask.children]

end BoundedRowTask

/-- A stage-local row or the matrix produced by its completed correction-and-copy stage. -/
inductive HierarchyTask (k : ℕ) where
  | row (stage : ℕ) (task : BoundedRowTask k)
  | nextMatrix (stage : ℕ)
  | basePreparation (stage bin : ℕ)
  | baseNormalized (stage bin : ℕ)
  | residual (stage : ℕ)
  | residualPreparation (stage bin : ℕ)
  | residualNormalized (stage bin : ℕ)
  deriving DecidableEq

namespace HierarchyTask

/-- The row bound, one matrix-output slot and one separating slot. -/
@[expose] def stride (k : ℕ) : ℕ := 4 * (20 * k + 28)

/-- Rank computed only from stage, constructor and finite iteration index. -/
@[expose] def rank {k : ℕ} : HierarchyTask k → ℕ
  | .row l t => stride k * l + 4 * t.localTask.rank k
  | .nextMatrix l => stride k * l + 4 * (20 * k + 27) + 3
  | .basePreparation l _ => stride k * l + 13
  | .baseNormalized l _ => stride k * l + 14
  | .residual l => stride k * l + 4 * (20 * k + 27)
  | .residualPreparation l _ => stride k * l + 4 * (20 * k + 27) + 1
  | .residualNormalized l _ => stride k * l + 4 * (20 * k + 27) + 2

/-- Dense-bin edges interleave with the existing finite correction iteration order. -/
inductive BinDependency {k : ℕ} : HierarchyTask k → HierarchyTask k → Prop where
  | basePreparation (l i) : BinDependency (.row l .base) (.basePreparation l i)
  | baseRaw (l i) : BinDependency (.row l .base) (.baseNormalized l i)
  | baseNormalized (l i) : BinDependency (.basePreparation l i) (.baseNormalized l i)
  | baseInput (l i) (j : Fin k) : BinDependency (.baseNormalized l i) (.row l (.input j))
  | basePilotInput (l i) (j : Fin k) :
      BinDependency (.baseNormalized l i) (.row l (.pilotInput j))
  | residualRow (l) (t : BoundedRowTask k) : BinDependency (.row l t) (.residual l)
  | residualPreparation (l i) : BinDependency (.residual l) (.residualPreparation l i)
  | residualRaw (l i) : BinDependency (.residual l) (.residualNormalized l i)
  | residualNormalized (l i) :
      BinDependency (.residualPreparation l i) (.residualNormalized l i)
  | copy (l i) : BinDependency (.residualNormalized l i) (.nextMatrix l)

/-- Actual dependencies: local recipes, the residual/copy matrix output, and the two
cross-stage calls replacing the old local leaves. Base-stage leaves read `S` and `e₀`. -/
inductive Dependency {k : ℕ} : HierarchyTask k → HierarchyTask k → Prop where
  | rowChild {l : ℕ} {parent child : BoundedRowTask k}
      (h : child.localTask ∈ parent.localTask.children k) :
      Dependency (.row l child) (.row l parent)
  | matrixBase (l : ℕ) : Dependency (.row l .base) (.nextMatrix l)
  | matrixCorrection (l : ℕ) :
      Dependency (.row l (.correction (Fin.last k))) (.nextMatrix l)
  | matrixResidual (l : ℕ) : Dependency (.residual l) (.nextMatrix l)
  | matrixWeights (l : ℕ) : Dependency (.row l .weights) (.nextMatrix l)
  | base (l : ℕ) : Dependency (.nextMatrix l) (.row (l + 1) .base)
  | previousReward (l : ℕ) :
      Dependency (.row l (.projectedReward (Fin.last k))) (.row (l + 1) .previousReward)
  | bin {child parent : HierarchyTask k} (h : BinDependency child parent) :
      Dependency child parent

/-- All stochastic-bin edges decrease the same constructor-computed global rank. -/
theorem rank_lt_of_binDependency {k : ℕ} {child parent : HierarchyTask k}
    (h : BinDependency child parent) : child.rank < parent.rank := by
  cases h with
  | residualRow l t =>
    have := t.rank_le
    simp only [rank]
    omega
  | _ =>
    simp only [rank, CorrectionRowTask.rank,
      PilotRowTask.rank, PilotTask.rank]
    omega

/-- Every finite local row fits strictly before its stage's matrix output. -/
theorem row_rank_lt_nextMatrix {k : ℕ} (l : ℕ) (t : BoundedRowTask k) :
    (row l t).rank < (nextMatrix (k := k) l).rank := by
  have := t.rank_le
  simp only [rank]
  omega

/-- Every local and cross-stage call decreases the same computed natural rank. -/
theorem rank_lt_of_dependency {k : ℕ} {child parent : HierarchyTask k}
    (h : Dependency child parent) : child.rank < parent.rank := by
  cases h with
  | bin h => exact rank_lt_of_binDependency h
  | rowChild h =>
    have := CorrectionRowTask.rank_lt_of_mem_children h
    simp only [rank]
    omega
  | matrixResidual l => simp only [rank]; omega
  | matrixBase l => exact row_rank_lt_nextMatrix l .base
  | matrixCorrection l => exact row_rank_lt_nextMatrix l (.correction (Fin.last k))
  | matrixWeights l => exact row_rank_lt_nextMatrix l .weights
  | base l =>
    simp only [rank, stride, CorrectionRowTask.rank,
      PilotRowTask.rank, PilotTask.rank, Nat.mul_add, Nat.mul_one]
    omega
  | previousReward l =>
    have := BoundedRowTask.rank_le (BoundedRowTask.projectedReward (Fin.last k))
    simp only [rank, stride, CorrectionRowTask.rank,
      Fin.val_last, Nat.mul_add, Nat.mul_one] at *
    omega

/-- Concrete call graph. The inherited matrix and reward are leaves only at stage zero;
zero-iteration corrections and maxima remain local constants. -/
@[expose] def children {k : ℕ} : HierarchyTask k → List (HierarchyTask k)
  | .row 0 .base | .row 0 .previousReward => []
  | .row (l + 1) .base => [.nextMatrix l]
  | .row (l + 1) .previousReward => [.row l (.projectedReward (Fin.last k))]
  | .row l t => t.children.map (.row l)
  | .nextMatrix l => [.residual l, .row l .weights]
  | .basePreparation l _ => [.row l .base]
  | .baseNormalized l i => [.row l .base, .basePreparation l i]
  | .residual l => [.row l .base, .row l (.correction (Fin.last k))]
  | .residualPreparation l _ => [.residual l]
  | .residualNormalized l i => [.residual l, .residualPreparation l i]

/-- Every listed call belongs to the semantic constructor dependency relation. -/
theorem dependency_of_mem_children {k : ℕ} {parent child : HierarchyTask k}
    (h : child ∈ parent.children) : Dependency child parent := by
  cases parent with
  | nextMatrix l =>
    simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact .matrixResidual l
    · exact .matrixWeights l
  | basePreparation l i =>
    simp only [children, List.mem_singleton] at h
    subst child
    exact .bin (.basePreparation l i)
  | baseNormalized l i =>
    simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact .bin (.baseRaw l i)
    · exact .bin (.baseNormalized l i)
  | residual l =>
    simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact .bin (.residualRow l _)
  | residualPreparation l i =>
    simp only [children, List.mem_singleton] at h
    subst child
    exact .bin (.residualPreparation l i)
  | residualNormalized l i =>
    simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact .bin (.residualRaw l i)
    · exact .bin (.residualNormalized l i)
  | row l t =>
    cases t with
    | base | previousReward =>
      cases l with
      | zero => simp [children] at h
      | succ l =>
        simp only [children, List.mem_singleton] at h
        subst child
        first | exact .base l | exact .previousReward l
    | _ =>
      simp only [children] at h
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
      apply Dependency.rowChild
      rw [← BoundedRowTask.children_localTask]
      exact List.mem_map.mpr ⟨c, hc, rfl⟩

/-- The concrete global call graph decreases, including both former local leaves. -/
theorem rank_lt_of_mem_children {k : ℕ} {parent child : HierarchyTask k}
    (h : child ∈ parent.children) : child.rank < parent.rank :=
  rank_lt_of_dependency (dependency_of_mem_children h)

/-- Induction follows bounded calls to original inputs or local zero-iteration constants.
This is structural task induction, not the estimator's statistical-budget induction. -/
theorem induction {k : ℕ} {motive : HierarchyTask k → Prop}
    (step : ∀ t, (∀ c ∈ t.children, motive c) → motive t) (t : HierarchyTask k) : motive t := by
  induction h : t.rank using Nat.strong_induction_on generalizing t with
  | ind r ih =>
    apply step
    intro c hc
    exact ih c.rank (h ▸ rank_lt_of_mem_children hc) c rfl

end HierarchyTask
end Matrix.HierarchyParams

namespace Matrix

universe u

variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  {V : ℕ → Type u} [∀ l, Fintype (V l)] [∀ l, LinearOrder (V l)]
  (e : ∀ l, V (l + 1) ≃ Lex (V l × Fin (P.m + 1)))
  {ι κ Γ Ζ : ℕ → Type u} [∀ l, Fintype (ι l)] [∀ l, Fintype (κ l)]
  [∀ l, Fintype (Γ l)] [∀ l, Fintype (Ζ l)]
  (X : ∀ l, ι l → V l → Prop) (Y : ∀ l, κ l → V l → Prop)
  [∀ l s v, Decidable (X l s v)] [∀ l t v, Decidable (Y l t v)]
  (S : Matrix (V 0) (V 0) ℝ) (e₀ : V 0 → ℝ)
  (Xs : ∀ l, Γ l → V l → Prop) (Z Zt : ∀ l, Ζ l → V l → Prop)
  [∀ l s v, Decidable (Xs l s v)] [∀ l t v, Decidable (Z l t v)]
  [∀ l t v, Decidable (Zt l t v)]
  {n : ℕ → ℕ}
  (A : ∀ l, P.CorrectionSampling (X l) (Y l) (Xs l) (Z l) (Zt l)
    (q⁻¹ ^ l) (hierarchy P e X Y S l) (n l))

open HierarchyParams

/-- Actual value types: local rows retain their distinct matrix/vector/seed types;
the matrix output lives on the next hierarchy domain. -/
abbrev hierarchyTaskValueType : HierarchyTask P.k → Type u
  | .row l t => t.localTask.Value P.m (V l) (κ l) (Γ l) (Ζ l)
  | .nextMatrix l => Matrix (V (l + 1)) (V (l + 1)) ℝ
  | .residual l => Matrix (V l) (V l) ℝ
  | .basePreparation l _ | .baseNormalized l _ |
      .residualPreparation l _ | .residualNormalized l _ =>
    DenseBinRecipe → Γ l × Ζ l → Matrix (V l) (V l) ℝ

/-- Interpret bounded tasks using the actual hierarchy and transported reward. The two
cross-stage equations below resolve the former local base leaves to earlier constructors. -/
@[expose] noncomputable def hierarchyTaskValue (t : HierarchyTask P.k) :
    hierarchyTaskValueType P (V := V) (κ := κ) (Γ := Γ) (Ζ := Ζ) t :=
  match t with
  | .row l t => (A l).value
      (rewardTransport (hierarchyProj P e X Y S) (hierarchyCorrection P e X Y S) l *ᵥ e₀)
      t.localTask
  | .nextMatrix l => hierarchy P e X Y S (l + 1)
  | .residual l => P.residual (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l)
  | .basePreparation l i => fun B σ =>
      DenseRowRecipe.preparation B.h B.ρ B.K (B.scales i) (Z l)
        (hierarchy P e X Y S l) σ.2
  | .baseNormalized l i => fun B =>
      DenseRowRecipe.normalized (boundedRoutedBinCutoff B.χ B.scales B.cap i B.route)
        B.ρ B.K (B.scales i) (Xs l) (Z l) (Zt l) (hierarchy P e X Y S l)
        (fun σ => DenseRowRecipe.preparation B.h B.ρ B.K (B.scales i) (Z l)
          (hierarchy P e X Y S l) σ.2)
  | .residualPreparation l i => fun B σ =>
      DenseRowRecipe.preparation B.h B.ρ B.K (B.scales i) (Z l)
        (P.residual (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l)) σ.2
  | .residualNormalized l i => fun B =>
      DenseRowRecipe.normalized (boundedRoutedBinCutoff B.χ B.scales B.cap i B.route)
        B.ρ B.K (B.scales i) (Xs l) (Z l) (Zt l)
        (P.residual (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l))
        (fun σ => DenseRowRecipe.preparation B.h B.ρ B.K (B.scales i) (Z l)
          (P.residual (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l)) σ.2)

/-- One constructor evaluated on arbitrary whole child functions. This is the structural
ACCESS assembly, before statistical-budget recursion. Incoming gates in correction recipes
are computed on completed child matrices. No aggregate mean or error is a parameter. -/
@[expose] noncomputable def hierarchyTaskRecipe
    (child : (t : HierarchyTask P.k) →
      hierarchyTaskValueType P (V := V) (κ := κ) (Γ := Γ) (Ζ := Ζ) t)
    (t : HierarchyTask P.k) :
    hierarchyTaskValueType P (V := V) (κ := κ) (Γ := Γ) (Ζ := Ζ) t :=
  match t with
  | .row 0 .base => S
  | .row (l + 1) .base => child (.nextMatrix l)
  | .row 0 .previousReward => e₀
  | .row (l + 1) .previousReward => fun a =>
      child (.row l (.projectedReward (Fin.last P.k))) (e l a)
  | .row l (.pilotInput i) => CorrectionRowRecipe.input
      (child (.row l .base)) (child (.row l (.pilotCorrection i.castSucc)))
      (child (.row l .base))
  | .row l (.input i) => CorrectionRowRecipe.input
      (child (.row l .base)) (child (.row l (.correction i.castSucc)))
      (child (.row l .base))
  | .row l (.score i) => PilotRowRecipe.score P (Y l) (q⁻¹ ^ l)
      (child (.row l (.pilotInput i)))
  | .row l (.detector i) => PilotRowRecipe.detector P (X l) (Y l)
      (child (.row l (.score i)))
  | .row l (.maximum i) => Fin.cases 0 (fun j => PilotRowRecipe.maximum
      (child (.row l (.maximum j.castSucc))) (child (.row l (.detector j)))) i
  | .row l (.pilotCorrection i) => Fin.cases 0 (fun j => fun x y =>
      (q⁻¹ ^ l) * P.atomCutoff (child (.row l (.pilotInput j)) x y / (q⁻¹ ^ l)) *
        P.γ (child (.row l (.maximum j.succ)) y)) i
  | .row l (.correction i) => Fin.cases 0 (fun j => fun x y =>
      (q⁻¹ ^ l) * P.atomCutoff (child (.row l (.input j)) x y / (q⁻¹ ^ l)) *
        P.γ (child (.row l (.maximum (Fin.last P.k))) y)) i
  | .row l (.pilotPreparation i) => (A l).preparationRecipe
      (child (.row l (.pilotInput i)))
  | .row l (.preparation i) => (A l).preparationRecipe (child (.row l (.input i)))
  | .row l (.pilotNormalized i) => (A l).normalizedRecipe
      (child (.row l (.pilotInput i))) (child (.row l (.pilotPreparation i)))
      (child (.row l (.maximum i.succ)))
  | .row l (.normalized i) => (A l).normalizedRecipe
      (child (.row l (.input i))) (child (.row l (.preparation i)))
      (child (.row l (.maximum (Fin.last P.k))))
  | .row l .weights => detectorWeight P.κ (child (.row l (.maximum (Fin.last P.k))))
  | .row l (.reward i) => child (.row l .previousReward) +
      child (.row l (.correction i)) *ᵥ child (.row l .previousReward)
  | .row l (.projectedReward i) => fun a =>
      child (.row l .weights) (ofLex a).2 (ofLex a).1 * child (.row l (.reward i)) (ofLex a).1
  | .residual l => CorrectionRowRecipe.residual (child (.row l .base))
      (child (.row l (.correction (Fin.last P.k))))
      (child (.row l (.correction (Fin.last P.k)))) (child (.row l .base))
  | .nextMatrix l => (copyStage (P.copyCutoff (q⁻¹ ^ l)) P.m
      (child (.row l .weights)) (child (.residual l))).submatrix
        (fun a => ofLex (e l a)) (fun b => ofLex (e l b))
  | .basePreparation l i => fun B σ =>
      DenseRowRecipe.preparation B.h B.ρ B.K (B.scales i) (Z l)
        (child (.row l .base)) σ.2
  | .baseNormalized l i => fun B =>
      DenseRowRecipe.normalized (boundedRoutedBinCutoff B.χ B.scales B.cap i B.route)
        B.ρ B.K (B.scales i) (Xs l) (Z l) (Zt l)
        (child (.row l .base)) (child (.basePreparation l i) B)
  | .residualPreparation l i => fun B σ =>
      DenseRowRecipe.preparation B.h B.ρ B.K (B.scales i) (Z l) (child (.residual l)) σ.2
  | .residualNormalized l i => fun B =>
      DenseRowRecipe.normalized (boundedRoutedBinCutoff B.χ B.scales B.cap i B.route)
        B.ρ B.K (B.scales i) (Xs l) (Z l) (Zt l)
        (child (.residual l)) (child (.residualPreparation l i) B)

omit [∀ l, LinearOrder (V l)] in
/-- The existing residual-preparation evaluator reads a completed raw child before
applying the nonlinear preparation recipe. The child may depend on the full environment;
this equation also applies when it is a conditional-walk average. -/
theorem hierarchyTaskRecipe_residualPreparation {Ω : Type*}
    (child : Ω → (t : HierarchyTask P.k) →
      hierarchyTaskValueType P (V := V) (κ := κ) (Γ := Γ) (Ζ := Ζ) t)
    (l i : ℕ) (raw : Ω → Matrix (V l) (V l) ℝ)
    (hchild : ∀ ω, child ω (.residual l) = raw ω)
    (B : DenseBinRecipe) (ω : Ω) (σ : Γ l × Ζ l) :
    hierarchyTaskRecipe P e X Y S e₀ Xs Z Zt A (child ω) (.residualPreparation l i) B σ =
      DenseRowRecipe.preparation B.h B.ρ B.K (B.scales i) (Z l) (raw ω) σ.2 := by
  simp only [hierarchyTaskRecipe, hchild]

/-- True residual substitution uses the actual correction hierarchy equation. -/
theorem hierarchyTaskRecipe_residual (l : ℕ) :
    hierarchyTaskRecipe P e X Y S e₀ Xs Z Zt A
      (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A) (.residual l) =
      hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.residual l) := by
  simp only [hierarchyTaskRecipe, hierarchyTaskValue, CorrectionSampling.value,
    Fin.val_last, P.correctionIter_last, CorrectionRowRecipe.residual_eq, P.residual_eq]
  rfl

/-- Both global bin preparations and normalized bins preserve the true hierarchy semantics.
Preparatory substitution is the actual earlier preparation, rather than an asserted normalizer. -/
theorem hierarchyTaskRecipe_bins (l i : ℕ) :
    (hierarchyTaskRecipe P e X Y S e₀ Xs Z Zt A
      (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A) (.basePreparation l i) =
      hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.basePreparation l i)) ∧
    (hierarchyTaskRecipe P e X Y S e₀ Xs Z Zt A
      (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A) (.baseNormalized l i) =
      hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.baseNormalized l i)) ∧
    (hierarchyTaskRecipe P e X Y S e₀ Xs Z Zt A
      (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A) (.residualPreparation l i) =
      hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.residualPreparation l i)) ∧
    (hierarchyTaskRecipe P e X Y S e₀ Xs Z Zt A
      (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A) (.residualNormalized l i) =
      hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.residualNormalized l i)) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- At stage zero, the row base is exactly the supplied matrix. -/
theorem hierarchyTask_base_zero :
    hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row 0 .base) = S := by
  simp only [hierarchyTaskValue, CorrectionSampling.value,
    PilotRowRecipe.value, PilotTask.value, hierarchy]

/-- At positive stages, the base row is the actual preceding correction-and-copy output. -/
theorem hierarchyTask_base_succ (l : ℕ) :
    hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row (l + 1) .base) =
      hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.nextMatrix l) := rfl

/-- Stage zero's reward reads the original reward, including the zero reward. -/
theorem hierarchyTask_previousReward_zero :
    hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row 0 .previousReward) = e₀ := by
  simp only [hierarchyTaskValue, CorrectionSampling.value,
    rewardTransport, one_mulVec]

/-- The old previous-reward leaf is precisely the preceding projected-reward constructor,
transported by the actual domain equivalence. Its whole vector is called at the parent vertex. -/
theorem hierarchyTask_previousReward_succ (l : ℕ) :
    hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row (l + 1) .previousReward) =
      fun a => hierarchyTaskValue P e X Y S e₀ Xs Z Zt A
        (.row l (.projectedReward (Fin.last P.k))) (e l a) := by
  change rewardTransport _ _ (l + 1) *ᵥ e₀ = _
  rw [rewardTransport_succ_mulVec]
  ext a
  rw [hierarchyProj_mulVec]
  simp only [hierarchyTaskValue, CorrectionSampling.value,
    Fin.val_last, P.correctionIter_last, hierarchyCorrection]

/-- The matrix output reads exactly its earlier base, final actual correction and copy
weights. This is the existing residual and copy recipe, including all copy symbols. -/
theorem hierarchyTask_nextMatrix (l : ℕ) :
    hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.nextMatrix l) =
      (copyStage (P.copyCutoff (q⁻¹ ^ l)) P.m
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l .weights))
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l .base) -
          hierarchyTaskValue P e X Y S e₀ Xs Z Zt A
            (.row l (.correction (Fin.last P.k))) +
          hierarchyTaskValue P e X Y S e₀ Xs Z Zt A
            (.row l (.correction (Fin.last P.k))) *
          hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l .base))).submatrix
        (fun a => ofLex (e l a)) (fun b => ofLex (e l b)) := by
  simp only [hierarchyTaskValue, hierarchy, HierarchyParams.next, HierarchyParams.residual,
    CorrectionSampling.value, PilotRowRecipe.value,
    PilotTask.value, Fin.val_last, P.correctionIter_last, submatrix_submatrix]
  rfl

/-- Preparations call the bounded earlier input as a whole matrix. -/
theorem hierarchyTask_preparation (l : ℕ) (i : Fin P.k) :
    hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.preparation i)) =
      (A l).preparationRecipe
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.input i))) := rfl

/-- Normalization calls the bounded earlier input, preparation and completed pilot maximum. -/
theorem hierarchyTask_normalized (l : ℕ) (i : Fin P.k) :
    hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.normalized i)) =
      (A l).normalizedRecipe
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.input i)))
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.preparation i)))
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A
          (.row l (.maximum (Fin.last P.k)))) := rfl

/-- The actual input calls the base on both sides of the product. The right row is
applied at the summation midpoint, as in the inherited local request recipe. -/
theorem hierarchyTask_input (l : ℕ) (i : Fin P.k) :
    hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.input i)) =
      CorrectionRowRecipe.input
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l .base))
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.correction i.castSucc)))
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l .base)) := rfl

/-- Pilot preparation is also a call to its bounded earlier raw input. -/
theorem hierarchyTask_pilotPreparation (l : ℕ) (i : Fin P.k) :
    hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.pilotPreparation i)) =
      (A l).preparationRecipe
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.pilotInput i))) := rfl

/-- The pilot normalized child uses the current completed maximum, rather than the final
maximum used by the actual correction. Finite indices include this successor maximum. -/
theorem hierarchyTask_pilotNormalized (l : ℕ) (i : Fin P.k) :
    hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.pilotNormalized i)) =
      (A l).normalizedRecipe
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.pilotInput i)))
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.pilotPreparation i)))
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.maximum i.succ))) := rfl

/-- The reward sample reads the actual bounded weight, normalized correction and inherited
reward children. The two vector evaluations have distinct source vertices: parent and midpoint.
The seed predicates retain the inherited roles/rates/suffixes from `A l`. -/
theorem hierarchyTask_rewardRecipe (l : ℕ) (hn : n l < P.k)
    (σ : Γ l × Ζ l) (a : V (l + 1)) :
    (A l).projectedRewardRecipe
        (hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l .previousReward)) σ (e l a) =
      hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l .weights)
          (ofLex (e l a)).2 (ofLex (e l a)).1 *
        hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l .previousReward)
          (ofLex (e l a)).1 +
      hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l .weights)
          (ofLex (e l a)).2 (ofLex (e l a)).1 * (q⁻¹ ^ l / (A l).π) *
        ∑ z, hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l (.normalized ⟨n l, hn⟩))
          σ (ofLex (e l a)).1 z *
          hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row l .previousReward) z := rfl

/-- The recursive reward client uses the *actual* preceding projected reward in (7.5),
including the normalized child's local preparation. The first vector keeps its inherited
source; the summand calls the same whole vector at the midpoint. All predicates can have
fixed suffixes already applied. No old source vertex is stored in the right child. -/
theorem expect_hierarchyTaskReward_crossStage
    (l : ℕ) (hn : n (l + 1) + 1 = P.k)
    (he : ∀ j a b, e j a < e j b → a < b)
    (hq : 0 < q) (hCπ : 0 < Cπ) (hS : S.IsStrictUpperTriangular)
    (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : S *ᵥ 1 ≤ 1) {π : ℕ → ℝ}
    (hch : ∀ j < l + 1, Cslib.Probability.RetentionChannels
      (X j) (Y j) (q⁻¹ ^ j) (π j) cπ Cπ Cpair Cvar)
    (a : V (l + 2))
    (hx : ({s | Xs (l + 1) s (ofLex (e (l + 1) a)).1} : Finset (Γ (l + 1))).Nonempty) :
    (𝔼 σ ∈ ({s | Xs (l + 1) s (ofLex (e (l + 1) a)).1} : Finset (Γ (l + 1))) ×ˢ
      (univ : Finset (Ζ (l + 1))),
      (A (l + 1)).projectedRewardRecipe
        (fun b => hierarchyTaskValue P e X Y S e₀ Xs Z Zt A
          (.row l (.projectedReward (Fin.last P.k))) (e l b)) σ (e (l + 1) a)) =
      hierarchyTaskValue P e X Y S e₀ Xs Z Zt A (.row (l + 2) .previousReward) a := by
  rw [← hierarchyTask_previousReward_succ P e X Y S e₀ Xs Z Zt A l]
  exact expect_hierarchyTaskReward P e X Y S (l + 1) (n (l + 1))
    (Xs (l + 1)) (Z (l + 1)) (Zt (l + 1)) (A (l + 1)) hn
    he hq hCπ hS hS0 hS1 hch e₀ a hx

end Matrix
