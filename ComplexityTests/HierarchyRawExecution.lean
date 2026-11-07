/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of scheduled raw-task execution)
import Complexity.Foundations.Probability.HierarchyRawExecution
import Complexity.Foundations.Probability.HierarchyApproximateHistory
import all ComplexityTests.PolynomialBudgetHistory

/-!
The supplied history returns a nonzero whole table. A nonempty residual group samples
budget one against the literal budget-zero approximation, retaining a nonzero coarse
reference error in the existing perturbation theorem. Both positive bins and the once-negative
ray execute, and the complete RAW program returns eleven. This is structural execution,
not recursively available or canonically accurate substituted children.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace RawExecutionRegression

private abbrev Table := Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ

private def data (HP : FourthRootHierarchyParams 16 1 16 32 8) : BudgetData HP 5 :=
  { PolynomialBudgetHistory.data HP with binRate := fun _ => rate 0 }
private def request (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  { PolynomialBudgetHistory.request HP with task := .residual 0 }
private def history {k : ℕ} (_ : ℕ) (_ : HierarchyTask.Request k (Fin 3) (ZMod 5)) :
    Option (BudgetValue 5) := some (.row (fun _ _ _ => 1))

private lemma positive (HP : FourthRootHierarchyParams 16 1 16 32 8) (m bin : ℕ) :
    (data HP).positiveSample history m bin .residual (request HP) =
      some (fun _ _ _ => 6) := by
  unfold BudgetData.positiveSample BudgetData.row
  simp only [history, Option.bind_some, BudgetValue.row?]
  apply congrArg some
  funext σ x y
  have hf (τ : Environment 5 3) (role : Fin 3) (suffix : List (ZMod 5)) (v : ZMod 5) :
      (⟨role, 1, suffix⟩ : CorrectionRowTask.Channel (Fin 3) (List (ZMod 5))).retains
        (channels (1 : ZMod 5)) τ v := by
    simpa only [gridChannel, rate, pow_zero, inv_one, one_pow] using
      PolynomialBudgetHistory.full τ role suffix v
  norm_num [data, PolynomialBudgetHistory.data, request, PolynomialBudgetHistory.request,
    BudgetData.midpoint,
    BudgetData.midpointRole, HierarchyTask.rawRequests, gridChannel, rate,
    HierarchyTask.usageRatio, hf]

private lemma sample (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (m : ℕ) (bin : Option ℕ) :
    (data HP).sample history m .residual (request HP) bin =
      some (if m = 0 then 0 else
        match bin with
        | some _ => fun _ _ _ => 6
        | none => fun _ _ _ => -1) := by
  by_cases hm : m = 0
  · subst m
    simp only [BudgetData.sample, ↓reduceIte]
  · cases bin with
    | some bin => simp only [BudgetData.sample, hm, ↓reduceIte, positive]
    | none =>
      simp only [BudgetData.sample, hm, ↓reduceIte, BudgetData.row, history,
        Option.bind_some, BudgetValue.row?]
      apply congrArg some
      funext σ x y
      have hf (τ : Environment 5 3) (role : Fin 3) (suffix : List (ZMod 5)) (v : ZMod 5) :
          (⟨role, 1, suffix⟩ : CorrectionRowTask.Channel (Fin 3) (List (ZMod 5))).retains
            (channels (1 : ZMod 5)) τ v := by
        simpa only [gridChannel, rate, pow_zero, inv_one, one_pow] using
          PolynomialBudgetHistory.full τ role suffix v
      norm_num [data, PolynomialBudgetHistory.data, request, PolynomialBudgetHistory.request,
    BudgetData.midpoint,
        gridChannel, rate, HierarchyTask.usageRatio, hf]

private lemma scale (HP : FourthRootHierarchyParams 16 1 16 32 8) (bin : Option ℕ) :
    (data HP).sampleScale (request HP) bin = 0 := by
  cases bin <;> norm_num [BudgetData.sampleScale, data, request,
    PolynomialBudgetHistory.request, BudgetData.midpoint, gridChannel, rate]

-- This is a nonempty group: fine=1>0 and coarse=0, with a literal nonzero fine sample.
-- The coarse reference has size seven, and that error remains in the bound.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let A : Table := fun _ _ _ => 6
    let C : Table := 0
    let A₀ : Table := fun _ _ _ => 5
    let C₀ : Table := fun _ _ _ => 7
    LogSpaceEstimation.lastBudget 2 1 (data HP).slack
        ((data HP).sampleScale (request HP) (some 0)) = 1 ∧
    LogSpaceEstimation.lastBudget 2 2 (data HP).slack
        ((data HP).sampleScale (request HP) (some 0)) = 0 ∧
    (data HP).pairedSample history 2 1 .residual (request HP) (some 0) =
      some (fun _ _ _ => 6) ∧
    ∀ (σ : Environment 5 3) (x y : ZMod 5),
      |(A - C) σ x y - (A₀ - C₀) σ x y| ≤
        |A σ x y - A₀ σ x y| + |C σ x y - C₀ σ x y| := by
  dsimp only
  have hf : (data HP).sample history
      (LogSpaceEstimation.lastBudget 2 1 (data HP).slack
        ((data HP).sampleScale (request HP) (some 0))) .residual (request HP) (some 0) =
      some (fun _ _ _ => 6) := by
    rw [scale]
    change (data HP).sample history 1 .residual (request HP) (some 0) = some _
    exact sample HP 1 (some 0)
  have hc : (data HP).sample history
      (LogSpaceEstimation.lastBudget 2 2 (data HP).slack
        ((data HP).sampleScale (request HP) (some 0))) .residual (request HP) (some 0) =
      some 0 := by
    rw [scale]
    change (data HP).sample history 0 .residual (request HP) (some 0) = some 0
    exact (data HP).sample_zero history .residual (request HP) (some 0)
  have hp := (data HP).pairedSample_of_errors history 2 1 .residual (request HP) (some 0)
    (fun _ _ _ => 6) 0 (fun _ _ _ => 5) (fun _ _ _ => 7) hf hc (by
      rw [scale]
      change (1 : ℕ) ≠ 0
      decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [scale]; rfl
  · rw [scale]; rfl
  · simpa only [sub_zero] using hp.1
  · exact hp.2

private def amplitude : Option ℕ → Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ
  | some _ => fun _ _ _ => 6
  | none => fun _ _ _ => -1

private lemma pair_one (HP : FourthRootHierarchyParams 16 1 16 32 8) (bin : Option ℕ) :
    (data HP).pairedSample history 2 1 .residual (request HP) bin =
      some (amplitude bin) := by
  simp only [BudgetData.pairedSample, scale, show (data HP).slack = 1 from rfl]
  norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff, sample,
    amplitude]

private lemma pair_two (HP : FourthRootHierarchyParams 16 1 16 32 8) (bin : Option ℕ) :
    (data HP).pairedSample history 2 2 .residual (request HP) bin = some 0 := by
  simp only [BudgetData.pairedSample, scale, show (data HP).slack = 1 from rfl]
  norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]

private lemma complete_const (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (M d : ℕ) (A : Matrix (ZMod 5) (ZMod 5) ℝ) :
    (data HP).complete M (request HP) (fun _ => A) d = some (fun _ => A) := by
  rw [BudgetData.complete_grid _ M _ 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl _ d]
  apply congrArg some
  funext σ x y
  rw [conditionalWalk_const]
  have hx : X (0 : Fin 3) (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [1]) σ x := by
    simpa only [X, show side 5 0 = 5 by norm_num [side]] using full_retains (σ 0) _
  have hy : Y (2 : Fin 3) (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [2, 3]) σ y := by
    simpa only [Y, show side 5 0 = 5 by norm_num [side]] using full_retains (σ 2) _
  exact ite_eq_left ⟨hx, hy⟩

private lemma group_one (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).completedGroup history 2 1 .residual (request HP) =
      some (fun _ _ _ => 11) := by
  have hinputs : ((data HP).rays .residual).mapM
      ((data HP).pairedSample history 2 1 .residual (request HP)) =
        some (((data HP).rays .residual).map amplitude) := by
    apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact fun bin _ => pair_one HP bin
  have hin : (fun σ x y => ((((data HP).rays .residual).map amplitude).map
      (fun A => A σ x y)).sum) = fun _ _ _ => (11 : ℝ) := by
    funext σ x y
    norm_num [BudgetData.rays, data, PolynomialBudgetHistory.data, amplitude,
      List.map_map, List.sum_append]
  unfold BudgetData.completedGroup
  rw [ite_eq_right (by simp [BudgetData.rays]), hinputs]
  simp only [bind, Option.bind_some]
  rw [hin]
  exact complete_const HP 2 1 (fun _ _ => 11)

-- Both positive rays contribute six; the single negative ray contributes minus one.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).raw history 2 .residual (request HP) = some (fun _ _ _ => 11) := by
  have hzero : (data HP).completedGroup history 2 2 .residual (request HP) =
      some 0 := by
    have hinputs : ((data HP).rays .residual).mapM
        ((data HP).pairedSample history 2 2 .residual (request HP)) =
          some (((data HP).rays .residual).map (fun _ => 0)) := by
      apply List.mapM_eq_some_iff_forall₂.mpr
      rw [List.forall₂_map_right_iff, List.forall₂_same]
      exact fun bin _ => pair_two HP bin
    unfold BudgetData.completedGroup
    rw [ite_eq_right (by simp [BudgetData.rays]), hinputs]
    simp only [bind, Option.bind_some]
    have hin : (fun σ x y =>
        ((((data HP).rays .residual).map (fun _ =>
          (0 : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ))).map
            (fun A => A σ x y)).sum) = 0 := by
      funext σ x y
      simp
    rw [hin]
    exact complete_const HP 2 2 0
  rw [BudgetData.raw, show Nat.log2 2 = 1 by decide]
  norm_num [List.range_succ, dyadicSlack, hzero, group_one]

-- Every actual endpoint sample exists; no canonical accuracy is a premise.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ) :
    ∃ A, (data HP).raw history M .residual (request HP) = some A := by
  apply (data HP).raw_available history M .residual (request HP) 0 2 (by decide)
    0 0 [1] [2, 3] rfl rfl
  intro j _ bin _
  dsimp only
  intro _
  exact ⟨⟨_, sample HP _ bin⟩, ⟨_, sample HP _ bin⟩⟩

-- Structural dispatch retains each later input's actual constructor.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ)
    (i : Fin HP.k) (hi : i.val ≠ 0) (pilot : Bool)
    (hp : 0 < (data HP).requestPrecision M
      { request HP with task := .row 0 (if pilot then .pilotInput i else .input i) }) :
    (data HP).step history M
      { request HP with task := .row 0 (if pilot then .pilotInput i else .input i)} =
      ((data HP).raw history M (if pilot then .pilotInput i else .input i)
        { request HP with task := .row 0 (if pilot then .pilotInput i else .input i)}).map
        BudgetValue.row := by
  cases pilot
  · exact (data HP).step_input history M _ i rfl hi hp
  · exact (data HP).step_pilotInput history M _ i rfl hp

-- A positive-precision residual now dispatches; inactive constructors still reject.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ)
    (hp : 0 < (data HP).requestPrecision M (request HP)) :
    (data HP).step history M (request HP) =
      ((data HP).raw history M .residual (request HP)).map BudgetValue.row :=
  (data HP).step_residual history M _ rfl hp
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ)
    (hp : ¬ 0 < (data HP).requestPrecision M (request HP)) :
    (data HP).step history M (request HP) = none := by
  simp only [BudgetData.step, show (request HP).task = .residual 0 from rfl, hp, ↓reduceIte]

end RawExecutionRegression
