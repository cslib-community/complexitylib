/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of finite rooted child-cost reserves)
import Complexity.Foundations.Probability.NormalizedAtomRows.RootReserveOutput
import all ComplexityTests.ReserveOutput
import all ComplexityTests.HierarchyChildError

/-! Domain-sensitive errors, finite once-negative coefficients and actual normalized
nonconstant children. Existing regression fixtures and their exact checks are retained. -/
set_option linter.privateModule false
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace ChildRootReserveRegression
private def src : CorrectionRowTask.Channel (Fin 3) (List Unit) := ⟨0, 1, [()]⟩
private def mid : CorrectionRowTask.Channel (Fin 3) (List Unit) := ⟨1, 1, [(), ()]⟩
private def dst : CorrectionRowTask.Channel (Fin 3) (List Unit) := ⟨2, 1, [()]⟩
private def mask (role : Fin 3) (_ : ℝ) (_ : List Unit) (_ : Unit) (v : Bool) : Prop :=
  role ≠ 1 ∨ v = false
private def truth (r : HierarchyTask.Request 1 (Fin 3) Unit) : Matrix Bool Bool ℝ :=
  match r.task with
  | .baseNormalized _ _ => fun _ _ => 0
  | _ => fun _ z => if z = false then 1 else 0
private def estimate (r : HierarchyTask.Request 1 (Fin 3) Unit) : Matrix Bool Bool ℝ :=
  match r.task with
  | .baseNormalized _ _ => fun z _ => if r.source.role = 1 ∧ z = true then 1 else 0
  | _ => fun _ z => if z = false then 1 else 0
private lemma final_task : HierarchyTask.correctionAtomTask (k := 1) 0 false 1 =
    .row 0 (.normalized 0) := HierarchyTask.correctionAtomTask_last_succ 0 0

-- The right child has zero error on its own source but arbitrary error off that source.
-- Its terminal mask is full, so this also checks a full-rank/off-source edge.
example :
    let r := (HierarchyTask.rawRequests (k := 1) 0 0 .residual src mid dst 1).right
    rootDistPow 4 2 1 (fun σ z => mid.retains mask σ z)
      (fun σ y => dst.retains mask σ y) (fun _ => estimate r) (fun _ => truth r) = 0 ∧
    estimate r true true - truth r true true = 1 := by
  norm_num [rootDistPow, rowNormPow, HierarchyTask.rawRequests, estimate, truth, src, mid, dst,
    CorrectionRowTask.Channel.retains, mask, sum_filter]

-- The actual left-support guard removes exactly that off-source right error.
example : HierarchyTask.positiveChildError mask 0 0 .residual src mid dst 1 1 1
    estimate truth false true = 0 := by
  norm_num [HierarchyTask.positiveChildError, HierarchyTask.rawRequests, estimate, truth,
    final_task, src, mid, dst, HierarchyTask.usageRatio, CorrectionRowTask.Channel.retains,
    mask, sum_filter]

-- The guard still pays an error if either left factor is nonzero.
example : HierarchyTask.positiveChildError NumericCalls.mask 0 0 .residual
    NumericCalls.src NumericCalls.mid NumericCalls.dst 1 3 1
    NumericCalls.estimate NumericCalls.truth () () = 6 := by
  norm_num [HierarchyTask.positiveChildError, HierarchyTask.rawRequests,
    NumericCalls.final_task, HierarchyTask.usageRatio, CorrectionRowTask.Channel.retains,
    NumericCalls.src, NumericCalls.mid, NumericCalls.dst, NumericCalls.mask,
    NumericCalls.estimate, NumericCalls.truth]

-- Explicit two-bin coefficient: two positive coefficients, one negative coefficient.
example : HierarchyTask.residualCostCoefficient (k := 1) NumericCalls.mask (range 2) 0
    NumericCalls.src NumericCalls.mid NumericCalls.dst (fun _ => 1) 3 1 = 1345544 := by
  norm_num [HierarchyTask.residualCostCoefficient, HierarchyTask.rawRequests,
    HierarchyTask.usageRatio, CorrectionRowTask.Channel.retains, NumericCalls.src,
    NumericCalls.mid, NumericCalls.dst, NumericCalls.mask]

example : HierarchyTask.residualCostCoefficient (k := 1) NumericCalls.mask ∅ 0
    NumericCalls.src NumericCalls.mid NumericCalls.dst (fun _ => 1) 3 1 = 8 := by
  norm_num [HierarchyTask.residualCostCoefficient, HierarchyTask.usageRatio,
    CorrectionRowTask.Channel.retains, NumericCalls.src, NumericCalls.mid, NumericCalls.dst,
    NumericCalls.mask]

-- Exactly matching children have zero actual conditional cost, including empty slices.
example (bins : Finset ℕ) (S : Finset Unit) (CA CB : ℝ)
    (A : ℕ → Unit → HierarchyTask.Request 1 (Fin 3) Unit → Matrix Unit Unit ℝ) :
    (𝔼 σ ∈ S, ((∑ i ∈ bins, HierarchyTask.positiveChildError NumericCalls.mask 0 i .residual
      NumericCalls.src NumericCalls.mid NumericCalls.dst 1 CA CB (A i σ) (A i σ) () ()) +
      HierarchyTask.negativeChildError NumericCalls.mask 0 0 .residual NumericCalls.src
        NumericCalls.mid NumericCalls.dst 1 (A 0 σ) (A 0 σ) () ())) = 0 := by
  simp [HierarchyTask.positiveChildError, HierarchyTask.negativeChildError,
    HierarchyTask.rawRequests]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
-- Real normalized request outputs on the inherited four-role/spectator/suffix fixture.
-- They are positive and nonconstant; zero canonical raw data has zero normalized output.
set_option backward.isDefEq.respectTransparency false in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let r : HierarchyTask.Request HP.k (Fin 4) (ZMod 5) :=
      ⟨.baseNormalized 0 0, gridChannel 0 0 [1], gridChannel 2 0 [4], gridChannel 2 0 [4]⟩
    let A := fun σ => normalizedRequest 1 id r (ReserveOutputRegression.fixtureCutoff 0)
      HP.ρ HP.K (fun σ _ _ => ReserveOutputRegression.value σ) (fun _ _ _ => 1) σ
    A ReserveOutputRegression.low 0 0 = 1 ∧ A ReserveOutputRegression.high 0 0 = 2 ∧
    canonicalRequestChild HP 1 id (fun _ _ => 0) (ReserveOutputRegression.fixtureCutoff 0)
      (fun _ => 1) (fun _ => 1) 66 r ReserveOutputRegression.low 0 0 = 0 := by
  dsimp only
  rw [ReserveOutputRegression.dense HP 0 (by decide) 0 2 (by decide) [1] [4],
    ReserveOutputRegression.dense HP 0 (by decide) 0 2 (by decide) [1] [4]]
  constructor
  · norm_num [ReserveOutputRegression.value, ReserveOutputRegression.low]
  constructor
  · norm_num [ReserveOutputRegression.value, ReserveOutputRegression.high]
  · unfold canonicalRequestChild denseChild normalizedRequest
    split_ifs
    · simp [DenseRowRecipe.normalized, ReserveOutputRegression.fixtureCutoff]
    · rfl

end ChildRootReserveRegression
