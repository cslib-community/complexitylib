/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of finite rooted child-cost reserves)
import Complexity.Computability.LogSpaceDerandomization.NormalizedAtomRows.RootReserveOutput
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

-- A real normalized dense child with two source seeds and a terminal mask. Its error
-- shares the source coordinate, so it is correlated with the mask. The rare unit error
-- meets the integrated budget even though the corresponding per-atom payment fails.
namespace IntegratedChildRootRegression
private abbrev E := (Fin 100 × Fin 100) × Bool
private abbrev X (a : (Fin 100 × Fin 100)) (_ : Unit) : Prop := a = (0, 0) ∨ a = (0, 1)
private abbrev Y (a : Bool) (_ : Unit) : Prop := a = true
private def A (σ : E) : Matrix Unit Unit ℝ :=
  DenseRowRecipe.normalized (fun d => min 1 (max 0 d)) (fun _ => 1) 2 1 X Y Y
    (fun _ _ => if σ.1 = (0, 0) then 1 else 0) (fun _ _ _ => 1) σ
private lemma form (σ : E) (x y : Unit) : A σ x y = if σ.1 = (0, 0) ∧ σ.2 = true then 1 else 0 := by
  have hn : (({a | X a x} : Finset (Fin 100 × Fin 100)) ×ˢ
      ({a | Y a y} : Finset Bool)).Nonempty :=
    ⟨((0, 0), true), by
      simp only [mem_product, mem_filter, mem_univ, true_and]
      exact ⟨Or.inl rfl, trivial⟩⟩
  simp only [A, DenseRowRecipe.normalized, rowGate, CorrectionRowRecipe.normalizer]
  rw [expect_const hn]
  norm_num only [min_self, div_one, max_eq_right (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  by_cases h0 : σ.1 = (0, 0) <;> by_cases ht : σ.2 = true <;> simp [Y, h0, ht]
set_option backward.isDefEq.respectTransparency false in
private lemma moment : rootDistPow 4 1 1 (fun σ x => X σ.1 x) (fun σ y => Y σ.2 y)
    A (fun _ _ _ => 0) = 1 / 20000 := by
  have hrow (σ : E) :
      (∑ x ∈ ({x | X σ.1 x} : Finset Unit), ∑ y ∈ ({y | Y σ.2 y} : Finset Unit),
        |A σ x y ^ (4⁻¹ : ℝ) - (0 : ℝ) ^ (4⁻¹ : ℝ)| ^ 4) =
      if σ.1 = (0, 0) ∧ σ.2 = true then 1 else 0 := by
    by_cases h0 : σ.1 = (0, 0) <;> by_cases ht : σ.2 = true <;> simp [form, X, Y, h0, ht]
  unfold rootDistPow rowNormPow
  simp only [mul_one, inv_one, one_mul]
  change (𝔼 σ : E, _) = _
  have heq : (𝔼 σ : E, ∑ x ∈ ({x | X σ.1 x} : Finset Unit),
      ∑ y ∈ ({y | Y σ.2 y} : Finset Unit),
        |A σ x y ^ (4⁻¹ : ℝ) - (0 : ℝ) ^ (4⁻¹ : ℝ)| ^ 4) =
      𝔼 σ : E, if σ.1 = (0, 0) ∧ σ.2 = true then (1 : ℝ) else 0 :=
    congrArg (fun f : E → ℝ => 𝔼 σ, f σ) (funext hrow)
  norm_num only [Nat.cast_ofNat]
  norm_num only at heq
  exact heq.trans (by norm_num [expect_eq_sum_div_card, Fintype.sum_prod_type, ite_and])
end IntegratedChildRootRegression
namespace IntegratedChildRootRegression
private abbrev channels (role : Fin 3) (_ : ℝ) (_ : List Unit) (σ : E) (_ : Unit) : Prop :=
  if role = 0 then X σ.1 () else Y σ.2 ()
private abbrev src : CorrectionRowTask.Channel (Fin 3) (List Unit) := ⟨0, 1, [()]⟩
private abbrev mid : CorrectionRowTask.Channel (Fin 3) (List Unit) := ⟨1, 1, [(), ()]⟩
private abbrev dst : CorrectionRowTask.Channel (Fin 3) (List Unit) := ⟨2, 1, [()]⟩
private lemma density : (dens {σ : E | Y σ.2 ()} : ℝ) = 1 / 2 := by
  have hd := Cslib.Probability.dens_filter_fst_and_snd (fun _ : (Fin 100 × Fin 100) => True)
    (fun t : Bool => t = true)
  norm_num only [true_and, filter_true, dens_univ, one_mul] at hd
  have hb : (dens {t : Bool | t = true} : ℝ) = 1 / 2 := by norm_num [dens, filter_insert]
  exact (congrArg (fun z : ℚ≥0 => (z : ℝ)) hd).trans hb
private lemma coefficient : HierarchyTask.residualCostCoefficient (k := 1) channels ∅ 0
    src mid dst (fun _ => 1) 1 1 = 8 := by
  norm_num [HierarchyTask.residualCostCoefficient, HierarchyTask.usageRatio, src, mid, dst,
    CorrectionRowTask.Channel.retains, channels, density]
private lemma calls :
    #(HierarchyTask.residualErrorCalls (k := 1) ∅ 0 src mid dst (fun _ => 1)) = 1 := by
  simp [HierarchyTask.residualErrorCalls]
set_option backward.isDefEq.respectTransparency false in
example :
    rowNormPow 4 1 1 (fun σ x => src.retains channels σ x)
      (fun σ y => dst.retains channels σ y)
      (fun _ => HierarchyTask.conditionalChildCost (k := 1) channels ∅ 0 src mid dst (fun _ => 1)
        1 1 (fun _ σ _ => A σ) (fun _ _ _ _ _ => 0)) ≤ 4626 / 20000 := by
  apply HierarchyTask.conditionalChildCost_le_of_root_budgets (B := 1) channels ∅ 0
    src mid dst (fun _ => 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun _ σ _ => A σ) (fun _ _ _ _ _ => 0)
  · intro i r hr
    simp only [HierarchyTask.residualErrorCalls, biUnion_empty, empty_union, mem_singleton,
      Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl⟩
    norm_num [src]
  · intro i r hr σ x y
    rw [form]
    split_ifs <;> norm_num
  · intro i r hr σ x y hy
    simp only [HierarchyTask.residualErrorCalls, biUnion_empty, empty_union, mem_singleton,
      Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl⟩
    have ht : σ.2 ≠ true := by simpa [CorrectionRowTask.Channel.retains, channels, dst, Y] using hy
    simp [form, ht]
  · intro i r hr
    simp only [HierarchyTask.residualErrorCalls, biUnion_empty, empty_union, mem_singleton,
      Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl⟩
    change rootDistPow 4 1 1 (fun σ x => X σ.1 x) (fun σ y => Y σ.2 y)
      A (fun _ _ _ => 0) ≤ _
    rw [moment, coefficient, calls]
    norm_num [src]
example : A ((0, 0), true) () () = 1 ∧ A ((0, 1), true) () () = 0 ∧
    (4626 / 20000 : ℝ) / (1 + 8) < 1 := by
  norm_num [form]
end IntegratedChildRootRegression
