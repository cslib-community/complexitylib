/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of actual selected-preparation noise allocation)
import Complexity.Foundations.Probability.HierarchyInitialSecondNoiseAllocation
import Complexity.Foundations.Probability.HierarchyInitialFeasibility
import all ComplexityTests.ActualSecondSignal
import all ComplexityTests.PolynomialBudgetHistory

/-! Covered-field charge families and literal preparation walks. The production H4
walk regression uses arbitrary first-history input, not a successful recursive IH. -/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

namespace SecondNoiseAllocation
open Cslib.RotationMap
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Self loops in the nonlazy graph prevent the lazy walk from killing a nonzero
-- vector exactly. This is used only to check strict positivity, not the upper bound.
private lemma lazy_kernel {V D : Type*} [Finite V] [Nonempty V]
    [Fintype D] [Nonempty D] (G : RotationMap V D)
    (hloop : ∀ v, ∃ i, G.neighbor v i = v) (f : V → ℝ)
    (hf : G.lazy.walk f = 0) : f = 0 := by
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨v, _, hv⟩ := exists_max_image univ (fun v => |f v|) univ_nonempty
  have hb (w : V) : |f w| ≤ |f v| := hv w (mem_univ w)
  by_contra hn
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  have hpos : 0 < |f v| := (abs_pos.mpr hw).trans_le (hb w)
  have he := congrFun hf v
  rw [G.walk_lazy_apply] at he
  change (f v + G.walk f v) / 2 = 0 at he
  obtain ⟨i, hi⟩ := hloop v
  by_cases hs : 0 ≤ f v
  · have hm : |f v| = f v := abs_of_nonneg hs
    have ht : (𝔼 _i : D, -(f v)) < 𝔼 i, f (G.neighbor v i) := by
      apply expect_lt_expect
      · intro j _
        exact (neg_le_of_abs_le ((hb _).trans_eq hm))
      · exact ⟨i, mem_univ _, by rw [hi]; linarith [hpos]⟩
    rw [Fintype.expect_const, ← G.walk_apply] at ht
    linarith
  · have hm : |f v| = -f v := abs_of_neg (lt_of_not_ge hs)
    have ht : (𝔼 i, f (G.neighbor v i)) < 𝔼 _i : D, -(f v) := by
      apply expect_lt_expect
      · intro j _
        exact (le_abs_self _).trans ((hb _).trans_eq hm)
      · exact ⟨i, mem_univ _, by rw [hi]; linarith [hpos]⟩
    rw [Fintype.expect_const, ← G.walk_apply] at ht
    linarith

private lemma kernel_pow {V : Type*} (T : (V → ℝ) →ₗ[ℝ] (V → ℝ))
    (hT : ∀ f, T f = 0 → f = 0) (t : ℕ) (f : V → ℝ)
    (hf : (T ^ t) f = 0) : f = 0 := by
  induction t generalizing f with
  | zero => exact hf
  | succ t ih =>
    rw [pow_succ, Module.End.mul_apply] at hf
    exact hT f (ih _ hf)

-- The exact production H4 graph has nonlazy self loops: its M=1 free-bit
-- component moves the unique point. Vertex reindexing preserves that loop.
private lemma full_graph_kernel (x y : ZMod 5) (f : RetainedPairSlice
    (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
    (retainedMask 2 (side 5 0) 1 [3]) x y → ℝ)
    (hf : (graph (0 : Fin 3) 2 (by decide) (side 5 0) (side 5 0)
      (side_le 5 0) (side_le 5 0) (CopyPadding.identifier 1 [1])
      (CopyPadding.identifier 1 [3]) x y).walk f = 0) : f = 0 := by
  let core := ofPerms (componentMove 4 1 (fun _ : Fin 3 => 5)
    (pairSide (P := 5) (0 : Fin 3) 2 (side 5 0) (side 5 0)))
  let e := (componentEquiv (H := 4) 1
    (pairSide_le (0 : Fin 3) 2 (side 5 0) (side 5 0) (side_le 5 0) (side_le 5 0))
    (pairId (0 : Fin 3) 2 (CopyPadding.identifier 1 [1] x)
      (CopyPadding.identifier 1 [3] y))).symm
  let e' := (pairEquiv (0 : Fin 3) 2 (by decide) (side 5 0) (side 5 0)
    (CopyPadding.identifier 1 [1]) (CopyPadding.identifier 1 [3]) x y).symm
  have hh : core.lazy.walk (f ∘ e' ∘ e) = 0 := by
    funext v
    have h := congrFun hf (e' (e v))
    simpa only [graph, RotationMap.walk_reindex, Function.comp_def,
      Equiv.symm_apply_apply, Pi.zero_apply, core, e, e'] using h
  have hz := lazy_kernel core (fun v => ?_) (f ∘ e' ∘ e) hh
  · funext v
    have h := congrFun hz (e.symm (e'.symm v))
    simpa only [Function.comp_def, Equiv.apply_symm_apply, Pi.zero_apply] using h
  · refine ⟨(Sum.inr (Sum.inr (0 : Fin 4)), false), ?_⟩
    rw [RotationMap.neighbor_ofPerms_false]
    simp only [componentMove, RotationMap.boxProdPerms_inr]
    congr 1
    exact Subsingleton.elim _ _

private def prep (HP : FourthRootHierarchyParams 16 1 16 32 8) :=
  selectedPreparation HP 1 threeRoles [3] 0 (child randomBit)

private lemma prep_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (σ : Environment 5 3) (x y : ZMod 5) : prep HP σ x y = child randomBit σ x y := by
  have h := selected_eq HP randomBit σ x y
  unfold selected rawSamplePreparation at h
  have he : rawIncomingNormalized HP 1 id threeRoles 0 0 0 0 0 0 [1] [2] [3]
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2 id
      (fun (_ : HierarchyTask.Request 0 (Fin 3) (ZMod 5)) => child randomBit)
      (fun _ => prepChild) (fun _ _ _ => 9) = child randomBit := by
    funext τ a b
    exact raw_eq HP randomBit τ a b
  rw [he] at h
  exact h

private def productionWalk (HP : FourthRootHierarchyParams 16 1 16 32 8) (t : ℕ) :=
  conditionalWalk (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
    (retainedMask 2 (side 5 0) 1 [3])
    (graph (0 : Fin 3) 2 (by decide) (side 5 0) (side 5 0)
      (side_le 5 0) (side_le 5 0) (CopyPadding.identifier 1 [1])
      (CopyPadding.identifier 1 [3])) (fun _ _ => t) (prep HP)

-- A genuine nonconstant selected input has strictly positive centered noise after
-- EVERY finite production H4 length, hence also after the actual computed length.
-- This does not assert that this arbitrary first-history input is recursively available.
private theorem production_noise_pos
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (t : ℕ) :
    ∃ σ : Environment 5 3,
      0 < actualNoiseEntry (0 : Fin 3) 2 (side 5 0) (side 5 0) (side 5 0) 1 [1] [3] 0
        (fun _ _ => 0) (firstSignalIncrement (fun _ _ _ _ => 7) 0
          (secondSignalIncrement (fun _ => productionWalk HP t) 3))
        (fun _ _ _ _ => 0) 1 0 σ 0 0 := by
  let Xs := retainedMask (0 : Fin 3) (side 5 0) (1 : ZMod 5) [1]
  let Yu := retainedMask (2 : Fin 3) (side 5 0) (1 : ZMod 5) [3]
  let G : RotationMap (RetainedPairSlice Xs Yu (0 : ZMod 5) 0) _ :=
    graph (0 : Fin 3) 2 (by decide) (side 5 0) (side 5 0)
    (side_le 5 0) (side_le 5 0) (CopyPadding.identifier 1 [1])
    (CopyPadding.identifier 1 [3]) (0 : ZMod 5) 0
  let c := rowSliceMean Xs Yu (prep HP) 0 0
  have hret (σ : Environment 5 3) : σ ∈ ({σ | Xs σ 0 ∧ Yu σ 0} : Finset _) := by
    simp only [mem_filter, mem_univ, true_and]
    constructor <;> exact full_retains _ _
  have he (σ : Environment 5 3) := actualNoiseEntry_secondSignalIncrement
    (0 : Fin 3) 2 (side 5 0) (side 5 0) (side 5 0) 1 [1] [3]
    (fun _ => graph (0 : Fin 3) 2 (by decide) (side 5 0) (side 5 0)
      (side_le 5 0) (side_le 5 0) (CopyPadding.identifier 1 [1])
      (CopyPadding.identifier 1 [3])) (fun _ _ _ => t)
    (fun _ => prep HP) (fun _ _ _ _ => 7) 0 3 (fun _ _ => 0) 0 σ 0 0
  change ∀ σ, actualNoiseEntry (0 : Fin 3) 2 (side 5 0) (side 5 0) (side 5 0) 1
    [1] [3] 0 (fun _ _ => 0) (firstSignalIncrement (fun _ _ _ _ => 7) 0
      (secondSignalIncrement (fun _ => productionWalk HP t) 3))
    (fun _ _ _ _ => 0) 1 0 σ 0 0 = |(3 : ℝ)| * |productionWalk HP t σ 0 0 - c| at he
  by_contra hn
  push Not at hn
  have hc (σ : Environment 5 3) : productionWalk HP t σ 0 0 = c := by
    have h := hn σ
    rw [he σ] at h
    change |(3 : ℝ)| * |productionWalk HP t σ 0 0 - c| ≤ 0 at h
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at h
    have hab : |productionWalk HP t σ 0 0 - c| = 0 := by
      linarith [abs_nonneg (productionWalk HP t σ 0 0 - c)]
    exact sub_eq_zero.mp (abs_eq_zero.mp hab)
  have hz : (G.walk ^ (2 * t)) (fun τ => prep HP τ.val 0 0 - c) = 0 := by
    funext τ
    have h := hc τ.val
    change conditionalWalk Xs Yu (fun x y => _) (fun _ _ => t) (prep HP) τ.val 0 0 = c at h
    simp only [conditionalWalk, hret, ↓reduceDIte] at h
    change ((G.walk ^ (2 * t)) (fun τ => prep HP τ.val 0 0)) τ = c at h
    rw [show (fun τ : RetainedPairSlice Xs Yu 0 0 => prep HP τ.val 0 0 - c) =
      (fun τ : RetainedPairSlice Xs Yu 0 0 => prep HP τ.val 0 0) - (fun _ => c) by rfl,
      map_sub, RotationMap.walk_pow_const]
    exact sub_eq_zero.mpr h
  have hz' : (fun τ : RetainedPairSlice Xs Yu 0 0 => prep HP τ.val 0 0 - c) = 0 :=
    kernel_pow G.walk (full_graph_kernel 0 0) (2 * t) _ hz
  have hconst (σ : Environment 5 3) : prep HP σ 0 0 = c := by
    let τ : RetainedPairSlice Xs Yu 0 0 := ⟨σ, by
      simp only [mem_filter, mem_univ, true_and]
      constructor <;> exact full_retains _ _⟩
    have h := congrFun hz' τ
    exact sub_eq_zero.mp h
  have hlow := hconst envLow
  have hhigh := hconst envHigh
  simp only [Pi.zero_apply, prep_eq, child, randomBit, envLow, envHigh, Pi.zero_apply,
    Pi.one_apply, decide_true, and_self, ↓reduceIte, one_ne_zero, decide_false,
    Bool.false_eq_true, false_and] at hlow hhigh
  linarith

-- The real Option completion produces the literal preparation list. Its input is
-- the nonconstant selected child above, and its steps are the production B.steps.
-- No claim is made that this arbitrary first history equals initialPrefixes.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ) :
    let B := PolynomialBudgetHistory.data HP
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
      ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 0 [1],
        gridChannel 2 0 [3], gridChannel 2 0 [3]⟩
    ∃ W, (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation 0 r (child randomBit))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W ∧
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 5 r.source.rate (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
          (retainedMask 2 (side 5 0) 1 [3])
          (actualNoiseEntry (0 : Fin 3) 2 (side 5 0) (side 5 0) (side 5 0) 1 [1] [3] 0
            B.base (firstSignalIncrement (fun _ => child randomBit) 0
              (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) 3))
            (fun _ _ _ _ => 0) 1 j) ≤ B.initialSecondNoiseMoment M r 3 j := by
  dsimp only
  let B := PolynomialBudgetHistory.data HP
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
    ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 0 [1],
      gridChannel 2 0 [3], gridChannel 2 0 [3]⟩
  have hc (i : ℕ) := B.complete_grid M r (0 : Fin 3) 2 (by decide) 0 0 [1] [3]
    rfl rfl (B.binPreparation 0 r (child randomBit)) (dyadicSlack (Nat.log2 M + 1) i)
  have hex : ∃ W, (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation 0 r (child randomBit))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W := by
    simp_rw [hc]
    exact ⟨_, List.mapM_pure⟩
  obtain ⟨W, hW⟩ := hex
  refine ⟨W, hW, ?_⟩
  intro j hj
  exact B.initialSecondSignal_noise_allocated M 0 r threeRoles smallHorizon 0 0 0
    (by decide) (by decide) [1] [3] rfl rfl rfl rfl
    (fun _ => child randomBit) W hW B.base 3 j hj

-- In particular finite computed lengths do not make this production noise zero.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M d : ℕ) :
    ∃ σ : Environment 5 3,
      0 < actualNoiseEntry (0 : Fin 3) 2 (side 5 0) (side 5 0) (side 5 0) 1 [1] [3] 0
        (fun _ _ => 0) (firstSignalIncrement (fun _ _ _ _ => 7) 0
          (secondSignalIncrement (fun _ => productionWalk HP
            ((PolynomialBudgetHistory.data HP).steps M (PolynomialBudgetHistory.request HP) d)) 3))
        (fun _ _ _ _ => 0) 1 0 σ 0 0 :=
  production_noise_pos HP _

-- Both input support and the zero boundary use genuine selected preparations.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 3) :
    #{y ∈ ({y | retainedMask threeRoles.terminal (side 5 0) (1 : ZMod 5) [3] σ y} :
      Finset (ZMod 5)) | prep HP σ 0 y ≠ 0} < HP.K ∧
    selectedPreparation HP 1 threeRoles [3] 0 (fun _ _ _ => 0) σ 0 0 = 0 := by
  exact ⟨selectedPreparation_support HP
    (FourthRootHierarchyParams.NormalizedRow.rank_pos HP) 1 threeRoles [3] 0
    (child randomBit) σ 0, selectedPreparation_zero HP 1 threeRoles [3] 0 σ 0 0⟩

example {P : ℕ} [Fact P.Prime] (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (B : BudgetData HP P) (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (j : ℕ) : B.initialSecondNoiseMoment M r 0 j = 0 := by
  simp only [BudgetData.initialSecondNoiseMoment, abs_zero, zero_mul,
    zero_pow (by decide : 4 ≠ 0), min_self]

-- The charge precedes every field, request and precision, with growing full bin,
-- source, terminal and usage horizons. Usage remains strictly narrower than rank.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ζ tolerance : ℝ)
    (ht : 0 < tolerance) :
    ∃ A : ℕ, ∀ (P : ℕ) [Fact P.Prime] (n p : ℕ) (H : Horizon P),
      n + 2 * A + (512 * HP.K + 1) + 2 ≤ H.maxExponent →
      let B : BudgetData HP P :=
        { PolynomialBudgetHistory.uniformData HP P (H.maxExponent) with rankCharge := A }
      let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
        ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 n [1],
          gridChannel 2 (n + 1) [2, 3], gridChannel 2 (n + 2) [2, 3]⟩
      let M := 16 * (A * r.task.rank + p + 4 * n + 4)
      B.requestPrecision M r = p + 2 ∧ 0 < B.requestPrecision M r ∧
      ∀ j, B.initialSecondNoiseMoment M r ζ j ≤
        (tolerance * (2 : ℝ) ^ (-((p : ℝ) + 2)) *
          (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  obtain ⟨A, hA⟩ := BudgetData.initialSecondNoiseMoment_exists_charge HP ζ tolerance ht
  refine ⟨A, ?_⟩
  intro P _ n p H hn
  dsimp only
  let B : BudgetData HP P :=
    { PolynomialBudgetHistory.uniformData HP P (H.maxExponent) with rankCharge := A }
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 n [1],
      gridChannel 2 (n + 1) [2, 3], gridChannel 2 (n + 2) [2, 3]⟩
  let M := 16 * (A * r.task.rank + p + 4 * n + 4)
  have hp : B.requestPrecision M r = p + 2 := by
    rw [B.requestPrecision_grid M n (n + 1) r rfl rfl]
    dsimp only [B, PolynomialBudgetHistory.uniformData, M]
    push_cast
    ring
  have hfield : (512 * HP.K + 1) * 2 ^ (2 * A) ≤ P := by
    calc
      _ ≤ 2 ^ (512 * HP.K + 1) * 2 ^ (2 * A) :=
        Nat.mul_le_mul_right _ (show 512 * HP.K + 1 ≤ 2 ^ (512 * HP.K + 1) from
          Nat.lt_two_pow_self.le)
      _ = 2 ^ ((512 * HP.K + 1) + 2 * A) := (pow_add _ _ _).symm
      _ ≤ 2 ^ H.maxExponent := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ P := H.side_admissible
  refine ⟨hp, by rw [hp]; positivity, ?_⟩
  intro j
  simpa only [hp] using hA B hfield M n r rfl (by rw [hp]; positivity) j

-- There are admissible prime fields at every such growing horizon; coverage is
-- satisfiable rather than an unsupported numerical hypothesis.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (A n : ℕ) :
    ∃ P, P.Prime ∧ ∃ H : Horizon P,
      H.maxExponent = n + 2 * A + (512 * HP.K + 1) + 2 := by
  obtain ⟨P, hP, _, _, H, he, _⟩ :=
    exists_bounded_depth_prime (n + 2 * A + (512 * HP.K + 1) + 2) 0 (by positivity)
  exact ⟨P, hP, H, he⟩


-- The actual computed true/one branch selects this scalar on its execution guards.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M n j : ℕ)
    (coefficient ζ Lh Lρ : ℝ) :
    let B := PolynomialBudgetHistory.data HP
    let r := PolynomialBudgetHistory.request HP
    B.initialComputedPrecisionMoment M n r threeRoles 0 0 [1] [2, 3]
      coefficient ζ Lh Lρ j true 1 = B.initialSecondNoiseMoment M r ζ j := by
  dsimp only
  let B := PolynomialBudgetHistory.data HP
  let r := PolynomialBudgetHistory.request HP
  have hadm : B.initialSecondNoiseAdmissible r threeRoles 0 0 [1] [2, 3] :=
    ⟨rfl, rfl, rfl, ⟨smallHorizon, by decide⟩, 0, by decide, rfl⟩
  have hs := B.initialComputedPrecisionMoment_secondNoise_le M n r threeRoles 0 0
    [1] [2, 3] coefficient ζ Lh Lρ j hadm
  exact (min_eq_left hs).symm.trans (B.initialSecondNoiseMoment_min_precision M n r
    threeRoles 0 0 [1] [2, 3] coefficient ζ Lh Lρ j)

-- A non-polynomial auxiliary input cannot silently receive the sparse polynomial salary.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M n j : ℕ)
    (coefficient ζ Lh Lρ : ℝ) :
    let B : BudgetData HP 5 :=
      { PolynomialBudgetHistory.data HP with auxiliary := fun _ _ => 0 }
    let r := PolynomialBudgetHistory.request HP
    ¬ B.initialSecondNoiseAdmissible r threeRoles 0 0 [1] [2, 3] ∧
      B.initialComputedPrecisionMoment M n r threeRoles 0 0 [1] [2, 3]
        coefficient ζ Lh Lρ j true 1 =
        (|ζ| * (2 : ℝ) ^ (-B.requestPrecision M r) *
          (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  dsimp only
  let B : BudgetData HP 5 :=
      { PolynomialBudgetHistory.data HP with auxiliary := fun _ _ => 0 }
  let r := PolynomialBudgetHistory.request HP
  have hadm : ¬ B.initialSecondNoiseAdmissible r threeRoles 0 0 [1] [2, 3] := by
    intro h
    have he := congrFun (congrFun h.1 0) HP.θ
    change (0 : ℝ) = polynomialPrepCutoff4 HP.θ HP.θ at he
    rw [polynomialPrepCutoff4_eq_one HP.θ_pos
      (show 3 * HP.θ / 4 ≤ HP.θ by linarith [HP.θ_pos])] at he
    norm_num at he
  refine ⟨hadm, ?_⟩
  have fallback (D : BudgetData HP 5)
      (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      (h : ¬ D.initialSecondNoiseAdmissible q threeRoles 0 0 [1] [2, 3]) :
      D.initialComputedPrecisionMoment M n q threeRoles 0 0 [1] [2, 3]
        coefficient ζ Lh Lρ j true 1 =
        (|ζ| * (2 : ℝ) ^ (-D.requestPrecision M q) *
          (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
    simp [BudgetData.initialComputedPrecisionMoment, BudgetData.initialComputedRelativeMoment,
      BudgetData.initialComputedMoment, h]
  exact fallback B r hadm

end SecondNoiseAllocation
