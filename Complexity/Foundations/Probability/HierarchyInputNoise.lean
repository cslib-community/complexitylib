/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInputProduct
public import Complexity.Foundations.Probability.HierarchyRelativeNoise

/-!
# Positive-only actual INPUT noise

The actual INPUT ray is C + Eᵢ C, with no negative correction. Its paired
input splits into the canonical zero/positive boundary and two actual endpoint
errors. All terms share the environment. The production walk, source and pair
densities, decoder denominator and prefix cube remain unchanged.

The proofs adapt Christian Reitwiessner's residual noise APIs; conditional walk
execution retains Samuel Schlesinger's hierarchy construction. These are finite
noise payments, not a uniform precision allocation or recursive availability theorem.
The exhausted final mean still omits the whole positive canonical ray. Paying that
mean (including any finite coverage gap) and incoming PREP is the next consumer;
this module does not pay RAW's noise-plus-mean error or the full reserve.

## Main results

* `decodedGroupInput_input_split`: actual input equals semantic boundary plus transport.
* `inputTransportedGroupInput_centered_relative_minkowski_le`: both endpoint root costs.
* `inputSemantic_centered_relative_fourth_le`: finite canonical boundary cost.
* `rawFirstPrefixes_input_finite_noise`: complete first-channel decoder noise consumer.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability Cslib.RowCompression NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P) (a : Fin HP.k)

/-- Genuine task-indexed positive ray; `none` is zero and is never summed. -/
@[expose] def inputCanonicalRay
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : Option ℕ) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  match bin with
  | none => 0
  | some b => fun σ => HierarchyTask.rawPositiveSample (channels B.padding)
      0 b (.input a) r.source (midpoint r) r.terminal (B.binRate b)
      (fun q => B.residualCanonicalChild b q σ)

/-- Budget-independent canonical sampling at positive endpoints, with the genuine
zero boundary. The ray list contains only the listed positive bins. -/
@[expose] def inputSemanticGroupInput (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  fun σ x y => ((B.rays (.input a)).map fun bin =>
    (if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0
      then 0 else B.inputCanonicalRay a r bin σ x y) -
    (if LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0
      then 0 else B.inputCanonicalRay a r bin σ x y)).sum

/-- The actual transported fine error minus the actual transported coarse error.
No canonical support or equality between different positive endpoint calls is assumed. -/
@[expose] def inputTransportedGroupInput
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  fun σ x y => ((B.rays (.input a)).map fun bin =>
    (((B.sample history (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin))
        (.input a) r bin).getD 0 σ x y) -
      (if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0
        then 0 else B.inputCanonicalRay a r bin σ x y)) -
    (((B.sample history (LogSpaceEstimation.lastBudget M (2 * d) B.slack
        (B.sampleScale r bin)) (.input a) r bin).getD 0 σ x y) -
      (if LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0
        then 0 else B.inputCanonicalRay a r bin σ x y))).sum

/-- The positive reference and the two transported endpoint perturbations reconstruct
exactly the executed input. This identity does not require successful calls. -/
theorem decodedGroupInput_input_split
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    B.decodedGroupInput history M d (.input a) r =
      B.inputSemanticGroupInput a M d r + B.inputTransportedGroupInput a history M d r := by
  funext σ x y
  simp only [decodedGroupInput, inputSemanticGroupInput, inputTransportedGroupInput,
    Pi.add_apply, Matrix.add_apply, ← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro bin _
  ring

/-- Semantic cancellation concerns zero versus positive status, not equality of
actual samples at different positive budgets. Fine bins exhausted at both ends cancel too. -/
theorem inputSemanticGroupInput_eq_zero_of_two_mul_lt (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hd : 2 * d < M) :
    B.inputSemanticGroupInput a M d r = 0 := by
  funext σ x y
  unfold inputSemanticGroupInput
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨bin, _, rfl⟩ := List.mem_map.mp ha
  have hz : (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0) ↔
      (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0) := by
    unfold LogSpaceEstimation.lastBudget
    omega
  simp only [hz, sub_self]

/-- Before the semantic boundary, the ACTUAL input is precisely its transported
perturbation. It need not vanish, even if both endpoint calls succeed. -/
theorem decodedGroupInput_input_eq_transported_of_two_mul_lt
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hd : 2 * d < M) :
    B.decodedGroupInput history M d (.input a) r =
      B.inputTransportedGroupInput a history M d r := by
  rw [B.decodedGroupInput_input_split a,
    B.inputSemanticGroupInput_eq_zero_of_two_mul_lt a M d r hd, zero_add]

/-- Beyond the parent boundary all actual endpoints are zero, without a positive
history call or any accuracy assertion at budget zero. -/
theorem decodedGroupInput_input_eq_zero_of_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hd : M ≤ d) :
    B.decodedGroupInput history M d (.input a) r = 0 := by
  have hf (bin : Option ℕ) :
      LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  have hc (bin : Option ℕ) :
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  funext σ x y
  simp [decodedGroupInput, hf, hc, B.sample_zero]

/-- The actual conditional budget separates semantic sampling from transported
endpoint perturbations, with the fixed factor eight for arbitrary correlation.
All pair densities, denominators and actual spectral factors remain inside both
budgets. Paying the transported term from own-request IH is still required. -/
theorem rawRelativeNoiseBudget_input_split_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (j : ℕ) :
    B.rawRelativeNoiseBudget M r s t hst ks ku ss su
      (fun i => B.decodedGroupInput history M (dyadicSlack (Nat.log2 M + 1) i)
        (.input a) r) G j ≤
      8 * (B.rawRelativeNoiseBudget M r s t hst ks ku ss su
        (fun i => B.inputSemanticGroupInput a M (dyadicSlack (Nat.log2 M + 1) i) r) G j +
      B.rawRelativeNoiseBudget M r s t hst ks ku ss su
        (fun i => B.inputTransportedGroupInput a history M
          (dyadicSlack (Nat.log2 M + 1) i) r) G j) := by
  let Xs := retainedMask s (side P ks) B.padding ss
  let Yu := retainedMask t (side P ku) B.padding su
  let graphs := graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
    (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su)
  let S := fun i => B.inputSemanticGroupInput a M (dyadicSlack (Nat.log2 M + 1) i) r
  let E := fun i => B.inputTransportedGroupInput a history M
    (dyadicSlack (Nat.log2 M + 1) i) r
  let q := fun (A : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) i x y =>
    (({σ | Xs σ x ∧ Yu σ y} : Finset (Environment P 3)).dens : ℝ) *
      (2 * (graphs x y).spectralExpansion ^
        (2 * B.steps M r (dyadicSlack (Nat.log2 M + 1) i)) *
        𝔼 σ ∈ ({σ | Xs σ x ∧ Yu σ y} : Finset (Environment P 3)),
          |(A i σ x y - rowSliceMean Xs Yu (A i) x y) / (rate ku + G x y)| ^ 4)
  have hq (i : ℕ) (x y : ZMod P) :
      q (fun i => S i + E i) i x y ≤ 8 * (q S i x y + q E i x y) := by
    have hp (σ : Environment P 3) :
        |((S i + E i) σ x y - rowSliceMean Xs Yu (S i + E i) x y) /
            (rate ku + G x y)| ^ 4 ≤
          8 * (|(S i σ x y - rowSliceMean Xs Yu (S i) x y) /
            (rate ku + G x y)| ^ 4 +
          |(E i σ x y - rowSliceMean Xs Yu (E i) x y) /
            (rate ku + G x y)| ^ 4) := by
      simp only [rowSliceMean, Pi.add_apply, Matrix.add_apply, expect_add_distrib]
      rw [show (S i σ x y + E i σ x y -
          ((𝔼 τ ∈ {τ | Xs τ x ∧ Yu τ y}, S i τ x y) +
            𝔼 τ ∈ {τ | Xs τ x ∧ Yu τ y}, E i τ x y)) / (rate ku + G x y) =
          (S i σ x y - 𝔼 τ ∈ {τ | Xs τ x ∧ Yu τ y}, S i τ x y) /
            (rate ku + G x y) +
          (E i σ x y - 𝔼 τ ∈ {τ | Xs τ x ∧ Yu τ y}, E i τ x y) /
            (rate ku + G x y) by ring]
      have ht := add_pow_le
        (abs_nonneg ((S i σ x y - rowSliceMean Xs Yu (S i) x y) / (rate ku + G x y)))
        (abs_nonneg ((E i σ x y - rowSliceMean Xs Yu (E i) x y) / (rate ku + G x y))) 4
      norm_num only [Nat.reduceSub, Nat.reducePow] at ht
      exact (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) 4).trans ht
    have he := expect_le_expect (s := {σ | Xs σ x ∧ Yu σ y}) (fun σ _ => hp σ)
    simp only [expect_add_distrib, ← mul_expect] at he
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤
        (({σ | Xs σ x ∧ Yu σ y} : Finset (Environment P 3)).dens : ℝ) *
          (2 * (graphs x y).spectralExpansion ^
            (2 * B.steps M r (dyadicSlack (Nat.log2 M + 1) i))) by
      exact mul_nonneg (by positivity) (mul_nonneg (by norm_num)
        (pow_nonneg (RotationMap.spectralExpansion_nonneg _) _)))
    dsimp only [q]
    nlinarith only [hh]
  have hNu : 0 ≤ ((P : ℝ) * r.source.rate)⁻¹ := by
    rw [hs]
    exact inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le)
  simp_rw [B.decodedGroupInput_input_split a]
  change (j : ℝ) ^ 3 * ∑ i ∈ range j,
    ((P : ℝ) * r.source.rate)⁻¹ * ∑ x, ∑ y, q (fun i => S i + E i) i x y ≤ _
  calc
    _ ≤ (j : ℝ) ^ 3 * ∑ i ∈ range j,
        ((P : ℝ) * r.source.rate)⁻¹ * ∑ x, ∑ y, 8 * (q S i x y + q E i x y) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum; intro i _
      apply mul_le_mul_of_nonneg_left _ hNu
      apply sum_le_sum; intro x _
      apply sum_le_sum; intro y _
      exact hq i x y
    _ = _ := by
      simp only [mul_add, sum_add_distrib, ← mul_sum, rawRelativeNoiseBudget]
      dsimp only [q, S, E, Xs, Yu, graphs]
      ring

/-- Both positive literal endpoint root allowances, with exhausted endpoints zero. -/
@[expose] def inputEndpointRootSum (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (e : ℕ → Option ℕ → ℝ) : ℝ :=
  ∑ bin ∈ (B.bins.image some),
    ((if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0 then 0
      else e (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)) bin) +
    (if LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0 then 0
      else e (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)) bin))

omit [Fact P.Prime] in
/-- Full exhaustion removes all endpoint costs without any IH, even if the
allowances are nonzero. This holds for every listed bin and every denominator. -/
theorem inputEndpointRootSum_eq_zero_of_le (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (e : ℕ → Option ℕ → ℝ)
    (hd : M ≤ d) : B.inputEndpointRootSum M d r e = 0 := by
  have hf (bin : Option ℕ) :
      LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  have hc (bin : Option ℕ) :
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  simp [inputEndpointRootSum, hf, hc]

/-- Relative endpoint errors are summed before centering. Both actual positive
budgets are paid; zero endpoints need no accuracy. The denominator is fixed by
the pair, so division commutes with its conditional mean even at a zero divisor. -/
theorem inputTransportedGroupInput_centered_relative_minkowski_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (X Y : Environment P 3 → ZMod P → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] (hNu : 0 ≤ (P : ℝ) * r.source.rate)
    (den : Matrix (ZMod P) (ZMod P) ℝ) (e : ℕ → Option ℕ → ℝ)
    (he0 : ∀ m bin, 0 ≤ e m bin)
    (he : ∀ bin ∈ B.rays (.input a), ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) ∨
        m = LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)) →
      rowNormPow 4 P r.source.rate X Y
        (fun σ x y => ((B.sample history m (.input a) r bin).getD 0 σ x y -
          B.inputCanonicalRay a r bin σ x y) / den x y) ≤ e m bin ^ 4) :
    rowNormPow 4 P r.source.rate X Y (fun σ x y =>
      (B.inputTransportedGroupInput a history M d r σ x y -
        rowSliceMean X Y (B.inputTransportedGroupInput a history M d r) x y) / den x y) ≤
      16 * B.inputEndpointRootSum M d r e ^ 4 := by
  unfold inputEndpointRootSum
  let S := (B.bins.image some)
  let E := fun m bin σ x y => ((B.sample history m (.input a) r bin).getD 0 σ x y -
    (if m = 0 then 0 else B.inputCanonicalRay a r bin σ x y)) / den x y
  let allowance := fun m bin => if m = 0 then 0 else e m bin
  let f := fun bin => LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
  let c := fun bin => LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
  have hS (bin : Option ℕ) : bin ∈ S ↔ bin ∈ B.rays (.input a) := by
    simp only [S, rays, List.append_nil, List.mem_map, mem_toList, mem_image]
  have ha (m : ℕ) (bin : Option ℕ) : 0 ≤ allowance m bin := by
    dsimp only [allowance]; split_ifs <;> first | positivity | exact he0 _ _
  have hE (m : ℕ) (bin : Option ℕ) (hb : bin ∈ S)
      (hmc : m = f bin ∨ m = c bin) :
      rowNormPow 4 P r.source.rate X Y (E m bin) ≤ allowance m bin ^ 4 := by
    by_cases hm : m = 0
    · subst m; simp [E, allowance, B.sample_zero, rowNormPow]
    · simpa only [E, allowance, hm, ↓reduceIte] using he bin ((hS bin).mp hb) m (by omega) hmc
  have hpair (bin : Option ℕ) (hb : bin ∈ S) :
      rowNormPow 4 P r.source.rate X Y
        (fun σ x y => E (f bin) bin σ x y - E (c bin) bin σ x y) ≤
          (allowance (f bin) bin + allowance (c bin) bin) ^ 4 := by
    have h := rowNormPow_sum_le_pow_sum (X := X) (by decide : 4 ≠ 0) hNu Y
      (univ : Finset Bool)
      (fun b => if b then E (f bin) bin else -E (c bin) bin)
      (fun _ => 1) (fun b => if b then allowance (f bin) bin else allowance (c bin) bin)
      (by intros; norm_num) (by intro b _; cases b <;> exact ha _ _)
      (by
        intro b _; cases b
        · simpa only [Bool.false_eq_true, ↓reduceIte, rowNormPow, Pi.neg_apply, abs_neg]
            using hE (c bin) bin hb (Or.inr rfl)
        · exact hE (f bin) bin hb (Or.inl rfl))
    simpa only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, one_mul, Pi.neg_apply,
      sub_eq_add_neg, add_comm] using h
  have hsum (v : Option ℕ → ℝ) :
      ((B.rays (.input a)).map v).sum = ∑ bin ∈ S, v bin := by
    rw [show S = _ from rfl, sum_image (fun _ _ _ _ h => Option.some.inj h)]
    simp only [rays, List.append_nil, List.map_map, Function.comp_def, sum_map_toList]
  have hin : (fun σ x y => B.inputTransportedGroupInput a history M d r σ x y /
      den x y) =
      fun σ x y => ∑ bin ∈ S, (E (f bin) bin σ x y - E (c bin) bin σ x y) := by
    funext σ x y
    change (((B.rays (.input a)).map _).sum / den x y) = _
    rw [hsum, Finset.sum_div]
    apply sum_congr rfl
    intro bin _
    dsimp only [E, f, c]
    ring
  have hi := rowNormPow_sum_le_pow_sum (X := X) (by decide : 4 ≠ 0) hNu Y S
    (fun bin σ x y => E (f bin) bin σ x y - E (c bin) bin σ x y)
    (fun _ => 1) (fun bin => allowance (f bin) bin + allowance (c bin) bin)
    (by intros; norm_num) (by intro bin _; exact add_nonneg (ha _ _) (ha _ _)) hpair
  simp only [one_mul] at hi
  rw [← hin] at hi
  have hc := rowNormPow_centered_sub_fourth_le hNu X Y
    (fun σ x y => B.inputTransportedGroupInput a history M d r σ x y / den x y) 0
  simp only [rowSliceMean, Pi.zero_apply, expect_const_zero, sub_zero,
    ← expect_div, ← sub_div] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left hi (by norm_num))


/-- Positive INPUT rays contain only the listed bins; the empty list is literal zero.
Success is required only of actual paired calls, which handle equal and zero endpoints
without child calls. General-product children remain inside them. -/
theorem completedGroup_input_of_paired
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (A : Option ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : ∀ bin ∈ B.rays (.input a),
      B.pairedSample history M d (.input a) r bin = some (A bin)) :
    B.completedGroup history M d (.input a) r = some (conditionalWalk
      (X s (side P ks) (CopyPadding.identifier B.padding ss))
      (Y t (side P ku) (CopyPadding.identifier B.padding su))
      (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
        (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
      (fun _ _ => B.steps M r d)
      (fun σ x y => ((B.rays (.input a)).map (fun bin => A bin σ x y)).sum)) := by
  have hm : (B.rays (.input a)).mapM (B.pairedSample history M d (.input a) r) =
      some ((B.rays (.input a)).map A) := by
    apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact hA
  by_cases hempty : B.bins = ∅
  · simp only [completedGroup, rays, hempty, toList_empty, List.map_nil,
      List.append_nil, List.isEmpty_nil, ↓reduceIte, Option.some.injEq]
    funext σ x y
    symm
    simpa only [Pi.zero_apply, Matrix.zero_apply, List.sum_nil, ite_self] using
      conditionalWalk_const
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y t (side P ku) (CopyPadding.identifier B.padding su))
        (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
          (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
        (fun _ _ => B.steps M r d) (fun _ _ : ZMod P => (0 : ℝ)) σ x y
  have he : (B.rays (.input a)).isEmpty = false := by simp [rays, hempty]
  unfold completedGroup
  rw [he]
  simp only [Bool.false_eq_true, ↓reduceIte, hm, bind, Option.bind_some,
    List.map_map, Function.comp_def]
  exact B.complete_grid M r s t hst ks ku ss su hs hu _ d

/-- Actual input prefix noise from successful literal paired samples. The input
family is constrained by execution, rather than by an assumed output/noise bound.
The empty prefix is included. The retained obligation is an input moment, not an IH
or a claim of fixed-constant allocation over unbounded rate/bin families. -/
theorem rawFirstPrefixes_input_relative_noise
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (A : ℕ → Option ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (j : ℕ) (hj : j ≤ Nat.log2 M + 1)
    (hA : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays (.input a),
      B.pairedSample history M (dyadicSlack (Nat.log2 M + 1) i) (.input a) r bin =
        some (A i bin))
    (G : Matrix (ZMod P) (ZMod P) ℝ) :
    let Xs := retainedMask s (side P ks) B.padding ss
    let Yu := retainedMask t (side P ku) B.padding su
    let F := B.rawFirstPrefixes history M (.input a) r
    rowNormPow 4 P r.source.rate Xs Yu
      (fun σ x y => (F j σ x y - rowSliceMean Xs Yu (F j) x y) / (rate ku + G x y)) ≤
      B.rawRelativeNoiseBudget M r s t hst ks ku ss su
        (fun i σ x y => ((B.rays (.input a)).map (fun bin => A i bin σ x y)).sum) G j := by
  dsimp only
  let input := fun i σ x y => ((B.rays (.input a)).map (fun bin => A i bin σ x y)).sum
  let Xs := retainedMask s (side P ks) B.padding ss
  let Yu := retainedMask t (side P ku) B.padding su
  let graphs := graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
    (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su)
  let W := fun i => conditionalWalk Xs Yu graphs
    (fun _ _ => B.steps M r (dyadicSlack (Nat.log2 M + 1) i)) (input i)
  have hF : B.rawFirstPrefixes history M (.input a) r j =
      fun σ x y => ∑ i ∈ range j, W i σ x y := by
    funext σ x y
    apply sum_congr rfl
    intro i hi
    rw [B.completedGroup_input_of_paired a history M _ r s t hst ks ku ss su hs hu
      (A i) (hA i ((mem_range.mp hi).trans_le hj)), Option.getD_some]
    rfl
  have hmean (x y : ZMod P) : rowSliceMean Xs Yu
      (B.rawFirstPrefixes history M (.input a) r j) x y =
      ∑ i ∈ range j, rowSliceMean Xs Yu (input i) x y := by
    rw [hF]
    unfold rowSliceMean
    rw [expect_sum_comm]
    apply sum_congr rfl
    intro i _
    exact rowSliceMean_conditionalWalk _ _ _ _ _ x y
  change rowNormPow 4 P r.source.rate Xs Yu (fun σ x y =>
    (B.rawFirstPrefixes history M (.input a) r j σ x y -
      rowSliceMean Xs Yu (B.rawFirstPrefixes history M (.input a) r j) x y) /
        (rate ku + G x y)) ≤ _
  simp_rw [hmean]
  rw [hF]
  simp_rw [← sum_sub_distrib, sum_div]
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  apply (rowNormPow_sum_fourth_le _ hNu _ _ _).trans
  simp only [card_range, rawRelativeNoiseBudget]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro i _
  exact rowNormPow_conditionalWalk_div_le_sum _ _ hNu _ _ _ _

/-- Full-terminal first-channel decoder noise, with arbitrary second increments.
Its denominator-retaining payment is the actual paired-input conditional budget.
Completion availability and payment of that budget from child IH remain separate. -/
theorem rawFirstPrefixes_input_actualNoiseEntry
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (husage : r.usage = r.terminal)
    (A : ℕ → Option ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (i : ℕ) (hi : i < Nat.log2 M + 1)
    (hA : ∀ j < Nat.log2 M + 1, ∀ bin ∈ B.rays (.input a),
      B.pairedSample history M (dyadicSlack (Nat.log2 M + 1) j) (.input a) r bin =
        some (A j bin))
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ) :
    rowNormPow 4 P r.source.rate
      (retainedMask s (side P ks) B.padding ss) (retainedMask t (side P ka) B.padding st)
      (actualNoiseEntry s t (side P ks) (side P ka) (side P ka) B.padding ss st ka G
        (firstSignalIncrement (B.rawFirstPrefixes history M (.input a) r) ka second) 0 0 i) ≤
      B.rawRelativeNoiseBudget M r s t hst ks ka ss st
        (fun j σ x y => ((B.rays (.input a)).map (fun bin => A j bin σ x y)).sum) G (i + 1) := by
  rw [actualNoiseEntry_first_prefix_row_eq s t (side P ks) (side P ka) (side P ka)
    B.padding ss st _ ka G hG second 0 (by intros; rfl)]
  simp only [rowSliceMean, ← expect_div, ← sub_div]
  exact B.rawFirstPrefixes_input_relative_noise a history M r s t hst ks ka ss st hs
    (husage.trans ht) A (i + 1) (by omega) hA G

/-- The same decoder payment expressed only with literal endpoint availability.
Equal endpoints make no calls; zero endpoints need no positive-budget success.
`decodedGroupInput` retains only positive bins and both real last budgets.
Own-request accuracy is deliberately not inferred from this availability premise. -/
theorem rawFirstPrefixes_input_decoded_noise
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (husage : r.usage = r.terminal)
    (hcalls : ∀ j < Nat.log2 M + 1, ∀ bin ∈ B.rays (.input a),
      let d := dyadicSlack (Nat.log2 M + 1) j
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f (.input a) r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c (.input a) r bin = some C))
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    (i : ℕ) (hi : i < Nat.log2 M + 1) :
    rowNormPow 4 P r.source.rate
      (retainedMask s (side P ks) B.padding ss) (retainedMask t (side P ka) B.padding st)
      (actualNoiseEntry s t (side P ks) (side P ka) (side P ka) B.padding ss st ka G
        (firstSignalIncrement (B.rawFirstPrefixes history M (.input a) r) ka second) 0 0 i) ≤
      B.rawRelativeNoiseBudget M r s t hst ks ka ss st
        (fun j => B.decodedGroupInput history M (dyadicSlack (Nat.log2 M + 1) j)
          (.input a) r) G (i + 1) := by
  let A := fun j bin =>
    (B.sample history (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r bin)) (.input a) r bin).getD 0 -
    (B.sample history (LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r bin)) (.input a) r bin).getD 0
  have hA (j : ℕ) (hj : j < Nat.log2 M + 1) (bin : Option ℕ)
      (hb : bin ∈ B.rays (.input a)) :
      B.pairedSample history M (dyadicSlack (Nat.log2 M + 1) j) (.input a) r bin =
        some (A j bin) :=
    B.pairedSample_decoded history M _ (.input a) r bin (hcalls j hj bin hb)
  exact B.rawFirstPrefixes_input_actualNoiseEntry a history M r s t hst ks ka ss st hs ht
    husage A i hi hA G hG second

/-- Literal boundary coefficient: exhausted endpoints are zero, positive ones one. -/
@[expose] def inputBoundaryCoefficient (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : Option ℕ) : ℝ :=
  (if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0 then 0 else 1) -
  (if LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0 then 0 else 1)

/-- Finite canonical relative endpoint cap, with the denominator inside the norm. -/
@[expose] def inputCanonicalRelativeCap
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (den : Matrix (ZMod P) (ZMod P) ℝ) (bin : Option ℕ) : ℝ :=
  ‖fun z : Environment P 3 × (ZMod P × ZMod P) =>
    B.inputCanonicalRay a r bin z.1 z.2.1 z.2.2 / den z.2.1 z.2.2‖

/-- Boundary-weighted sum of finite canonical endpoint caps. No negative ray. -/
@[expose] def inputBoundaryCapSum (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (den : Matrix (ZMod P) (ZMod P) ℝ) : ℝ :=
  ∑ bin ∈ B.bins.image some,
    |B.inputBoundaryCoefficient M d r bin| * B.inputCanonicalRelativeCap a r den bin

/-- The semantic boundary is paid even when all positive endpoint errors vanish.
This finite bound uses no support approximation or independence. -/
theorem inputSemantic_centered_relative_fourth_le
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (X Y : Environment P 3 → ZMod P → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] (hNu : 0 ≤ (P : ℝ) * r.source.rate)
    (den : Matrix (ZMod P) (ZMod P) ℝ) :
    rowNormPow 4 P r.source.rate X Y (fun σ x y =>
      (B.inputSemanticGroupInput a M d r σ x y -
        rowSliceMean X Y (B.inputSemanticGroupInput a M d r) x y) / den x y) ≤
      16 * (B.inputBoundaryCapSum a M d r den) ^ 4 *
        rowNormPow 4 P r.source.rate X Y (fun _ _ _ => 1) := by
  have hid (σ x y) : B.inputSemanticGroupInput a M d r σ x y / den x y =
      ∑ bin ∈ B.bins.image some, B.inputBoundaryCoefficient M d r bin *
        (B.inputCanonicalRay a r bin σ x y / den x y) := by
    rw [sum_image (fun _ _ _ _ h => Option.some.inj h)]
    simp only [inputSemanticGroupInput, rays, List.append_nil, List.map_map,
      Function.comp_def, sum_map_toList, Finset.sum_div]
    apply sum_congr rfl
    intro b _
    unfold inputBoundaryCoefficient
    split_ifs <;> ring
  have hpoint (σ x y) : |B.inputSemanticGroupInput a M d r σ x y / den x y| ≤
      B.inputBoundaryCapSum a M d r den := by
    rw [hid]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro bin _
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact (show |(fun z : Environment P 3 × (ZMod P × ZMod P) =>
      B.inputCanonicalRay a r bin z.1 z.2.1 z.2.2 / den z.2.1 z.2.2) (σ, x, y)| ≤
        B.inputCanonicalRelativeCap a r den bin from by
      simpa only [inputCanonicalRelativeCap, Real.norm_eq_abs] using norm_le_pi_norm
        (fun z : Environment P 3 × (ZMod P × ZMod P) =>
          B.inputCanonicalRay a r bin z.1 z.2.1 z.2.2 / den z.2.1 z.2.2) (σ, x, y))
  have hi : rowNormPow 4 P r.source.rate X Y
      (fun σ x y => B.inputSemanticGroupInput a M d r σ x y / den x y) ≤
      (B.inputBoundaryCapSum a M d r den) ^ 4 *
        rowNormPow 4 P r.source.rate X Y (fun _ _ _ => 1) := by
    apply rowNormPow_le_mul hNu
    intro σ x y _ _
    simpa only [abs_one, one_pow, mul_one] using
      pow_le_pow_left₀ (abs_nonneg _) (hpoint σ x y) 4
  have hc := rowNormPow_centered_sub_fourth_le hNu X Y
    (fun σ x y => B.inputSemanticGroupInput a M d r σ x y / den x y) 0
  simp only [rowSliceMean, Pi.zero_apply, expect_const_zero, sub_zero,
    ← expect_div, ← sub_div] at hc
  exact (hc.trans (mul_le_mul_of_nonneg_left hi (by norm_num))).trans_eq (by ring)

/-- Fixed finite production spectral factor, at the unchanged walk length. -/
@[expose] def inputNoiseSpectralFactor (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P)) (i : ℕ) : ℝ :=
  ‖fun xy : ZMod P × ZMod P => 2 *
    (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
      (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su)
      xy.1 xy.2).spectralExpansion ^
        (2 * B.steps M r (dyadicSlack (Nat.log2 M + 1) i))‖

/-- A finite semantic-plus-transport payment. This is not a uniform allocation. -/
@[expose] def inputFiniteNoisePayment (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (G : Matrix (ZMod P) (ZMod P) ℝ) (j : ℕ)
    (e : ℕ → ℕ → Option ℕ → ℝ) : ℝ :=
  let X := retainedMask s (side P ks) B.padding ss
  let Y := retainedMask t (side P ku) B.padding su
  let W := rowNormPow 4 P r.source.rate X Y (fun _ _ _ => 1)
  8 * ((j : ℝ) ^ 3 * ∑ i ∈ range j,
    B.inputNoiseSpectralFactor M r s t hst ks ku ss su i *
      (16 * B.inputBoundaryCapSum a M (dyadicSlack (Nat.log2 M + 1) i)
        r (fun x y => rate ku + G x y) ^ 4 * W +
      16 * B.inputEndpointRootSum M (dyadicSlack (Nat.log2 M + 1) i) r (e i) ^ 4))

/-- Complete finite INPUT noise payment from own positive endpoint moments.
Semantic boundary and transported errors are both paid on the actual masks;
no target output/noise estimate is an assumption. -/
theorem rawRelativeNoiseBudget_input_finite_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (j : ℕ)
    (e : ℕ → ℕ → Option ℕ → ℝ) (he0 : ∀ i m bin, 0 ≤ e i m bin)
    (he : ∀ i ∈ range j, ∀ bin ∈ B.rays (.input a), ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) i)
        B.slack (B.sampleScale r bin) ∨
      m = LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) i)
        B.slack (B.sampleScale r bin)) →
      rowNormPow 4 P r.source.rate
        (retainedMask s (side P ks) B.padding ss)
        (retainedMask t (side P ku) B.padding su)
        (fun σ x y => ((B.sample history m (.input a) r bin).getD 0 σ x y -
          B.inputCanonicalRay a r bin σ x y) / (rate ku + G x y)) ≤ e i m bin ^ 4) :
    B.rawRelativeNoiseBudget M r s t hst ks ku ss su
      (fun i => B.decodedGroupInput history M (dyadicSlack (Nat.log2 M + 1) i)
        (.input a) r) G j ≤ B.inputFiniteNoisePayment a M r s t hst ks ku ss su G j e := by
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hS := B.rawRelativeNoiseBudget_le_of_centered_fourth M r s t hst ks ku ss su hs
    (fun i => B.inputSemanticGroupInput a M (dyadicSlack (Nat.log2 M + 1) i) r) G j _
    (fun i _ => B.inputSemantic_centered_relative_fourth_le a M _ r _ _ hNu _)
  have hT := B.rawRelativeNoiseBudget_le_of_centered_fourth M r s t hst ks ku ss su hs
    (fun i => B.inputTransportedGroupInput a history M (dyadicSlack (Nat.log2 M + 1) i) r) G j _
    (fun i hi => B.inputTransportedGroupInput_centered_relative_minkowski_le a history M _ r
      _ _ hNu _ (e i) (he0 i) (he i hi))
  have hsplit := B.rawRelativeNoiseBudget_input_split_le a history M r s t hst
    ks ku ss su hs G j
  unfold inputFiniteNoisePayment
  simp only [mul_add, sum_add_distrib, inputNoiseSpectralFactor] at hS hT ⊢
  linarith only [hS, hT, hsplit]

/-- Actual first-channel decoder noise with finite boundary and endpoint payment.
Successful positive calls and endpoint accuracy are independent hypotheses. -/
theorem rawFirstPrefixes_input_finite_noise
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (husage : r.usage = r.terminal)
    (hcalls : ∀ j < Nat.log2 M + 1, ∀ bin ∈ B.rays (.input a),
      let d := dyadicSlack (Nat.log2 M + 1) j
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f (.input a) r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c (.input a) r bin = some C))
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    (i : ℕ) (hi : i < Nat.log2 M + 1)
    (e : ℕ → ℕ → Option ℕ → ℝ) (he0 : ∀ i m bin, 0 ≤ e i m bin)
    (he : ∀ l ∈ range (i + 1), ∀ bin ∈ B.rays (.input a), ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) l)
        B.slack (B.sampleScale r bin) ∨
      m = LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) l)
        B.slack (B.sampleScale r bin)) →
      rowNormPow 4 P r.source.rate
        (retainedMask s (side P ks) B.padding ss)
        (retainedMask t (side P ka) B.padding st)
        (fun σ x y => ((B.sample history m (.input a) r bin).getD 0 σ x y -
          B.inputCanonicalRay a r bin σ x y) / (rate ka + G x y)) ≤ e l m bin ^ 4) :
    rowNormPow 4 P r.source.rate
      (retainedMask s (side P ks) B.padding ss) (retainedMask t (side P ka) B.padding st)
      (actualNoiseEntry s t (side P ks) (side P ka) (side P ka) B.padding ss st ka G
        (firstSignalIncrement (B.rawFirstPrefixes history M (.input a) r) ka second) 0 0 i) ≤
      B.inputFiniteNoisePayment a M r s t hst ks ka ss st G (i + 1) e := by
  exact (B.rawFirstPrefixes_input_decoded_noise a history M r s t hst ks ka ss st hs ht
    husage hcalls G hG second i hi).trans
      (B.rawRelativeNoiseBudget_input_finite_le a history M r s t hst ks ka ss st hs
        G (i + 1) e he0 he)

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
