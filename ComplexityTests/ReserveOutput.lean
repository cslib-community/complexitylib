/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of common envelopes and actual finite reserve output)
import Complexity.Computability.LogSpaceDerandomization.NormalizedAtomRows.ReserveOutput

/-! Actual full-matrix two-bin input, nonzero common envelopes and empty prefixes. -/
set_option linter.privateModule false
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace ReserveOutputRegression
private theorem large_K (HP : FourthRootHierarchyParams 16 1 16 32 8) : 5 < HP.K := by
  have hg := HP.gate
  have hn : 0 ≤ 32 * (HP.k : ℝ) / HP.η :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) HP.η_pos.le
  have hk : (5 : ℝ) < HP.K := by linarith
  exact_mod_cast hk
private def roles : RoleProfile 4 := ⟨0, 1, 2, by decide, by decide, by decide⟩
private def value (σ : Environment 5 4) : ℝ := if (σ 3).1 0 = 0 then 1 else 2
private def estimates (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (_precision _bin : ℕ) (r : HierarchyTask.Request HP.k (Fin 4) (ZMod 5))
    (σ : Environment 5 4) : Matrix (ZMod 5) (ZMod 5) ℝ :=
  match r.task with | .baseNormalized _ _ => fun _ _ => value σ | _ => fun _ _ => 1
private def prep (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (_precision _bin : ℕ) (_r : HierarchyTask.Request HP.k (Fin 4) (ZMod 5))
    (_σ : Environment 5 4) : Matrix (ZMod 5) (ZMod 5) ℝ := fun _ _ => 1
private def maximum (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (_precision _bin : ℕ) (_r : HierarchyTask.Request HP.k (Fin 4) (ZMod 5))
    (_σ : Environment 5 4) : ZMod 5 → ℝ := fun _ => 0

private def fixtureCutoff (i : ℕ) (d : ℝ) : ℝ := min 4 (max 0 ((i + 1) * d))

private lemma fixtureCutoff_range (i : ℕ) (d : ℝ) :
    fixtureCutoff i d ∈ Set.Icc 0 4 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

private lemma dense (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (bin : ℕ) (hbin : bin ≤ 1) (s t : Fin 4) (hst : s ≠ t) (ss st : List (ZMod 5))
    (σ : Environment 5 4) (x y : ZMod 5) :
    normalizedRequest 1 id
      (⟨HierarchyTask.baseNormalized 0 bin, gridChannel s 0 ss, gridChannel t 0 st,
        gridChannel t 0 st⟩ : HierarchyTask.Request HP.k (Fin 4) (ZMod 5))
      (fixtureCutoff bin) HP.ρ HP.K (fun σ _ _ => value σ)
      (fun _ _ _ => 1) σ x y = (bin + 1) * value σ := by
  have hr : Admissible (⟨HierarchyTask.baseNormalized 0 bin, gridChannel s 0 ss,
      gridChannel t 0 st, gridChannel t 0 st⟩ : HierarchyTask.Request HP.k (Fin 4) (ZMod 5)) :=
    ⟨hst, rfl, rfl⟩
  have hs : side 5 0 = 5 := by norm_num [side]
  unfold normalizedRequest
  rw [dite_eq_left hr]
  dsimp only
  simp only [DenseRowRecipe.normalized, coordinate, gridChannel,
    semanticSide_grid, hs, full_retains, ↓reduceIte]
  have hv0 : 0 ≤ value σ := by unfold value; split_ifs <;> norm_num
  have hv2 : value σ ≤ 2 := by unfold value; split_ifs <;> norm_num
  have hbin' : (bin : ℝ) ≤ 1 := by exact_mod_cast hbin
  have hb : ((bin : ℝ) + 1) * value σ ≤ 4 := by nlinarith
  norm_num [rate, rowGate, kthLargest, not_le.mpr (large_K HP),
    CorrectionRowRecipe.normalizer, HP.ρ_one 0 HP.η_pos.le, fixtureCutoff,
    max_eq_right (mul_nonneg (by positivity) hv0), min_eq_right hb]
  rw [max_eq_right (mul_nonneg (by positivity) hv0), min_eq_right hb]

private lemma rank_six_zero (b : ZMod 5 → ℝ) : kthLargest 6 univ b = 0 := by
  have hf : (univ.filter fun x : ZMod 5 => 6 ≤ #{w : ZMod 5 | b x ≤ b w}) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro x _ hx
    have hc : #{w : ZMod 5 | b x ≤ b w} ≤ 5 :=
      (card_filter_le _ _).trans (by simp)
    omega
  simp [kthLargest, hf]

private theorem actual_positive_child (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin 4) (hst : s ≠ t) (ss st : List (ZMod 5)) (σ : Environment 5 4) (x y : ZMod 5) :
    correctionRequest 1 id
      (⟨.row 0 (.normalized ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩),
        gridChannel s 0 ss, gridChannel t 0 st,
        gridChannel t 0 st⟩ : HierarchyTask.Request HP.k (Fin 4) (ZMod 5))
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
      HP.γ HP.K 6 (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ => 0) σ x y = HP.Q 1 := by
  have hr : Admissible (⟨.row 0 (.normalized ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩),
      gridChannel s 0 ss,
      gridChannel t 0 st, gridChannel t 0 st⟩ : HierarchyTask.Request HP.k (Fin 4) (ZMod 5)) :=
    ⟨hst, rfl, rfl⟩
  have hs : side 5 0 = 5 := by norm_num [side]
  have hcap := HP.toHierarchyParams.atomCutoff_eq (by norm_num : (0:ℝ) ≤ 1)
    (by have := Nat.cast_nonneg (α := ℝ) HP.k; linarith)
  unfold correctionRequest
  rw [dite_eq_left hr]
  dsimp only
  simp only [CorrectionRowRecipe.normalized, coordinate, gridChannel,
    semanticSide_grid, hs, full_retains, ↓reduceIte]
  have hτ : HP.incomingCutoff 0 = 1 :=
    HP.incomingCutoff_one (by rw [HP.τ₀_eq]; norm_num)
  simp only [incomingGate, filter_true, rank_six_zero]
  norm_num [rate, rowGate, kthLargest, not_le.mpr (large_K HP),
    CorrectionRowRecipe.normalizer, HP.ρ_one 0 HP.η_pos.le, hτ,
    HP.γ_one 0 (by norm_num), hcap]


private def input (HP : FourthRootHierarchyParams 16 1 16 32 8) (precision : ℕ) :=
  estimatedResidualInput HP 1 id roles 0 0 0 0 1 [1] [2, 3] [4]
    (fun _ => 0) 6 fixtureCutoff (estimates HP) (prep HP) (maximum HP) precision

-- The finite scalar fixture is globally bounded; the routed-bin noise client below
-- uses the genuine top/fine recipes. Summing over five midpoints gives each positive
-- bin contribution (i+1)*v*(1+5*Q(1)); one Q(1) is removed.
set_option backward.isDefEq.respectTransparency false in
private theorem input_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (precision : ℕ) (σ : Environment 5 4) :
    input HP precision σ 0 0 = 3 * value σ + HP.Q 1 * (15 * value σ - 1) := by
  have hs : side 5 0 = 5 := by norm_num [side]
  simp only [input, estimatedResidualInput, HierarchyTask.rawPositiveSample,
    HierarchyTask.rawNegativeSample, HierarchyTask.rawRequests,
    HierarchyTask.correctionAtomTask_last HP.k_pos]
  dsimp only [roles]
  simp only [gridChannel, min_self, incomingChildren]
  have d0 := dense HP 0 (by decide) 0 2 (by decide) [1] [4] σ 0 0
  have d1 := dense HP 1 (by decide) 0 2 (by decide) [1] [4] σ 0 0
  have r0 := dense HP 0 (by decide) 1 2 (by decide) [2, 3] [4] σ
  have r1 := dense HP 1 (by decide) 1 2 (by decide) [2, 3] [4] σ
  have a := actual_positive_child HP 0 1 (by decide) [1] [2, 3] σ
  have neg := actual_positive_child HP 0 2 (by decide) [1] [4] σ 0 0
  dsimp only [gridChannel] at d0 d1 r0 r1 a neg
  simp only [sum_range_succ, sum_range_zero, zero_add]
  unfold estimates prep maximum
  simp_rw [d0, d1, r0, r1, a, neg]
  have hside : semanticSide 5 1 = 5 := by
    simpa only [rate, pow_zero, inv_one, one_pow, hs] using semanticSide_grid 5 0
  norm_num [HierarchyTask.usageRatio, CorrectionRowTask.Channel.retains, channels,
    gridChannel, semanticSide_grid, hs, full_retains, rate, hside, ZMod.val_lt]
  ring

private def frame : Frame 5 4 1 := Classical.choice inferInstance
private def low : Environment 5 4 := fun _ => (0, frame)
private def high : Environment 5 4 := fun _ => (1, frame)

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    input HP 0 low 0 0 = 3 + 14 * HP.Q 1 ∧
    input HP 7 high 0 0 = 6 + 29 * HP.Q 1 ∧
    0 < input HP 0 low 0 0 ∧ input HP 0 low 0 0 < input HP 7 high 0 0 := by
  rw [input_eq, input_eq]
  simp only [value, low, high, Pi.zero_apply, Pi.one_apply, ↓reduceIte, one_ne_zero]
  have := HP.Q_nonneg 1
  constructor
  · ring
  constructor
  · ring
  constructor <;> nlinarith [input_eq HP 0 low, input_eq HP 7 high]


-- The finite maximum preserves the actual first envelope: one prefix of size one,
-- scaled by 2^dyadicSlack(1,0)=2, has common B exactly 1/2, never zero.
set_option backward.isDefEq.respectTransparency false in
private lemma first_envelope (HP : FourthRootHierarchyParams 16 1 16 32 8) (j : ℕ) :
    firstMeanEnvelope roles 1 [1] [4] 0 0 (input HP j) (fun _ _ => 0) 0 0 = 1 := by
  have hi (σ : Environment 5 4) : (1 : ℝ) ≤ input HP j σ 0 0 := by
    rw [input_eq]
    have hv : (1 : ℝ) ≤ value σ := by unfold value; split_ifs <;> norm_num
    nlinarith [HP.Q_nonneg 1]
  have he : (1 : ℝ) ≤ 𝔼 σ : Environment 5 4, input HP j σ 0 0 := by
    calc
      _ = 𝔼 _σ : Environment 5 4, (1 : ℝ) := (Fintype.expect_const _).symm
      _ ≤ _ := expect_le_expect fun σ _ => hi σ
  have hs : side 5 0 = 5 := by norm_num [side]
  simp only [firstMeanEnvelope, rowSliceMean, hs, retainedMask, full_retains, and_self,
    filter_true, sub_zero, rate, pow_zero, inv_one, one_pow, add_zero, div_one]
  exact min_eq_left (he.trans (le_abs_self _))

example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (A : ℕ → Environment 5 4 → Matrix (ZMod 5) (ZMod 5) ℝ) :
    commonMeanEnvelope roles 1 [1] [4] 0 0 0 1 1 0 (1 / 4)
      (input HP) A (fun _ _ => 0) 0 0 0 = 1 / 2 := by
  norm_num [commonMeanEnvelope, finiteEnvelope, twoSignalMeanEnvelope, first_envelope,
    dyadicSlack, kthLargest]

example : finiteEnvelope (∅ : Finset ℕ) (fun _ => (2 : ℝ))
    (fun _ (_ _ : Unit) => (7 : ℝ)) () () = 0 := finiteEnvelope_empty _ _ _ _

-- Empty conditioning stays zero for a nonzero input, without a positive-slice premise.
example : rowNormPow 4 5 1 (fun (_ : Unit) (_ : Unit) => False) (fun _ _ => True)
    (fun _ => finiteEnvelope (range 2) (fun _ => (1 : ℝ))
      (fun i (_ _ : Unit) => (i + 1 : ℝ))) = 0 := by
  simp [rowNormPow]

-- Actual first-prefix index zero is the first completed raw walk, not the zero seed.
set_option backward.isDefEq.respectTransparency false in
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (rawSteps : ℕ → ℕ) (second : Environment 5 4 → ZMod 5 → ℕ → ZMod 5 → ℝ) :
    let A := fun j => conditionalWalk (retainedMask roles.source (side 5 0) 1 [1])
      (retainedMask roles.terminal (side 5 0) 1 [4])
      (graph roles.source roles.terminal roles.source_terminal (side 5 0) (side 5 0)
        (side_le 5 0) (side_le 5 0) (fun x => CopyPadding.identifier 1 [1] x)
        (fun y => CopyPadding.identifier 1 [4] y)) (fun _ _ => rawSteps j) (input HP j)
    actualClippedMean HP roles.source roles.terminal (side 5 0) (side 5 0) (side 5 0)
      1 [1] [4] 0 (fun _ _ => 0) (1 / 4) (firstSignalIncrement A 0 second)
      (fun _ _ _ _ => 0) 0 0 0 0 = 1 := by
  dsimp only
  rw [actualClippedMean_first_eq]
  exact first_envelope HP 1

private def actualCost (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    Matrix (ZMod 5) (ZMod 5) ℝ :=
  let source := gridChannel roles.source 0 [1]
  let mid := gridChannel roles.midpoint 0 [2, 3]
  let terminal := gridChannel roles.terminal 0 [4]
  let χ := polynomialSwitch4 (1 / 2) 1
  let cutoff := fun i => routedBinCutoff χ (fun _ => rate 0) i (fun _ => 1)
  let bounded := fun i => boundedRoutedBinCutoff χ (fun _ => rate 0) 4 i (fun _ => 1)
  let estimated := fun i σ r => incomingChildren HP 1 id 6 (bounded i)
    (estimates HP 1 i) (prep HP 1 i) (maximum HP 1 i) r σ
  let canonical := fun i σ r => canonicalRequestChild HP 1 id (fun _ _ => 0)
    (cutoff i) (fun _ => 1) (fun _ => 1) 66 r σ
  rowSliceMean (retainedMask roles.source (side 5 0) 1 [1])
    (retainedMask roles.terminal (side 5 0) 1 [4]) (fun σ x y =>
      (∑ i ∈ range 2, HierarchyTask.positiveChildError (channels 1)
        0 i .residual source mid terminal (rate 0)
        (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max (4 : ℝ) 16)
        (estimated i σ) (canonical i σ) x y) +
      HierarchyTask.negativeChildError (channels 1) 0 0 .residual source mid terminal
        (rate 0) (estimated 0 σ) (canonical 0 σ) x y)

-- The actual lower-child cost reserve is satisfiable at a finite tolerance. This
-- asserts neither small recursive error nor a growth bound for this tolerance.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) {amplification : ℝ}
    (ha : 0 ≤ amplification) :
    ∃ ε : ℝ, 0 < ε ∧ rowNormPow 4 5 (rate 0)
      (retainedMask roles.source (side 5 0) 1 [1])
      (retainedMask roles.terminal (side 5 0) 1 [4]) (fun _ => actualCost HP) ≤
        (ε / (2 * ((1 : ℕ) + 1))) ^ 4 / (1 + (rate 0)⁻¹ ^ 4 + amplification) := by
  let M := rowNormPow 4 5 1 (retainedMask roles.source (side 5 0) 1 [1])
    (retainedMask roles.terminal (side 5 0) 1 [4]) (fun _ => actualCost HP)
  have hM : 0 ≤ M := rowNormPow_nonneg (by norm_num : (0 : ℝ) ≤ 5 * 1) _
  let t := M + amplification + 3
  have ht : 1 ≤ t := by dsimp only [t]; linarith
  have ht2 : t ≤ t ^ 2 := by nlinarith
  have ht4 : t ^ 2 ≤ t ^ 4 := by nlinarith [sq_nonneg (t ^ 2 - 1)]
  refine ⟨4 * t, by positivity, ?_⟩
  norm_num only [rate, pow_zero, inv_one, one_pow, Nat.cast_add, Nat.cast_one]
  have he : 4 * t / 4 = t := by ring
  rw [he]
  apply (le_div_iff₀ (by positivity : 0 < 2 + amplification)).mpr
  change M * (2 + amplification) ≤ t ^ 4
  have : M * (2 + amplification) ≤ t ^ 2 := by
    dsimp only [t]
    nlinarith [mul_nonneg hM ha, sq_nonneg M, sq_nonneg amplification]
  exact this.trans ht4

end ReserveOutputRegression
