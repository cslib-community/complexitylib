/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of actual finite estimated input and noise)
import Complexity.Computability.LogSpaceDerandomization.NormalizedAtomRows.FirstPayment
import all ComplexityTests.HierarchyRawMoment

/-! Fixed structural requests, a nonconstant two-bin input, exact signs and finite steps. -/
set_option linter.privateModule false
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace EstimatedInputRegression
private def roles : RoleProfile 4 := ⟨0, 1, 2, by decide, by decide, by decide⟩
private def value (σ : Environment 5 4) : ℝ := if (σ 3).1 0 = 0 then 1 else 2
private def estimates (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (_precision _bin : ℕ) (r : HierarchyTask.Request HP.k (Fin 4) (ZMod 5))
    (σ : Environment 5 4) : Matrix Unit Unit ℝ :=
  match r.task with | .baseNormalized _ _ => fun _ _ => value σ | _ => fun _ _ => 1
private def prep (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (_precision _bin : ℕ) (_r : HierarchyTask.Request HP.k (Fin 4) (ZMod 5))
    (_σ : Environment 5 4) : Matrix Unit Unit ℝ := fun _ _ => 1
private def maximum (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (_precision _bin : ℕ) (_r : HierarchyTask.Request HP.k (Fin 4) (ZMod 5))
    (_σ : Environment 5 4) : Unit → ℝ := fun _ => 0

private def fixtureCutoff (i : ℕ) (d : ℝ) : ℝ := min 4 (max 0 ((i + 1) * d))

private lemma fixtureCutoff_range (i : ℕ) (d : ℝ) :
    fixtureCutoff i d ∈ Set.Icc 0 4 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

private lemma dense (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (bin : ℕ) (hbin : bin ≤ 1) (s t : Fin 4) (hst : s ≠ t) (ss st : List (ZMod 5))
    (σ : Environment 5 4) :
    normalizedRequest 1 (fun (_ : Unit) => 0)
      (⟨HierarchyTask.baseNormalized 0 bin, gridChannel s 0 ss, gridChannel t 0 st,
        gridChannel t 0 st⟩ : HierarchyTask.Request HP.k (Fin 4) (ZMod 5))
      (fixtureCutoff bin) HP.ρ HP.K (fun σ _ _ => value σ)
      (fun _ _ _ => 1) σ () () = (bin + 1) * value σ := by
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
  norm_num [rate, rowGate, kthLargest, not_le.mpr (_root_.big_K HP),
    CorrectionRowRecipe.normalizer, HP.ρ_one 0 HP.η_pos.le, fixtureCutoff,
    max_eq_right (mul_nonneg (by positivity) hv0), min_eq_right hb]
  rw [max_eq_right (mul_nonneg (by positivity) hv0), min_eq_right hb]

private theorem actual_positive_child (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin 4) (hst : s ≠ t) (ss st : List (ZMod 5)) (σ : Environment 5 4) :
    correctionRequest 1 (fun (_ : Unit) => 0)
      (⟨.row 0 (.normalized ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩),
        gridChannel s 0 ss, gridChannel t 0 st,
        gridChannel t 0 st⟩ : HierarchyTask.Request HP.k (Fin 4) (ZMod 5))
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
      HP.γ HP.K 2 (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ => 0) σ () () = HP.Q 1 := by
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
  norm_num [rate, rowGate, kthLargest, not_le.mpr (_root_.big_K HP), incomingGate,
    CorrectionRowRecipe.normalizer, HP.ρ_one 0 HP.η_pos.le, hτ,
    HP.γ_one 0 (by norm_num), hcap]


private def input (HP : FourthRootHierarchyParams 16 1 16 32 8) (precision : ℕ) :=
  estimatedResidualInput HP 1 (fun (_ : Unit) => 0) roles 0 0 0 0 1 [1] [2, 3] [4]
    (fun _ => 0) 2 fixtureCutoff (estimates HP) (prep HP) (maximum HP) precision

-- The finite scalar fixture is globally bounded; the routed-bin noise client below
-- uses the genuine top/fine recipes. Each positive bin contributes (i+1)*v*(1+Q(1));
-- one Q(1) is removed.
set_option backward.isDefEq.respectTransparency false in
private theorem input_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (precision : ℕ) (σ : Environment 5 4) :
    input HP precision σ () () = 3 * value σ + HP.Q 1 * (3 * value σ - 1) := by
  have hs : side 5 0 = 5 := by norm_num [side]
  simp only [input, estimatedResidualInput, HierarchyTask.rawPositiveSample,
    HierarchyTask.rawNegativeSample, HierarchyTask.rawRequests,
    HierarchyTask.correctionAtomTask_last HP.k_pos]
  dsimp only [roles]
  simp only [gridChannel, min_self, incomingChildren]
  have d0 := dense HP 0 (by decide) 0 2 (by decide) [1] [4] σ
  have d1 := dense HP 1 (by decide) 0 2 (by decide) [1] [4] σ
  have r0 := dense HP 0 (by decide) 1 2 (by decide) [2, 3] [4] σ
  have r1 := dense HP 1 (by decide) 1 2 (by decide) [2, 3] [4] σ
  have a := actual_positive_child HP 0 1 (by decide) [1] [2, 3] σ
  have neg := actual_positive_child HP 0 2 (by decide) [1] [4] σ
  dsimp only [gridChannel] at d0 d1 r0 r1 a neg
  simp only [sum_range_succ, sum_range_zero, zero_add, Fintype.sum_unique]
  unfold estimates prep maximum
  rw [d0, d1, r0, r1, a, neg]
  have hside : semanticSide 5 1 = 5 := by
    simpa only [rate, pow_zero, inv_one, one_pow, hs] using semanticSide_grid 5 0
  norm_num [HierarchyTask.usageRatio, CorrectionRowTask.Channel.retains, channels,
    gridChannel, semanticSide_grid, hs, full_retains, rate, hside, ZMod.val_lt]
  ring

private def frame : Frame 5 4 1 := Classical.choice inferInstance
private def low : Environment 5 4 := fun _ => (0, frame)
private def high : Environment 5 4 := fun _ => (1, frame)

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    input HP 0 low () () = 3 + 2 * HP.Q 1 ∧
    input HP 7 high () () = 6 + 5 * HP.Q 1 ∧
    0 < input HP 0 low () () ∧ input HP 0 low () () < input HP 7 high () () := by
  rw [input_eq, input_eq]
  simp only [value, low, high, Pi.zero_apply, Pi.one_apply, ↓reduceIte, one_ne_zero]
  have := HP.Q_nonneg 1
  constructor
  · ring
  constructor
  · ring
  constructor <;> nlinarith [input_eq HP 0 low, input_eq HP 7 high]

-- Top cap 3 is separate from the fine-bin cap 16, and the scale sum stays literal.
example : estimatedBinCap 3 0 = 3 ∧ estimatedBinCap 3 1 = 16 := by
  norm_num [estimatedBinCap]

-- The sparse left product has support one even when the ambient row has five entries.
example : (∑ z : Fin 5, (if z = 0 then (3 : ℝ) else 0) * 2) = 1 * 3 * 2 ∧
    (1 : ℕ) < Fintype.card (Fin 5) := by norm_num [Fin.sum_univ_succ]

private def cutoff (i : ℕ) : ℝ → ℝ :=
  boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) rate 3 i (fun _ => 1)
private lemma cutoff_range (i : ℕ) (v : ℝ) :
    cutoff i v ∈ Set.Icc 0 (estimatedBinCap 3 i) :=
  boundedRoutedBinCutoff_grid_range _ id (by norm_num)
    (monotone_polynomialSwitch4 (by norm_num))
    (fun _ hv => polynomialSwitch4_of_le (by norm_num) hv)
    (fun _ hv => polynomialSwitch4_of_ge (by norm_num) hv)
    (fun _ => ⟨polynomialSwitch4_nonneg _ _ _, polynomialSwitch4_le_one _ _ _⟩)
    rate_antitone (fun i => (adjacent_rate_ratio i).le) i v

-- Fixed HP.k, independent precision, actual bounded bins and a chosen finite noise length.
-- The RAW moment coefficient keeps P=5, not the left support cardinality one above.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (raw prep : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 4) (ZMod 5) →
      Environment 5 4 → Matrix (ZMod 5) (ZMod 5) ℝ)
    (maximum : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 4) (ZMod 5) →
      Environment 5 4 → ZMod 5 → ℝ) (precision slack : ℕ)
    {Lh Lρ ζ ε : ℝ} (hε : 0 < ε) :
    let amplification := (5 : ℝ) * (|ζ| * (Lh + Lρ) / rate 2) ^ 4
    let steps := spectralWalkLength (1 - 1 / (155648 * (4 + 1) * (4 : ℝ) ^ 4))
      (amplification * 32 * (16 * 5 * (estimatedResidualBound HP 5 1 2 1 id
        (estimatedBinCap 3)) ^ 4)) ε slack
    let input := estimatedResidualInput HP 1 id roles 0 0 1 2 1 [1] [2, 3] [4] id 2
      cutoff raw prep maximum precision
    let F := conditionalWalk (retainedMask roles.source (side 5 0) 1 [1])
      (retainedMask roles.terminal (side 5 2) 1 [4])
      (graph roles.source roles.terminal roles.source_terminal (side 5 0) (side 5 2)
        (side_le 5 0) (side_le 5 2) (fun x => CopyPadding.identifier 1 [1] x)
        (fun y => CopyPadding.identifier 1 [4] y)) (fun _ _ => steps) input
    amplification * rowNormPow 4 5 (rate 0)
      (retainedMask roles.source (side 5 0) 1 [1])
      (retainedMask roles.terminal (side 5 2) 1 [4])
      (fun σ x y => F σ x y - rowSliceMean (retainedMask roles.source (side 5 0) 1 [1])
        (retainedMask roles.terminal (side 5 2) 1 [4]) input x y) ≤
      (ε * (64 : ℝ)⁻¹ ^ slack) ^ 4 := by
  exact estimatedResidualInput_scaled_noise_le_dyadic HP
    (lt_trans (by decide : 0 < 1) (_root_.big_K HP)) 1 roles
    ⟨2, 4, by decide, by decide⟩ 0 0 1 2 1 (by decide) [1] [2, 3] [4] id 2
    cutoff (estimatedBinCap 3) (by intro i; unfold estimatedBinCap; split_ifs <;> norm_num)
    cutoff_range raw prep maximum precision _ (by positivity) hε slack le_rfl

-- The same finite input feeds actual first-prefix noise, with chosen steps and zero start.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (raw prep : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 4) (ZMod 5) →
      Environment 5 4 → Matrix (ZMod 5) (ZMod 5) ℝ)
    (maximum : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 4) (ZMod 5) →
      Environment 5 4 → ZMod 5 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    let steps := fun _ : ℕ => spectralWalkLength
      (1 - 1 / (155648 * (4 + 1) * (4 : ℝ) ^ 4))
      ((rate 2)⁻¹ ^ 4 * 32 * (16 * 5 *
        (estimatedResidualBound HP 5 1 2 1 id (estimatedBinCap 3)) ^ 4)) ε (dyadicSlack 0 0)
    let input := estimatedResidualInput HP 1 id roles 0 0 1 2 1 [1] [2, 3] [4] id 2
      cutoff raw prep maximum
    let F := fun j => conditionalWalk (retainedMask roles.source (side 5 0) 1 [1])
      (retainedMask roles.terminal (side 5 2) 1 [4])
      (graph roles.source roles.terminal roles.source_terminal (side 5 0) (side 5 2)
        (side_le 5 0) (side_le 5 2) (fun x => CopyPadding.identifier 1 [1] x)
        (fun y => CopyPadding.identifier 1 [4] y)) (fun _ _ => steps j) (input j)
    rowNormPow 4 5 (rate 0) (retainedMask roles.source (side 5 0) 1 [1])
      (retainedMask roles.terminal (side 5 2) 1 [4])
      (actualNoiseEntry roles.source roles.terminal (side 5 0) (side 5 2) (side 5 2) 1 [1] [4]
        2 (fun _ _ => 0) (firstSignalIncrement F 2 (fun _ _ _ _ => 0))
        (fun _ _ _ _ => 0) 0 0) ≤ (ε * (64 : ℝ)⁻¹ ^ dyadicSlack 0 0) ^ 4 := by
  exact actualEstimatedFirstSignal_noise_le_dyadic HP
    (lt_trans (by decide : 0 < 1) (_root_.big_K HP)) 1 roles
    ⟨2, 4, by decide, by decide⟩ 0 0 1 2 1 (by decide) [1] [2, 3] [4] id 2
    cutoff (estimatedBinCap 3) (by intro i; unfold estimatedBinCap; split_ifs <;> norm_num)
    cutoff_range raw prep maximum _ (fun _ _ => 0) (by intros; rfl)
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) (by intros; rfl) 0 hε 0 le_rfl

-- Literal correction base remains zero; empty source/terminal conditioning has zero mean.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (σ : Environment 5 4) : incomingChildren HP 1 (fun (_ : Unit) => 0) 2 (fun _ => 1)
      (estimates HP 0 0) (prep HP 0 0) (maximum HP 0 0)
      ⟨.row 0 (.correction 0), gridChannel 0 0 [1], gridChannel 1 0 [2],
        gridChannel 1 0 [2]⟩ σ () () = 0 := rfl
example : rowSliceMean (fun (_ : Unit) (_ : Unit) => False) (fun _ _ => True)
    (fun _ _ _ => (7 : ℝ)) () () = 0 := by simp [rowSliceMean]

end EstimatedInputRegression
