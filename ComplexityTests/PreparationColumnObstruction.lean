/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of the auxiliary maximum profile obstruction)
import Complexity.Foundations.Probability.PreparationColumnObstruction
import all ComplexityTests.HierarchyPreparationRanks

/-!
A legitimate finite-bin BudgetData execution deletes just the split row of a stochastic
canonical reference. RAW2 and PREP3 use the actual H4 completion, distinct roles, nonempty
original suffixes and full terminal usage. The width can grow with HP and all rank caps
fixed. This is NOT exhaustive polynomial bins, a production-family IH counterexample,
or an estimator error lower bound. RAW is spatially nonconstant but stationary in its
full-mask environment. The predecessor test separately exercises environment-nonconstant
completed RAW with nonzero own error. Both gates close in the overloaded column while
the auxiliary-maximum profile keeps charging it.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment Matrix.PreparationColumn
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
namespace PreparationColumnRegression
variable {P : ℕ} [Fact P.Prime]

private def data (HP : FourthRootHierarchyParams 16 1 16 32 8) : BudgetData HP P where
  padding := 1
  base := reference 0 1
  bins := {0}
  binRate := fun _ => 1
  cutoff := fun _ => polynomialSwitch4 (1 / 2) 1
  auxiliary := fun _ _ => 1
  slack := 1
  slack_pos := by decide
  rankCharge := 0
  binCap := 1
  binCap_nonneg := zero_le_one
  cutoff_bounds := fun _ d =>
    ⟨polynomialSwitch4_nonneg _ _ d, polynomialSwitch4_le_one _ _ d⟩

private def input (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
  ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 0 [1],
    gridChannel 2 0 [2, 3], gridChannel 2 0 [2, 3]⟩
private def prep (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
  { input HP with task := .row 0 (.pilotPreparation ⟨0, HP.k_pos⟩) }

private lemma cap (HP : FourthRootHierarchyParams 16 1 16 32 8) : 2 < HP.K := by
  have hg := HP.gate
  have hn : 0 ≤ 32 * (HP.k : ℝ) / HP.η :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) HP.η_pos.le
  have hk : (2 : ℝ) < HP.K := by linarith
  exact_mod_cast hk

private lemma full (A : FrameChannel P 4 1) (s : List (ZMod P)) (z : ZMod P) :
    frameRetains P 4 (semanticSide P (rate 0)) A (CopyPadding.identifier 1 s z) := by
  rw [semanticSide_grid, show side P 0 = P by simp [side]]
  exact full_retains A _

private lemma initial (HP : FourthRootHierarchyParams 16 1 16 32 8) (bin : ℕ) :
    (data (P := P) HP).initialSample (input (P := P) HP) bin = fun _ => deleted 0 1 := by
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨.baseNormalized 0 bin, gridChannel 0 0 [1],
      gridChannel 2 0 [2, 3], gridChannel 2 0 [2, 3]⟩
  have hr : Admissible r := ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩
  have hs (x : ZMod P) : ({a | splitSource 1 id r hr a x} : Finset _).Nonempty := by
    have he : ({a | splitSource 1 id r hr a x} : Finset _) = univ := by
      ext a
      simp only [mem_filter, mem_univ, true_and, splitSource, coordinate, r, gridChannel]
      exact iff_true_intro (full _ _ _)
    rw [he]
    exact univ_nonempty
  have ht (A : FrameChannel P 4 1) (z : ZMod P) : splitTerminal 1 id r A z := full A _ z
  have hu (A : FrameChannel P 4 1) (z : ZMod P) : splitUsage 1 id r A z := full A _ z
  have hg (z : ZMod P) :
      rowGate HP.ρ HP.K 1 (reference (0 : ZMod P) 1) univ z = 1 := by
    simp only [rowGate, div_one]
    rw [(row_ranks 0 1 z (cap HP)).2, HP.ρ_one 0 HP.η_pos.le]
  funext σ x y
  have hR : (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      (input (P := P) HP).source (BudgetData.midpoint (input (P := P) HP))
      (input (P := P) HP).terminal ((data (P := P) HP).binRate bin)).direct = r := by
    simp [HierarchyTask.rawRequests, input, BudgetData.midpoint, data, r, gridChannel, rate]
  change 1 * HierarchyTask.usageRatio (channels 1) (input (P := P) HP).terminal
      _ y * denseChild 1 id _ _ _ HP.ρ HP.K _ σ x y = _
  rw [hR]
  have huR : HierarchyTask.usageRatio (k := HP.k) (channels (1 : ZMod P))
      (input (P := P) HP).terminal r y = 1 := by
    rw [usageRatio_grid 1 _ r 0 0 rfl rfl y]
    have hP : P ≠ 0 := (Fact.out : P.Prime).ne_zero
    norm_num [r, gridChannel, rate, side, hP]
  rw [huR, one_mul, one_mul, denseChild_eq 1 id r hr _ _ HP.ρ HP.K _ σ x y (hs x)]
  change denseAtom (splitTerminal 1 id r) (splitUsage 1 id r)
    (polynomialSwitch4 (1 / 2) 1) (fun _ => 1) HP.ρ HP.K r.terminal.rate
      (reference 0 1) (σ r.terminal.role) x y = _
  rw [show r.terminal.rate = 1 from by simp [r, gridChannel, rate]]
  simp only [denseAtom, ht, ↓reduceIte, atomNormalizer, hu, filter_true, atomPrep, one_mul]
  simp_rw [hg]
  norm_num only [Fintype.expect_const, min_self, div_one, one_mul]
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> by_cases hy1 : y = 1
  all_goals simp only [reference, deleted, hx, hy, hy1, ↓reduceIte]
  all_goals norm_num [polynomialSwitch4_of_le (by norm_num : (1 / 2 : ℝ) < 1),
    polynomialSwitch4_of_ge (by norm_num : (1 / 2 : ℝ) < 1)]

private lemma complete_const (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (M : ℕ) (A : Matrix (ZMod P) (ZMod P) ℝ) (slack : ℕ := 0) :
    (data (P := P) HP).complete M (input (P := P) HP) (fun _ => A) slack = some (fun _ => A) := by
  rw [BudgetData.complete_grid _ M _ 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl _ slack]
  apply congrArg some
  funext σ x y
  rw [conditionalWalk_const]
  have hx : X (0 : Fin 3) (side P 0) (CopyPadding.identifier (1 : ZMod P) [1]) σ x := by
    simpa only [X, show side P 0 = P by simp [side]] using full_retains (σ 0) _
  have hy : Y (2 : Fin 3) (side P 0) (CopyPadding.identifier (1 : ZMod P) [2, 3]) σ y := by
    simpa only [Y, show side P 0 = P by simp [side]] using full_retains (σ 2) _
  simp only [show (data (P := P) HP).padding = 1 from rfl, hx, hy, and_self, ↓reduceIte]

private lemma raw (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data (P := P) HP).raw
      (fun m r => if m < 2 then (data (P := P) HP).evaluate m r else none)
      2 (.pilotInput ⟨0, HP.k_pos⟩) (input (P := P) HP) = some (fun _ => deleted 0 1) := by
  have hs (bin : ℕ) : (data (P := P) HP).sampleScale (input (P := P) HP) (some bin) = 0 := by
    norm_num [BudgetData.sampleScale, data, input, gridChannel, rate]
  have hc (a b : ℕ) :
      ((if a = 0 then 0 else fun (_ : Environment P 3) => deleted (0 : ZMod P) 1) -
        (if b = 0 then 0 else fun (_ : Environment P 3) => deleted (0 : ZMod P) 1)) =
      fun (_ : Environment P 3) x y =>
        (if a = 0 then 0 else deleted 0 1 x y) -
          (if b = 0 then 0 else deleted 0 1 x y) := by
    funext σ x y
    split_ifs <;> rfl
  have hm (l : List ℕ) (f : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
      l.mapM (fun x => some (f x)) = some (l.map f) := List.mapM_pure
  have he : ((data (P := P) HP).rays (.pilotInput ⟨0, HP.k_pos⟩)).isEmpty = false := by
    simp [BudgetData.rays, data]
  unfold BudgetData.raw BudgetData.completedGroup
  simp only [he, Bool.false_eq_true, ↓reduceIte]
  simp only [BudgetData.rays, List.append_nil, List.mapM_map]
  dsimp only [Function.comp_def]
  simp_rw [BudgetData.pairedSample_initial _ 2 _ (by decide), initial, hs, hc]
  simp only [bind, pure]
  simp_rw [hm]
  simp only [Option.bind_some, List.map_map]
  dsimp only [Function.comp_def]
  simp_rw [complete_const, hm]
  simp only [Option.bind_some]
  norm_num [List.range_succ, Cslib.RowCompression.dyadicSlack, bind, pure, data,
    LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]

private lemma evaluated (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data (P := P) HP).evaluate 2 (input (P := P) HP) = some (.row (fun _ => deleted 0 1)) := by
  have hp : 0 < (data (P := P) HP).requestPrecision 2 (input (P := P) HP) := by
    rw [BudgetData.requestPrecision_grid _ 2 0 0 _ rfl rfl]
    norm_num [data]
  rw [BudgetData.evaluate_eq]
  simp only [BudgetData.step,
    show (input (P := P) HP).task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) from rfl,
    hp, ↓reduceIte]
  rw [raw HP]
  rfl

-- The reference is the actual stage-zero canonical input, not a residual-zero surrogate.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data (P := P) HP).canonicalPreparationInput true ⟨0, HP.k_pos⟩ (prep (P := P) HP) =
      reference 0 1 := by
  simp [BudgetData.canonicalPreparationInput, PilotTask.value, pilotInput,
    pilotCorrection_zero, data]

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data (P := P) HP).evaluate 2 (input (P := P) HP) = some (.row (fun _ => deleted 0 1)) :=
  evaluated HP

private lemma retains (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (σ : Environment P 3) (z : ZMod P) :
    (input (P := P) HP).source.retains (channels (data (P := P) HP).padding) σ z ∧
      (input (P := P) HP).usage.retains (channels (data (P := P) HP).padding) σ z := by
  constructor <;> exact full _ _ _

private lemma own_moment (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    rowNormPow 4 P (input (P := P) HP).source.rate
      (fun σ x => (input (P := P) HP).source.retains (channels (data (P := P) HP).padding) σ x)
      (fun σ y => (input (P := P) HP).usage.retains (channels (data (P := P) HP).padding) σ y)
      (fun (_ : Environment P 3) (x y : ZMod P) => deleted 0 1 x y - reference 0 1 x y) =
      (P : ℝ)⁻¹ * (1 / 8) := by
  have he : (fun σ x => (input (P := P) HP).source.retains
      (channels (data (P := P) HP).padding) σ x) = fun _ _ => True := by
    funext σ x; exact propext (iff_true_intro (retains HP σ x).1)
  have hu : (fun σ y => (input (P := P) HP).usage.retains
      (channels (data (P := P) HP).padding) σ y) = fun _ _ => True := by
    funext σ y; exact propext (iff_true_intro (retains HP σ y).2)
  simp only [he, hu]
  simpa only [ZMod.card, input, gridChannel, show rate 0 = 1 by simp [rate]] using
    own_error_moment (Environment P 3) (0 : ZMod P) 1 zero_ne_one

-- Positive own precision and a genuinely nonzero own error coexist with the obstruction.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data (P := P) HP).evaluate 2 (input (P := P) HP) = some (.row (fun _ => deleted 0 1)) ∧
    0 < (data (P := P) HP).requestPrecision 2 (input (P := P) HP) ∧
    0 < (P : ℝ)⁻¹ * (1 / 8) ∧
    (P : ℝ)⁻¹ * (1 / 8) ≤
      ((2 : ℝ) ^ (-(data (P := P) HP).requestPrecision 2 (input (P := P) HP))) ^ 4 := by
  have hp : (data (P := P) HP).requestPrecision 2 (input (P := P) HP) = 1 / 8 := by
    rw [BudgetData.requestPrecision_grid _ 2 0 0 _ rfl rfl]
    norm_num [data]
  have hP : (1 : ℝ) ≤ P := by exact_mod_cast (Fact.out : P.Prime).one_lt.le
  refine ⟨evaluated HP, by rw [hp]; norm_num, by positivity, ?_⟩
  have hi : (P : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hP
  have he : (1 / 2 : ℝ) ≤ ((2 : ℝ) ^ (-(1 / 8 : ℝ))) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [hp]
  exact (by nlinarith : (P : ℝ)⁻¹ * (1 / 8) ≤ 1 / 2).trans he

private lemma prep_zero (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (hP : ⌈4 * (1 + 32 * HP.R)⌉₊ < P) :
    (data (P := P) HP).incomingPreparation (prep (P := P) HP) (fun _ => deleted 0 1) = 0 := by
  funext σ x y
  have hX : ({z | (prep (P := P) HP).source.retains (channels (data (P := P) HP).padding) σ z} :
      Finset (ZMod P)) = univ := by ext z; simp [prep, (retains HP σ z).1]
  have hT : ({w | (prep (P := P) HP).terminal.retains (channels (data (P := P) HP).padding) σ w} :
      Finset (ZMod P)) = univ := by
    ext w
    have ht : (prep (P := P) HP).terminal = (input (P := P) HP).usage := rfl
    simp [ht, (retains HP σ w).2]
  unfold BudgetData.incomingPreparation
  rw [hX, hT, show (prep (P := P) HP).terminal.rate = 1 from by
    simp [prep, input, gridChannel, rate]]
  by_cases hy : y = 0
  · subst y
    exact (closed_column HP 0 1 x (cap HP)
      (Nat.ceil_pos.mpr (by linarith [HP.R_var])) (by simpa using hP)).1
  · have he : deleted (0 : ZMod P) 1 x y = 0 := by
      by_cases hx : x = 0 <;> simp [deleted, reference, hy, hx]
    have hz : polynomialPrepCutoff4 HP.θ 0 = 0 :=
      polynomialPrepCutoff4_eq_zero HP.θ_pos (by linarith [HP.θ_pos])
    simp only [correctionPrep, he, zero_div, hz, zero_mul]
    rfl

-- Literal PREP3 consumes RAW2 at childBudget=2 with the original production walk length.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (hP : ⌈4 * (1 + 32 * HP.R)⌉₊ < P) :
    (data (P := P) HP).evaluate 3 (prep (P := P) HP) = some (.row 0) := by
  have hp : 0 < (data (P := P) HP).requestPrecision 3 (prep (P := P) HP) := by
    rw [BudgetData.requestPrecision_grid _ 3 0 0 _ rfl rfl]
    norm_num [data]
  have hc : (data (P := P) HP).childBudget 3 = 2 := by
    norm_num [BudgetData.childBudget, data, LogSpaceEstimation.lastBudget,
      LogSpaceEstimation.scaleCutoff]
  have he : (data (P := P) HP).evaluate ((data (P := P) HP).childBudget 3)
      {prep HP with task := .row 0 (.pilotInput ⟨0, HP.k_pos⟩)} =
      some (.row (fun _ => deleted 0 1)) := by rw [hc]; exact evaluated HP
  rw [BudgetData.evaluate_preparation _ 3 true ⟨0, HP.k_pos⟩ _ rfl hp
    (by rw [hc]; decide) _ he, prep_zero HP hP]
  rw [BudgetData.complete_grid _ 3 _ 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl]
  simp only [Option.map_some]
  apply congrArg some
  apply congrArg BudgetValue.row
  funext σ x y
  change conditionalWalk _ _ _ _ (fun _ _ _ => (0 : ℝ)) σ x y = 0
  rw [conditionalWalk_const]
  split_ifs <;> rfl

-- No width restriction K/Kc>width is used: the row cap follows from two-entry support.
-- Full masks below are precisely the actual request masks by `retains` above.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) {D Lh Lρ Lτ : ℝ}
    (hh : 0 ≤ Lh) (hr : 0 ≤ Lρ) (ht : 0 ≤ Lτ)
    (hwidth : D ^ 4 < 8 * P * Lτ ^ 4) :
    D ^ 4 * rowNormPow 4 P 1 (fun (_ : Environment P 3) (_ : ZMod P) => True)
      (fun _ _ => True) (fun _ x y => deleted 0 1 x y - reference 0 1 x y) <
    rowNormPow 4 P 1 (fun (_ : Environment P 3) (_ : ZMod P) => True)
      (fun _ _ => True) (fun _ x y =>
        preparationRankError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
          (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ 1 Lh Lρ Lτ
          (deleted 0 1) (reference 0 1) univ univ x y) := by
  simpa only [ZMod.card] using profile_not_paid (Environment P 3) HP (0 : ZMod P) 1
    zero_ne_one (cap HP) ⌈4 * (1 + 32 * HP.R)⌉₊ hh hr ht (by simpa using hwidth)

-- Arbitrarily large fields meet the explicit failure threshold with HP, D and Ltau fixed.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (D Lτ : ℝ) (ht : 0 < Lτ) :
    ∃ P : ℕ, P.Prime ∧ ⌈4 * (1 + 32 * HP.R)⌉₊ < P ∧
      HP.K < P ∧ D ^ 4 < 8 * P * Lτ ^ 4 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (max (⌈4 * (1 + 32 * HP.R)⌉₊ : ℝ) HP.K)
    (D ^ 4 / (8 * Lτ ^ 4)))
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes n
  have hnp : (n : ℝ) ≤ p := by exact_mod_cast hp
  have hcap : (⌈4 * (1 + 32 * HP.R)⌉₊ : ℝ) < p :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) (hn.trans_le hnp)
  have hK : (HP.K : ℝ) < p :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) (hn.trans_le hnp)
  have hD : D ^ 4 / (8 * Lτ ^ 4) < p :=
    lt_of_le_of_lt (le_max_right _ _) (hn.trans_le hnp)
  refine ⟨p, hprime, by exact_mod_cast hcap, by exact_mod_cast hK, ?_⟩
  have h := (div_lt_iff₀ (show 0 < 8 * Lτ ^ 4 by positivity)).mp hD
  nlinarith [h]

-- The actual completed RAW is spatially nonconstant at every prime width.
example : deleted (0 : ZMod P) 1 0 0 = 0 ∧ deleted (0 : ZMod P) 1 1 0 = 1 := by
  simp [deleted, reference, one_ne_zero]

end PreparationColumnRegression
