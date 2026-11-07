/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of actual polynomial evaluator histories)
import Complexity.Foundations.Probability.HierarchyEvaluatorInitial
import Complexity.Foundations.Probability.HierarchyTransportedPreparation

/-! A positive identity/full-rate evaluator history with actual ratio-16 bins and polynomial
preparation. The top bin carries the input, the fine bin vanishes. This exact stationary
fixture does not claim nonconstant mixing error or a general canonical parent step. -/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
set_option backward.isDefEq.respectTransparency false
namespace PolynomialBudgetHistory
private def base : Matrix (ZMod 5) (ZMod 5) ℝ := 1
private def numerator (i : ℕ) (d : ℝ) : ℝ :=
  boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) rate 1 i (fun _ => 1) d
private lemma large_K (HP : FourthRootHierarchyParams 16 1 16 32 8) : 5 < HP.K := by
  have hg := HP.gate
  have hn : 0 ≤ 32 * (HP.k : ℝ) / HP.η :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) HP.η_pos.le
  have hk : (5 : ℝ) < HP.K := by linarith
  exact_mod_cast hk
private lemma numerator_values : numerator 0 0 = 0 ∧ numerator 0 1 = 1 ∧
    numerator 1 0 = 0 ∧ numerator 1 16 = 0 := by
  norm_num [numerator, boundedRoutedBinCutoff, routedBinCutoff, binWeight, rate,
    polynomialSwitch4, polynomialTransition4, transitionPolynomial4]
private def data (HP : FourthRootHierarchyParams 16 1 16 32 8) : BudgetData HP 5 where
  padding := 1
  base := base
  bins := {0, 1}
  binRate := rate
  cutoff := numerator
  auxiliary := fun _ => polynomialPrepCutoff4 HP.θ
  slack := 1
  slack_pos := by decide
  rankCharge := 0
  binCap := 16
  binCap_nonneg := by norm_num
  cutoff_bounds := by
    intro i d
    have hstep (j : ℕ) : rate j = 16 * rate (j + 1) := by
      simp only [rate, pow_succ, _root_.mul_inv_rev]
      ring
    simpa only [DenseBinRecipe.polynomialUnrouted, numerator,
      show max (1 : ℝ) 16 = 16 by norm_num] using
      (DenseBinRecipe.polynomialUnrouted_numerator_laws HP
      rate_pos hstep (by norm_num : (0 : ℝ) ≤ 1) i d).1
private def request (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 0 [1],
    gridChannel 2 0 [2, 3], gridChannel 2 0 [2, 3]⟩
private lemma full (σ : Environment 5 3) (role : Fin 3) (suffix : List (ZMod 5))
    (v : ZMod 5) : (gridChannel role 0 suffix).retains (channels (1 : ZMod 5)) σ v := by
  simp only [gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid]
  simpa only [show side 5 0 = 5 by norm_num [side]] using full_retains (σ role) _
private lemma prep_values (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    polynomialPrepCutoff4 HP.θ 0 = 0 ∧ polynomialPrepCutoff4 HP.θ 1 = 1 := by
  have hθ : HP.θ < 1 := by linarith [HP.θ_lt_θ₂, HP.θ₂_lt]
  exact ⟨polynomialPrepCutoff4_eq_zero HP.θ_pos (by linarith [HP.θ_pos]),
    polynomialPrepCutoff4_eq_one HP.θ_pos (by linarith)⟩
private lemma gate_one (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (b : ℝ) (A : Matrix (ZMod 5) (ZMod 5) ℝ) (S : Finset (ZMod 5)) (x : ZMod 5) :
    rowGate HP.ρ HP.K b A S x = 1 := by
  unfold rowGate
  rw [kthLargest_eq_zero_of_card_lt
    ((card_le_univ S).trans_lt (by simpa using large_K HP))]
  exact HP.ρ_one 0 HP.η_pos.le
private lemma top_dense (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (σ : Environment 5 3) (x y : ZMod 5) :
    denseChild 1 id (request HP) (numerator 0) (polynomialPrepCutoff4 HP.θ)
      HP.ρ HP.K base σ x y = base x y := by
  have hr : Admissible (request HP) := ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩
  have hn := source_nonempty 1 id (request HP) hr (by decide)
    Function.injective_id (⟨1, 4, by decide, by decide⟩ : Horizon 5) (s := 0) (by decide) rfl x
  rw [denseChild_eq 1 id (request HP) hr _ _ _ _ _ σ x y hn]
  have ht (A : FrameChannel 5 4 1) (v : ZMod 5) : splitTerminal 1 id (request HP) A v := by
    change frameRetains 5 4 (semanticSide 5 (rate 0)) A _
    rw [semanticSide_grid, show side 5 0 = 5 by norm_num [side]]
    exact full_retains A _
  have hu (A : FrameChannel 5 4 1) (v : ZMod 5) : splitUsage 1 id (request HP) A v := ht A v
  simp only [denseAtom, ht, ↓reduceIte, atomNormalizer, atomPrep, hu, filter_true,
    gate_one, mul_one, Fintype.expect_const]
  norm_num only [request, gridChannel, rate, pow_zero, inv_one, one_pow, div_one]
  by_cases hxy : x = y
  · subst y
    norm_num [base, prep_values HP, numerator_values]
  · norm_num [base, Matrix.one_apply_ne hxy, prep_values HP, numerator_values]
private lemma initial (HP : FourthRootHierarchyParams 16 1 16 32 8) (i : ℕ)
    (hi : i ∈ (data HP).bins) :
    (data HP).initialSample (request HP) i = fun _ x y => if i = 0 then base x y else 0 := by
  have hi' : i = 0 ∨ i = 1 := by simpa only [data, mem_insert, mem_singleton] using hi
  funext σ x y
  rcases hi' with rfl | rfl
  · unfold BudgetData.initialSample
    have hr : (HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
        (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
        ((data HP).binRate 0)).direct = {request HP with task := .baseNormalized 0 0} := by
      simp [HierarchyTask.rawRequests, data, request, gridChannel, rate]
    change rate 0 * _ * denseChild _ _ _ _ _ _ _ _ σ x y = _
    rw [hr, denseChild_congr_task]
    change rate 0 * HierarchyTask.usageRatio (channels (1 : ZMod 5)) (request HP).terminal
      {request HP with task := .baseNormalized 0 0} y *
      denseChild 1 id (request HP) (numerator 0) (polynomialPrepCutoff4 HP.θ)
        HP.ρ HP.K base σ x y = _
    rw [usageRatio_grid (k := HP.k) 1 (request HP).terminal
      {request HP with task := .baseNormalized 0 0} 0 0 rfl rfl y]
    rw [top_dense]
    norm_num [side, rate]
  · change _ * _ * denseChild _ _ _ (numerator 1) _ _ _ base σ x y = (0 : ℝ)
    have hz : ∀ v w : ZMod 5, numerator 1 (base v w / rate 1) = 0 := by
      intro v w
      by_cases hvw : v = w
      · subst w; norm_num [base, rate, numerator_values]
      · simp only [base, Matrix.one_apply_ne hvw, zero_div, numerator_values.2.2.1]
    unfold denseChild normalizedRequest DenseRowRecipe.normalized
    dsimp only
    split_ifs <;> simp only [HierarchyTask.rawRequests, data, hz, zero_mul, zero_div,
      mul_zero]
private lemma complete_const_task (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (M d : ℕ) (A : Matrix (ZMod 5) (ZMod 5) ℝ)
    (task : HierarchyTask HP.k) :
    (data HP).complete M {request HP with task := task} (fun _ => A) d = some (fun _ => A) := by
  rw [BudgetData.complete_grid _ M _ 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl _ d]
  apply congrArg some
  funext σ x y
  rw [conditionalWalk_const]
  change (if _ then A x y else 0) = A x y
  have hx : X (0 : Fin 3) (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [1]) σ x := by
    simpa only [X, show side 5 0 = 5 by norm_num [side]] using full_retains (σ 0) _
  have hy : Y (2 : Fin 3) (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [2, 3]) σ y := by
    simpa only [Y, show side 5 0 = 5 by norm_num [side]] using full_retains (σ 2) _
  exact ite_eq_left ⟨hx, hy⟩
private lemma complete_const (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (M d : ℕ) (A : Matrix (ZMod 5) (ZMod 5) ℝ) :
    (data HP).complete M (request HP) (fun _ => A) d = some (fun _ => A) :=
  complete_const_task HP M d A (request HP).task
private lemma group_input (HP : FourthRootHierarchyParams 16 1 16 32 8) (d : ℕ)
    (task : HierarchyTask HP.k := (request HP).task) :
    (data HP).initialGroupInput 2 d {request HP with task := task} = fun _ x y =>
      (if LogSpaceEstimation.lastBudget 2 d 1 0 = 0 then 0 else base x y) -
      (if LogSpaceEstimation.lastBudget 2 (2 * d) 1 0 = 0 then 0 else base x y) := by
  funext σ x y
  unfold BudgetData.initialGroupInput
  have hi (i : ℕ) (hi : i ∈ (data HP).bins) :
      (data HP).initialSample {request HP with task := task} i =
        fun _ x y => if i = 0 then base x y else 0 := initial HP i hi
  rw [sum_congr rfl (fun i hmem => by rw [hi i hmem])]
  norm_num [BudgetData.sampleScale, data, request, gridChannel, rate]
private lemma prefixes_task (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (task : HierarchyTask HP.k) :
    (data HP).initialPrefixes 2 {request HP with task := task} =
      some (fun j _ => if 2 ≤ j then base else 0) := by
  have hg (d : ℕ) := BudgetData.completedGroup_initial (data HP) 2 d (by decide)
    (show (data HP).bins.Nonempty from by simp [data]) {request HP with task := task}
  simp_rw [group_input] at hg
  unfold BudgetData.initialPrefixes
  change (do
    let groups ← (List.range (Nat.log2 2 + 1)).mapM fun j =>
      (data HP).completedGroup _ 2 (Cslib.RowCompression.dyadicSlack (Nat.log2 2 + 1) j)
        (.pilotInput ⟨0, HP.k_pos⟩) {request HP with task := task}
    pure fun j σ x y => ((groups.take j).map
      (fun (A : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) => A σ x y)).sum) = _
  simp_rw [hg]
  norm_num [List.range_succ, Cslib.RowCompression.dyadicSlack,
    LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
  simp_rw [complete_const_task]
  simp only [Option.bind_some]
  apply congrArg some
  funext j σ x y
  cases j with
  | zero => simp
  | succ j => cases j <;> simp

private lemma prefixes (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).initialPrefixes 2 (request HP) =
      some (fun j _ => if 2 ≤ j then base else 0) :=
  prefixes_task HP (request HP).task

-- The actual (nonpilot) constructor executes the same nonzero base-stage recipe.
-- Its own precision is used, and its zero-budget boundary remains unavailable.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).evaluate 2 {request HP with task := .row 0 (.input ⟨0, HP.k_pos⟩)} =
        some (.row (fun _ => base)) ∧
      (data HP).evaluate 0 {request HP with task := .row 0 (.input ⟨0, HP.k_pos⟩)} = none ∧
      base (0 : ZMod 5) 0 = 1 ∧ CorrectionRowRecipe.input base 0 base = base := by
  refine ⟨?_, ?_, by simp [base], by ext x y; simp [CorrectionRowRecipe.input]⟩
  · simpa only [show Nat.log2 2 + 1 = 2 by decide, le_refl, ↓reduceIte] using
      BudgetData.evaluate_initial_prefix (data HP) 2
        {request HP with task := .row 0 (.input ⟨0, HP.k_pos⟩)} false rfl rfl
        (by norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision,
          data, request, gridChannel, rate]) _ (prefixes_task HP (.row 0 (.input ⟨0, HP.k_pos⟩)))
  · rw [BudgetData.evaluate_eq]
    norm_num [BudgetData.step, BudgetData.requestPrecision, LogSpaceEstimation.precision,
      data, request, gridChannel, rate]

-- Every positive lower budget in this interval has a real nonzero dense output,
-- simultaneously with range, rank support and own-source/full-rank rooted errors.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (m : ℕ) (hm : m < 3) (hm0 : 0 < m) :
    ∃ A, (data HP).evaluate m {request HP with task := .baseNormalized 0 0} = some (.row A) ∧
      (∀ σ, A σ (0 : ZMod 5) 0 = 1) ∧
      (∀ σ x y, A σ x y ∈ Set.Icc 0 (2 * (data HP).binCap)) ∧
      (∀ σ x, #{y ∈ ({y | (request HP).terminal.retains (channels (1 : ZMod 5)) σ y} :
        Finset _) | A σ x y ≠ 0} < HP.K) ∧
      rootDistPow 4 5 (request HP).source.rate
        (fun σ x => (request HP).source.retains (channels (1 : ZMod 5)) σ x)
        (fun σ y => (request HP).terminal.retains (channels (1 : ZMod 5)) σ y)
        A (fun _ => base) = 0 := by
  have he : HP.η₂ ≤ 1 / 2 := by
    have hθ := HP.θ₂_lt
    norm_num at hθ
    linarith [HP.η₂_lt, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_lt_θ₂]
  have hz : ∀ d, d ≤ 1 / 2 → (data HP).cutoff 0 d = 0 := fun _ hd =>
    boundedRoutedBinCutoff_eq_zero (by norm_num)
      (fun _ h => polynomialSwitch4_of_le (by norm_num) h)
      rate_pos rate_antitone hd 0 (fun _ => 1)
  obtain ⟨A, hA, htarget, hrange, _, hsupp, _, hroot⟩ :=
    BudgetData.evaluate_lower_dense_contract (data HP) 3 m hm hm0
      {request HP with task := .baseNormalized 0 0} 0 rfl
      (show Admissible (request HP) from ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩)
      (1 / 2) HP.η₂ (by norm_num) he hz HP.ρ_zero
  have ht : denseChild (n := HP.k) 1 id {request HP with task := .baseNormalized 0 0} (numerator 0)
      (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K base = fun _ => base := by
    rw [denseChild_congr_task]
    funext σ x y
    exact top_dense HP σ x y
  change A = denseChild (n := HP.k) 1 id {request HP with task := .baseNormalized 0 0} (numerator 0)
    (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K base at htarget
  refine ⟨A, by simpa only [hm, ↓reduceIte] using hA, ?_, hrange, hsupp, ?_⟩
  · intro σ
    rw [htarget, ht]
    simp [base]
  · change rootDistPow 4 5 (request HP).source.rate
      (fun σ x => (request HP).source.retains (channels (1 : ZMod 5)) σ x)
      (fun σ y => (request HP).terminal.retains (channels (1 : ZMod 5)) σ y) A
      (denseChild (n := HP.k) 1 id {request HP with task := .baseNormalized 0 0}
        (numerator 0) (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K base) = 0 at hroot
    simpa only [ht] using hroot

-- A score successor consumes the actual earlier pilotInput result at budget 2 < 3.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).evaluate 3 {request HP with task := .row 0 (.score ⟨0, HP.k_pos⟩)} =
      some (.row (fun σ => PilotRowRecipe.score HP.toHierarchyParams
        (fun τ y => (request HP).terminal.retains (channels (1 : ZMod 5)) τ y)
        (request HP).terminal.rate base σ)) := by
  have hA := BudgetData.evaluate_initial_prefix (data HP) 2 (request HP) true rfl rfl
    (by norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision,
      data, request, gridChannel, rate]) _ (prefixes HP)
  have hchild : (data HP).childBudget 3 = 2 := by
    norm_num [BudgetData.childBudget, data, LogSpaceEstimation.lastBudget,
      LogSpaceEstimation.scaleCutoff]
  apply (BudgetData.evaluate_score_child (data HP) 3 (by decide)
    {request HP with task := .row 0 (.score ⟨0, HP.k_pos⟩)} ⟨0, HP.k_pos⟩ rfl
    (by norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision,
      data, request, gridChannel, rate]) (fun _ => base) ?_).1
  simpa only [hchild, show Nat.log2 2 + 1 = 2 by decide, le_refl, ↓reduceIte, request] using hA

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).initialPrefixes 2 (request HP) =
      some (fun j _ => if 2 ≤ j then base else 0) ∧
    (data HP).auxiliary 0 0 = 0 ∧ (data HP).auxiliary 0 1 = 1 ∧
    (data HP).initialSample (request HP) 0 = (fun _ => base) ∧
    (data HP).initialSample (request HP) 1 = (fun _ _ _ => 0) := by
  refine ⟨prefixes HP, (prep_values HP).1, (prep_values HP).2, ?_, ?_⟩
  · simpa only [↓reduceIte] using initial HP 0 (by simp [data])
  · simpa only [one_ne_zero, ↓reduceIte] using initial HP 1 (by simp [data])

-- The primitive matrix is substochastic and the actual top/fine bins cover it exactly.
-- The zero fine contribution is part of valid unequal-rate geometry, not a duplicated half-bin.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (∀ x y, 0 ≤ base x y) ∧ base *ᵥ 1 ≤ 1 ∧ ∀ x y,
      ∑ i ∈ (data HP).bins, rate i * numerator i (base x y / rate i) = base x y := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    simp only [base, Matrix.one_apply]
    split_ifs <;> norm_num
  · simp [base]
  · intro x y
    have hC (x y : ZMod 5) : 0 ≤ (data HP).base x y := by
      simp only [data, base, Matrix.one_apply]
      split_ifs <;> norm_num
    have hC1 : (data HP).base *ᵥ 1 ≤ 1 := by simp [data, base]
    have hc := BudgetData.initialBins_polynomial_sum (data HP) 1
      (by ext i; simp only [data, mem_insert, mem_singleton, mem_range]; omega) rfl rfl hC hC1 x y
    change (∑ i ∈ (data HP).bins,
      (data HP).binRate i * (data HP).cutoff i ((data HP).base x y / (data HP).binRate i)) = _
    rw [hc]
    by_cases hxy : x = y
    · subst y
      norm_num [data, base, rate, polynomialSwitch4, polynomialTransition4,
        transitionPolynomial4]
    · simp [data, base, Matrix.one_apply_ne hxy]

private lemma preparation (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (A : Matrix (ZMod 5) (ZMod 5) ℝ) (hA : A = 0 ∨ A = base)
    (task : HierarchyTask HP.k := (request HP).task) :
    (data HP).binPreparation 0 {request HP with task := task} (fun _ => A) = fun _ => A := by
  funext σ x y
  unfold BudgetData.binPreparation densePreparation DenseRowRecipe.preparation atomPrep
  rw [gate_one, mul_one]
  change polynomialPrepCutoff4 HP.θ (A x y / rate 0) = A x y
  norm_num only [rate, pow_zero, inv_one, one_pow, div_one]
  rcases hA with rfl | rfl
  · exact (prep_values HP).1
  · by_cases hxy : x = y
    · subst y; simpa only [base, Matrix.one_apply_eq] using (prep_values HP).2
    · simpa only [base, Matrix.one_apply_ne hxy] using (prep_values HP).1

private def increment (ζ : ℝ) (x : ZMod 5) (j : ℕ) (y : ZMod 5) (ν : Fin 2) : ℝ :=
  if j = 1 then if ν = 0 then base x y else ζ * base x y else 0

private lemma compressed_task (HP : FourthRootHierarchyParams 16 1 16 32 8) (ζ floor : ℝ)
    (task : HierarchyTask HP.k) :
    (data HP).compressedBin 2 0 0 ζ floor {request HP with task := task} = some (fun _σ x y =>
      let a := Cslib.RowCompression.iterate univ
        (NormalizedMoments.compatibleCapacity HP.K 2) (fun _ => HP.K)
        (Cslib.RowCompression.dyadicFloor floor 2) (increment ζ x) ⟨0, 0⟩ 2
      FourthRootHierarchyParams.NormalizedRow.output (numerator 0) HP.ρ ζ
        (a.row y 0) (a.row y 1)
        (Cslib.RowCompression.firstRank univ HP.K a.defaultValue a.row)) := by
  have hactive : 0 < (data HP).requestPrecision 2 {request HP with task := task} := by
    norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision, data,
      request, gridChannel, rate]
  unfold BudgetData.compressedBin
  simp only [BudgetData.decodePrefixes]
  rw [ite_eq_right (by simp only [hactive, not_true_eq_false]; norm_num [request, gridChannel])]
  simp only [prefixes_task, bind, Option.bind_some]
  norm_num [List.range_succ, Cslib.RowCompression.dyadicSlack]
  simp_rw [preparation HP 0 (Or.inl rfl) task, preparation HP base (Or.inr rfl) task]
  simp_rw [complete_const_task]
  simp only [Option.bind_some]
  apply congrArg some
  funext σ x y
  have ht (z : ZMod 5) : (request HP).terminal.retains (channels (data HP).padding) σ z :=
    full σ 2 [2, 3] z
  simp only [show (request HP).usage = (request HP).terminal from rfl, ht, ↓reduceIte]
  apply congrArg (fun a : Cslib.RowCompression.State (ZMod 5) =>
    FourthRootHierarchyParams.NormalizedRow.output (numerator 0) HP.ρ ζ
      (a.row y 0) (a.row y 1)
      (Cslib.RowCompression.firstRank univ HP.K a.defaultValue a.row))
  apply Cslib.RowCompression.iterate_congr
  intro j hj
  funext z ν
  interval_cases j <;> fin_cases ν <;>
    norm_num [NormalizedMoments.firstSignalIncrement, NormalizedMoments.secondSignalIncrement,
      increment, rate]

private lemma compressed (HP : FourthRootHierarchyParams 16 1 16 32 8) (ζ floor : ℝ) :
    (data HP).compressedBin 2 0 0 ζ floor (request HP) = some (fun _σ x y =>
      let a := Cslib.RowCompression.iterate univ
        (NormalizedMoments.compatibleCapacity HP.K 2) (fun _ => HP.K)
        (Cslib.RowCompression.dyadicFloor floor 2) (increment ζ x) ⟨0, 0⟩ 2
      FourthRootHierarchyParams.NormalizedRow.output (numerator 0) HP.ρ ζ
        (a.row y 0) (a.row y 1)
        (Cslib.RowCompression.firstRank univ HP.K a.defaultValue a.row)) :=
  compressed_task HP ζ floor (request HP).task

open Cslib.RowCompression in
private lemma wide_advance (n K : ℕ) (hn : 5 < n) (hK : 5 < K)
    {floor z : ℝ} (hf : 0 ≤ floor) (hz : z ≤ floor)
    (w Δ : ZMod 5 → Fin 2 → ℝ) :
    advance univ n K floor Δ ⟨z, w⟩ =
      ⟨floor, fun y => updateEntry floor floor ((w + Δ) y)⟩ := by
  have hk (j : ℕ) (hj : 5 < j) (f : ZMod 5 → ℝ) : kthLargest j univ f = 0 :=
    kthLargest_eq_zero_of_card_lt (by simpa using hj) f
  have ht : threshold univ n floor z (w + Δ) = floor := by
    simp only [threshold, hk n hn, max_eq_left hf, max_eq_right hz]
  have hd : newDefault univ n K floor z (w + Δ) = floor := by
    rw [newDefault, ht, hk K hK]
    exact max_eq_left ((min_le_left _ _).trans (max_le hz hf))
  unfold advance update
  simp only [ht, hd]

open Cslib.RowCompression in
private lemma actual_iterate (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (x : ZMod 5) :
    let ζ := HP.η / 4
    let f := dyadicFloor ζ 2
    let a := iterate univ (NormalizedMoments.compatibleCapacity HP.K 2) (fun _ => HP.K)
      f (increment ζ x) ⟨0, 0⟩ 2
    a.defaultValue = f 1 ∧ (∀ y,
      a.row y = if x = y then (fun ν => if ν = 0 then 1 + f 0 else ζ)
        else defaultEntry (f 1)) ∧ ∀ i < 2,
      stepThreshold univ (NormalizedMoments.compatibleCapacity HP.K 2) (fun _ => HP.K)
        f (increment ζ x) ⟨0, 0⟩ i ≤ f i := by
  intro ζ f a
  have hζ : 0 < ζ := by dsimp only [ζ]; linarith [HP.η_pos]
  have hf (j : ℕ) : 0 ≤ f j := dyadicFloor_nonneg hζ.le 2 j
  have h01 : f 0 ≤ f 1 := by
    have h := dyadicFloor_mul_le_succ hζ.le (m := 2) (i := 0) (by decide)
    linarith [hf 0]
  have hn (j : ℕ) : 5 < NormalizedMoments.compatibleCapacity HP.K 2 j :=
    (large_K HP).trans_le (NormalizedMoments.compatibleCapacity_bounds HP.K 2 j).1
  have hzero : advance univ (NormalizedMoments.compatibleCapacity HP.K 2 0) HP.K
      (f 0) (increment ζ x 0) ⟨0, 0⟩ = ⟨f 0, fun _ => defaultEntry (f 0)⟩ := by
    rw [wide_advance _ _ (hn 0) (large_K HP) (hf 0) (hf 0)]
    congr 1
    funext y
    apply updateEntry_eq_default_of_size_le
    norm_num [increment, entrySize]
    exact hf 0
  have hno (i : ℕ) (hi : i < 2) :
      stepThreshold univ (NormalizedMoments.compatibleCapacity HP.K 2) (fun _ => HP.K)
        f (increment ζ x) ⟨0, 0⟩ i ≤ f i := by
    have hk (j : ℕ) (g : ZMod 5 → ℝ) :
        kthLargest (NormalizedMoments.compatibleCapacity HP.K 2 j) univ g = 0 :=
      kthLargest_eq_zero_of_card_lt (by simpa using hn j) g
    interval_cases i
    · simp only [stepThreshold, inputRow, iterate_zero, threshold, hk,
        max_eq_left (hf 0), max_eq_right (hf 0)]
      exact le_rfl
    · simp only [stepThreshold, inputRow, iterate_succ, iterate_zero]
      rw [hzero]
      simp only [threshold, hk, max_eq_left (hf 1), max_eq_right h01]
      exact le_rfl
  dsimp only [a]
  simp only [iterate_succ, iterate_zero]
  rw [hzero, wide_advance _ _ (hn 1) (large_K HP) (hf 1) h01]
  refine ⟨rfl, ?_, hno⟩
  intro y
  dsimp only [State.row]
  by_cases hxy : x = y
  · rw [ite_eq_left hxy]
    have hv : ((fun _ : ZMod 5 => defaultEntry (f 0)) + increment ζ x 1) y =
        (fun ν => if ν = 0 then 1 + f 0 else ζ) := by
      funext ν
      fin_cases ν <;> simp [increment, defaultEntry, base, hxy, add_comm]
    rw [hv]
    apply updateEntry_eq_self_of_three_mul_le (hf 1) (hf 1) (by linarith [hf 1])
    have hsize := abs_apply_le_entrySize (fun ν : Fin 2 => if ν = 0 then 1 + f 0 else ζ) 1
    have hb := dyadicFloor_le_scale_div hζ.le 2 1
    simp only [Fin.isValue, one_ne_zero, ↓reduceIte, abs_of_pos hζ] at hsize
    linarith
  · rw [ite_eq_right hxy]
    apply updateEntry_eq_default_of_size_le
    have hv : ((fun _ : ZMod 5 => defaultEntry (f 0)) + increment ζ x 1) y =
        defaultEntry (f 0) := by
      funext ν
      fin_cases ν <;> simp [increment, defaultEntry, base, Matrix.one_apply_ne hxy]
    rw [hv]
    norm_num [entrySize, defaultEntry, abs_of_nonneg (hf 0), hf 0]
    linarith [hf 1]

open Cslib.RowCompression in
private lemma compressed_value_task (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (task : HierarchyTask HP.k) :
    (data HP).compressedBin 2 0 0 (HP.η / 4) (HP.η / 4) {request HP with task := task} =
      some (fun _ => base) := by
  rw [compressed_task]
  apply congrArg some
  funext σ x y
  dsimp only
  obtain ⟨hd, hr, _⟩ := actual_iterate HP x
  have hζ : 0 < HP.η / 4 := by linarith [HP.η_pos]
  have hf := dyadicFloor_nonneg hζ.le 2 1
  have hη : dyadicFloor (HP.η / 4) 2 1 ≤ HP.η := by
    linarith [dyadicFloor_le_scale_div hζ.le 2 1, HP.η_pos]
  have hk (f : ZMod 5 → ℝ) : kthLargest HP.K univ f = 0 :=
    kthLargest_eq_zero_of_card_lt (by simpa using large_K HP) f
  simp only [firstRank, hk, hd, max_eq_left hf,
    FourthRootHierarchyParams.NormalizedRow.output, HP.ρ_one _ hη, mul_one]
  rw [hr y]
  by_cases hxy : x = y
  · rw [ite_eq_left hxy]
    have hn : numerator 0 (1 + dyadicFloor (HP.η / 4) 2 0) = 1 := by
      have h0 := dyadicFloor_nonneg hζ.le 2 0
      exact (boundedRoutedBinCutoff_zero_saturates (χ := polynomialSwitch4 (1 / 2) 1)
        (b := rate) (by norm_num : (0 : ℝ) ≤ 1) (by linarith) le_rfl).trans
        numerator_values.2.1
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero, hn]
    rw [hxy]
    norm_num [FourthRootHierarchyParams.NormalizedRow.clip, hζ.ne', base]
  · rw [ite_eq_right hxy]
    have hsmall : dyadicFloor (HP.η / 4) 2 1 ≤ 1 / 2 := by
      have hθ := HP.θ₂_lt
      norm_num at hθ
      linarith [HP.η₂_lt, HP.η_lt_η₂, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_lt_θ₂]
    have hn : numerator 0 (dyadicFloor (HP.η / 4) 2 1) = 0 :=
      boundedRoutedBinCutoff_eq_zero (by norm_num)
        (fun _ h => polynomialSwitch4_of_le (by norm_num) h)
        rate_pos rate_antitone hsmall 0 (fun _ => 1)
    simp only [defaultEntry, Fin.isValue, ↓reduceIte, one_ne_zero, hn, zero_div,
      base, Matrix.one_apply_ne hxy]

open Cslib.RowCompression in
private lemma compressed_value (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).compressedBin 2 0 0 (HP.η / 4) (HP.η / 4) (request HP) =
      some (fun _ => base) :=
  compressed_value_task HP (request HP).task

-- A positive small-floor computation can have nonzero error at a low budget. Here
-- both actual scheduled endpoints are zero, while the genuine top-bin diagonal is one.
private lemma prefixes_one (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (task : HierarchyTask HP.k) :
    (data HP).initialPrefixes 1 { request HP with task := task } = some (fun _ => 0) := by
  have hg (d : ℕ) := BudgetData.completedGroup_initial (data HP) 1 d (by decide)
    (show (data HP).bins.Nonempty from by simp [data])
    { request HP with task := task }
  have hi (d : ℕ) : (data HP).initialGroupInput 1 d
      { request HP with task := task } = fun _ => 0 := by
    funext σ x y
    unfold BudgetData.initialGroupInput
    have hb (i : ℕ) : (data HP).sampleScale { request HP with task := task } (some i) ≤ 0 := by
      change ⌊Real.logb 2 (rate i / rate 0)⌋ ≤ 0
      rw [show rate 0 = 1 by norm_num [rate], div_one]
      have hr := rate_antitone (Nat.zero_le i)
      norm_num only [rate, pow_zero, inv_one] at hr
      exact Int.floor_nonpos (Real.logb_nonpos (by norm_num) (rate_pos i).le hr)
    have hz (i e : ℕ) : LogSpaceEstimation.lastBudget 1 e 1
        ((data HP).sampleScale { request HP with task := task } (some i)) = 0 := by
      unfold LogSpaceEstimation.lastBudget LogSpaceEstimation.scaleCutoff
      omega
    change (∑ bin ∈ (data HP).bins,
      ((if LogSpaceEstimation.lastBudget 1 d 1
          ((data HP).sampleScale { request HP with task := task } (some bin)) = 0
        then 0 else (data HP).initialSample { request HP with task := task } bin σ x y) -
      (if LogSpaceEstimation.lastBudget 1 (2 * d) 1
          ((data HP).sampleScale { request HP with task := task } (some bin)) = 0 then 0
        else (data HP).initialSample { request HP with task := task } bin σ x y))) = 0
    simp only [hz, ↓reduceIte, sub_self, sum_const_zero]
  simp_rw [hi, complete_const_task] at hg
  unfold BudgetData.initialPrefixes
  change (do
    let groups ← (List.range (Nat.log2 1 + 1)).mapM fun j =>
      (data HP).completedGroup _ 1 (Cslib.RowCompression.dyadicSlack (Nat.log2 1 + 1) j)
        (.pilotInput ⟨0, HP.k_pos⟩) { request HP with task := task }
    pure fun j σ x y => ((groups.take j).map
      (fun (A : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) => A σ x y)).sum) = _
  simp_rw [hg]
  norm_num [List.range_succ]
  funext j σ x y
  cases j <;> simp

open Cslib.RowCompression NormalizedMoments in
private lemma compressed_one (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (task : HierarchyTask HP.k)
    (ζ : ℝ) (hζ : 0 < ζ) (hζη : ζ ≤ HP.η / 4) :
    (data HP).compressedBin 1 0 0 ζ ζ { request HP with task := task } = some 0 := by
  have hactive : 0 < (data HP).requestPrecision 1 { request HP with task := task } := by
    norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision, data,
      request, gridChannel, rate]
  unfold BudgetData.compressedBin
  simp only [BudgetData.decodePrefixes]
  rw [ite_eq_right (by simp only [hactive, not_true_eq_false]; norm_num [request, gridChannel])]
  simp only [prefixes_one, bind, Option.bind_some]
  norm_num only [show Nat.log2 1 = 0 by decide, Nat.zero_add, List.range_succ,
    List.range_zero, List.nil_append, List.mapM_cons, List.mapM_nil]
  have hp0 : (data HP).binPreparation 0 { request HP with task := task } 0 = 0 :=
    preparation HP 0 (Or.inl rfl)
  have hc0 (d : ℕ) : (data HP).complete 1 { request HP with task := task } 0 d = some 0 :=
    complete_const_task HP 1 d 0 task
  simp only [hp0, hc0, bind, Option.bind_some, pure]
  apply congrArg some
  funext σ x y
  have hf : 0 ≤ dyadicFloor ζ 1 0 := dyadicFloor_nonneg hζ.le 1 0
  have hn : 5 < NormalizedMoments.compatibleCapacity HP.K 1 0 :=
    (large_K HP).trans_le (NormalizedMoments.compatibleCapacity_bounds HP.K 1 0).1
  have hsmall : dyadicFloor ζ 1 0 ≤ 1 / 2 := by
    have hθ := HP.θ₂_lt
    norm_num at hθ
    have hfbound := dyadicFloor_le_scale_div hζ.le 1 0
    linarith [HP.η₂_lt, HP.η_lt_η₂, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_lt_θ₂, hζη]
  have hnumer : numerator 0 (dyadicFloor ζ 1 0) = 0 :=
    boundedRoutedBinCutoff_eq_zero (by norm_num)
      (fun _ h => polynomialSwitch4_of_le (by norm_num) h)
      rate_pos rate_antitone hsmall 0 (fun _ => 1)
  have ht : ({z | (request HP).terminal.retains (channels (data HP).padding) σ z} :
      Finset (ZMod 5)) = univ := by ext z; simp [request, data, full]
  have hu : { request HP with task := task }.usage.retains (channels (data HP).padding) σ y :=
    full σ 2 [2, 3] y
  simp only [ht, hu, ↓reduceIte]
  have hincr : firstSignalIncrement (fun _ => 0) 0
      (secondSignalIncrement (fun j σ x y =>
        ([0] : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ))[j - 1]?.getD 0 σ x y)
        ζ) σ x 0 = 0 := by
    ext z ν
    fin_cases ν <;> simp [firstSignalIncrement, secondSignalIncrement]
  simp only [iterate_succ, iterate_zero, hincr]
  rw [wide_advance _ _ hn (large_K HP) hf hf]
  have hrow (z : ZMod 5) : updateEntry (dyadicFloor ζ 1 0)
      (dyadicFloor ζ 1 0) ((0 + 0 : ZMod 5 → Fin 2 → ℝ) z) =
      defaultEntry (dyadicFloor ζ 1 0) := by
    apply updateEntry_eq_default_of_size_le
    simpa [entrySize] using hf
  simp only [hrow, defaultEntry, FourthRootHierarchyParams.NormalizedRow.output,
    show (data HP).cutoff 0 = numerator 0 from rfl, ↓reduceIte, hnumer, zero_mul, zero_div,
    Pi.zero_apply, Matrix.zero_apply]

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let ζ := HP.η / 4
    0 < ζ ∧ ζ ≤ HP.η ∧
      (data HP).compressedBin 1 0 0 ζ ζ (request HP) = some 0 ∧
      ∀ σ x, |(0 : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) σ x x -
        denseChild 1 id (request HP) (numerator 0) (polynomialPrepCutoff4 HP.θ)
          HP.ρ HP.K base σ x x| = 1 := by
  dsimp only
  refine ⟨by linarith [HP.η_pos], by linarith [HP.η_pos],
    compressed_one HP (request HP).task (HP.η / 4) (by linarith [HP.η_pos]) le_rfl, ?_⟩
  intro σ x
  rw [top_dense]
  norm_num [base]

-- A nonzero error also occurs with every scalar small-floor premise of the parent
-- normalization allocation satisfied. All parameters are chosen explicitly from HP.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ scale ζ : ℝ, 0 < scale ∧ scale ≤ HP.η ∧
      scale ≤ HP.toHierarchyParams.atomCap / 10000 ∧ 0 < ζ ∧ ζ ≤ scale / 2 ∧
      ζ ≤ scale ∧ ζ ≤ 1 ∧ ζ ≤ HP.θ ∧
      (data HP).compressedBin 1 0 0 ζ ζ (request HP) = some 0 ∧
      ∀ σ x, |(0 : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) σ x x -
        denseChild 1 id (request HP) (numerator 0) (polynomialPrepCutoff4 HP.θ)
          HP.ρ HP.K base σ x x| = 1 := by
  let scale := min HP.η (min HP.θ (min 1 (HP.toHierarchyParams.atomCap / 10000)))
  have hcap := FourthRootHierarchyParams.NormalizedRow.cap_pos HP
  have hs : 0 < scale := lt_min HP.η_pos
    (lt_min HP.θ_pos (lt_min zero_lt_one (div_pos hcap (by norm_num))))
  have hη : scale ≤ HP.η := min_le_left _ _
  have hθ : scale ≤ HP.θ := (min_le_right _ _).trans (min_le_left _ _)
  have h1 : scale ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc : scale ≤ HP.toHierarchyParams.atomCap / 10000 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨scale, scale / 4, hs, hη, hc, by positivity, by linarith,
    by linarith, by linarith, by linarith, ?_, ?_⟩
  · exact compressed_one HP (request HP).task (scale / 4) (by positivity) (by linarith)
  · intro σ x
    rw [top_dense]
    norm_num [base]

-- A literal parent pair at M=2 executes its nonzero-error compressed child at m=1.
-- The reset-right request is separately executed on its own source, despite zero left correction.
private lemma right_available (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (ζ : ℝ) (M : ℕ) (hM : 0 < M) :
    let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
      (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
      ((data HP).binRate 0)
    ∃ A, (data HP).compressedBin M 0 0 ζ ζ Q.right = some A := by
  dsimp only
  let q := (HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
    (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
    ((data HP).binRate 0)).right
  have hs : q.source = gridChannel 1 0 [] := by
    simp [q, HierarchyTask.rawRequests, BudgetData.midpoint, BudgetData.midpointRole,
      request, gridChannel]
  have ht : q.terminal = gridChannel 2 0 [2, 3] := rfl
  have hu : q.usage = gridChannel 2 0 [2, 3] := by
    simp [q, HierarchyTask.rawRequests, request, data, gridChannel]
  obtain ⟨F, hF⟩ : ∃ F, (data HP).initialPrefixes M q = some F :=
    ⟨_, ((data HP).initialPrefixes_grid M hM (by simp [data])
      q 1 2 (by decide) 0 0 [] [2, 3] hs ht).1⟩
  obtain ⟨W, hW⟩ : ∃ W, (List.range (Nat.log2 M + 1)).mapM (fun j =>
      (data HP).complete M q ((data HP).binPreparation 0 q (F (j + 1)))
        (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j)) = some W := by
    have hc (j : ℕ) := (data HP).complete_grid M q 1 2 (by decide) 0 0 [] [2, 3] hs hu
      ((data HP).binPreparation 0 q (F (j + 1)))
      (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j)
    simp_rw [hc]
    exact ⟨_, List.mapM_pure⟩
  have hp : 0 < (data HP).requestPrecision M q := by
    norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision, data, hs, ht,
      gridChannel, rate]
    positivity
  change ∃ A, (data HP).compressedBin M 0 0 ζ ζ q = some A
  unfold BudgetData.compressedBin
  rw [ite_eq_right (by simp [hp, ht, gridChannel, hM.ne'])]
  simp only [hF, bind, Option.bind_some, hW, pure]
  exact ⟨_, rfl⟩

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ scale ζ : ℝ, 0 < scale ∧ scale ≤ HP.η ∧ scale ≤ max (1 : ℝ) 16 / 10000 ∧
      0 < ζ ∧ ζ ≤ scale / 2 ∧ ζ ≤ scale ∧ ζ ≤ 1 ∧
      (data HP).pairedSample (fun m q => if m < 2 then
        (data HP).compressedHistory (fun _ => 0) ζ ζ m q else none)
        2 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) (some 0) = some 0 ∧
      ∀ σ x, |(0 : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) σ x x -
        (data HP).initialSample (request HP) 0 σ x x| = 1 := by
  let scale := min HP.η (min 1 (max (1 : ℝ) 16 / 10000))
  have hs : 0 < scale := lt_min HP.η_pos (lt_min zero_lt_one (by norm_num))
  have hη : scale ≤ HP.η := min_le_left _ _
  have h1 : scale ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hc : scale ≤ max (1 : ℝ) 16 / 10000 :=
    (min_le_right _ _).trans (min_le_right _ _)
  let ζ := scale / 4
  have hζ : 0 < ζ := by dsimp only [ζ]; positivity
  have hd :
      let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
        (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
        ((data HP).binRate 0)
      (data HP).compressedBin 1 0 0 ζ ζ Q.direct = some 0 := by
    simpa only [HierarchyTask.rawRequests, request, data, gridChannel, rate, pow_zero,
      inv_one, min_self] using
      compressed_one HP (.baseNormalized 0 0) ζ hζ (by dsimp only [ζ]; linarith)
  obtain ⟨R, hR⟩ := right_available HP ζ 1 (by decide)
  have hp := (data HP).positiveSample_initial_compressed (fun _ => 0) ζ ζ 2 1 0
    (by decide) (request HP) 0 R hd hR
  have hp0 : (data HP).positiveSample (fun m q => if m < 2 then
      (data HP).compressedHistory (fun _ => 0) ζ ζ m q else none)
      1 0 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) = some 0 := by
    convert hp.1 using 1
    congr 1
    funext σ x y
    simp
  refine ⟨scale, ζ, hs, hη, hc, hζ, by dsimp only [ζ]; linarith,
    by dsimp only [ζ]; linarith, by dsimp only [ζ]; linarith, ?_, ?_⟩
  · have hf : LogSpaceEstimation.lastBudget 2 1 (data HP).slack
        ((data HP).sampleScale (request HP) (some 0)) = 1 := by
      norm_num [BudgetData.sampleScale, data, request, gridChannel, rate,
        LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
    have hc0 : LogSpaceEstimation.lastBudget 2 (2 * 1) (data HP).slack
        ((data HP).sampleScale (request HP) (some 0)) = 0 := by
      norm_num [BudgetData.sampleScale, data, request, gridChannel, rate,
        LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
    simp only [BudgetData.pairedSample, hf, hc0, one_ne_zero, ↓reduceIte]
    simp only [BudgetData.sample, one_ne_zero, ↓reduceIte, hp0,
      bind, Option.bind_some, pure, sub_zero]
  · intro σ x
    rw [initial HP 0 (by simp [data])]
    norm_num [base]

-- The actual paired schedule at parent budget one executes its zero boundary twice.
-- No positive lower-budget availability or rooted certificate can be smuggled into this edge.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let B := data HP
    B.pairedSample (fun n q => if n < 1 then
      B.compressedHistory (fun _ => 0) (HP.η / 4) (HP.η / 4) n q else none)
      1 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) (some 0) = some 0 ∧
    ∃ A C,
      B.pairedSample (fun n q => if n < 1 then
        B.compressedHistory (fun _ => 0) (HP.η / 4) (HP.η / 4) n q else none)
        1 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) (some 0) = some A ∧
      B.pairedSample (fun n q => if n < 1 then B.evaluate n q else none)
        1 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) (some 0) = some C ∧
      rowNormPow 4 5 (request HP).source.rate
        (fun σ x => (request HP).source.retains (channels B.padding) σ x)
        (fun σ y => (request HP).usage.retains (channels B.padding) σ y) (A - C) ≤ 0 := by
  dsimp only
  constructor
  · norm_num [BudgetData.pairedSample, BudgetData.sampleScale, data, request, gridChannel,
      rate, LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
  · have h := BudgetData.pairedSample_initial_compressed_root (data HP) (fun _ => 0)
      (HP.η / 4) (HP.η / 4) 1 1 0 (by decide) (request HP)
      (by norm_num [request, gridChannel, rate]) (fun _ => 0) rfl (fun _ => 0)
      (fun _ => le_rfl) (fun n hn hn0 => by omega)
    simpa only [add_zero, mul_zero, Nat.cast_ofNat] using h

-- The same zero endpoints pass through both literal bins and the actual common group walk.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ F G,
      (data HP).completedGroup (fun n q => if n < 1 then
        (data HP).compressedHistory (fun _ => 0) (HP.η / 4) (HP.η / 4) n q else none)
        1 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) = some F ∧
      (data HP).completedGroup (fun n q => if n < 1 then (data HP).evaluate n q else none)
        1 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) = some G ∧
      rowNormPow 4 5 (request HP).source.rate
        (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
        (fun σ y => (request HP).usage.retains (channels (data HP).padding) σ y) (F - G) ≤ 0 := by
  have hb (i : ℕ) (hi : i ∈ (data HP).bins) : i = 0 ∨ i = 1 := by simpa [data] using hi
  have ha (i : ℕ) (hi : i ∈ (data HP).bins) :
      (data HP).pairedSample (fun n q => if n < 1 then
        (data HP).compressedHistory (fun _ => 0) (HP.η / 4) (HP.η / 4) n q else none)
        1 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) (some i) = some 0 := by
    rcases hb i hi with rfl | rfl <;>
      norm_num [BudgetData.pairedSample, BudgetData.sampleScale, data, request, gridChannel,
        rate, LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
  have hc (i : ℕ) (hi : i ∈ (data HP).bins) :
      (data HP).pairedSample (fun n q => if n < 1 then (data HP).evaluate n q else none)
        1 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) (some i) = some 0 := by
    rcases hb i hi with rfl | rfl <;>
      norm_num [BudgetData.pairedSample, BudgetData.sampleScale, data, request, gridChannel,
        rate, LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
  have h := BudgetData.completedGroup_initial_compressed_error (data HP) (fun _ => 0)
    (HP.η / 4) (HP.η / 4) 1 1 (by simp [data]) (request HP) 0 2 (by decide)
    0 0 [1] [2, 3] rfl rfl (fun _ => 0) (fun _ => 0) (fun _ => 0) ha hc
    (fun _ _ => by simp [rowNormPow])
  simpa only [sum_const_zero, mul_zero, Nat.cast_ofNat] using h

-- Every scheduled endpoint is zero at M=1, independently of the supplied history.
private lemma group_one_zero (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → Option (BudgetValue 5)) :
    (data HP).completedGroup history 1 1 (.pilotInput ⟨0, HP.k_pos⟩)
      (request HP) = some 0 := by
  have hz (d : ℕ) (bin : Option ℕ) : LogSpaceEstimation.lastBudget 1 d (data HP).slack
      ((data HP).sampleScale (request HP) bin) = 0 := by
    unfold LogSpaceEstimation.lastBudget LogSpaceEstimation.scaleCutoff
    change 1 - max d (1 * (1 + _)) = 0
    omega
  have hp (bin : Option ℕ) : (data HP).pairedSample history 1 1
      (.pilotInput ⟨0, HP.k_pos⟩) (request HP) bin = some 0 := by
    simp only [BudgetData.pairedSample, hz, ↓reduceIte]
  unfold BudgetData.completedGroup
  split
  · rfl
  · have hm : ((data HP).rays (.pilotInput ⟨0, HP.k_pos⟩)).mapM (fun bin =>
        (data HP).pairedSample history 1 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) bin) =
        some (((data HP).rays (.pilotInput ⟨0, HP.k_pos⟩)).map (fun _ =>
          (0 : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ))) := by
      apply List.mapM_eq_some_iff_forall₂.mpr
      rw [List.forall₂_map_right_iff, List.forall₂_same]
      exact fun bin _ => hp bin
    rw [hm]
    simp only [bind, Option.bind_some, List.map_map, Function.comp_def,
      Pi.zero_apply, Matrix.zero_apply, List.sum_map_zero]
    convert complete_const HP 1 1 0 using 1
    congr 1

-- Consume the nonlinear sensitivity payment on an actual computed zero history.
-- The target is nonzero; a zero transport payment does not erase its semantic deficit.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ζ : ℝ)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) :
    ∃ groups,
      (List.range (Nat.log2 1 + 1)).mapM (fun j =>
        (data HP).completedGroup (fun m q => if m < 1 then
          (data HP).compressedHistory (fun _ => 0) ζ ζ m q else none) 1
          (dyadicSlack (Nat.log2 1 + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          (request HP)) = some groups ∧
      rowNormPow 4 5 (rate 0) (retainedMask threeRoles.source (side 5 0) (data HP).padding [1])
        (retainedMask threeRoles.terminal (side 5 0) (data HP).padding [2, 3])
        (fun _ => secondMeanEnvelope threeRoles (data HP).padding [1] [2, 3] 0 0 0 Lh Lρ ζ
          (fun σ x y => ((groups.take 1).map (fun T => T σ x y)).sum) (data HP).base) ≤
        5 * (|ζ| * (Lh + Lρ) / rate 0) ^ 4 *
          (data HP).initialTransportMoment 1 1 (request HP) threeRoles 0 0 [1] [2, 3]
            (fun _ => 0) 0 := by
  have ha (j : ℕ) (hj : j < Nat.log2 1 + 1) :
      (data HP).completedGroup (fun m q => if m < 1 then
        (data HP).compressedHistory (fun _ => 0) ζ ζ m q else none) 1
        (dyadicSlack (Nat.log2 1 + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { request HP with usage := (request HP).terminal } = some 0 := by
    have hj0 : j = 0 := by norm_num at hj; omega
    subst j
    simpa only [request, show dyadicSlack (Nat.log2 1 + 1) 0 = 1 by decide]
      using group_one_zero HP _
  have hc (j : ℕ) (hj : j < Nat.log2 1 + 1) :
      (data HP).completedGroup (fun m q => if m < 1 then (data HP).evaluate m q else none) 1
        (dyadicSlack (Nat.log2 1 + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { request HP with usage := (request HP).terminal } = some 0 := by
    have hj0 : j = 0 := by norm_num at hj; omega
    subst j
    simpa only [request, show dyadicSlack (Nat.log2 1 + 1) 0 = 1 by decide]
      using group_one_zero HP _
  obtain ⟨groups, hgroups, hb⟩ := (data HP).initial_compressed_preparation 1 (by decide) 1
    (by ext i; simp only [data, mem_insert, mem_singleton, mem_range]; omega)
    rfl rfl rfl (by norm_num [data]) (⟨1, 4, by decide, by decide⟩ : Horizon 5) (by decide)
    (request HP) threeRoles 0 0 [1] [2, 3] rfl rfl (by decide)
    (by intro x y; by_cases h : x = y <;> simp [data, base, h]) (by simp [data, base])
    (fun _ => 0) ζ ζ (fun _ => 0) (fun _ => 0) (fun _ => 0) ha hc
    (fun _ _ => by simp [rowNormPow]) 0 0 (by decide) rfl hLh hLρ hh hρ
  exact ⟨groups, hgroups, (hb 0 (by decide)).1⟩

-- The same actual zero-boundary history consumes the sharp parent reserve without
-- supplying a final error or changing the decoder. The canonical target remains nonzero.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {ζ scale floor : ℝ} (hζ : 0 < ζ) (hs : 0 < scale) (hmargin : scale ≤ HP.η)
    (hcap : scale ≤ max (1 : ℝ) 16 / 10000) (hsmall : ζ ≤ scale / 2)
    (hf : 0 < floor) (hfs : floor ≤ scale) (hf1 : floor ≤ 1) :
    ∃ C Cp : ℝ, 0 ≤ C ∧ 0 ≤ Cp ∧
      rootDistPow 4 5 (request HP).source.rate
        (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
        (fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y)
        ((data HP).decodePrefixes 1 0 0 ζ floor (request HP) (fun _ => 0) [0])
        (denseChild (data HP).padding id (request HP) ((data HP).cutoff 0)
          (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K base) ≤
        (data HP).initialFourMaxReserve 1 0 0 ζ floor (request HP) threeRoles 0 0 [1] [2, 3]
          base (fun _ => 0) [0] 1 C Cp := by
  obtain ⟨C, hC, hscales⟩ := BudgetData.exists_initial_compressed_fourMax HP
    (by norm_num : (0 : ℝ) ≤ 1) hζ hs hmargin hcap hsmall
  obtain ⟨Cp, hCp, hbound⟩ := hscales floor hf hfs hf1
  have hgroups : (List.range (Nat.log2 1 + 1)).mapM (fun j =>
      (data HP).completedGroup (fun m q => if m < 1 then
        (data HP).compressedHistory (fun _ => 0) ζ floor m q else none) 1
        (dyadicSlack (Nat.log2 1 + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { request HP with usage := (request HP).terminal }) = some [0] := by
    rw [show { request HP with usage := (request HP).terminal } = request HP from rfl]
    norm_num only [show Nat.log2 1 = 0 by decide, Nat.zero_add, List.range_succ,
      List.range_zero, List.nil_append, List.mapM_cons, List.mapM_nil]
    rw [show dyadicSlack 1 0 = 1 by decide, group_one_zero]
    rfl
  have hF : (fun p σ x y =>
      (([0] : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)).take p |>.map
        (fun T => T σ x y)).sum) =
      (fun _ => (0 : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)) := by
    funext p σ x y
    cases p <;> simp
  have hW : (List.range (Nat.log2 1 + 1)).mapM (fun j =>
      (data HP).complete 1 (request HP) ((data HP).binPreparation 0 (request HP)
        ((fun _ => 0) (j + 1))) (dyadicSlack (Nat.log2 1 + 1) j)) = some [0] := by
    have hw (j : ℕ) : (data HP).complete 1 (request HP)
        ((data HP).binPreparation 0 (request HP) ((fun _ => 0) (j + 1)))
        (dyadicSlack (Nat.log2 1 + 1) j) = some 0 := by
      rw [show (data HP).binPreparation 0 (request HP) 0 = 0 from
        preparation HP 0 (Or.inl rfl)]
      exact complete_const HP 1 _ 0
    simp_rw [hw]
    norm_num [List.range_succ]
  have hstep (i : ℕ) : rate i = 16 * rate (i + 1) := by
    simp only [rate, pow_succ, _root_.mul_inv_rev]
    ring
  have hb := hbound (data HP) rate rate_pos hstep 1 0 0 (request HP)
    ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩ rfl rfl rfl base
    (by intro x y; by_cases h : x = y <;> simp [base, Matrix.one_apply, h])
    (fun _ => 0) ζ floor [0] hgroups
  dsimp only at hb
  rw [hF] at hb
  refine ⟨C, Cp, hC, hCp, ?_⟩
  apply hb [0] _ threeRoles 0 0 [1] [2, 3] rfl rfl rfl
  convert hW using 1
  apply congrArg (fun f : ℕ → Option (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) =>
    (List.range (Nat.log2 1 + 1)).mapM f)
  funext j
  rw [show (fun σ x y =>
    (([0] : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)).take (j + 1) |>.map
      (fun T => T σ x y)).sum) = 0 from congrFun hF (j + 1)]

-- Positive decoder scale with an oversized floor gives a computed child with genuine
-- nonzero error. This tests transport inputs, not an admissible small-floor allocation.
open Cslib.RowCompression in
private lemma compressed_large_floor (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ A, (data HP).compressedBin 2 0 0 1 4096 (request HP) = some A ∧
      ∀ σ x, |A σ x x - base x x| = 1 := by
  rw [compressed]
  refine ⟨_, rfl, ?_⟩
  intro σ x
  have hn (j : ℕ) : 5 < NormalizedMoments.compatibleCapacity HP.K 2 j :=
    (large_K HP).trans_le (NormalizedMoments.compatibleCapacity_bounds HP.K 2 j).1
  have hf0 : dyadicFloor 4096 2 0 = 1 / 256 := by norm_num [dyadicFloor, dyadicSlack]
  have hf1 : dyadicFloor 4096 2 1 = 4 := by norm_num [dyadicFloor, dyadicSlack]
  have hd : (iterate univ (NormalizedMoments.compatibleCapacity HP.K 2) (fun _ => HP.K)
      (dyadicFloor 4096 2) (increment 1 x) ⟨0, 0⟩ 2).defaultValue = 4 := by
    simp only [iterate_succ, iterate_zero, hf0, hf1]
    rw [wide_advance _ _ (hn 0) (large_K HP) (by norm_num) (by norm_num)]
    rw [wide_advance _ _ (hn 1) (large_K HP) (by norm_num) (by norm_num)]
  have hk (f : ZMod 5 → ℝ) : kthLargest HP.K univ f = 0 :=
    kthLargest_eq_zero_of_card_lt (by simpa using large_K HP) f
  have hη : HP.η₂ ≤ 4 := by
    have hθ := HP.θ₂_lt
    norm_num at hθ
    linarith [HP.η₂_lt, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_lt_θ₂]
  dsimp only
  simp only [firstRank, hk, hd, max_eq_left (by norm_num : (0 : ℝ) ≤ 4),
    FourthRootHierarchyParams.NormalizedRow.output, HP.ρ_zero 4 hη,
    mul_zero, zero_div]
  norm_num [base]

-- Both scheduled groups execute below capacity: this is proved for the actual iterate,
-- not supplied as a premise of the accuracy check below.
open Cslib.RowCompression in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (x : ZMod 5) :
    ∀ i < 2, stepThreshold univ (NormalizedMoments.compatibleCapacity HP.K 2)
      (fun _ => HP.K) (dyadicFloor (HP.η / 4) 2) (increment (HP.η / 4) x) ⟨0, 0⟩ i ≤
        dyadicFloor (HP.η / 4) 2 i :=
  (actual_iterate HP x).2.2

-- The executed positive history and compression have zero rooted error against the
-- actual dense polynomial target; no final-output accuracy premise is supplied.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).compressedBin 2 0 0 (HP.η / 4) (HP.η / 4) (request HP) =
      some (fun _ => base) ∧
    rootDistPow 4 5 (rate 0)
      (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
      (fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y)
      (fun _ => base)
      (denseChild 1 id (request HP) (numerator 0) (polynomialPrepCutoff4 HP.θ)
        HP.ρ HP.K base) = 0 := by
  refine ⟨compressed_value HP, ?_⟩
  have hd : denseChild 1 id (request HP) (numerator 0) (polynomialPrepCutoff4 HP.θ)
      HP.ρ HP.K base = fun _ => base := by
    funext σ x y
    exact top_dense HP σ x y
  rw [hd]
  simp [rootDistPow, rowNormPow]

private lemma mean_loss (HP : FourthRootHierarchyParams 16 1 16 32 8) (j : ℕ)
    (hj : j < 2) (x y : ZMod 5) :
    let F := fun j (_ : Environment 5 3) => if 2 ≤ j then base else 0
    NormalizedMoments.actualClippedMean HP 0 2 (side 5 0) (side 5 0) (side 5 0)
      1 [1] [2, 3] 0 base (HP.η / 4)
      (NormalizedMoments.firstSignalIncrement F 0 (fun _ _ _ _ => 0)) 0 0 j x y =
      min 1 ((data HP).initialPolynomialLoss 2 1 j (request HP) x y /
        (rate 0 + base x y)) := by
  have hC (x y : ZMod 5) : 0 ≤ (data HP).base x y := by
    simp only [data, base, Matrix.one_apply]
    split_ifs <;> norm_num
  exact BudgetData.initialFirstSignal_clippedMean (data HP) 2 (by decide) 1
    (by ext i; simp only [data, mem_insert, mem_singleton, mem_range]; omega)
    rfl rfl rfl (by norm_num [data])
    (⟨1, 4, by decide, by decide⟩ : Horizon 5) (by decide)
    (request HP) 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl (by decide)
    hC (by simp [data, base]) _ (prefixes HP) j (by simpa using hj)
    (side 5 0) (HP.η / 4) (fun _ _ _ _ => 0) x y

-- A nonzero deterministic loss at the first actual prefix is not erased by scalar
-- coverage. At the next prefix it vanishes. The initial coarse boundary is checked too.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (x : ZMod 5) :
    (data HP).initialFineLoss 2 2 0 (request HP) x x = 1 ∧
    (data HP).initialFineLoss 2 2 1 (request HP) x x = 0 ∧
    (data HP).initialCoarseLoss 2 2 (request HP) x x = 0 := by
  norm_num [BudgetData.initialFineLoss, BudgetData.initialCoarseLoss,
    BudgetData.sampleScale, data, request, gridChannel, rate, base, numerator,
    boundedRoutedBinCutoff, routedBinCutoff, binWeight, polynomialSwitch4,
    polynomialTransition4, transitionPolynomial4, Cslib.RowCompression.dyadicSlack,
    LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]

-- Exact actual predecoder mean statistics: early inactive mass costs 1/2, and the
-- completed history costs zero. The target stays the canonical initial base.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (x : ZMod 5) :
    let F := fun j (_ : Environment 5 3) => if 2 ≤ j then base else 0
    let μ := fun j => NormalizedMoments.actualClippedMean HP 0 2 (side 5 0) (side 5 0)
      (side 5 0) 1 [1] [2, 3] 0 base (HP.η / 4)
      (NormalizedMoments.firstSignalIncrement F 0 (fun _ _ _ _ => 0)) 0 0 j x x
    μ 0 = 1 / 2 ∧ μ 1 = 0 := by
  dsimp only
  rw [mean_loss HP 0 (by decide), mean_loss HP 1 (by decide)]
  norm_num [BudgetData.initialPolynomialLoss, BudgetData.initialFineLoss,
    BudgetData.initialCoarseLoss, BudgetData.sampleScale, data, request, gridChannel,
    rate, base, numerator, boundedRoutedBinCutoff, routedBinCutoff, binWeight,
    polynomialSwitch4, polynomialTransition4, transitionPolynomial4,
    Cslib.RowCompression.dyadicSlack, LogSpaceEstimation.lastBudget,
    LogSpaceEstimation.scaleCutoff]

private def scaledData (HP : FourthRootHierarchyParams 16 1 16 32 8) (w : ℝ) :
    BudgetData HP 5 := {data HP with base := w • base}

-- Both the nonzero fine-bin case and the omitted-fine case use a successful actual
-- history. This checks canonical means at unequal bin/terminal rates, not only scalar sums.
private lemma scaledHistory_mean (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (w : ℝ) (hw : w = 1 / 16 ∨ w = 1 / 256) (x : ZMod 5) :
    ∃ F, (scaledData HP w).initialPrefixes 8 (request HP) = some F ∧
      rowSliceMean (X 0 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [1]))
        (Y 2 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [2, 3])) (F 4) x x =
        if w = 1 / 16 then w else 0 := by
  let B := scaledData HP w
  have hbins : B.bins.Nonempty := by simp [B, scaledData, data]
  obtain ⟨hgrid, _⟩ := B.initialPrefixes_grid 8 (by decide) hbins
    (request HP) 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl
  dsimp only at hgrid
  obtain ⟨F, hF⟩ : ∃ F, B.initialPrefixes 8 (request HP) = some F := ⟨_, hgrid⟩
  have hw0 : 0 ≤ w := by rcases hw with rfl | rfl <;> norm_num
  have hw1 : w ≤ 1 := by rcases hw with rfl | rfl <;> norm_num
  have hC (v z : ZMod 5) : 0 ≤ B.base v z := by
    change 0 ≤ w * base v z
    apply mul_nonneg hw0
    simp only [base, Matrix.one_apply]
    split_ifs <;> norm_num
  have hC1 : B.base *ᵥ 1 ≤ 1 := by
    intro v
    simpa [B, scaledData, data, base, Matrix.smul_mulVec] using hw1
  have hm := B.initialPrefix_polynomial_mean 8 (by decide) 1
    (by ext i; simp only [B, scaledData, data, mem_insert, mem_singleton, mem_range]; omega)
    rfl rfl rfl (by norm_num [B, scaledData, data])
    (⟨1, 4, by decide, by decide⟩ : Horizon 5) (by decide)
    (request HP) 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl (by decide)
    hC hC1 F hF 3 (by decide) x x
  dsimp only at hm
  refine ⟨F, hF, ?_⟩
  have hscale : Real.logb 2 (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.logb_pow]
    norm_num
  rcases hw with rfl | rfl <;>
    norm_num [B, scaledData, data, base, request, gridChannel,
      BudgetData.initialFineLoss, BudgetData.initialCoarseLoss, BudgetData.sampleScale,
      numerator, boundedRoutedBinCutoff, routedBinCutoff, binWeight, rate,
      polynomialSwitch4, polynomialTransition4, transitionPolynomial4,
      Cslib.RowCompression.dyadicSlack, LogSpaceEstimation.lastBudget,
      LogSpaceEstimation.scaleCutoff, hscale] at hm ⊢ <;> linarith

example (HP : FourthRootHierarchyParams 16 1 16 32 8) (x : ZMod 5) :
    ∃ F, (scaledData HP (1 / 16)).initialPrefixes 8 (request HP) = some F ∧
      rowSliceMean (X 0 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [1]))
        (Y 2 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [2, 3])) (F 4) x x = 1 / 16 := by
  simpa using scaledHistory_mean HP (1 / 16) (Or.inl rfl) x

example (HP : FourthRootHierarchyParams 16 1 16 32 8) (x : ZMod 5) :
    ∃ F, (scaledData HP (1 / 256)).initialPrefixes 8 (request HP) = some F ∧
      rowSliceMean (X 0 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [1]))
        (Y 2 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [2, 3])) (F 4) x x = 0 := by
  simpa using scaledHistory_mean HP (1 / 256) (Or.inr rfl) x

-- At this positive omitted entry every retained-bin mass is zero; the entire canonical
-- deficit remains explicit even after all scheduled groups have executed.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (x : ZMod 5) :
    (scaledData HP (1 / 256)).initialPolynomialLoss 8 1 3 (request HP) x x = 1 / 256 ∧
    (scaledData HP (1 / 256)).initialFineLoss 8 4 3 (request HP) x x = 0 ∧
    (scaledData HP (1 / 256)).initialCoarseLoss 8 4 (request HP) x x = 0 := by
  norm_num [BudgetData.initialPolynomialLoss, BudgetData.initialFineLoss,
    BudgetData.initialCoarseLoss, scaledData, data, base, numerator,
    boundedRoutedBinCutoff, routedBinCutoff, binWeight, rate, polynomialSwitch4,
    polynomialTransition4, transitionPolynomial4]

private lemma scale_cutoffs (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∀ bin ∈ (data HP).bins, LogSpaceEstimation.scaleCutoff (data HP).slack
      ((data HP).sampleScale { (request HP) with usage := (request HP).terminal }
        (some bin)) < 8 := by
  have hscale : Real.logb 2 (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.logb_pow]
    norm_num
  have hsmall : Real.logb 2 (1 / 16 : ℝ) = -4 := by
    rw [one_div, Real.logb_inv, hscale]
  intro bin hi
  have hi' : bin = 0 ∨ bin = 1 := by simpa only [data, mem_insert, mem_singleton] using hi
  rcases hi' with rfl | rfl <;>
    norm_num [BudgetData.sampleScale, LogSpaceEstimation.scaleCutoff, data, request,
      gridChannel, rate, Real.logb_inv, hscale, hsmall]

-- A successful actual history consumes the new final deterministic payment. The positive
-- fine-bin and wholly omitted-entry cases both satisfy the actual scale allocation.
-- This controls the first clipped mean only, not preparation or compressed output.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (w : ℝ) (hw : w = 1 / 16 ∨ w = 1 / 256) (x : ZMod 5) :
    ∃ F, (scaledData HP w).initialPrefixes 8 (request HP) = some F ∧
      NormalizedMoments.actualClippedMean HP 0 2 (side 5 0) (side 5 0) (side 5 0)
        1 [1] [2, 3] 0 (w • base) (HP.η / 4)
        (NormalizedMoments.firstSignalIncrement F 0 (fun _ _ _ _ => 0)) 0 0 3 x x ≤ 1 / 16 := by
  obtain ⟨F, hF, _⟩ := scaledHistory_mean HP w hw x
  have hw0 : 0 ≤ w := by rcases hw with rfl | rfl <;> norm_num
  have hw1 : w ≤ 1 := by rcases hw with rfl | rfl <;> norm_num
  have hC (v z : ZMod 5) : 0 ≤ (scaledData HP w).base v z := by
    change 0 ≤ w * base v z
    apply mul_nonneg hw0
    simp only [base, Matrix.one_apply]
    split_ifs <;> norm_num
  have hC1 : (scaledData HP w).base *ᵥ 1 ≤ 1 := by
    intro v
    simpa [scaledData, data, base, Matrix.smul_mulVec] using hw1
  refine ⟨F, hF, ?_⟩
  have hp := BudgetData.initialFirstSignal_clippedMean_final (scaledData HP w) 8 (by decide)
    1 (by ext i; simp only [scaledData, data, mem_insert, mem_singleton, mem_range]; omega)
    rfl rfl rfl (by norm_num [scaledData, data])
    (⟨1, 4, by decide, by decide⟩ : Horizon 5) (by decide)
    (request HP) 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl (by decide)
    hC hC1 F hF (by decide) (scale_cutoffs HP) (side 5 0) (HP.η / 4)
    (fun _ _ _ _ => 0) x x
  norm_num [scaledData, data, rate] at hp ⊢
  exact hp

-- At budget eight only the initial group is inactive; its charge is paid by the tiny
-- first floor. Every later inactive charge is zero, including at an omitted positive entry.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (i : ℕ) (hi : 0 < i) :
    (data HP).initialInactiveCharge 8 i (request HP) = 0 :=
  BudgetData.initialInactiveCharge_eq_zero_of_pos (data HP) 8 i (by decide) hi
    (request HP) (scale_cutoffs HP)

-- The stationary charge is global over all four executed groups. Shrinking the floor
-- does not remove the 72 L coefficient; omitted coverage and the initial charge survive.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) {δ L : ℝ}
    (hδ : 0 < δ) (hL : 0 ≤ L) :
    (36 * L + 72 * L / δ) * (∑ i ∈ range 4,
      Cslib.RowCompression.dyadicFloor δ 4 i *
        (data HP).initialMeanCharge 8 1 i 0 (request HP)) ≤
      (36 * L * δ + 72 * L) *
        (1 / 16 / 1023 + 17 * (1 / 1024 : ℝ) ^ 8) := by
  have hp := BudgetData.initialMeanCharge_preloss (data HP) 8 1 0 (by decide)
    (request HP) (by intro bin; exact (rate_pos bin).le) (scale_cutoffs HP) hδ hL
  norm_num [data, rate] at hp ⊢
  exact hp

-- The edge budget does not satisfy the allocation premise: the fine-bin cutoff is five.
-- Therefore the final uniform charge remains positive, even though the identity fixture's
-- actual fine-bin mass is zero. No arbitrary target is capped to erase this distinction.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).initialMeanCharge 2 1 1 0 (request HP) = 17 / 16 := by
  have hscale : Real.logb 2 (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.logb_pow]
    norm_num
  have hsmall : Real.logb 2 (1 / 16 : ℝ) = -4 := by
    rw [one_div, Real.logb_inv, hscale]
  norm_num [BudgetData.initialMeanCharge, BudgetData.initialInactiveCharge,
    BudgetData.sampleScale, LogSpaceEstimation.scaleCutoff, data, request, gridChannel,
    rate, Cslib.RowCompression.dyadicSlack, Real.logb_inv, hscale, hsmall]

-- The coarse boundary vanishes even at zero budget, without a successful-history premise.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (x y : ZMod 5) :
    (data HP).initialCoarseLoss 0 1 (request HP) x y = 0 := by
  simpa using BudgetData.initialCoarseLoss_eq_zero (data HP) 0 (request HP) x y

-- These are the literal preparation executions used by compressedBin, including the
-- initially inactive prefix. The nonzero deterministic bias is not second walk noise.
private lemma preparation_walks (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (List.range (Nat.log2 2 + 1)).mapM (fun j =>
      (data HP).complete 2 (request HP)
        ((data HP).binPreparation 0 (request HP)
          ((fun i (_ : Environment 5 3) => if 2 ≤ i then base else 0) (j + 1)))
        (Cslib.RowCompression.dyadicSlack (Nat.log2 2 + 1) j)) =
      some [0, fun _ => base] := by
  norm_num [List.range_succ, Cslib.RowCompression.dyadicSlack]
  simp_rw [preparation HP 0 (Or.inl rfl), preparation HP base (Or.inr rfl)]
  simp_rw [complete_const]
  rfl

private lemma genuine_mean (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (x y : ZMod 5) :
    NormalizedMoments.genuineMean (P := 5) (J := 3) HP 0 2 (side 5 0) (side 5 0)
      (CopyPadding.identifier (1 : ZMod 5) [1] x) 1 [2, 3] 0 base x y = base x y := by
  have hprep : NormalizedMoments.genuinePrep (P := 5) (J := 3) HP 2 1 [2, 3] 0 base =
      fun _ => base := by
    funext σ a b
    unfold NormalizedMoments.genuinePrep DenseRowRecipe.preparation atomPrep
    rw [gate_one, mul_one]
    norm_num only [rate, pow_zero, inv_one, one_pow, div_one]
    by_cases hab : a = b
    · subst b; simpa only [base, Matrix.one_apply_eq] using (prep_values HP).2
    · simpa only [base, Matrix.one_apply_ne hab] using (prep_values HP).1
  unfold NormalizedMoments.genuineMean
  rw [hprep]
  have hf (σ : Environment 5 3) :
      frameRetains 5 4 (side 5 0) (σ 0) (CopyPadding.identifier 1 [1] x) ∧
      frameRetains 5 4 (side 5 0) (σ 2) (CopyPadding.identifier 1 [2, 3] y) := by
    simpa only [gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid]
      using And.intro (full σ 0 [1] x) (full σ 2 [2, 3] y)
  simp [rowSliceMean, hf]

-- At the first executed prefix, genuine preparation is one on the diagonal but
-- preparation of F(1) is zero. At the final prefix and off the diagonal bias is zero.
private lemma actual_preparation_edges
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (x y : ZMod 5) (hxy : x ≠ y) :
    let F := fun i (_ : Environment 5 3) => if 2 ≤ i then base else 0
    let W : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) := [0, fun _ => base]
    let Δ := NormalizedMoments.firstSignalIncrement F 0
      (NormalizedMoments.secondSignalIncrement (fun i σ a b => W[i - 1]?.getD 0 σ a b)
        (HP.η / 4))
    (data HP).initialPrefixes 2 (request HP) = some F ∧
    (List.range 2).mapM (fun j => (data HP).complete 2 (request HP)
      ((data HP).binPreparation 0 (request HP) (F (j + 1)))
      (Cslib.RowCompression.dyadicSlack 2 j)) = some W ∧
    NormalizedMoments.actualClippedMean HP 0 2 (side 5 0) (side 5 0) (side 5 0)
      1 [1] [2, 3] 0 base (HP.η / 4) Δ (fun _ _ _ _ => 0) 1 0 x x = HP.η / 4 ∧
    NormalizedMoments.actualClippedMean HP 0 2 (side 5 0) (side 5 0) (side 5 0)
      1 [1] [2, 3] 0 base (HP.η / 4) Δ (fun _ _ _ _ => 0) 1 1 x x = 0 ∧
    NormalizedMoments.actualClippedMean HP 0 2 (side 5 0) (side 5 0) (side 5 0)
      1 [1] [2, 3] 0 base (HP.η / 4) Δ (fun _ _ _ _ => 0) 1 0 x y = 0 := by
  dsimp only
  have hret (τ : Environment 5 3) (role : Fin 3) (su : List (ZMod 5)) (v : ZMod 5) :
      NormalizedMoments.retainedMask role (side 5 0) 1 su τ v := by
    simpa only [NormalizedMoments.retainedMask, gridChannel,
      CorrectionRowTask.Channel.retains, channels, semanticSide_grid] using full τ role su v
  have hη : 0 ≤ HP.η / 4 := div_nonneg HP.η_pos.le (by norm_num)
  have hη1 : HP.η / 4 ≤ 1 := by
    linarith [HP.η_lt_η₂, HP.η₂_lt, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_lt_θ₂, HP.θ₂_lt]
  refine ⟨prefixes HP, by simpa using preparation_walks HP, ?_, ?_, ?_⟩
  all_goals
    unfold NormalizedMoments.actualClippedMean NormalizedMoments.twoMaskMean
    simp only [Fin.isValue, one_ne_zero, ↓reduceIte,
      NormalizedMoments.actualPrefix_twoSignal_second]
    rw [genuine_mean]
    norm_num [rowSliceMean, hret, base, Matrix.one_apply, hxy,
      abs_of_nonneg hη, min_eq_right hη1]

-- Sensitivity's actual-history consumer must pay the positive early bias; the envelope
-- cannot be replaced by centered walk noise, which is zero in this stationary fixture.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Lh Lρ : ℝ, 0 ≤ Lh ∧ 0 ≤ Lρ ∧ ∀ x : ZMod 5,
      HP.η / 4 ≤ NormalizedMoments.secondMeanEnvelope threeRoles 1 [1] [2, 3]
        0 0 0 Lh Lρ (HP.η / 4) (fun _ => 0) base x x := by
  obtain ⟨Lh, Lρ, hLh, hLρ, hh, hρ⟩ := NormalizedMoments.preparation_stability_constants HP
  refine ⟨Lh, Lρ, hLh, hLρ, ?_⟩
  intro x
  let F := fun i (_ : Environment 5 3) => if 2 ≤ i then base else 0
  let W : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) := [0, fun _ => base]
  have hp := BudgetData.initialSecondSignal_clippedMean_le (data HP) 2 0 0 0 (request HP)
    threeRoles 0 [1] [2, 3] rfl rfl rfl rfl F W (preparation_walks HP)
    hLρ hh hρ (HP.η / 4) 0 (by decide) x x
  have he := (actual_preparation_edges HP x (x + 1) (by simp)).2.2.1
  have hb := he.symm.le.trans hp
  simpa only [F, data, threeRoles, ↓reduceIte, show ¬ 2 ≤ 1 by decide] using hb

-- Integrate the same actual postincrement history: the deterministic term remains
-- the literal deficit's row norm, alongside the original full-rank first-noise rate.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Lh Lρ : ℝ, 0 ≤ Lh ∧ 0 ≤ Lρ ∧
    let F := fun i (_ : Environment 5 3) => if 2 ≤ i then base else 0
    let W : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) := [0, fun _ => base]
    let Xs := NormalizedMoments.retainedMask (0 : Fin 3) (side 5 0) (1 : ZMod 5) [1]
    let Ya := NormalizedMoments.retainedMask (2 : Fin 3) (side 5 0) (1 : ZMod 5) [2, 3]
    rowNormPow 4 5 (rate 0) Xs Ya (fun _ x y =>
      NormalizedMoments.actualClippedMean HP 0 2 (side 5 0) (side 5 0) (side 5 0)
        1 [1] [2, 3] 0 base (HP.η / 4)
        (NormalizedMoments.firstSignalIncrement F 0
          (NormalizedMoments.secondSignalIncrement (fun i σ a b => W[i - 1]?.getD 0 σ a b)
            (HP.η / 4))) (fun _ _ _ _ => 0) 1 0 x y) ≤
      5 * (|HP.η / 4| * (Lh + Lρ) / rate 0) ^ 4 * (8 *
        (((2 : ℝ) ^ (-(data HP).requestPrecision 2
          {request HP with usage := (request HP).terminal}) * (64 / 63) *
            (1 / 64 : ℝ) ^ Cslib.RowCompression.dyadicSlack (Nat.log2 2 + 1) 0) ^ 4 +
          rowNormPow 4 5 (rate 0) Xs Ya
            (fun _ => (data HP).initialPolynomialLoss 2 1 0 (request HP)))) := by
  obtain ⟨Lh, Lρ, hLh, hLρ, hh, hρ⟩ := NormalizedMoments.preparation_stability_constants HP
  refine ⟨Lh, Lρ, hLh, hLρ, ?_⟩
  have hC (x y : ZMod 5) : 0 ≤ (data HP).base x y := by
    simp only [data, base, Matrix.one_apply]
    split_ifs <;> norm_num
  exact BudgetData.initialSecondSignal_mean_moment (data HP) 2 (by decide) 1
    (by ext i; simp only [data, mem_insert, mem_singleton, mem_range]; omega)
    rfl rfl rfl (by norm_num [data])
    (⟨1, 4, by decide, by decide⟩ : Horizon 5) (by decide)
    (request HP) threeRoles 0 0 [1] [2, 3] rfl rfl (by decide) hC
    (by simp [data, base]) _ (prefixes HP) 0 (by decide) 0 0 le_rfl rfl
    _ (preparation_walks HP) hLh hLρ hh hρ (HP.η / 4)

-- The actual compressedBin raw-prefix consumer combines both envelopes before any
-- second-noise payment. Here both centered noises vanish, while the early bias survives.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Lh Lρ : ℝ, 0 ≤ Lh ∧ 0 ≤ Lρ ∧ ∀ (σ : Environment 5 3) (x : ZMod 5),
    let F := fun i (_ : Environment 5 3) => if 2 ≤ i then base else 0
    let W : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) := [0, fun _ => base]
    let Δ := NormalizedMoments.firstSignalIncrement F 0
      (NormalizedMoments.secondSignalIncrement (fun i τ a b => W[i - 1]?.getD 0 τ a b)
        (HP.η / 4))
    let truth := requestSignals (HP.η / 4) (data HP).padding id (request HP) (fun _ => base)
      ((data HP).binPreparation 0 (request HP) (fun _ => base))
    Cslib.RowCompression.clippedError (truth σ x x 0) (truth σ x x 1)
      (Cslib.RowCompression.uncompressedRow (Δ σ x) 0 1 x) ≤
      (data HP).initialMeanCharge 2 1 0 0 (request HP) +
        NormalizedMoments.secondMeanEnvelope threeRoles 1 [1] [2, 3]
          0 0 0 Lh Lρ (HP.η / 4) (fun _ => 0) base x x := by
  obtain ⟨Lh, Lρ, hLh, hLρ, hh, hρ⟩ := NormalizedMoments.preparation_stability_constants HP
  refine ⟨Lh, Lρ, hLh, hLρ, ?_⟩
  intro σ x
  have hC (a b : ZMod 5) : 0 ≤ (data HP).base a b := by
    simp only [data, base, Matrix.one_apply]
    split_ifs <;> norm_num
  have hp := BudgetData.initial_requestSignals_two_envelopes (data HP) 2 (by decide) 1
    (by ext i; simp only [data, mem_insert, mem_singleton, mem_range]; omega)
    rfl rfl rfl (by norm_num [data])
    (⟨1, 4, by decide, by decide⟩ : Horizon 5) (by decide)
    (request HP) threeRoles 0 0 [1] [2, 3] rfl rfl (by decide) hC
    (by simp [data, base]) _ (prefixes HP) 0 (by decide) 0 0 rfl
    _ (preparation_walks HP) hLρ hh hρ (HP.η / 4) σ x x
  have hret (τ : Environment 5 3) (role : Fin 3) (su : List (ZMod 5)) (v : ZMod 5) :
      NormalizedMoments.retainedMask role (side 5 0) 1 su τ v := by
    simpa only [NormalizedMoments.retainedMask, gridChannel,
      CorrectionRowTask.Channel.retains, channels, semanticSide_grid] using full τ role su v
  dsimp only at hp ⊢
  simpa only [data, threeRoles, NormalizedMoments.actualNoiseEntry, Pi.zero_def,
    Nat.zero_add, Nat.reduceSub, show ¬ 2 ≤ 1 by decide, Matrix.zero_apply, mul_zero,
    expect_const_zero,
    NormalizedMoments.twoMaskMean, Fin.isValue, ↓reduceIte, one_ne_zero,
    NormalizedMoments.actualPrefix_twoSignal_first,
    NormalizedMoments.actualPrefix_twoSignal_second, Nat.add_sub_cancel,
    List.getElem?_cons_zero, Option.getD_some, Pi.zero_apply, zero_mul,
    rowSliceMean, hret, and_self, filter_true, expect_const, sub_self, abs_zero,
    zero_div, add_zero] using hp

-- The real successful compressed output supplies its own histories and paid second noise.
-- This positive stationary case still has early deterministic preparation bias.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).compressedBin 2 0 0 (HP.η / 4) (HP.η / 4) (request HP) =
      some (fun _ => base) ∧
    ∃ F W,
      (data HP).initialPrefixes 2 (request HP) = some F ∧
      (List.range (Nat.log2 2 + 1)).mapM (fun i =>
        (data HP).complete 2 (request HP) ((data HP).binPreparation 0 (request HP) (F (i + 1)))
          (Cslib.RowCompression.dyadicSlack (Nat.log2 2 + 1) i)) = some W ∧
      ∀ j < Nat.log2 2 + 1,
        rowNormPow 4 5 (rate 0) (NormalizedMoments.retainedMask 0 (side 5 0) 1 [1])
          (NormalizedMoments.retainedMask 2 (side 5 0) 1 [2, 3])
          (NormalizedMoments.actualNoiseEntry 0 2 (side 5 0) (side 5 0) (side 5 0)
            1 [1] [2, 3] 0 base (NormalizedMoments.firstSignalIncrement F 0
              (NormalizedMoments.secondSignalIncrement
                (fun i σ x y => W[i - 1]?.getD 0 σ x y) (HP.η / 4)))
            (fun _ _ _ _ => 0) 1 j) ≤
          (|HP.η / 4| * (2 : ℝ) ^ (-(data HP).requestPrecision 2 (request HP)) *
            (1 / 64 : ℝ) ^ Cslib.RowCompression.dyadicSlack (Nat.log2 2 + 1) j) ^ 4 := by
  refine ⟨compressed_value HP, ?_⟩
  exact BudgetData.compressedBin_secondNoise (data HP) 2 0 0
    (fun d => ⟨polynomialPrepCutoff4_nonneg _ _, polynomialPrepCutoff4_le_one _ _⟩)
    (HP.η / 4) (HP.η / 4) (request HP) threeRoles 0 0 [1] [2, 3] rfl rfl
    (fun _ => base) (compressed_value HP)

-- Zero second scaling keeps every executed second prefix zero despite positive preparation.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let F := fun i (_ : Environment 5 3) => if 2 ≤ i then base else 0
    let W : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) := [0, fun _ => base]
    (List.range (Nat.log2 2 + 1)).mapM (fun i =>
      (data HP).complete 2 (request HP) ((data HP).binPreparation 0 (request HP) (F (i + 1)))
        (Cslib.RowCompression.dyadicSlack (Nat.log2 2 + 1) i)) = some W ∧
    W[1]?.getD 0 = (fun _ => base) ∧ ∀ j (σ : Environment 5 3) (x y : ZMod 5),
      NormalizedMoments.actualPrefix (NormalizedMoments.firstSignalIncrement F 0
        (NormalizedMoments.secondSignalIncrement
          (fun i τ a b => W[i - 1]?.getD 0 τ a b) 0)) (fun _ _ _ _ => 0) j σ x y 1 = 0 := by
  dsimp only
  refine ⟨preparation_walks HP, rfl, ?_⟩
  intro j σ x y
  rw [NormalizedMoments.actualPrefix_twoSignal_second, zero_mul]

-- Nonconstant supplied first histories exercise the actual allocated preparation walk.
-- This is a mixing bound for that completed input, not a new evaluator induction fixture.
private def varyingHistory (_ : ℕ) (σ : Environment 5 3) : Matrix (ZMod 5) (ZMod 5) ℝ :=
  if (σ 1).1 0 = 0 then base else 0

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ W : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ),
      (List.range (Nat.log2 2 + 1)).mapM (fun i =>
        (data HP).complete 2 (request HP)
          ((data HP).binPreparation 0 (request HP) (varyingHistory (i + 1)))
          (Cslib.RowCompression.dyadicSlack (Nat.log2 2 + 1) i)) = some W ∧
      (∃ σ τ : Environment 5 3,
        (data HP).binPreparation 0 (request HP) (varyingHistory 1) σ 0 0 = 1 ∧
        (data HP).binPreparation 0 (request HP) (varyingHistory 1) τ 0 0 = 0) ∧
      rowNormPow 4 5 (rate 0) (NormalizedMoments.retainedMask 0 (side 5 0) 1 [1])
        (NormalizedMoments.retainedMask 2 (side 5 0) 1 [2, 3])
        (NormalizedMoments.actualNoiseEntry 0 2 (side 5 0) (side 5 0) (side 5 0)
          1 [1] [2, 3] 0 base (NormalizedMoments.firstSignalIncrement varyingHistory 0
            (NormalizedMoments.secondSignalIncrement
              (fun i σ x y => W[i - 1]?.getD 0 σ x y) (-3)))
          (fun _ _ _ _ => 0) 1 0) ≤
        (3 * (2 : ℝ) ^ (-(data HP).requestPrecision 2 (request HP)) *
          (1 / 64 : ℝ) ^ Cslib.RowCompression.dyadicSlack (Nat.log2 2 + 1) 0) ^ 4 := by
  have hc (i : ℕ) := BudgetData.complete_grid (data HP) 2 (request HP) 0 2
    (by decide) 0 0 [1] [2, 3] rfl rfl
    ((data HP).binPreparation 0 (request HP) (varyingHistory (i + 1)))
    (Cslib.RowCompression.dyadicSlack (Nat.log2 2 + 1) i)
  let W := (List.range (Nat.log2 2 + 1)).map fun i => conditionalWalk
    (X (0 : Fin 3) (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [1]))
    (Y (2 : Fin 3) (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [2, 3]))
    (graph (0 : Fin 3) 2 (by decide) (side 5 0) (side 5 0) (side_le 5 0) (side_le 5 0)
      (CopyPadding.identifier (1 : ZMod 5) [1]) (CopyPadding.identifier (1 : ZMod 5) [2, 3]))
    (fun _ _ => (data HP).steps 2 (request HP)
      (Cslib.RowCompression.dyadicSlack (Nat.log2 2 + 1) i))
    ((data HP).binPreparation 0 (request HP) (varyingHistory (i + 1)))
  have hW : (List.range (Nat.log2 2 + 1)).mapM (fun i =>
      (data HP).complete 2 (request HP)
        ((data HP).binPreparation 0 (request HP) (varyingHistory (i + 1)))
        (Cslib.RowCompression.dyadicSlack (Nat.log2 2 + 1) i)) = some W := by
    simp_rw [hc]
    exact List.mapM_pure
  refine ⟨W, hW, ?_, ?_⟩
  · let f : Frame 5 4 1 := Classical.choice inferInstance
    let σ : Environment 5 3 := fun _ => (0, f)
    let τ : Environment 5 3 := fun _ => (1, f)
    refine ⟨σ, τ, ?_, ?_⟩
    · change densePreparation (data HP).padding id (request HP) ((data HP).auxiliary 0)
        HP.ρ HP.K (varyingHistory 1 σ) σ 0 0 = 1
      have hp := congrFun (congrFun (congrFun (preparation HP base (Or.inr rfl)) σ) 0) 0
      simpa [BudgetData.binPreparation, varyingHistory, σ, base] using hp
    · change densePreparation (data HP).padding id (request HP) ((data HP).auxiliary 0)
        HP.ρ HP.K (varyingHistory 1 τ) τ 0 0 = 0
      have hp := congrFun (congrFun (congrFun (preparation HP 0 (Or.inl rfl)) τ) 0) 0
      simpa [BudgetData.binPreparation, varyingHistory, τ] using hp
  · have hn := BudgetData.initialSecondSignal_noise_moment (data HP) 2 0
      (fun d => ⟨polynomialPrepCutoff4_nonneg _ _, polynomialPrepCutoff4_le_one _ _⟩)
      (request HP) threeRoles 0 0 [1] [2, 3] rfl rfl varyingHistory W hW
      0 base (-3) 0 (by decide)
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at hn
    exact hn


-- This consumer supplies actual successful executions, and no clipped-error or final
-- budget premise. The small-floor restriction is exactly the decoder scale requirement.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (hscale : HP.η ≤ max (1 : ℝ) 16 / 10000) :
    ∃ C Cpre : ℝ, 0 ≤ C ∧ 0 ≤ Cpre ∧
      let m := Nat.log2 2 + 1
      let n := compatibleCapacity HP.K m
      let X := fun σ x => (request HP).source.retains (channels (data HP).padding) σ x
      let Y := fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y
      let F := fun j (_ : Environment 5 3) => if 2 ≤ j then base else 0
      let W : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) := [0, fun _ => base]
      let Δ := firstSignalIncrement F 0
        (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) (HP.η / 4))
      let raw : Environment 5 3 → ZMod 5 → ZMod 5 → Fin 2 → ℝ := 0
      let truth := requestSignals (HP.η / 4) (data HP).padding id (request HP) (fun _ => base)
        ((data HP).binPreparation 0 (request HP) (fun _ => base))
      let ε := actualFourMax HP threeRoles.source threeRoles.terminal
        (side 5 0) (side 5 0) (side 5 0)
        (data HP).padding [1] [2, 3] 0 base (HP.η / 4) Δ raw
      let εfinal := ε (Nat.log2 2)
        let S := fun σ => ({y | Y σ y} : Finset (ZMod 5))
        let Pre := fun σ x => ∑ i ∈ range m, dyadicFloor (HP.η / 4) m i * ε i σ x
        let No := fun σ x => if ∀ i < m,
          stepThreshold (S σ) n (fun _ => HP.K) (dyadicFloor (HP.η / 4) m) (Δ σ x) ⟨0, raw σ x⟩ i ≤
            dyadicFloor (HP.η / 4) m i then εfinal σ x else 0
        let Tail := fun σ x => ∑ j ∈ range m,
          if IsFirstOverflow (S σ) n (fun _ => HP.K) (dyadicFloor (HP.η / 4) m)
              (Δ σ x) ⟨0, raw σ x⟩ j ∧
            heavyCountEvent Y univ (fun y => truth σ x y 0)
              (dyadicFloor (HP.η / 4) m j) (n j) σ then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x else 0
        rootDistPow 4 5 (request HP).source.rate X Y (fun _ => base)
          (denseChild (data HP).padding id (request HP) ((data HP).cutoff 0)
            (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K base) ≤
          128 * (HP.K : ℝ) * (Cpre ^ 4 * vertexNormPow 4 5 (request HP).source.rate X Pre +
            C ^ 4 * vertexNormPow 4 5 (request HP).source.rate X No +
            C ^ 4 * vertexNormPow 4 5 (request HP).source.rate X Tail) +
          ∑ j ∈ range m, (64 * (HP.K : ℝ) * ((2 * max 1 16) ^ (4⁻¹ : ℝ)) ^ 4 / ((n j : ℝ) *
            dyadicFloor (HP.η / 4) m j ^ 4)) *
            rowNormPow 4 5 (request HP).source.rate X Y (fun σ x y =>
              clippedError (truth σ x y 0) (truth σ x y 1)
              (uncompressedRow (Δ σ x) (raw σ x) (j + 1) y)) := by
  have hζ : 0 < HP.η / 4 := by linarith [HP.η_pos]
  obtain ⟨C, hC, hfloor⟩ := BudgetData.exists_compressedBin_fourMax HP
    (by norm_num : (0 : ℝ) ≤ 1) hζ HP.η_pos le_rfl hscale (by linarith)
  have hf1 : HP.η / 4 ≤ 1 := by norm_num at hscale; linarith
  obtain ⟨Cp, hCp, hbound⟩ := hfloor (HP.η / 4) hζ (by linarith) hf1
  refine ⟨C, Cp, hC, hCp, ?_⟩
  have hr : Admissible (request HP) := ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩
  exact hbound (data HP) rate rate_pos (fun i => by
    simp only [rate, pow_succ, _root_.mul_inv_rev]; ring) 2 0 0 (request HP) hr rfl rfl rfl
    base (by intro x y; by_cases h : x = y <;> simp [base, Matrix.one_apply, h]) _ (prefixes HP) _
    (preparation_walks HP) _ (compressed_value HP) threeRoles 0 0 [1] [2, 3] rfl rfl rfl

-- Zero zeta kills the actual usage signal; the positive early first-mean error remains
-- in the concrete Minkowski budget instead of being assumed away.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let F := fun j (_ : Environment 5 3) => if 2 ≤ j then base else 0
    let W : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) := [0, fun _ => base]
    let Δ := firstSignalIncrement F 0
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) 0)
    let X := retainedMask (0 : Fin 3) (side 5 0) (1 : ZMod 5) [1]
    let a := fun ν => vertexNormPow 4 5 (request HP).source.rate X
      (actualMeanMax HP 0 2 (side 5 0) (side 5 0) (side 5 0) 1 [1] [2, 3]
        0 base 0 Δ 0 ν 0) ^ (4⁻¹ : ℝ)
    vertexNormPow 4 5 (request HP).source.rate X
      (actualFourMax HP 0 2 (side 5 0) (side 5 0) (side 5 0) 1 [1] [2, 3]
        0 base 0 Δ 0 0) ≤
      ((a 0 + a 1) +
        ((2 : ℝ) ^ (-(data HP).requestPrecision 2
          {(request HP) with usage := (request HP).terminal}) * (64 / 63) / rate 0) *
          (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 2 + 1) 0) ^ 4 := by
  have h := BudgetData.initialFourMax_moment (data HP) 2 0 0 (by decide)
    (by simp [data])
    (fun d => ⟨polynomialPrepCutoff4_nonneg _ _, polynomialPrepCutoff4_le_one _ _⟩)
    (request HP) threeRoles 0 0 [1] [2, 3] rfl rfl rfl _ (prefixes HP) _
    (preparation_walks HP) base
    (by intro x y; by_cases h : x = y <;> simp [base, Matrix.one_apply, h]) 0 0
    (by decide)
  simpa only [threeRoles, data, Nat.cast_ofNat, abs_zero, zero_mul, add_zero] using h


-- The paid inequality consumes the genuine successful budget-2 history. Its RHS has
-- canonical charges/Jensen deficits and a selected deterministic tail, with no supplied
-- clipped-error moment or output budget. The positive early deficit is retained.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (hscale : HP.η ≤ max (1 : ℝ) 16 / 10000) :
    ∃ C Cp Lh Lρ : ℝ, 0 ≤ C ∧ 0 ≤ Cp ∧ 0 ≤ Lh ∧ 0 ≤ Lρ ∧
      let F := fun j (_ : Environment 5 3) => if 2 ≤ j then base else 0
      let W : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) := [0, fun _ => base]
      let m := Nat.log2 2 + 1
      let X := retainedMask threeRoles.source (side 5 0) (data HP).padding [1]
      let Ya := retainedMask threeRoles.terminal (side 5 0) (data HP).padding [2, 3]
      let Δ := firstSignalIncrement F 0
        (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) (HP.η / 4))
      let q := fun i => (data HP).initialMeanCharge 2 1 i 0 (request HP)
      let e₀ := (2 : ℝ) ^ (-(data HP).requestPrecision 2
          {(request HP) with usage := (request HP).terminal}) *
        (64 / 63) / rate 0
      let e₁ := |(HP.η / 4)| * (2 : ℝ) ^ (-(data HP).requestPrecision 2 (request HP))
      let deficit := fun i => rowNormPow 4 5 (rate 0) X Ya
        (fun _ => (data HP).initialPolynomialLoss 2 1 i (request HP))
      let prep := fun i => (5 : ℝ) * (|(HP.η / 4)| * (Lh + Lρ) / rate 0) ^ 4 *
        (8 * ((e₀ * rate 0 * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4 + deficit i))
      let a := fun i => (vertexNormPow 4 5 (rate 0) X (fun _ _ => q i)) ^ (4⁻¹ : ℝ) +
        (prep i) ^ (4⁻¹ : ℝ)
      let meanTail := fun σ x => ∑ j ∈ range m,
        if meanFirstEvent threeRoles.terminal (data HP).padding [2, 3] 0 m j (HP.η / 4) base
            (compatibleCapacity HP.K m) (fun _ => HP.K) Δ 0 σ x then
          meanRowTail threeRoles.terminal (side 5 0) (data HP).padding [2, 3] m j
            (actualClippedMean HP threeRoles.source threeRoles.terminal
              (side 5 0) (side 5 0) (side 5 0)
              (data HP).padding [1] [2, 3] 0 base (HP.η / 4) Δ 0 0) σ x +
          meanRowTail threeRoles.terminal (side 5 0) (data HP).padding [2, 3] m j
            (actualClippedMean HP threeRoles.source threeRoles.terminal
              (side 5 0) (side 5 0) (side 5 0)
              (data HP).padding [1] [2, 3] 0 base (HP.η / 4) Δ 0 1) σ x
        else 0
      let radius := (2 * max (1 : ℝ) 16) ^ (4⁻¹ : ℝ)
      let w := fun i => 64 * (HP.K : ℝ) * radius ^ 4 /
        ((compatibleCapacity HP.K m i : ℝ) * dyadicFloor (HP.η / 4) m i ^ 4)
      let c := 64 * (HP.K : ℝ) * radius ^ 4 / (HP.η / 4) ^ 4
      rootDistPow 4 5 (rate 0) X Ya (fun _ => base)
        (denseChild (data HP).padding id (request HP) ((data HP).cutoff 0)
          (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K base) ≤
        128 * (HP.K : ℝ) *
          (Cp ^ 4 * ((∑ i ∈ range m, dyadicFloor (HP.η / 4) m i * a i) +
            (HP.η / 4) * (e₀ + e₁) / 511) ^ 4 +
          C ^ 4 * (a (Nat.log2 2) + (e₀ + e₁) / 64) ^ 4 +
          C ^ 4 * (vertexNormPow 4 5 (rate 0) X meanTail ^ (4⁻¹ : ℝ) +
            (e₀ + e₁) * (7 / 9)) ^ 4) +
        64 * ((∑ i ∈ range m, w i *
          (rowNormPow 4 5 (rate 0) X Ya (fun _ _ _ => q i) + prep i)) +
          (c * e₀ ^ 4 / 63 + c * e₁ ^ 4 / 63)) := by
  have hζ : 0 < HP.η / 4 := by linarith [HP.η_pos]
  obtain ⟨C, hC, hfloor⟩ := BudgetData.exists_compressedBin_paid HP
    hζ HP.η_pos le_rfl hscale (by linarith)
  have hf1 : HP.η / 4 ≤ 1 := by norm_num at hscale; linarith
  obtain ⟨Cp, hCp, hbound⟩ := hfloor (HP.η / 4) hζ (by linarith) hf1
  obtain ⟨Lh, Lρ, hLh, hLρ, hh, hρ⟩ := preparation_stability_constants HP
  refine ⟨C, Cp, Lh, Lρ, hC, hCp, hLh, hLρ, ?_⟩
  have hr : Admissible (request HP) := ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩
  exact hbound (data HP) 2 1 (by decide)
    (by ext i; simp only [data, mem_insert, mem_singleton, mem_range]; omega)
    rfl rfl rfl (by norm_num [data])
    (⟨1, 4, by decide, by decide⟩ : Horizon 5) (by decide)
    (request HP) hr threeRoles 0 0 0 [1] [2, 3] rfl rfl rfl (by decide) (by decide)
    (by intro x y; by_cases h : x = y <;> simp [data, base, h])
    (by simp [data, base]) 0 _ (prefixes HP) _ (preparation_walks HP) _ (compressed_value HP)
    Lh Lρ hLh hLρ hh hρ

-- Both deterministic actual-history means now receive scheduled heavy rarity, while
-- all three noise payments retain their unconditional constants. Rank is in the horizon.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (hscale : HP.η ≤ max (1 : ℝ) 16 / 10000) :
    ∃ C Cp Lh Lρ : ℝ, 0 ≤ C ∧ 0 ≤ Cp ∧ 0 ≤ Lh ∧ 0 ≤ Lρ ∧
      let m := Nat.log2 2 + 1
      let X := retainedMask threeRoles.source (side 5 0) (data HP).padding [1]
      let Ya := retainedMask threeRoles.terminal (side 5 0) (data HP).padding [2, 3]
      let q := fun i => (data HP).initialMeanCharge 2 1 i 0 (request HP)
      let e₀ := (2 : ℝ) ^ (-(data HP).requestPrecision 2
          {(request HP) with usage := (request HP).terminal}) *
        (64 / 63) / rate 0
      let e₁ := |(HP.η / 4)| * (2 : ℝ) ^ (-(data HP).requestPrecision 2 (request HP))
      let deficit := fun i => rowNormPow 4 5 (rate 0) X Ya
        (fun _ _ _ => rate 1 + (data HP).initialInactiveCharge 2 i (request HP))
      let prep := fun i => (5 : ℝ) * (|(HP.η / 4)| * (Lh + Lρ) / rate 0) ^ 4 *
        (8 * ((e₀ * rate 0 * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4 + deficit i))
      let a := fun i => (vertexNormPow 4 5 (rate 0) X (fun _ _ => q i)) ^ (4⁻¹ : ℝ) +
        (prep i) ^ (4⁻¹ : ℝ)
      let rarity := fun j => ((2 + 256 / dyadicFloor (HP.η / 4) m j) /
        (compatibleCapacity HP.K m j : ℝ)) ^ (4⁻¹ : ℝ)
      let tail := ∑ j ∈ range m, rarity j * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) *
        ((rowNormPow 4 5 (rate 0) X Ya (fun _ _ _ => q i)) ^ (4⁻¹ : ℝ) +
          (prep i) ^ (4⁻¹ : ℝ))
      let radius := (2 * max (1 : ℝ) 16) ^ (4⁻¹ : ℝ)
      let w := fun i => 64 * (HP.K : ℝ) * radius ^ 4 /
        ((compatibleCapacity HP.K m i : ℝ) * dyadicFloor (HP.η / 4) m i ^ 4)
      let c := 64 * (HP.K : ℝ) * radius ^ 4 / (HP.η / 4) ^ 4
      rootDistPow 4 5 (rate 0) X Ya (fun _ => base)
        (denseChild (data HP).padding id (request HP) ((data HP).cutoff 0)
          (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K base) ≤
        128 * (HP.K : ℝ) *
          (Cp ^ 4 * ((∑ i ∈ range m, dyadicFloor (HP.η / 4) m i * a i) +
            (HP.η / 4) * (e₀ + e₁) / 511) ^ 4 +
          C ^ 4 * (a (Nat.log2 2) + (e₀ + e₁) / 64) ^ 4 +
          C ^ 4 * (tail +
            (e₀ + e₁) * (7 / 9)) ^ 4) +
        64 * ((∑ i ∈ range m, w i *
          (rowNormPow 4 5 (rate 0) X Ya (fun _ _ _ => q i) + prep i)) +
          (c * e₀ ^ 4 / 63 + c * e₁ ^ 4 / 63)) := by
  have hζ : 0 < HP.η / 4 := by linarith [HP.η_pos]
  obtain ⟨C, hC, hfloor⟩ := BudgetData.exists_compressedBin_allocated HP
    hζ HP.η_pos le_rfl hscale (by linarith)
  have hf1 : HP.η / 4 ≤ 1 := by norm_num at hscale; linarith
  obtain ⟨Cp, hCp, hbound⟩ := hfloor (HP.η / 4) hζ (by linarith) hf1
  obtain ⟨Lh, Lρ, hLh, hLρ, hh, hρ⟩ := preparation_stability_constants HP
  refine ⟨C, Cp, Lh, Lρ, hC, hCp, hLh, hLρ, ?_⟩
  have hr : Admissible (request HP) := ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩
  exact hbound (data HP) 2 1 (by decide)
    (by ext i; simp only [data, mem_insert, mem_singleton, mem_range]; omega)
    rfl rfl rfl (by norm_num [data])
    (⟨1, 4, by decide, by decide⟩ : Horizon 5) (by decide)
    (request HP) hr threeRoles 0 0 0 [1] [2, 3] rfl rfl rfl (by decide) (by decide) (by decide)
    (by intro x y; by_cases h : x = y <;> simp [data, base, h])
    (by simp [data, base]) 0 _ (prefixes HP) _ (preparation_walks HP) _ (compressed_value HP)
    Lh Lρ hLh hLρ hh hρ

-- The actual early deficit is positive; the new pointwise payment cannot erase it.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (x : ZMod 5) :
    0 < (data HP).initialPolynomialLoss 2 1 0 (request HP) x x ∧
      (data HP).initialPolynomialLoss 2 1 1 (request HP) x x = 0 := by
  norm_num [BudgetData.initialPolynomialLoss, BudgetData.initialFineLoss,
    BudgetData.initialCoarseLoss, BudgetData.sampleScale, data, request, gridChannel,
    rate, base, numerator, boundedRoutedBinCutoff, routedBinCutoff, binWeight,
    polynomialSwitch4, polynomialTransition4, transitionPolynomial4,
    Cslib.RowCompression.dyadicSlack, LogSpaceEstimation.lastBudget,
    LogSpaceEstimation.scaleCutoff]

-- With sufficient budget the envelope has one explicit inactive group and positive
-- omitted-coverage charge at every later group; at the small edge budget it need not.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (i : ℕ) :
    (data HP).initialMeanCharge 8 1 i 0 (request HP) ≤
      1 / 16 + if i = 0 then 17 else 0 := by
  have hb := BudgetData.initialMeanCharge_le_schedule (data HP) 8 1 i 0 (by decide)
    (request HP) (fun bin => (rate_pos bin).le) (scale_cutoffs HP)
  norm_num [data, rate] at hb ⊢
  exact hb

-- A concrete sufficient-budget history retains the early group coefficient v(0)*28^4;
-- its inactive charge is not multiplied by the weights of all four groups.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (v : ℕ → ℝ)
    (hv : ∀ j, 0 ≤ v j) :
    (∑ j ∈ range 4, v j * ∑ i ∈ Ico j 4, (28 : ℝ) ^ (4 - i) *
      (data HP).initialMeanCharge 8 1 i 0 (request HP)) ≤
      1 / 16 * (∑ j ∈ range 4, v j * ∑ i ∈ Ico j 4, (28 : ℝ) ^ (4 - i)) +
        v 0 * 28 ^ 4 * 17 := by
  have hb := BudgetData.initialMeanCharge_tail_schedule (data HP) 8 1 0 (by decide)
    (request HP) (fun bin => (rate_pos bin).le) (scale_cutoffs HP) v hv
  norm_num [data, rate] at hb ⊢
  exact hb

-- Full-rank fourth moments see the actual early identity deficit and exact final zero.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let X := NormalizedMoments.retainedMask (0 : Fin 3) (side 5 0) (1 : ZMod 5) [1]
    let Y := NormalizedMoments.retainedMask (2 : Fin 3) (side 5 0) (1 : ZMod 5) [2, 3]
    rowNormPow 4 5 (rate 0) X Y
      (fun _ => (data HP).initialPolynomialLoss 2 1 0 (request HP)) = 1 ∧
    rowNormPow 4 5 (rate 0) X Y
      (fun _ => (data HP).initialPolynomialLoss 2 1 1 (request HP)) = 0 := by
  dsimp only
  have hret (τ : Environment 5 3) (role : Fin 3) (su : List (ZMod 5)) (v : ZMod 5) :
      NormalizedMoments.retainedMask role (side 5 0) 1 su τ v := by
    simpa only [NormalizedMoments.retainedMask, gridChannel,
      CorrectionRowTask.Channel.retains, channels, semanticSide_grid] using full τ role su v
  have he (j : ℕ) (hj : j < 2) (x y : ZMod 5) :
      (data HP).initialPolynomialLoss 2 1 j (request HP) x y =
        if j = 0 then base x y else 0 := by
    interval_cases j <;> by_cases hxy : x = y <;>
      norm_num [BudgetData.initialPolynomialLoss, BudgetData.initialFineLoss,
        BudgetData.initialCoarseLoss, BudgetData.sampleScale, data, request, gridChannel,
        rate, base, Matrix.one_apply, numerator, boundedRoutedBinCutoff, routedBinCutoff, binWeight,
        polynomialSwitch4, polynomialTransition4, transitionPolynomial4,
        Cslib.RowCompression.dyadicSlack, LogSpaceEstimation.lastBudget,
        LogSpaceEstimation.scaleCutoff, hxy]
  simp [he 0 (by decide), he 1 (by decide), rowNormPow, hret, base,
    Matrix.one_apply, rate, apply_ite]

-- The slow linear depth has nonvacuous budget/precision guards on the original data.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (∀ bin ≤ 1, LogSpaceEstimation.scaleCutoff (data HP).slack
      ((data HP).sampleScale (request HP) (some bin)) < 128) ∧
    2 ≤ (data HP).requestPrecision 128 (request HP) := by
  have hg := BudgetData.slow_depth_guards (data HP) 128 (request HP) 0 0 rfl rfl rfl
    (by norm_num [data]) (by norm_num [data]) (by norm_num [data]) (by norm_num [data])
  norm_num only [data, Nat.reduceMul, Nat.reduceDiv, Nat.cast_one, mul_one] at hg
  exact hg

-- The negative scale is literal: this checks the natAbs cost, not a signed cutoff.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).sampleScale
      { (request HP) with terminal := gridChannel 2 1 [2, 3] } (some 3) = -8 := by
  rw [BudgetData.sampleScale_grid (data HP) _ 1 3 rfl rfl]
  norm_num

-- Letting terminal rank grow as fast as retained depth does not shrink this envelope.
-- This is an obstruction to using the charge alone, not to actual estimator accuracy.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).initialMeanCharge 8 1 1 1
      { (request HP) with terminal := gridChannel 2 1 [2, 3] } = 1 := by
  have hlog : Real.logb 2 (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.logb_pow]
    norm_num
  norm_num [BudgetData.initialMeanCharge, BudgetData.initialInactiveCharge,
    BudgetData.sampleScale, LogSpaceEstimation.scaleCutoff, data, request, gridChannel,
    rate, Cslib.RowCompression.dyadicSlack, Real.logb_inv, hlog]

-- A finite bounded prime and horizon exist together, including the largest identifier.
example : ∃ P, P.Prime ∧ 8 < P ∧ P ≤ 16 ∧
    ∃ H : Horizon P, H.maxExponent = 3 ∧ H.maxIdentifier = 7 := by
  exact exists_bounded_depth_prime 3 7 (by decide)

-- The chosen prime 13 pays two width factors against the actual omitted fourth moment.
example : (13 : ℝ) ^ 2 * rate 3 ^ 4 ≤ 4 * (1 / 16384 : ℝ) ^ 3 :=
  bounded_width_omission 13 3 (by decide)

private lemma available8 (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ F W A, (data HP).initialPrefixes 8 (request HP) = some F ∧
      (List.range 4).mapM (fun i => (data HP).complete 8 (request HP)
        ((data HP).binPreparation 0 (request HP) (F (i + 1)))
        (Cslib.RowCompression.dyadicSlack 4 i)) = some W ∧
      (data HP).compressedBin 8 0 0 (HP.η / 4) (HP.η / 4) (request HP) = some A := by
  obtain ⟨F, hF⟩ : ∃ F, (data HP).initialPrefixes 8 (request HP) = some F :=
    ⟨_, (BudgetData.initialPrefixes_grid (data HP) 8 (by decide) (by simp [data])
      (request HP) 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl).1⟩
  have hw (i : ℕ) : ∃ A, (data HP).complete 8 (request HP)
      ((data HP).binPreparation 0 (request HP) (F (i + 1)))
      (Cslib.RowCompression.dyadicSlack 4 i) = some A :=
    ⟨_, BudgetData.complete_grid (data HP) 8 (request HP) 0 2 (by decide) 0 0
      [1] [2, 3] rfl rfl _ _⟩
  choose walks hwalk using hw
  have hW : (List.range 4).mapM (fun i => (data HP).complete 8 (request HP)
      ((data HP).binPreparation 0 (request HP) (F (i + 1)))
      (Cslib.RowCompression.dyadicSlack 4 i)) = some ((List.range 4).map walks) := by
    simp_rw [hwalk]
    exact List.mapM_pure
  suffices hav : ∃ A, (data HP).compressedBin 8 0 0 (HP.η / 4) (HP.η / 4)
      (request HP) = some A by
    obtain ⟨A, hA⟩ := hav
    exact ⟨F, (List.range 4).map walks, A, hF, hW, hA⟩
  unfold BudgetData.compressedBin
  simp only [BudgetData.decodePrefixes]
  have hactive : 0 < (data HP).requestPrecision 8 (request HP) := by
    norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision, data,
      request, gridChannel, rate]
  rw [ite_eq_right (by simp only [hactive, not_true_eq_false]; norm_num [request, gridChannel])]
  simp only [hF, bind, Option.bind_some]
  norm_num only [show Nat.log2 8 + 1 = 4 by decide]
  rw [hW]
  exact ⟨_, rfl⟩

-- A successful budget-8 execution consumes the new full output theorem. This checks
-- availability and the literal quantitative bound; it is still a stationary fixture.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (hscale : HP.η ≤ max (1 : ℝ) 16 / 10000) :
    ∃ A C Cp Lh Lρ, (data HP).compressedBin 8 0 0 (HP.η / 4) (HP.η / 4)
      (request HP) = some A ∧ 0 ≤ C ∧ 0 ≤ Cp ∧ 0 ≤ Lh ∧ 0 ≤ Lρ ∧
      rootDistPow 4 5 (rate 0)
        (retainedMask threeRoles.source (side 5 0) (data HP).padding [1])
        (retainedMask threeRoles.terminal (side 5 0) (data HP).padding [2, 3]) A
        (denseChild (data HP).padding id (request HP) ((data HP).cutoff 0)
          (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K (data HP).base) ≤
        (data HP).initialGeometricRHS 8 1 (request HP) threeRoles 0 0 [1] [2, 3]
          (HP.η / 4) (HP.η / 4) Lh Lρ C Cp := by
  obtain ⟨F, W, A, hF, hW, hA⟩ := available8 HP
  have hζ : 0 < HP.η / 4 := by linarith [HP.η_pos]
  obtain ⟨C, hC, hfloor⟩ := BudgetData.exists_compressedBin_geometric HP
    hζ HP.η_pos le_rfl hscale (by linarith)
  have hf1 : HP.η / 4 ≤ 1 := by norm_num at hscale; linarith
  obtain ⟨Cp, hCp, hbound⟩ := hfloor (HP.η / 4) hζ (by linarith) hf1
  obtain ⟨Lh, Lρ, hLh, hLρ, hh, hρ⟩ := preparation_stability_constants HP
  refine ⟨A, C, Cp, Lh, Lρ, hA, hC, hCp, hLh, hLρ, ?_⟩
  have hr : Admissible (request HP) := ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩
  exact hbound (data HP) 8 1 (by decide)
    (by ext i; simp only [data, mem_insert, mem_singleton, mem_range]; omega)
    rfl rfl rfl (by norm_num [data])
    (⟨1, 4, by decide, by decide⟩ : Horizon 5) (by decide)
    (request HP) hr threeRoles 0 0 0 [1] [2, 3] rfl rfl rfl (by decide) (by decide)
    (by decide) (by norm_num [data])
    (by intro x y; by_cases h : x = y <;> simp [data, base, h])
    (by simp [data, base]) 0 F hF W (by simpa using hW) A hA Lh Lρ hLh hLρ hh hρ

-- Both width factors are present and nonzero; p=2n is enough at this edge.
example : (13 : ℝ) ^ 2 * ((2 : ℝ) ^ (-(6 : ℝ))) ^ 4 ≤
    4 * (1 / 64 : ℝ) ^ 3 :=
  bounded_width_precision_sq 13 3 (by decide) (by norm_num)

example : (13 : ℝ) * ((2 : ℝ) ^ (-(6 : ℝ))) ^ 4 <
    (13 : ℝ) ^ 2 * ((2 : ℝ) ^ (-(6 : ℝ))) ^ 4 := by
  have hp : 0 < ((2 : ℝ) ^ (-(6 : ℝ))) ^ 4 := by positivity
  nlinarith

-- The raw exceptional weight pays a square width before its nonzero moment is attached.
open Cslib.RowCompression NormalizedMoments in
example : (64 * (2 : ℝ) * 1 ^ 4 /
    ((compatibleCapacity 2 4 0 : ℝ) * dyadicFloor (1 / 8) 4 0 ^ 4)) * (13 : ℝ) ^ 2 ≤
      (64 * (2 : ℝ) * 1 ^ 4 / (1 / 8) ^ 4) * 4 * (1 / 262144 : ℝ) ^ 3 := by
  exact compatible_first_false_width (by norm_num) 2 4 13 3 1 (by decide)
    (by norm_num [dyadicSlack])

-- Fixed nonzero usage exponent and identifiers can be carried into bounded-prime choice.
-- This consumes eventual guards and Bertrand together; it asserts no output accuracy.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ N : ℕ, ∀ n ≥ N, 2 ≤ n ∧
      2 * (n : ℝ) ≤ (data HP).requestPrecision (128 * n) (request HP) ∧
      ∃ P, P.Prime ∧ 2 ^ n < P ∧ P ≤ 2 ^ (n + 1) ∧
        ∃ H : Horizon P, H.maxExponent = n ∧ H.maxIdentifier = 4 := by
  obtain ⟨N, hN⟩ := BudgetData.fixed_request_depth_guards (data HP) (request HP)
    0 0 2 4 rfl rfl rfl
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨_, _, _, hku, hid, _, hp⟩ := hN n hn
  refine ⟨hku, ?_, exists_bounded_depth_prime n 4 hid⟩
  simpa only [data, mul_one] using hp

-- The full payment can be made small on a family of actual successful outputs. The prime
-- varies with depth; all structural constants, rates and the positive floor are fixed first.
private def uniformData (HP : FourthRootHierarchyParams 16 1 16 32 8) (P n : ℕ) :
    BudgetData HP P where
  padding := 1
  base := 1
  bins := range (n + 1)
  binRate := rate
  cutoff := (data HP).cutoff
  auxiliary := (data HP).auxiliary
  slack := 1
  slack_pos := by decide
  rankCharge := 0
  binCap := 16
  binCap_nonneg := by norm_num
  cutoff_bounds := (data HP).cutoff_bounds

private def uniformRequest (HP : FourthRootHierarchyParams 16 1 16 32 8) (P : ℕ) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
  ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 0 [1],
    gridChannel 2 0 [2, 3], gridChannel 2 2 [2, 3]⟩

open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (hscale : HP.η ≤ max (1 : ℝ) 16 / 10000) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ P, ∃ _ : Fact P.Prime,
      2 ^ n < P ∧ P ≤ 2 ^ (n + 1) ∧ ∃ A,
      (uniformData HP P n).compressedBin (128 * n) 0 0 (HP.η / 4) (HP.η / 4)
        (uniformRequest HP P) = some A ∧
      rootDistPow 4 P (rate 0)
        (retainedMask threeRoles.source (side P 0) (1 : ZMod P) [1])
        (retainedMask threeRoles.terminal (side P 0) (1 : ZMod P) [2, 3]) A
        (denseChild 1 id (uniformRequest HP P) ((uniformData HP P n).cutoff 0)
          (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K (uniformData HP P n).base) ≤ ε ∧
      (uniformData HP P n).evaluate (128 * n)
        {uniformRequest HP P with task := .baseNormalized 0 0} = some (.row
          (denseChild 1 id (uniformRequest HP P) ((uniformData HP P n).cutoff 0)
            (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K (uniformData HP P n).base)) := by
  have hζ : 0 < HP.η / 4 := by linarith [HP.η_pos]
  obtain ⟨C, _, hfloor⟩ := BudgetData.exists_compressedBin_uniform_accuracy HP
    hζ HP.η_pos le_rfl hscale (by linarith)
  have hf1 : HP.η / 4 ≤ 1 := by norm_num at hscale; linarith
  obtain ⟨Cp, _, hbound⟩ := hfloor (HP.η / 4) hζ (by linarith) hf1
  obtain ⟨Lh, Lρ, hLh, hLρ, hh, hρ⟩ := preparation_stability_constants HP
  obtain ⟨N, hN⟩ := hbound 0 0 1 0 16 Lh Lρ (by decide) (by norm_num) ε hε
  refine ⟨max 3 N, ?_⟩
  intro n hn
  have hn3 : 3 ≤ n := (le_max_left _ _).trans hn
  have hnN : N ≤ n := (le_max_right _ _).trans hn
  have hid : 4 < 2 ^ n := (by decide : 4 < 2 ^ 3).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) hn3)
  obtain ⟨P, hprime, hlo, hhi, H, he, _⟩ := exists_bounded_depth_prime n 4 hid
  let : Fact P.Prime := ⟨hprime⟩
  refine ⟨P, inferInstance, hlo, hhi, ?_⟩
  have hr : Admissible (uniformRequest HP P) :=
    ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩
  have hbase : ∀ x y, 0 ≤ (uniformData HP P n).base x y := by
    intro x y
    change 0 ≤ (1 : Matrix (ZMod P) (ZMod P) ℝ) x y
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  simpa only [uniformData, mul_one] using
    hN (uniformData HP P n) n hnN hhi rfl rfl (by norm_num [uniformData]) rfl
      rfl rfl (by norm_num [uniformData]) H (by omega) (uniformRequest HP P) hr
      (by norm_num [uniformData]) threeRoles 2 [1] [2, 3] rfl rfl rfl (by omega)
      (by omega) (by decide) hbase (by simp [uniformData]) 0 hLh hLρ hh hρ

-- A positive structural charge is fixed before the depth; the same guards cover a
-- nonzero usage exponent without charging it as a terminal exponent.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ N : ℕ, ∀ n ≥ N,
      2 * (n : ℝ) ≤ ({ data HP with rankCharge := 7 }).requestPrecision
        (128 * n) (uniformRequest HP 5) := by
  obtain ⟨N, hN⟩ := BudgetData.fixed_charge_linear_guards (HP := HP) 0 0 1
    (7 * (uniformRequest HP 5).task.rank) (by decide)
  refine ⟨N, ?_⟩
  intro n hn
  simpa only [mul_one] using
    (hN 5 n { data HP with rankCharge := 7 } hn rfl (uniformRequest HP 5) rfl rfl le_rfl).2.2.1

-- A genuine small floor and a nonzero rooted child error supply the own-precision IH.
-- The coefficient is fixed for the only positive lower budget; no parent budget is used.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let ζ := min HP.η (1 / 10000) / 4
    let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
      (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
      ((data HP).binRate 0)
    let c := (2 : ℝ) ^ ((data HP).requestPrecision 1 Q.direct)
    0 < ζ ∧ ζ ≤ HP.η ∧ ζ ≤ max (1 : ℝ) 16 / 20000 ∧
    ∃ A C,
      (data HP).pairedSample (fun n q => if n < 2 then
        (data HP).compressedHistory (fun _ => 0) ζ ζ n q else none)
        2 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) (some 0) = some A ∧
      (data HP).pairedSample (fun n q => if n < 2 then (data HP).evaluate n q else none)
        2 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) (some 0) = some C ∧
      rowNormPow 4 5 (request HP).source.rate
        (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
        (fun σ y => (request HP).usage.retains (channels (data HP).padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
          (fun σ y => (request HP).usage.retains (channels (data HP).padding) σ y)
          (A - C) x y| / (rate 0 + base x y))) ≤
        8 * ((512 * (6 * (data HP).binCap + 3) ^ 3) *
          (rate 0 * (gridMass 5 0 / gridMass 5 (max 0 0)) / rate 0)) *
          (c ^ 4 * ((2 : ℝ) ^ (-(data HP).requestPrecision 1 Q.direct)) ^ 4) := by
  dsimp only
  let ζ := min HP.η (1 / 10000) / 4
  let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
    (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
    ((data HP).binRate 0)
  let c := (2 : ℝ) ^ ((data HP).requestPrecision 1 Q.direct)
  have hζ : 0 < ζ := by
    dsimp only [ζ]
    exact div_pos (lt_min HP.η_pos (by norm_num)) (by norm_num)
  have hη : ζ ≤ HP.η := by
    have h := min_le_left HP.η (1 / 10000 : ℝ)
    dsimp only [ζ]; linarith [HP.η_pos]
  refine ⟨hζ, hη, ?_, ?_⟩
  · have h := min_le_right HP.η (1 / 10000 : ℝ)
    norm_num; linarith
  · have hd : (data HP).compressedBin 1 0 0 ζ ζ Q.direct = some 0 := by
      simpa only [Q, HierarchyTask.rawRequests, request, data, gridChannel, rate, pow_zero,
        inv_one, min_self] using compressed_one HP (.baseNormalized 0 0) ζ hζ
        (by dsimp only [ζ]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
    have ht : denseChild (data HP).padding id Q.direct ((data HP).cutoff 0)
        ((data HP).auxiliary 0) HP.ρ HP.K (data HP).base = (fun _ => base) := by
      funext σ x y
      have hq : Q.direct = {request HP with task := .baseNormalized 0 0} := by
        simp [Q, HierarchyTask.rawRequests, request, data, gridChannel, rate]
      rw [hq, denseChild_congr_task]
      exact top_dense HP σ x y
    have hroot : rootDistPow 4 5 Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels (data HP).padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels (data HP).padding) σ y) 0
        (denseChild (data HP).padding id Q.direct ((data HP).cutoff 0)
          ((data HP).auxiliary 0) HP.ρ HP.K (data HP).base) ≤
        c ^ 4 * ((2 : ℝ) ^ (-(data HP).requestPrecision 1 Q.direct)) ^ 4 := by
      rw [ht, ← mul_pow]
      have hc : c * (2 : ℝ) ^ (-(data HP).requestPrecision 1 Q.direct) = 1 := by
        dsimp only [c]
        rw [← Real.rpow_add (by norm_num)]
        simp
      rw [hc, one_pow]
      have hs : Q.direct.source = gridChannel 0 0 [1] := rfl
      have hu : Q.direct.usage = gridChannel 2 0 [2, 3] := by
        simp [Q, HierarchyTask.rawRequests, request, data, gridChannel, rate]
      rw [hs, hu]
      simp only [rootDistPow, rowNormPow, data, full, filter_true]
      norm_num only [gridChannel, rate, base, Matrix.one_apply, Pi.zero_apply,
        zero_sub, abs_neg, Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0),
        apply_ite (fun t : ℝ => |t ^ (4⁻¹ : ℝ)| ^ 4)]
      norm_num [apply_ite abs, ite_pow]
    have hprep (v : ℝ) (hv : (data HP).cutoff 0 v ≠ 0) :
        (data HP).auxiliary 0 v = 1 := by
      exact HP.routedBin_prep_eq_one (by norm_num)
        (fun w hw => polynomialSwitch4_of_le (by norm_num) hw) rate_pos rate_antitone
        0 (fun _ => 1) hv
    have hK : 2 * (1 + 32 / HP.η) ≤ HP.K := by
      have hk : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
      have hdiv := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
      have hg := HP.gate
      norm_num only [mul_one] at hdiv
      nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) HP.η_pos.le]
    have hp := (data HP).pairedSample_initial_compressed_clipped_precision rfl rfl
      (by norm_num [data]) (⟨1, 4, by decide, by decide⟩ : Horizon 5)
      (fun _ => 0) ζ ζ 2 1 0 (by decide) (request HP)
      0 2 (by decide) 0 0 [1] [2, 3] rfl rfl (by decide) (by decide) hprep
      (by intro x y; by_cases h : x = y <;> simp [data, base, h]) (by simp [data, base]) hK
      (fun _ => 0) rfl c (fun m hm hmpos => by
        have he : m = 1 := by omega
        subst m
        exact ⟨hd, hroot, right_available HP ζ 1 (by decide)⟩)
    have hf : LogSpaceEstimation.lastBudget 2 1 (data HP).slack
        ((data HP).sampleScale (request HP) (some 0)) = 1 := by
      norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
        BudgetData.sampleScale, data, request, gridChannel, rate]
    have hc : LogSpaceEstimation.lastBudget 2 (2 * 1) (data HP).slack
        ((data HP).sampleScale (request HP) (some 0)) = 0 := by
      norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
        BudgetData.sampleScale, data, request, gridChannel, rate]
    simp only [hf, hc, BudgetData.initialEndpointCharge,
      BudgetData.initialClippedRootCoefficient, le_refl, Nat.one_ne_zero, ↓reduceIte,
      add_zero] at hp
    convert hp using 1;
      simp only [rowNormPow, rowSliceMean, data, request, gridChannel,
        CorrectionRowTask.Channel.retains, channels, semanticSide_grid, X, Y,
        Nat.cast_ofNat, ζ, c, Q]

-- Budget one consumes no positive child IH, even after all bins are completed.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (coefficient : ℝ) :
    ∃ F G,
      (data HP).completedGroup (fun n q => if n < 1 then
        (data HP).compressedHistory (fun _ => 0) (HP.η / 4) (HP.η / 4) n q else none)
        1 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) = some F ∧
      (data HP).completedGroup (fun n q => if n < 1 then (data HP).evaluate n q else none)
        1 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) = some G ∧
      rowNormPow 4 5 (request HP).source.rate
        (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
        (fun σ y => (request HP).usage.retains (channels (data HP).padding) σ y) (F - G) ≤ 0 := by
  have h := (data HP).completedGroup_initial_compressed_precision (fun _ => 0)
    (HP.η / 4) (HP.η / 4) 1 1 (by decide) (by simp [data]) (request HP)
    0 2 (by decide) 0 0 [1] [2, 3] rfl rfl (fun _ _ => 0) (fun _ => rfl) coefficient
    (fun _ _ n hn hnpos => by omega)
  simpa only [(data HP).initialRootGroupCharge_eq_zero_of_le 1 1 (request HP)
    coefficient le_rfl, Nat.cast_ofNat] using h

-- A positive full-rate history has nonzero literal group amplitude, but its exact
-- normalized conditional input noise is zero. The conservative absolute envelope is positive.
open NormalizedMoments in
private lemma relative_budget_two (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).initialRelativeNoiseBudget 2 (request HP) 0 2 (by decide) 0 0 [1] [2, 3]
      base 2 = 0 := by
  have hx (σ : Environment 5 3) (x : ZMod 5) :
      retainedMask 0 (side 5 0) (1 : ZMod 5) [1] σ x := by
    simpa only [retainedMask, show side 5 0 = 5 by norm_num [side]] using full_retains (σ 0) _
  have hy (σ : Environment 5 3) (y : ZMod 5) :
      retainedMask 2 (side 5 0) (1 : ZMod 5) [2, 3] σ y := by
    simpa only [retainedMask, show side 5 0 = 5 by norm_num [side]] using full_retains (σ 2) _
  have hq : {request HP with usage := (request HP).terminal} = request HP := rfl
  have hg (d : ℕ) : (data HP).initialGroupInput 2 d (request HP) = fun _ x y =>
      (if LogSpaceEstimation.lastBudget 2 d 1 0 = 0 then 0 else base x y) -
      (if LogSpaceEstimation.lastBudget 2 (2 * d) 1 0 = 0 then 0 else base x y) :=
    group_input HP d
  simp only [BudgetData.initialRelativeNoiseBudget, hq, hg]
  simp [rowSliceMean, show (data HP).padding = 1 from rfl, hx, hy]

-- With zero transported error, the semantic term is strictly sharper on this positive
-- history. The actual approximate-child error is tested separately above.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ζ Lh Lρ : ℝ)
    (σ : Environment 5 3) :
    (data HP).initialGroupInput 2 1 (request HP) σ 0 0 = 1 ∧
    (data HP).initialComputedRelativeMoment 2 1 (request HP) threeRoles 0 0 [1] [2, 3]
      (fun _ => 0) ζ Lh Lρ (Nat.log2 2) true 0 = 0 ∧
    0 < (data HP).initialComputedMoment 2 1 (request HP) threeRoles 0 0 [1] [2, 3]
      (fun _ => 0) ζ Lh Lρ (Nat.log2 2) true 0 := by
  constructor
  · have hg := congrFun (congrFun (congrFun (group_input HP 1) σ) 0) 0
    norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff, base] at hg
    exact hg
  constructor
  · have hnon := (data HP).initialComputedMoment_nonneg 2 1 (request HP) threeRoles
      0 0 [1] [2, 3] (fun _ => 0) (by intro; rfl) ζ Lh Lρ (Nat.log2 2) true 0
    simp only [BudgetData.initialComputedRelativeMoment, ↓reduceIte, Fin.isValue, and_self,
      sum_const_zero, mul_zero, zero_add, show Nat.log2 2 + 1 = 2 by decide,
      show (threeRoles : RoleProfile 3).source = 0 from rfl,
      show (threeRoles : RoleProfile 3).terminal = 2 from rfl,
      show (data HP).base = base from rfl, relative_budget_two, mul_zero]
    exact min_eq_right hnon
  · rw [(data HP).initialComputedMoment_final_firstNoise_zero]
    positivity

-- Actual small-floor compression has nonzero error on the diagonal. Its exact
-- denominator-weighted error improves even though the worst-pair factor below does not.
-- This is a checked remaining opportunity for support-sensitive child transport.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let ζ := min HP.η (1 / 10000) / 4
    ∃ D, (data HP).compressedBin 1 0 0 ζ ζ
      {request HP with task := .baseNormalized 0 0} = some D ∧
      rowNormPow 4 5 (request HP).source.rate
        (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
        (fun σ y => (request HP).usage.retains (channels (data HP).padding) σ y)
        (fun σ x y => (D σ x y - base x y) / (rate 0 + base x y)) = 1 / 16 := by
  dsimp only
  have hζ : 0 < min HP.η (1 / 10000 : ℝ) / 4 := by
    exact div_pos (lt_min HP.η_pos (by norm_num)) (by norm_num)
  have hζη : min HP.η (1 / 10000 : ℝ) / 4 ≤ HP.η / 4 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  refine ⟨0, compressed_one HP (.baseNormalized 0 0) _ hζ hζη, ?_⟩
  simp only [rowNormPow, request, data, full, filter_true]
  norm_num [gridChannel, rate, base, Matrix.one_apply, apply_ite abs, ite_pow]
  have he (x y : ZMod 5) :
      |(-(if x = y then (1 : ℝ) else 0)) / (1 + if x = y then 1 else 0)| ^ 4 =
        if x = y then 1 / 16 else 0 := by
    by_cases h : x = y <;> norm_num [h]
  simp_rw [he]
  norm_num

-- The actual identity target has zero off-diagonal entries: its worst-pair payment
-- retains the old inverse rate, despite the gain on strictly positive targets below.
example (ka : ℕ) :
    BudgetData.initialPerturbationFactor ka base = (rate ka)⁻¹ ^ 4 := by
  apply BudgetData.initialPerturbationFactor_eq_of_zero ka base
    (by intro x y; by_cases h : x = y <;> simp [base, Matrix.one_apply, h]) 0 1
  norm_num [base]

-- The actual cost function consumes the worst-pair refinement for a strictly positive
-- substochastic target. This compares its new branch with the previous relative branch,
-- without assuming that either charge has been absorbed into parent accuracy.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ζ Lh Lρ : ℝ) :
    let B : BudgetData HP 5 := { data HP with base := fun _ _ => 1 / 5 }
    B.initialComputedRelativeMoment 2 1 (request HP) threeRoles 0 0 [1] [2, 3]
      (fun _ => 1) ζ Lh Lρ 0 true 0 <
      8 * (16 * (rate 0)⁻¹ ^ 4 + B.initialRelativeNoiseBudget 2 (request HP)
        0 2 (by decide) 0 0 [1] [2, 3] B.base 1) := by
  dsimp only
  simp only [BudgetData.initialComputedRelativeMoment, Fin.isValue, and_self, ↓reduceIte,
    Nat.zero_add, Nat.cast_one, one_pow, range_one, sum_singleton, mul_one]
  apply (min_le_right _ _).trans_lt
  rw [BudgetData.initialPerturbationFactor_const]
  norm_num [rate, threeRoles]

-- The new generic payment also covers genuinely nonconstant perturbations, with a
-- strict gain at positive target and no cancellation or independence hypothesis.
example :
    rowNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
      (fun σ _ _ => ((if σ = 0 then (2 : ℝ) else 0) - 1) * (1 / 16 + 1)⁻¹) ≤
      BudgetData.initialPerturbationFactor (P := 5) 1 (fun _ _ => 1) *
        rowNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
          (fun σ _ _ => (if σ = 0 then (2 : ℝ) else 0) - 1) ∧
      BudgetData.initialPerturbationFactor (P := 5) 1 (fun _ _ => 1) < (rate 1)⁻¹ ^ 4 := by
  constructor
  · have hw := rowNormPow_mul_le_pi_norm (by norm_num : (0 : ℝ) ≤ 1 * 1)
      (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
      (fun σ _ _ => (if σ = 0 then (2 : ℝ) else 0) - 1)
      (fun (_ : Unit × Unit) => (1 / 16 + 1 : ℝ)⁻¹)
    norm_num [BudgetData.initialPerturbationFactor_const, rate] at hw ⊢
    exact hw
  · rw [BudgetData.initialPerturbationFactor_const]
    norm_num [rate]

-- Nonconstant, nonzero centered noise pays the fixed-pair target normalization, even
-- at a small rank rate; replacing the denominator by the rate loses a large factor.
example :
    rowNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
      (fun σ _ _ => ((if σ = 0 then (2 : ℝ) else 0) - 1) / (1 / 16 + 1)) =
        (16 / 17 : ℝ) ^ 4 ∧ (16 / 17 : ℝ) ^ 4 < 16 ^ 4 := by
  norm_num [rowNormPow, Fin.sum_univ_two, expect_eq_sum_div_card]

-- Centered transport keeps a nonconstant correlated perturbation centered at its own mean.
example :
    rowNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
      (fun σ _ _ => (if σ = 0 then (2 : ℝ) else 0) - 1) = 1 ∧
    rowNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
      (fun σ x y => (if σ = 0 then (2 : ℝ) else 0) -
        rowSliceMean (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
          (fun τ _ _ => if τ = 0 then (2 : ℝ) else 0) x y) ≤ 128 := by
  constructor
  · norm_num [rowNormPow, Fin.sum_univ_two, expect_eq_sum_div_card]
  · have h := rowNormPow_centered_fourth_le (by norm_num : (0 : ℝ) ≤ 1 * 1)
      (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
      (fun σ _ _ => if σ = 0 then (2 : ℝ) else 0) (fun _ _ _ => 1)
    norm_num [rowNormPow, rowSliceMean, Fin.sum_univ_two, expect_eq_sum_div_card] at h ⊢

-- All four costs and every sharp reserve term are consumed on the literal zero boundary.
-- The scalar floor is valid and positive; the canonical diagonal target is still one.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let ζ := min HP.η (1 / 10000) / 4
    ∃ Lh Lρ : ℝ, 0 ≤ Lh ∧ 0 ≤ Lρ ∧
      (data HP).initialFourMaxReserve 1 0 0 ζ ζ (request HP) threeRoles 0 0 [1] [2, 3]
        base (fun _ => 0) [0] 1 1 1 ≤
      (BudgetData.initialNumericalReserve HP 1 ζ 1 1 1
        (fun j =>
          let a := fun noise ν => (data HP).initialComputedPrecisionMoment 1 1 (request HP)
            threeRoles 0 0 [1] [2, 3] 0 ζ Lh Lρ j noise ν ^ (4⁻¹ : ℝ)
          (a false 0 + a false 1) + (a true 0 + a true 1))) ∧
      (data HP).initialFourMaxReserve 1 0 0 ζ ζ (request HP) threeRoles 0 0 [1] [2, 3]
        base (fun _ => 0) [0] 1 1 1 ≤
      let a := fun j noise ν => (data HP).initialComputedPrecisionMoment 1 1 (request HP)
        threeRoles 0 0 [1] [2, 3] 0 ζ Lh Lρ j noise ν ^ (4⁻¹ : ℝ)
      BudgetData.initialSeparatedReserve HP 1 1
            ((data HP).initialComputedFirstPreBudget 1 1 (request HP) threeRoles 0 0 [1] [2,
              3] 0 ζ +
              ∑ j ∈ range (Nat.log2 1 + 1), dyadicFloor ζ (Nat.log2 1 + 1) j *
                (a j false 1 + (a j true 0 + a j true 1)))
            ((data HP).initialComputedFirstFinalPayment 1 1 (request HP) threeRoles 0 0 [1] [2,
              3] 0 +
              (a (Nat.log2 1) false 1 + (a (Nat.log2 1) true 0 + a (Nat.log2 1) true 1)))
            (((data HP).initialComputedFirstTailBudget 1 1 (request HP) threeRoles 0 0 [1] [2,
              3] 0 ζ +
              ∑ j ∈ range (Nat.log2 1 + 1),
              (((2 + 256 / dyadicFloor ζ (Nat.log2 1 + 1) j) /
                (compatibleCapacity HP.K (Nat.log2 1 + 1) j : ℝ)) ^ (4⁻¹ : ℝ)) *
              ∑ i ∈ Ico j (Nat.log2 1 + 1), (28 : ℝ) ^ (Nat.log2 1 + 1 - i) *
                a i false 1) +
              ∑ i ∈ range (Nat.log2 1 + 1), (28 : ℝ) ^ (Nat.log2 1 + 1 - i) *
                (a i true 0 + a i true 1))
            (64 * ((data HP).initialComputedFirstRawBudget 1 1 (request HP) threeRoles 0 0 [1]
              [2, 3] 0 ζ
                ((2 * max 1 16) ^ (4⁻¹ : ℝ)) +
              ∑ j ∈ range (Nat.log2 1 + 1),
                (64 * (HP.K : ℝ) * ((2 * max 1 16) ^ (4⁻¹ : ℝ)) ^ 4 /
                  ((compatibleCapacity HP.K (Nat.log2 1 + 1) j : ℝ) *
                    dyadicFloor ζ (Nat.log2 1 + 1) j ^ 4)) *
                ((a j false 1 ^ 4) + (a j true 0 ^ 4 + a j true 1 ^ 4)))) := by
  dsimp only
  let ζ := min HP.η (1 / 10000) / 4
  obtain ⟨Lh, Lρ, hLh, hLρ, hh, hρ⟩ := preparation_stability_constants HP
  refine ⟨Lh, Lρ, hLh, hLρ, ?_⟩
  obtain ⟨groups, hrun, hp⟩ := (data HP).initial_compressed_precision_reserve 1 (by decide) 1
    (by ext i; simp only [data, mem_insert, mem_singleton, mem_range]; omega)
    rfl rfl rfl (by norm_num [data]) (⟨1, 4, by decide, by decide⟩ : Horizon 5) (by decide)
    (request HP) threeRoles 0 0 [1] [2, 3] rfl rfl (by decide)
    (by intro x y; by_cases h : x = y <;> simp [data, base, h])
    (by simp [data, base]) (fun _ => 0) ζ ζ (fun _ _ => 0) (fun _ => rfl) 0
    (fun _ _ m hm hmpos => by omega) 0 0 le_rfl rfl hLh hLρ hh hρ
    (by decide) (by
      dsimp only [ζ]
      exact (div_pos (lt_min HP.η_pos (by norm_num)) (by norm_num))) (by norm_num [data]) rfl 1 1 1
  have hgroups : (List.range (Nat.log2 1 + 1)).mapM (fun j =>
      (data HP).completedGroup (fun m q => if m < 1 then
        (data HP).compressedHistory (fun _ => 0) ζ ζ m q else none) 1
        (dyadicSlack (Nat.log2 1 + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { request HP with usage := (request HP).terminal }) = some [0] := by
    rw [show { request HP with usage := (request HP).terminal } = request HP from rfl]
    norm_num only [show Nat.log2 1 = 0 by decide, Nat.zero_add, List.range_succ,
      List.range_zero, List.nil_append, List.mapM_cons, List.mapM_nil]
    rw [show dyadicSlack 1 0 = 1 by decide, group_one_zero]
    rfl
  have hF : (fun p σ x y =>
      (([0] : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)).take p |>.map
        (fun T => T σ x y)).sum) =
      (fun _ => (0 : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)) := by
    funext p σ x y
    cases p <;> simp
  have hW : (List.range (Nat.log2 1 + 1)).mapM (fun j =>
      (data HP).complete 1 (request HP) ((data HP).binPreparation 0 (request HP)
        ((fun _ => 0) (j + 1))) (dyadicSlack (Nat.log2 1 + 1) j)) = some [0] := by
    have hw (j : ℕ) : (data HP).complete 1 (request HP)
        ((data HP).binPreparation 0 (request HP) ((fun _ => 0) (j + 1)))
        (dyadicSlack (Nat.log2 1 + 1) j) = some 0 := by
      rw [show (data HP).binPreparation 0 (request HP) 0 = 0 from
        preparation HP 0 (Or.inl rfl)]
      exact complete_const HP 1 _ 0
    simp_rw [hw]
    norm_num [List.range_succ]
  have he : groups = [0] := Option.some.inj (hrun.symm.trans hgroups)
  subst groups
  dsimp only at hp
  rw [hF] at hp
  have hb := hp [0] (by
    convert hW using 1
    apply congrArg (fun f : ℕ → Option (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) =>
      (List.range (Nat.log2 1 + 1)).mapM f)
    funext j
    rw [show (fun σ x y =>
      (([0] : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)).take (j + 1) |>.map
        (fun T => T σ x y)).sum) = 0 from congrFun hF (j + 1)])
  constructor
  · convert hb.1 using 1; congr 8
  · convert hb.2.1 using 1; congr 8

-- A constant weight costs its own fourth power, rather than five copies of that cost.
example : ‖fun _ : Fin 5 => (3 : ℝ)‖ ^ 4 = 81 ∧
    (∑ _ : Fin 5, |(3 : ℝ)| ^ 4) = 405 := by
  norm_num

-- Two exclusive events may be fully correlated with the values: there is no factor eight.
example :
    vertexNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True)
      (fun σ _ => ∑ j : Fin 2, if j = σ then (2 : ℝ) else 0) = 16 ∧
    vertexNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True)
      (fun σ _ => ∑ j : Fin 2, if j = σ then (2 : ℝ) else 0) =
      ∑ j : Fin 2, vertexNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True)
        (fun σ _ => if j = σ then (2 : ℝ) else 0) := by
  constructor
  · norm_num [vertexNormPow, Fin.sum_univ_two, expect_eq_sum_div_card]
  · exact vertexNormPow_sum_ite univ 4 (by decide) 1 1 (fun _ _ => True)
      (fun j σ _ => j = σ) (fun _ _ _ _ hi hj => hi.trans hj.symm) (fun _ _ _ => 2)

-- The final-noise envelope already exceeds the requested fourth power at terminal exponent
-- two, for every statistical budget. This tests an envelope obstruction, not actual error.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ) (R : RoleProfile 3) :
    let r := {request HP with
      terminal := gridChannel 2 2 [2, 3]
      usage := gridChannel 2 2 [2, 3]}
    ((2 : ℝ) ^ (-(data HP).requestPrecision M r)) ^ 4 <
      (data HP).initialComputedMoment M 1 r R 0 2 [1] [2, 3]
        (fun _ => 0) (HP.η / 4) 0 0 (Nat.log2 M) true 0 := by
  dsimp only
  rw [(data HP).initialComputedMoment_final_firstNoise_zero]
  have hp : 0 < ((2 : ℝ) ^ (-(data HP).requestPrecision M
      {request HP with
        terminal := gridChannel 2 2 [2, 3]
        usage := gridChannel 2 2 [2, 3]})) ^ 4 := by positivity
  norm_num
  linarith

-- A positive, nonconstant literal group: the diagonal survives and the zero target does
-- not acquire a floor-dependent charge. These are canonical executed input values.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 3) :
    (data HP).initialGroupInput 2 1 (request HP) σ 0 0 = 1 ∧
    (data HP).initialGroupInput 2 1 (request HP) σ 0 1 = 0 := by
  have h := group_input HP 1
  constructor
  · simpa [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff, base] using
      congrFun (congrFun (congrFun h σ) 0) 0
  · exact (data HP).initialGroupInput_polynomial_eq_zero rfl 2 1 (request HP) σ 0 1
      (by norm_num [data, base])

-- Both adjacent fine bins are genuinely active at an interior transition. Farther bins
-- vanish: the support count is independent of the number of retained bins.
example :
    #{i ∈ range 5 | binWeight (polynomialSwitch4 (1 / 2) 1) rate i (3 / 64) ≠ 0} = 2 := by
  rw [show range 5 = {0, 1, 2, 3, 4} by decide]
  norm_num [filter_insert, filter_singleton, binWeight, rate,
    polynomialSwitch4, polynomialTransition4, transitionPolynomial4]

private def supportHorizon : Horizon 5 := ⟨2, 4, by decide, by decide⟩

-- A positive small target, zeros off the diagonal and a smaller terminal rate coexist
-- with the normalized fourth-moment bound. No positive target floor appears.
open NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M d : ℕ) (x y : ZMod 5) :
    let B := scaledData HP (1 / 16)
    let r := {request HP with terminal := gridChannel 2 2 [2, 3]}
    let Xs := retainedMask 0 (side 5 0) B.padding [1]
    let Ya := retainedMask 2 (side 5 2) B.padding [2, 3]
    (𝔼 σ ∈ ({σ | Xs σ x ∧ Ya σ y} : Finset (Environment 5 3)),
      |(B.initialGroupInput M d r σ x y - rowSliceMean Xs Ya
        (B.initialGroupInput M d r) x y) / (rate 2 + B.base x y)| ^ 4) ≤ 4096 ^ 4 := by
  dsimp only
  have hC (v z : ZMod 5) : 0 ≤ (scaledData HP (1 / 16)).base v z := by
    change 0 ≤ (1 / 16 : ℝ) * (if v = z then 1 else 0)
    split_ifs <;> norm_num
  have hC1 : (scaledData HP (1 / 16)).base *ᵥ 1 ≤ 1 := by
    intro v
    norm_num [scaledData, data, base, Matrix.smul_mulVec]
  have h := (scaledData HP (1 / 16)).initialGroupInput_polynomial_relative_fourth_le
    rfl rfl supportHorizon (by
      intro i hi
      simp only [scaledData, data, mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl <;> decide)
    M d {request HP with terminal := gridChannel 2 2 [2, 3]}
    0 2 0 2 [1] [2, 3] rfl (by decide) hC hC1 x y
  simpa only [show (scaledData HP (1 / 16)).binCap = 16 from rfl,
    show (256 : ℝ) * 16 = 4096 by norm_num] using h

-- The actual computed minimum accepts the scheduled semantic bound, retaining arbitrary
-- transported-child charges. This does not assume those charges satisfy parent accuracy.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M j : ℕ)
    (ε : ℕ → ℝ) (ζ Lh Lρ : ℝ) :
    (data HP).initialComputedRelativeMoment M 1 (request HP) threeRoles 0 0 [1] [2, 3]
      ε ζ Lh Lρ j true 0 ≤
      min ((data HP).initialComputedMoment M 1 (request HP) threeRoles 0 0 [1] [2, 3]
        ε ζ Lh Lρ j true 0)
        (8 * (16 * BudgetData.initialPerturbationFactor 0 base *
          (((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i) +
          4096 ^ 4 * ((min (j + 1) (Nat.log2 M + 1) : ℕ) ^ (3 : ℕ) *
            ∑ i ∈ range (min (j + 1) (Nat.log2 M + 1)),
              ((2 : ℝ) ^ (-(data HP).requestPrecision M (request HP)) *
                (64 : ℝ)⁻¹ ^ Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) i) ^ 4))) := by
  have h := (data HP).initialComputedRelativeMoment_polynomial_firstNoise_le rfl rfl
    supportHorizon (by
      intro i hi
      simp only [data, mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl <;> decide)
    M 1 (request HP) threeRoles 0 0 [1] [2, 3] rfl rfl (by decide)
    (by intro x y; by_cases h : x = y <;> simp [data, base, h])
    (by intro x; simp [data, base]) ε ζ Lh Lρ j
  simpa only [show (data HP).base = base from rfl,
    show (data HP).binCap = 16 from rfl, show (256 : ℝ) * 16 = 4096 by norm_num,
    show {request HP with usage := (request HP).terminal} = request HP from rfl] using h

-- The clipped positive-mean estimate is instantiated by an actual small-floor compressed
-- child with nonzero error. Reset-right still executes; no exact-child premise is used.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let ζ := min HP.η (1 / 10000) / 4
    let Xs := X 0 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [1])
    let Ya := Y 2 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [2, 3])
    ∃ A, (data HP).positiveSample (fun m q => if m < 2 then
        (data HP).compressedHistory (fun _ => 0) ζ ζ m q else none)
        1 0 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) = some A ∧
      (∀ σ, |A σ 0 0 - (data HP).initialSample (request HP) 0 σ 0 0| = 1) ∧
      min 1 (|rowSliceMean Xs Ya (A - (data HP).initialSample (request HP) 0) 0 0| /
        (rate 0 + base 0 0)) ^ 4 ≤ 512 * (6 * (16 : ℝ) + 3) ^ 3 := by
  dsimp only
  let ζ := min HP.η (1 / 10000) / 4
  let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
    (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
    ((data HP).binRate 0)
  have hζ : 0 < ζ := div_pos (lt_min HP.η_pos (by norm_num)) (by norm_num)
  have hd : (data HP).compressedBin 1 0 0 ζ ζ Q.direct = some 0 := by
    simpa only [Q, HierarchyTask.rawRequests, request, data, gridChannel, rate, pow_zero,
      inv_one, min_self] using compressed_one HP (.baseNormalized 0 0) ζ hζ
      (by dsimp only [ζ]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  obtain ⟨R, hr⟩ := right_available HP ζ 1 (by decide)
  have hprep (v : ℝ) (hv : (data HP).cutoff 0 v ≠ 0) :
      (data HP).auxiliary 0 v = 1 := by
    exact HP.routedBin_prep_eq_one (by norm_num)
      (fun w hw => polynomialSwitch4_of_le (by norm_num) hw) rate_pos rate_antitone
      0 (fun _ => 1) hv
  have hK : 2 * (1 + 32 / HP.η) ≤ HP.K := by
    have hk : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
    have hg := HP.gate
    norm_num only [mul_one] at hdiv
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) HP.η_pos.le]
  obtain ⟨A, hrun, hbound⟩ := (data HP).positiveSample_initial_compressed_clipped_mean
    rfl rfl (by norm_num [data]) supportHorizon (fun _ => 0) ζ ζ 2 1 0 (by decide)
    (request HP) 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl (by decide) (by decide)
    hprep (by intro x y; by_cases h : x = y <;> simp [data, base, h])
    (by simp [data, base]) hK 0 R hd hr
  refine ⟨A, hrun, ?_, ?_⟩
  · have he := (data HP).positiveSample_initial_compressed (fun _ => 0) ζ ζ 2 1 0
      (by decide) (request HP) 0 R hd hr
    have hz : A = 0 := by
      apply Option.some.inj
      apply hrun.symm.trans
      convert he.1 using 1
      congr 1
      funext σ x y
      simp
    rw [hz]
    intro σ
    rw [initial HP 0 (by simp [data])]
    norm_num [base]
  · have hc (σ : Environment 5 3) : denseChild (data HP).padding id Q.direct
        ((data HP).cutoff 0) ((data HP).auxiliary 0) HP.ρ HP.K (data HP).base σ 0 0 = 1 := by
      have hq : Q.direct = {request HP with task := .baseNormalized 0 0} := by
        simp [Q, HierarchyTask.rawRequests, request, data, gridChannel, rate]
      rw [hq, denseChild_congr_task]
      simpa only [data, base, Matrix.one_apply_eq] using top_dense HP σ 0 0
    have hratio : HierarchyTask.usageRatio (channels (data HP).padding)
        (request HP).terminal Q.direct 0 = 1 := by
      have h := usageRatio_grid (data HP).padding (request HP).terminal Q.direct 0 0 rfl
        (by simp [Q, HierarchyTask.rawRequests, request, data, gridChannel, rate]) 0
      norm_num [gridMass, side] at h
      exact h
    have hx (σ : Environment 5 3) :
        X 0 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [1]) σ 0 := by
      simpa only [gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid,
        X] using full σ 0 [1] 0
    have hy (σ : Environment 5 3) :
        Y 2 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [2, 3]) σ 0 := by
      simpa only [gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid,
        Y] using full σ 2 [2, 3] 0
    have h := hbound 0 0
    dsimp only [Q] at hc
    simp_rw [hc] at h
    change _ ≤ _ * ((data HP).binRate 0 * HierarchyTask.usageRatio
      (channels (data HP).padding) (request HP).terminal Q.direct 0 / rate 0) *
      𝔼 σ ∈ _, |(0 : ℝ) ^ (4⁻¹ : ℝ) - _| ^ 4 at h
    rw [hratio] at h
    simp only [show (data HP).binRate 0 = 1 by norm_num [data, rate],
      show (data HP).padding = 1 from rfl, show (data HP).base = base from rfl,
      show (data HP).binCap = 16 from rfl,
      show rate 0 = 1 by norm_num [rate], Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0),
      Real.one_rpow, zero_sub, abs_neg, abs_one, one_pow, hx, hy, and_self, filter_true,
      Fintype.expect_const, mul_one, div_one] at h
    simpa only [show rate 0 = 1 by norm_num [rate]] using h

-- A literal compressed child is nonzero under a small floor; paired transport also
-- retains the earlier m=1 child with nonzero error, rather than assuming exact children.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ D, (data HP).compressedBin 2 0 0 (HP.η / 4) (HP.η / 4)
      {request HP with task := .baseNormalized 0 0} = some D ∧
      ∀ σ x, D σ x x = 1 := by
  exact ⟨_, compressed_value_task HP (.baseNormalized 0 0), fun _ _ => by simp [base]⟩

-- Adjacent unequal groups d=2 and d=1 share the literal m=2 endpoint. The history
-- executes nonzero dense children. Different completion lengths cancel only in the mean.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let r := request HP
    let history := fun n q => if n < 4 then (data HP).evaluate n q else none
    let Xs := X 0 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [1])
    let Ya := Y 2 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [2, 3])
    ∃ groups,
      (List.range (Nat.log2 4 + 1)).mapM (fun j => (data HP).completedGroup history 4
        (Cslib.RowCompression.dyadicSlack (Nat.log2 4 + 1) j)
        (.pilotInput ⟨0, HP.k_pos⟩) r) = some groups ∧
      rowSliceMean Xs Ya (fun σ x y => ((groups.take 2).map (fun T => T σ x y)).sum) 0 0 = 1 ∧
      rowSliceMean Xs Ya (fun σ x y => ((groups.take 3).map (fun T => T σ x y)).sum) 0 0 = 1 := by
  dsimp only
  let E := fun bin n => if n = 0 then 0 else (data HP).initialSample (request HP) bin
  obtain ⟨groups, hg, hm⟩ := (data HP).initial_sample_prefix_mean
    (fun n q => if n < 4 then (data HP).evaluate n q else none) 4 (by decide)
    (by simp [data]) (request HP) 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl E
    (fun bin _ n hn => (data HP).sample_initial_eq 4 (by decide) n hn bin (request HP))
  simp only [show (data HP).padding = 1 from rfl] at hm
  have hc (j : ℕ) (hj : j = 1 ∨ j = 2) : rowSliceMean
      (X 0 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [1]))
      (Y 2 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [2, 3]))
      (fun σ x y => ((groups.take (j + 1)).map (fun T => T σ x y)).sum) 0 0 = 1 := by
    rw [hm j (by rcases hj with hj | hj <;> subst j <;> decide) 0 0]
    have hx (σ : Environment 5 3) :
        X 0 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [1]) σ 0 := by
      simpa only [gridChannel, CorrectionRowTask.Channel.retains, channels,
        semanticSide_grid, X] using full σ 0 [1] 0
    have hy (σ : Environment 5 3) :
        Y 2 (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [2, 3]) σ 0 := by
      simpa only [gridChannel, CorrectionRowTask.Channel.retains, channels,
        semanticSide_grid, Y] using full σ 2 [2, 3] 0
    have hi := initial HP 0 (by simp [data])
    have hz := initial HP 1 (by simp [data])
    have he1 (n : ℕ) : E 1 n = 0 := by
      dsimp only [E]
      rw [hz]
      simp only [one_ne_zero, ↓reduceIte]
      split_ifs <;> rfl
    have hs0 : (data HP).sampleScale (request HP) (some 0) = 0 := by
      norm_num [BudgetData.sampleScale, data, request, gridChannel, rate]
    rcases hj with hj | hj <;> subst j
    all_goals
      rw [show (data HP).bins = {0, 1} from rfl, sum_insert (by decide), sum_singleton]
      simp only [he1, sub_self, rowSliceMean, Pi.zero_apply, Matrix.zero_apply,
        expect_const_zero, add_zero]
      rw [hs0]
      norm_num [show (data HP).slack = 1 from rfl, show Nat.log2 4 = 2 from rfl,
        Cslib.RowCompression.dyadicSlack, LogSpaceEstimation.lastBudget,
        LogSpaceEstimation.scaleCutoff, E, hi, hx, hy, base]
  exact ⟨groups, hg, hc 1 (Or.inl rfl), hc 2 (Or.inr rfl)⟩

-- The common endpoint is also an actually compressed, nonzero child with reset-right
-- execution. Coarse(d=1) and fine(d=2) are the same call, while each group's budgets differ.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let r := request HP
    let H := fun n q => if n < 4 then
      (data HP).compressedHistory (fun _ => 0) (HP.η / 4) (HP.η / 4) n q else none
    let budget := fun d => LogSpaceEstimation.lastBudget 4 d (data HP).slack
      ((data HP).sampleScale r (some 0))
    budget 1 = 3 ∧ budget 2 = 2 ∧ budget 4 = 0 ∧
    ∃ A, (data HP).sample H (budget (2 * 1)) (.pilotInput ⟨0, HP.k_pos⟩) r (some 0) =
        some A ∧
      (data HP).sample H (budget 2) (.pilotInput ⟨0, HP.k_pos⟩) r (some 0) = some A ∧
      ∀ σ, A σ 0 0 = 1 := by
  dsimp only
  have hs : (data HP).sampleScale (request HP) (some 0) = 0 := by
    norm_num [BudgetData.sampleScale, data, request, gridChannel, rate]
  simp only [hs, show (data HP).slack = 1 from rfl,
    LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
  norm_num only [Int.natAbs_zero, Nat.add_zero, mul_one, Nat.reduceMul]
  simp only [show max 1 1 = 1 from rfl, show max 2 1 = 2 from rfl,
    show max 4 1 = 4 from rfl, Nat.reduceSub, true_and]
  let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
    (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
    ((data HP).binRate 0)
  have hd : (data HP).compressedBin 2 0 0 (HP.η / 4) (HP.η / 4) Q.direct =
      some (fun _ => base) := by
    simpa only [Q, HierarchyTask.rawRequests, request, data, gridChannel, rate, pow_zero,
      inv_one, min_self] using compressed_value_task HP (.baseNormalized 0 0)
  obtain ⟨R, hr⟩ := right_available HP (HP.η / 4) 2 (by decide)
  have he := (data HP).positiveSample_initial_compressed (fun _ => 0) (HP.η / 4)
    (HP.η / 4) 4 2 0 (by decide) (request HP) (fun _ => base) R hd hr
  refine ⟨(fun σ x y => (data HP).binRate 0 * HierarchyTask.usageRatio
    (channels (data HP).padding) (request HP).terminal Q.direct y * base x y), ?_, ?_, ?_⟩
  · rw [BudgetData.sample, ite_eq_right (by decide : (2 : ℕ) ≠ 0)]
    exact he.1
  · rw [BudgetData.sample, ite_eq_right (by decide : (2 : ℕ) ≠ 0)]
    exact he.1
  · intro σ
    have hu : HierarchyTask.usageRatio (channels (data HP).padding) (request HP).terminal
        Q.direct 0 = 1 := by
      have h := usageRatio_grid (data HP).padding (request HP).terminal Q.direct 0 0 rfl
        (by simp [Q, HierarchyTask.rawRequests, request, data, gridChannel, rate]) 0
      norm_num [gridMass, side] at h
      exact h
    change (data HP).binRate 0 * _ * base 0 0 = 1
    rw [hu]
    norm_num [data, rate, base]

-- A positive-precision, full inactive initial prefix at a literal power-of-two budget.
-- Increasing retained depth changes this evaluator, not bins during an execution.
-- The schedule theorem pays its actual semantic row; no child availability is asserted.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let B : BudgetData HP 5 := {data HP with bins := range 3}
    let r := request HP
    B.requestPrecision 16 r = 1 ∧
    B.initialPolynomialLoss 16 2 0 r 0 0 = 1 ∧
    Cslib.RowCompression.dyadicFloor 1 (Nat.log2 16 + 1) 0 ^ 4 *
      rowNormPow 4 5 r.source.rate
        (NormalizedMoments.retainedMask (0 : Fin 3) (side 5 0) B.padding [1])
        (NormalizedMoments.retainedMask (2 : Fin 3) (side 5 0) B.padding [2, 3])
        (fun _ x y => min 1 (|B.initialPolynomialLoss 16 2 0 r x y| /
          (rate 0 + B.base x y))) ≤
      32 * ((2 : ℝ) ^ (-B.requestPrecision 16 r)) ^ 4 := by
  dsimp only
  let B : BudgetData HP 5 := {data HP with bins := range 3}
  have hp : B.requestPrecision 16 (request HP) = 1 := by
    rw [B.requestPrecision_grid 16 0 0 (request HP) rfl rfl]
    norm_num [B, data]
  refine ⟨hp, ?_, ?_⟩
  · have hcoarse := B.initialCoarseLoss_eq_zero 16 (request HP) 0 0
    rw [BudgetData.initialPolynomialLoss, hcoarse]
    norm_num [BudgetData.initialFineLoss, B, data, base, numerator,
      boundedRoutedBinCutoff, routedBinCutoff, binWeight, rate, polynomialSwitch4,
      polynomialTransition4, transitionPolynomial4, LogSpaceEstimation.lastBudget,
      Cslib.RowCompression.dyadicSlack, sum_range_succ]
  · have h := B.initialPolynomialLoss_first_schedule_family 16 2 0 0
      (by norm_num [B, data]) (by decide)
      (⟨1, 4, by decide, by decide⟩ : Horizon 5) (by decide) (request HP) rfl rfl
      (by intro x y; by_cases h : x = y <;> simp [B, data, base, h])
      threeRoles [1] [2, 3] 1 2 (by norm_num)
    simpa only [B, show (data HP).rankCharge = 0 from rfl, zero_mul, neg_zero,
      Real.rpow_zero, mul_one, one_mul, one_pow, threeRoles, Nat.cast_ofNat] using h.1

-- The structural charge is chosen before the field, retained depth and parent budget.
-- Every bin fits the SAME horizon used by the full reserve consumer. Child IH is not
-- asserted. The positive diagonal omitted mass is a real loss in the first-mean model.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (coefficient floor cap C Cp : ℝ) (hf : 0 < floor) :
    ∃ A : ℕ, ∀ n : ℕ, A * 36 + 1 < n →
      ∃ P, ∃ _ : Fact P.Prime, ∃ H : Horizon P,
      let B : BudgetData HP P := {uniformData HP P n with
        rankCharge := A, base := (rate n / 4) • (1 : Matrix (ZMod P) (ZMod P) ℝ)}
      let r := uniformRequest HP P
      H.maxExponent = n ∧ (∀ bin ∈ B.bins, bin ≤ H.maxExponent) ∧
      P ≤ 2 ^ (n + 1) ∧
      B.slack * (1 + 4 * (n + 0)) < 16 * n ∧ 16 * n ≤ 32 * B.slack * n ∧
      0 < B.requestPrecision (16 * n) r ∧
      0 < B.base 0 0 * (1 - polynomialSwitch4 (1 / 2) 1 (B.base 0 0 / rate n)) ∧
      B.base *ᵥ 1 ≤ 1 ∧
      (∀ ζ Lh Lρ : ℝ,
        B.initialComputedPrecisionMoment (16 * n) n r threeRoles 0 0 [1] [2, 3]
          coefficient ζ Lh Lρ (Nat.log2 (16 * n)) false 0 ^ (4⁻¹ : ℝ) ≤
          B.initialComputedFirstFinalBudget (16 * n) n r threeRoles 0 0 [1] [2, 3] coefficient) ∧
      BudgetData.initialSeparatedReserve HP C Cp
        (B.initialComputedFirstPreBudget (16 * n) n r threeRoles 0 0 [1] [2, 3] coefficient floor)
        (B.initialComputedFirstFinalBudget (16 * n) n r threeRoles 0 0 [1] [2, 3] coefficient)
        (B.initialComputedFirstTailBudget (16 * n) n r threeRoles 0 0 [1] [2, 3] coefficient floor)
        (64 * B.initialComputedFirstRawBudget (16 * n) n r threeRoles 0 0 [1] [2, 3]
          coefficient floor ((2 * max cap 16) ^ (4⁻¹ : ℝ))) ≤
        ((2 : ℝ) ^ (-B.requestPrecision (16 * n) r)) ^ 4 := by
  obtain ⟨A, hA⟩ := BudgetData.initialComputedFirstBudgets_exists_charge HP 16
    coefficient floor cap C Cp hf
  refine ⟨A, ?_⟩
  intro n hn
  obtain ⟨P, hprime, _, hP, H, he, _⟩ := exists_bounded_depth_prime n 0 (by positivity)
  let : Fact P.Prime := ⟨hprime⟩
  let B : BudgetData HP P := {uniformData HP P n with
    rankCharge := A, base := (rate n / 4) • (1 : Matrix (ZMod P) (ZMod P) ℝ)}
  let r := uniformRequest HP P
  have hC (x y : ZMod P) : 0 ≤ B.base x y := by
    change 0 ≤ (rate n / 4) * (1 : Matrix (ZMod P) (ZMod P) ℝ) x y
    by_cases h : x = y
    · subst y
      simpa using div_nonneg (rate_pos n).le (by norm_num : (0 : ℝ) ≤ 4)
    · simp [Matrix.one_apply_ne h]
  have hrank : r.task.rank = 36 := by
    norm_num [r, uniformRequest, HierarchyTask.rank, BoundedRowTask.localTask,
      CorrectionRowTask.rank, PilotRowTask.rank, PilotTask.rank]
  have hp : B.requestPrecision (16 * n) r = (n : ℝ) - A * 36 := by
    rw [B.requestPrecision_grid (16 * n) 0 0 r rfl rfl, hrank]
    dsimp only [B, uniformData]
    push_cast
    ring
  have hv : B.base 0 0 = rate n / 4 := by simp [B]
  have hs : (rate n / 4) / rate n = (1 / 4 : ℝ) := by field_simp [(rate_pos n).ne']
  refine ⟨P, inferInstance, H, he, ?_, hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro bin hb
    change bin ∈ range (n + 1) at hb
    rw [he]
    exact Nat.le_of_lt_succ (mem_range.mp hb)
  · change 1 * (1 + 4 * (n + 0)) < 16 * n
    omega
  · change 16 * n ≤ 32 * 1 * n
    omega
  · rw [hp]
    have hn' : (A : ℝ) * 36 + 1 < n := by exact_mod_cast hn
    linarith
  · rw [hv, hs, polynomialSwitch4_of_le (by norm_num) (by norm_num)]
    simpa only [sub_zero, mul_one] using div_pos (rate_pos n) (by norm_num : (0 : ℝ) < 4)
  · intro x
    change (((rate n / 4) • (1 : Matrix (ZMod P) (ZMod P) ℝ)) *ᵥ 1) x ≤ 1
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have hr : rate n ≤ 1 := by
      unfold rate
      have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h2)
    simpa only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] using
      (by linarith : rate n / 4 ≤ (1 : ℝ))
  · intro ζ Lh Lρ
    exact B.initialComputedPrecisionMoment_first_final_le (by change (0 : ℝ) ≤ A; positivity)
      rfl H (16 * n) n 0 0 (by omega)
      (fun bin hb => by
        change bin ∈ range (n + 1) at hb
        rw [he]
        exact Nat.le_of_lt_succ (mem_range.mp hb))
      r (by change 0 ≤ rate 0; exact (rate_pos 0).le) rfl rfl rfl
      threeRoles [1] [2, 3] coefficient ζ Lh Lρ
  · exact hA B rfl rfl (16 * n) n 0 0 (by omega) rfl rfl
      (by change 1 * (1 + 4 * (n + 0)) < 16 * n; omega)
      (by change 16 * n ≤ 32 * 1 * n; omega) (by omega) hP H (by omega) r
      (by rw [hrank]; decide) rfl rfl hC threeRoles [1] [2, 3]

-- The combined first-coordinate charge precedes the field and every depth/budget.
-- Every bin shares the horizon; precision is positive and the supported base is nonzero.
-- This is the numerical certificate, not joint recursive availability.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (coefficient floor cap C Cp : ℝ) (hf : 0 < floor) :
    ∃ A : ℕ, ∀ n : ℕ, A * 36 + 1 < n →
      ∃ P, ∃ _ : Fact P.Prime, ∃ H : Horizon P,
      let B : BudgetData HP P := {uniformData HP P n with rankCharge := A}
      let r := uniformRequest HP P
      H.maxExponent = n ∧ B.bins = range (n + 1) ∧ B.base 0 0 = 1 ∧
      0 < B.requestPrecision (16 * n) r ∧
      ∀ ζ Lh Lρ : ℝ,
        B.initialComputedFirstCoordinateReserve (16 * n) n r threeRoles 0 0 [1] [2, 3]
          coefficient ζ Lh Lρ floor cap C Cp ≤
          ((2 : ℝ) ^ (-B.requestPrecision (16 * n) r)) ^ 4 := by
  obtain ⟨A, hA⟩ := BudgetData.initialComputedFirstCoordinateReserve_exists_charge HP 16
    coefficient floor cap C Cp hf
  refine ⟨A, ?_⟩
  intro n hn
  obtain ⟨P, hprime, _, hP, H, he, _⟩ := exists_bounded_depth_prime n 0 (by positivity)
  let : Fact P.Prime := ⟨hprime⟩
  let B : BudgetData HP P := {uniformData HP P n with rankCharge := A}
  let r := uniformRequest HP P
  have hrank : r.task.rank = 36 := by
    norm_num [r, uniformRequest, HierarchyTask.rank, BoundedRowTask.localTask,
      CorrectionRowTask.rank, PilotRowTask.rank, PilotTask.rank]
  have hp : B.requestPrecision (16 * n) r = (n : ℝ) - A * 36 := by
    rw [B.requestPrecision_grid (16 * n) 0 0 r rfl rfl, hrank]
    dsimp only [B, uniformData]
    push_cast
    ring
  have hpositive : 0 < B.requestPrecision (16 * n) r := by
    rw [hp]
    have hn' : (A : ℝ) * 36 + 1 < n := by exact_mod_cast hn
    linarith
  refine ⟨P, inferInstance, H, he, rfl, ?_, hpositive, ?_⟩
  · simp [uniformData]
  · intro ζ Lh Lρ
    exact hA B rfl rfl rfl rfl (16 * n) n 0 0 (by omega) rfl
      (by change 1 * (1 + 4 * (n + 0)) < 16 * n; omega)
      (by change 16 * n ≤ 32 * 1 * n; omega) (by omega) hP H
      (by omega) (by omega) r threeRoles [1] [2, 3] rfl rfl rfl hpositive.le
      (by intro x y; by_cases h : x = y <;> simp [B, uniformData, h])
      (by change (1 : Matrix (ZMod P) (ZMod P) ℝ) *ᵥ 1 ≤ 1; simp)
      ζ Lh Lρ

-- A full-horizon nonzero semantic client of the actual reserve. Successful own-request
-- children remain an explicit hypothesis; this checks the assembled consumer without
-- claiming simultaneous recursive availability or paying the other three statistics.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → ℕ)
    (ζ floor coefficient Lh Lρ : ℝ) (hfloor : 0 < floor)
    (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (D : ℕ → ℕ → Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)
    (hzero : ∀ bin, D bin 0 = 0)
    (ih : ∀ bin ∈ range 3, ∀ m < 16, 0 < m →
      let B : BudgetData HP 5 := {data HP with bins := range 3}
      let r := request HP
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (BudgetData.midpoint r) r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some (D bin m) ∧
      rootDistPow 4 5 Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin m)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R)
    (cap Cdecoder Cpre : ℝ) :
    let B : BudgetData HP 5 := {data HP with bins := range 3}
    let M := 16
    let n := 2
    let r := request HP
    let R := threeRoles
    let ks := 0
    let ka := 0
    let ku := 0
    let bin := 0
    let ss : List (ZMod 5) := [1]
    let st : List (ZMod 5) := [2, 3]
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ W,
        (List.range (Nat.log2 M + 1)).mapM (fun i =>
          B.complete M r (B.binPreparation bin r (F (i + 1)))
            (dyadicSlack (Nat.log2 M + 1) i)) = some W →
        let a := fun j noise ν =>
          B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
            ζ Lh Lρ j noise ν ^ (4⁻¹ : ℝ)
        let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
          (4⁻¹ : ℝ) * |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
            (2 : ℝ) ^ (-B.rankCharge)
        let S := (32 : ℝ) ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r) *
          (2 : ℝ) ^ (-(B.rankCharge * r.task.rank))
        let x := 2 * (K * (4 * ∑' h, LogSpaceEstimation.scaleMajorant h) + S)
        B.initialFourMaxReserve M bin ka ζ floor r R ks ku ss st B.base F W cap
          Cdecoder Cpre ≤
          BudgetData.initialSeparatedReserve HP Cdecoder Cpre
            ((8 : ℝ) ^ (4⁻¹ : ℝ) * x * floor / 511 +
              ∑ j ∈ range (Nat.log2 M + 1), dyadicFloor floor (Nat.log2 M + 1) j *
                (a j false 1 + (a j true 0 + a j true 1)))
            ((8 : ℝ) ^ (4⁻¹ : ℝ) * x +
              (a (Nat.log2 M) false 1 + (a (Nat.log2 M) true 0 + a (Nat.log2 M) true 1)))
            (((8 : ℝ) ^ (4⁻¹ : ℝ) * x * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 +
              ∑ j ∈ range (Nat.log2 M + 1),
              (((2 + 256 / dyadicFloor floor (Nat.log2 M + 1) j) /
                (compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ)) ^ (4⁻¹ : ℝ)) *
              ∑ i ∈ Ico j (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) *
                a i false 1) +
              ∑ i ∈ range (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) *
                (a i true 0 + a i true 1))
            (64 * (8 * x ^ 4 * (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
                ((HP.K + 1) * floor ^ 4)) / 63 +
              ∑ j ∈ range (Nat.log2 M + 1),
                (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
                  ((compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ) *
                    dyadicFloor floor (Nat.log2 M + 1) j ^ 4)) *
                ((a j false 1 ^ 4) + (a j true 0 ^ 4 + a j true 1 ^ 4)))) := by
  dsimp only
  let B : BudgetData HP 5 := {data HP with bins := range 3}
  obtain ⟨groups, hrun, hp⟩ := B.initial_compressed_precision_reserve 16 (by decide) 2
    rfl rfl rfl rfl (by norm_num [B, data]) (⟨2, 4, by decide, by decide⟩ : Horizon 5)
    (by decide) (request HP) threeRoles 0 0 [1] [2, 3] rfl rfl (by decide)
    (by intro x y; by_cases h : x = y <;> simp [B, data, base, h])
    (by simp [B, data, base]) exponent ζ floor D hzero coefficient ih 0 0 le_rfl rfl
    hLh hLρ hh hρ (by decide) hfloor (by norm_num [B, data]) rfl cap Cdecoder Cpre
  refine ⟨groups, hrun, ?_⟩
  intro W hW
  exact (hp W hW).2.2 (by decide) (by norm_num [B, data])
    (by norm_num [B, data]) (by decide) (by decide)

-- Literal active/equal/zero endpoint budgets on both sides of the terminal grid.
-- The charge is fixed before either exponent varies.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ks k : ℕ) :
    let B : BudgetData HP 5 := {data HP with rankCharge := 7}
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) := {uniformRequest HP 5 with
      source := gridChannel 0 ks [1]
      terminal := gridChannel 2 (k + 1) [2, 3]}
    ∀ bin ∈ ({k, k + 2} : Finset ℕ),
      LogSpaceEstimation.lastBudget 20 4 B.slack (B.sampleScale r (some bin)) = 15 ∧
      LogSpaceEstimation.lastBudget 20 8 B.slack (B.sampleScale r (some bin)) = 12 ∧
      LogSpaceEstimation.lastBudget 20 1 B.slack (B.sampleScale r (some bin)) =
        LogSpaceEstimation.lastBudget 20 2 B.slack (B.sampleScale r (some bin)) ∧
      LogSpaceEstimation.lastBudget 0 4 B.slack (B.sampleScale r (some bin)) = 0 ∧
      ∀ e ∈ ({4, 8} : Finset ℕ),
        let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
          r.source (BudgetData.midpoint r) r.terminal (B.binRate bin)
        (2 : ℝ) ^ (4 * |(bin : ℝ) - (k + 1 : ℕ)|) *
            (2 : ℝ) ^ (-B.requestPrecision
              (LogSpaceEstimation.lastBudget 20 e B.slack (B.sampleScale r (some bin)))
              Q.direct) ≤
          (2 : ℝ) ^ (-B.requestPrecision 20 r) * (2 : ℝ) ^ (-B.rankCharge) *
            (2 : ℝ) ^ (25 * (4 : ℝ) / (8 * B.slack)) ∧
          25 * (4 : ℝ) / (8 * B.slack) < 6 * 4 := by
  dsimp only
  let B : BudgetData HP 5 := {data HP with rankCharge := 7}
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) := {uniformRequest HP 5 with
    source := gridChannel 0 ks [1]
    terminal := gridChannel 2 (k + 1) [2, 3]}
  intro bin hb
  have hscale : (B.sampleScale r (some bin)).natAbs = 4 := by
    rw [B.sampleScale_grid r (k + 1) bin rfl rfl]
    simp only [mem_insert, mem_singleton] at hb
    rcases hb with hbin | hbin <;> subst bin
    · have he : 4 * (((k + 1 : ℕ) : ℤ) - k) = 4 := by omega
      rw [he]; rfl
    · have he : 4 * (((k + 1 : ℕ) : ℤ) - (k + 2 : ℕ)) = -4 := by omega
      rw [he]; rfl
  have hf : LogSpaceEstimation.lastBudget 20 4 B.slack (B.sampleScale r (some bin)) = 15 := by
    norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
      hscale, show B.slack = 1 from rfl]
  have hc : LogSpaceEstimation.lastBudget 20 8 B.slack (B.sampleScale r (some bin)) = 12 := by
    norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
      hscale, show B.slack = 1 from rfl]
  refine ⟨hf, hc, ?_, ?_, ?_⟩
  · change LogSpaceEstimation.lastBudget 20 1 B.slack (B.sampleScale r (some bin)) =
      LogSpaceEstimation.lastBudget 20 2 B.slack (B.sampleScale r (some bin))
    norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
      hscale, show B.slack = 1 from rfl]
  · exact Nat.zero_sub _
  · intro e he
    exact B.requestPrecision_initial_active_pay (by norm_num [B]) rfl 20 4 ks (k + 1)
      bin e r rfl rfl rfl (by rw [hf, show 2 * 4 = 8 from rfl, hc]; decide) he

-- Exhaustion of just the coarse endpoint is literal, and equal positive pairs cancel.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    LogSpaceEstimation.lastBudget 2 1 (data HP).slack
      ((data HP).sampleScale (request HP) (some 0)) = 1 ∧
    LogSpaceEstimation.lastBudget 2 2 (data HP).slack
      ((data HP).sampleScale (request HP) (some 0)) = 0 ∧
    (data HP).pairedSample (fun _ _ => none) 20 1 (.pilotInput ⟨0, HP.k_pos⟩)
      {request HP with terminal := gridChannel 2 1 [2, 3]} (some 0) = some 0 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
      BudgetData.sampleScale, data, request, gridChannel, rate]
  · norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
      BudgetData.sampleScale, data, request, gridChannel, rate]
  · have hscale := (data HP).sampleScale_grid
      {request HP with terminal := gridChannel 2 1 [2, 3]} 1 0 rfl rfl
    norm_num only [Int.cast_ofNat, Int.cast_zero, sub_zero, mul_one] at hscale
    unfold BudgetData.pairedSample
    rw [hscale]
    norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
      show (data HP).slack = 1 from rfl]

-- The centered actual group consumer also accepts an arbitrary signed coefficient
-- at exhaustion; it demands no positive-budget child or reset-right call.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (coefficient : ℝ) :
    ∃ F G,
      (data HP).completedGroup (fun n q => if n < 1 then
        (data HP).compressedHistory (fun _ => 0) (HP.η / 4) (HP.η / 4) n q else none)
        1 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) = some F ∧
      (data HP).completedGroup (fun n q => if n < 1 then (data HP).evaluate n q else none)
        1 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) = some G ∧
      rowNormPow 4 5 (request HP).source.rate
        (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
        (fun σ y => (request HP).usage.retains (channels (data HP).padding) σ y)
        (fun σ x y => (F - G) σ x y - rowSliceMean
          (X 0 (side 5 0) (CopyPadding.identifier (data HP).padding [1]))
          (Y 2 (side 5 0) (CopyPadding.identifier (data HP).padding [2, 3]))
          (F - G) x y) ≤ 0 := by
  obtain ⟨F, G, hf, hg, hb, _⟩ :=
    (data HP).completedGroup_initial_compressed_centered_precision (fun _ => 0)
      (HP.η / 4) (HP.η / 4) 1 1 (by decide) (by simp [data]) (request HP)
      0 2 (by decide) 0 0 [1] [2, 3] rfl rfl (fun _ _ => 0) (fun _ => rfl) coefficient
      (by intro bin hb; dsimp only; intro _ n _ hn hnpos; omega)
  refine ⟨F, G, hf, hg, ?_⟩
  simpa only [(data HP).initialRootGroupCharge_eq_zero_of_le 1 1 (request HP)
    coefficient le_rfl, mul_zero, Nat.cast_ofNat] using hb

-- The sharp allocation envelope also cancels all exhausted pairs literally.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (coefficient : ℝ) :
    (data HP).initialActiveRootGroupCharge 1 1 (request HP) 0 coefficient = 0 := by
  have hf (bin : ℕ) : LogSpaceEstimation.lastBudget 1 1 (data HP).slack
      ((data HP).sampleScale (request HP) (some bin)) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  have hc (bin : ℕ) : LogSpaceEstimation.lastBudget 1 (2 * 1) (data HP).slack
      ((data HP).sampleScale (request HP) (some bin)) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  simp only [BudgetData.initialActiveRootGroupCharge, hf, hc, ↓reduceIte,
    sum_const_zero, mul_zero]

-- Actual budget-one direct error is nonzero, and its reset-right call succeeds.
-- Only the active top bin demands IH; the unused fine bin is not called at budget one.
private theorem positive_direct_precision (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let ζ := min HP.η (1 / 10000) / 4
    let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
      (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
      ((data HP).binRate 0)
    let c := (2 : ℝ) ^ ((data HP).requestPrecision 1 Q.direct)
    (data HP).compressedBin 1 0 0 ζ ζ Q.direct = some 0 ∧
    rootDistPow 4 5 Q.direct.source.rate
      (fun σ x => Q.direct.source.retains (channels (data HP).padding) σ x)
      (fun σ y => Q.direct.usage.retains (channels (data HP).padding) σ y) 0
      (denseChild (data HP).padding id Q.direct ((data HP).cutoff 0)
        ((data HP).auxiliary 0) HP.ρ HP.K (data HP).base) ≤
      c ^ 4 * ((2 : ℝ) ^ (-(data HP).requestPrecision 1 Q.direct)) ^ 4 ∧
    denseChild (data HP).padding id Q.direct ((data HP).cutoff 0)
      ((data HP).auxiliary 0) HP.ρ HP.K (data HP).base = (fun _ => base) := by
  dsimp only
  let ζ := min HP.η (1 / 10000) / 4
  let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
    (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
    ((data HP).binRate 0)
  let c := (2 : ℝ) ^ ((data HP).requestPrecision 1 Q.direct)
  have hζ : 0 < ζ := div_pos (lt_min HP.η_pos (by norm_num)) (by norm_num)
  have hd : (data HP).compressedBin 1 0 0 ζ ζ Q.direct = some 0 := by
    simpa only [Q, HierarchyTask.rawRequests, request, data, gridChannel, rate, pow_zero,
      inv_one, min_self] using compressed_one HP (.baseNormalized 0 0) ζ hζ
      (by dsimp only [ζ]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have ht : denseChild (data HP).padding id Q.direct ((data HP).cutoff 0)
      ((data HP).auxiliary 0) HP.ρ HP.K (data HP).base = (fun _ => base) := by
    funext σ x y
    have hq : Q.direct = {request HP with task := .baseNormalized 0 0} := by
      simp [Q, HierarchyTask.rawRequests, request, data, gridChannel, rate]
    rw [hq, denseChild_congr_task]
    exact top_dense HP σ x y
  have hroot : rootDistPow 4 5 Q.direct.source.rate
      (fun σ x => Q.direct.source.retains (channels (data HP).padding) σ x)
      (fun σ y => Q.direct.usage.retains (channels (data HP).padding) σ y) 0
      (denseChild (data HP).padding id Q.direct ((data HP).cutoff 0)
        ((data HP).auxiliary 0) HP.ρ HP.K (data HP).base) ≤
      c ^ 4 * ((2 : ℝ) ^ (-(data HP).requestPrecision 1 Q.direct)) ^ 4 := by
    rw [ht, ← mul_pow]
    have hc : c * (2 : ℝ) ^ (-(data HP).requestPrecision 1 Q.direct) = 1 := by
      dsimp only [c]
      rw [← Real.rpow_add (by norm_num)]
      simp
    rw [hc, one_pow]
    have hs : Q.direct.source = gridChannel 0 0 [1] := rfl
    have hu : Q.direct.usage = gridChannel 2 0 [2, 3] := by
      simp [Q, HierarchyTask.rawRequests, request, data, gridChannel, rate]
    rw [hs, hu]
    simp only [rootDistPow, rowNormPow, data, full, filter_true]
    norm_num only [gridChannel, rate, base, Matrix.one_apply, Pi.zero_apply,
      zero_sub, abs_neg, Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0),
      apply_ite (fun t : ℝ => |t ^ (4⁻¹ : ℝ)| ^ 4)]
    norm_num [apply_ite abs, ite_pow]
  exact ⟨hd, hroot, ht⟩

private theorem positive_centered_group (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let ζ := min HP.η (1 / 10000) / 4
    let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
      (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
      ((data HP).binRate 0)
    let c := (2 : ℝ) ^ ((data HP).requestPrecision 1 Q.direct)
    (data HP).compressedBin 1 0 0 ζ ζ Q.direct = some 0 ∧
    (∀ σ, |(0 : ℝ) - denseChild (data HP).padding id Q.direct ((data HP).cutoff 0)
      ((data HP).auxiliary 0) HP.ρ HP.K (data HP).base σ 0 0| = 1) ∧
    ∃ F G,
      (data HP).completedGroup (fun n q => if n < 2 then
        (data HP).compressedHistory (fun _ => 0) ζ ζ n q else none)
        2 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) = some F ∧
      (data HP).completedGroup (fun n q => if n < 2 then (data HP).evaluate n q else none)
        2 1 (.pilotInput ⟨0, HP.k_pos⟩) (request HP) = some G ∧
      rowNormPow 4 5 (request HP).source.rate
        (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
        (fun σ y => (request HP).usage.retains (channels (data HP).padding) σ y)
        (fun σ x y => (F - G) σ x y - rowSliceMean
          (X 0 (side 5 0) (CopyPadding.identifier (data HP).padding [1]))
          (Y 2 (side 5 0) (CopyPadding.identifier (data HP).padding [2, 3]))
          (F - G) x y) ≤
        (data HP).initialCenteredGroupCharge 2 1 (request HP) c ∧
      rowNormPow 4 5 (request HP).source.rate
        (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
        (fun σ y => (request HP).usage.retains (channels (data HP).padding) σ y)
        (fun σ x y => (F - G) σ x y - rowSliceMean
          (X 0 (side 5 0) (CopyPadding.identifier (data HP).padding [1]))
          (Y 2 (side 5 0) (CopyPadding.identifier (data HP).padding [2, 3]))
          (F - G) x y) ≤
        ((2 : ℝ) ^ (-(data HP).requestPrecision 2 (request HP)) * (64 : ℝ)⁻¹ ^ 1) ^ 4 *
          (data HP).initialActiveRootGroupCharge 2 1 (request HP) 0 c := by
  dsimp only
  let ζ := min HP.η (1 / 10000) / 4
  let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
    (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
    ((data HP).binRate 0)
  let c := (2 : ℝ) ^ ((data HP).requestPrecision 1 Q.direct)
  obtain ⟨hd, hroot, ht⟩ := positive_direct_precision HP
  refine ⟨hd, ?_, ?_⟩
  · intro σ
    rw [ht]
    norm_num [base]
  · obtain ⟨F, G, hf, hg, hb, ha⟩ :=
      (data HP).completedGroup_initial_compressed_centered_precision (fun _ => 0)
        ζ ζ 2 1 (by decide) (by simp [data]) (request HP) 0 2 (by decide)
        0 0 [1] [2, 3] rfl rfl (fun _ _ => 0) (fun _ => rfl) c (by
          intro bin hb
          dsimp only
          intro hne n _ hn hnpos
          have hbin : bin = 0 := by
            have hb' : bin = 0 ∨ bin = 1 := by simpa [data] using hb
            rcases hb' with h | h
            · exact h
            · subst bin
              exfalso
              have hscale := (data HP).sampleScale_grid (request HP) 0 1 rfl rfl
              norm_num at hscale
              rw [hscale] at hne
              norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
                show (data HP).slack = 1 from rfl] at hne
          subst bin
          have hn1 : n = 1 := by omega
          subst n
          exact ⟨hd, hroot, right_available HP ζ 1 (by decide)⟩)
    refine ⟨F, G, hf, hg, ?_, ha 0 0 (by norm_num [data]) rfl rfl rfl rfl⟩
    simpa only [BudgetData.initialCenteredGroupCharge, Nat.cast_ofNat] using hb

-- The same nonzero actual child error now feeds the literal two-group first-noise
-- payment, including the exhausted initial group. This fixture's stationary centered
-- noise is zero; the separate two-atom test below checks nonzero correlated noise.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let ζ := min HP.η (1 / 10000) / 4
    let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
      (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
      ((data HP).binRate 0)
    let c := (2 : ℝ) ^ ((data HP).requestPrecision 1 Q.direct)
    ∃ groups,
      (List.range 2).mapM (fun i => (data HP).completedGroup (fun n q => if n < 2 then
        (data HP).compressedHistory (fun _ => 0) ζ ζ n q else none)
        2 (dyadicSlack 2 i) (.pilotInput ⟨0, HP.k_pos⟩) (request HP)) = some groups ∧
      rowNormPow 4 5 (request HP).source.rate
        (retainedMask threeRoles.source (side 5 0) (data HP).padding [1])
        (retainedMask threeRoles.terminal (side 5 0) (data HP).padding [2, 3])
        (actualNoiseEntry threeRoles.source threeRoles.terminal (side 5 0) (side 5 0)
          (side 5 0) (data HP).padding [1] [2, 3] 0 base
          (firstSignalIncrement (fun p σ x y =>
            ((groups.take p).map (fun T => T σ x y)).sum) 0 (fun _ _ _ _ => 0)) 0 0 1) ≤
        (data HP).initialComputedBoundedCenteredNoise 2 (request HP) threeRoles
          0 0 [1] [2, 3] c 1 := by
  dsimp only
  obtain ⟨_, _, A₁, C₁, hA₁, hC₁, hb₁, _⟩ := positive_centered_group HP
  let ζ := min HP.η (1 / 10000) / 4
  have hz (e bin : ℕ) (he : 2 ≤ e) : LogSpaceEstimation.lastBudget 2 e (data HP).slack
      ((data HP).sampleScale (request HP) (some bin)) = 0 :=
    Nat.sub_eq_zero_of_le (he.trans (le_max_left _ _))
  obtain ⟨A₀, C₀, hA₀, hC₀, hb₀, _⟩ :=
    (data HP).completedGroup_initial_compressed_centered_precision (fun _ => 0)
      ζ ζ 2 2 (by decide) (by simp [data]) (request HP) 0 2 (by decide)
      0 0 [1] [2, 3] rfl rfl (fun _ _ => 0) (fun _ => rfl) 0 (by
        intro bin _
        dsimp only
        intro _ n hn _ hp
        simp only [hz 2 bin le_rfl, show 2 * 2 = 4 from rfl, hz 4 bin (by decide),
          mem_insert, mem_singleton] at hn
        omega)
  let A := fun i => if i = 0 then A₀ else A₁
  let C := fun i => if i = 0 then C₀ else C₁
  have hA (i : ℕ) (hi : i < Nat.log2 2 + 1) : (data HP).completedGroup
      (fun n q => if n < 2 then (data HP).compressedHistory (fun _ => 0) ζ ζ n q else none)
      2 (dyadicSlack (Nat.log2 2 + 1) i) (.pilotInput ⟨0, HP.k_pos⟩) (request HP) =
        some (A i) := by
    have hi' : i < 2 := by simpa using hi
    interval_cases i
    · simpa [A, dyadicSlack] using hA₀
    · simpa [A, dyadicSlack, ζ] using hA₁
  have hC (i : ℕ) (hi : i < Nat.log2 2 + 1) : (data HP).completedGroup
      (fun n q => if n < 2 then (data HP).evaluate n q else none)
      2 (dyadicSlack (Nat.log2 2 + 1) i) (.pilotInput ⟨0, HP.k_pos⟩) (request HP) =
        some (C i) := by
    have hi' : i < 2 := by simpa using hi
    interval_cases i
    · simpa [C, dyadicSlack] using hC₀
    · simpa [C, dyadicSlack] using hC₁
  let groups := (List.range 2).map A
  have hg : (List.range (Nat.log2 2 + 1)).mapM (fun i => (data HP).completedGroup
      (fun n q => if n < 2 then (data HP).compressedHistory (fun _ => 0) ζ ζ n q else none)
      2 (dyadicSlack (Nat.log2 2 + 1) i) (.pilotInput ⟨0, HP.k_pos⟩) (request HP)) =
        some groups := by
    change _ = some ((List.range (Nat.log2 2 + 1)).map A)
    apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact fun i hi => hA i (List.mem_range.mp hi)
  refine ⟨groups, hg, ?_⟩
  apply (data HP).initial_compressed_centered_first_noise (fun _ => 0) ζ ζ 2 (by decide)
    (by simp [data]) (request HP) threeRoles 0 0 [1] [2, 3] rfl rfl A C _ hA hC
    _ groups hg (by intro x y; by_cases h : x = y <;> simp [data, base, h])
    (side 5 0) (fun _ _ _ _ => 0) 1 (by decide)
  intro i hi
  simp only [show { request HP with usage := (request HP).terminal } = request HP from rfl]
  have hi' : i < 2 := by simpa using hi
  interval_cases i
  · have hz' := (data HP).initialRootGroupCharge_eq_zero_of_le 2 2 (request HP) 0 le_rfl
    rw [hz', mul_zero] at hb₀
    norm_num [A, C, dyadicSlack]
    rw [BudgetData.initialCenteredGroupCharge,
      (data HP).initialRootGroupCharge_eq_zero_of_le 2 2 (request HP) _ le_rfl, mul_zero]
    simpa [threeRoles, request, gridChannel, CorrectionRowTask.Channel.retains,
      channels, semanticSide_grid, retainedMask, X, Y, rowNormPow, rowSliceMean] using hb₀
  · simpa [A, C, dyadicSlack, threeRoles, request, gridChannel,
      CorrectionRowTask.Channel.retains, channels, semanticSide_grid, retainedMask,
      X, Y, rowNormPow, rowSliceMean] using hb₁

-- Fully correlated two-atom noise receives a geometric Minkowski payment, rather
-- than a sum of component moments. Both the exact moment and its paid bound are checked.
example :
    let Z := fun (σ : Fin 2) (_ _ : Unit) => if σ = 0 then (1 : ℝ) else -1
    rowNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
      (fun σ x y => ∑ i ∈ range 2, (1 / 2 : ℝ) ^ (i + 1) * Z σ x y) =
        (3 / 4 : ℝ) ^ 4 ∧
    rowNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
      (fun σ x y => ∑ i ∈ range 2, (1 / 2 : ℝ) ^ (i + 1) * Z σ x y) ≤
        (∑ i ∈ range 2, (1 / 2 : ℝ) ^ (i + 1)) ^ 4 := by
  dsimp only
  constructor
  · norm_num [rowNormPow, Fin.sum_univ_two, expect_eq_sum_div_card, sum_range_succ]
  · have h := rowNormPow_sum_le_pow_sum
      (X := fun (_ : Fin 2) (_ : Unit) => True) (by decide : 4 ≠ 0)
      (by norm_num : (0 : ℝ) ≤ 1 * 1) (fun (_ : Fin 2) (_ : Unit) => True)
      (range 2) (fun _ σ (_ _ : Unit) => if σ = 0 then (1 : ℝ) else -1)
      (fun i => (1 / 2 : ℝ) ^ (i + 1)) (fun _ => 1)
      (by intros; positivity) (by intros; norm_num)
      (by intros; norm_num [rowNormPow, Fin.sum_univ_two, expect_eq_sum_div_card])
    simpa only [mul_one] using h

-- Choose the charge before the field, varying admissible horizon, positive parent
-- precision and whole bin family. No joint recursive availability is inferred.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (L : ℕ) (coefficient : ℝ) :
    ∃ A : ℕ, ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P),
      B.binCap = 1 → B.rankCharge = A → B.binRate = rate →
      ∀ (H : Horizon P) (n M j ks ka : ℕ), n ≤ L → B.bins = range (n + 1) →
      n ≤ H.maxExponent → ka ≤ n → j < Nat.log2 M + 1 →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
      r.source.rate = rate ks → r.terminal.rate = rate ka →
      r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) →
      0 < B.requestPrecision M { r with usage := r.terminal } →
      (∀ x y, 0 ≤ B.base x y) → ∀ (R : RoleProfile 3) (ss st : List (ZMod P)),
      B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient 0 0 0 j true 0 ≤
        8 * (((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
          (1 / 2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 +
          B.initialRelativeNoiseBudget M r R.source R.terminal R.source_terminal
            ks ka ss st B.base (j + 1)) := by
  obtain ⟨A, hA⟩ := BudgetData.initialComputedPrecisionMoment_firstNoise_exists_charge
    (HP := HP) 1 coefficient L
  refine ⟨A, ?_⟩
  intro P _ B hcap hcharge hrate H n M j ks ka hn hbins hH hka hj r hs ht htask hp hbase
    R ss st
  exact hA B hcap hcharge hrate H M j ks ka hj (hka.trans hn) (hka.trans hH)
    (fun bin hb => by rw [hbins, mem_range] at hb; omega)
    (by rw [hbins, card_range]; omega) r hs ht htask hp.le hbase R ss st n 0 0 0

-- Exhausted actual endpoints still have exactly zero centered payment, independently
-- of the signed error coefficient and the chosen structural charge.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (coefficient : ℝ) :
    (data HP).initialCenteredGroupCharge 1 1 (request HP) coefficient = 0 := by
  rw [BudgetData.initialCenteredGroupCharge,
    (data HP).initialRootGroupCharge_eq_zero_of_le 1 1 (request HP) coefficient le_rfl,
    mul_zero]

-- The charge-first family has concrete positive precision at every requested p>0.
-- Whole bin families of depths zero, one and two use the same charge and field.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (coefficient : ℝ) :
    ∃ A : ℕ, ∀ n ≤ 2, ∀ p : ℕ, 0 < p →
      let B : BudgetData HP 5 := {data HP with bins := range (n + 1), rankCharge := A}
      let M := 16 * (36 * A + p)
      B.requestPrecision M (request HP) = p ∧
      ∀ j < Nat.log2 M + 1,
        B.initialComputedPrecisionMoment M n (request HP) threeRoles 0 0 [1] [2, 3]
          coefficient 0 0 0 j true 0 ≤
        8 * (((2 : ℝ) ^ (-(p : ℝ)) *
          (1 / 2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 +
          B.initialRelativeNoiseBudget M (request HP) threeRoles.source threeRoles.terminal
            threeRoles.source_terminal 0 0 [1] [2, 3] B.base (j + 1)) := by
  obtain ⟨A, hA⟩ := BudgetData.initialComputedPrecisionMoment_firstNoise_exists_charge
    (HP := HP) 16 coefficient 2
  refine ⟨A, ?_⟩
  intro n hn p hp
  dsimp only
  let B : BudgetData HP 5 := {data HP with bins := range (n + 1), rankCharge := A}
  let M := 16 * (36 * A + p)
  have hrank : (request HP).task.rank = 36 := by
    norm_num [request, HierarchyTask.rank, BoundedRowTask.localTask,
      CorrectionRowTask.rank, PilotRowTask.rank, PilotTask.rank]
  have hprecision : B.requestPrecision M (request HP) = p := by
    rw [B.requestPrecision_grid M 0 0 (request HP) rfl rfl, hrank]
    dsimp only [B, M, data]
    push_cast
    ring
  refine ⟨hprecision, ?_⟩
  intro j hj
  have h := hA B rfl rfl rfl supportHorizon M j 0 0 hj (by decide) (by decide)
    (fun bin hb => by
      change bin ∈ range (n + 1) at hb
      rw [mem_range] at hb
      change bin ≤ 2
      omega)
    (by change (range (n + 1)).card ≤ 2 + 1; rw [card_range]; omega)
    (request HP) rfl rfl rfl (by
      change 0 ≤ B.requestPrecision M (request HP)
      rw [hprecision]
      positivity)
    (by intro x y; by_cases h : x = y <;> simp [B, data, base, h])
    threeRoles [1] [2, 3] n 0 0 0
  simpa only [show { request HP with usage := (request HP).terminal } = request HP from rfl,
    hprecision] using h

-- The actual nonzero direct-child error also enters the unbounded normalized lane.
-- Its reset-right call is executed separately; bin one is unused and needs no child.
open Cslib.RowCompression NormalizedMoments in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let ζ := min HP.η (1 / 10000) / 4
    let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
      (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
      ((data HP).binRate 0)
    let c := (2 : ℝ) ^ ((data HP).requestPrecision 1 Q.direct)
    ∃ groups,
      (List.range 2).mapM (fun i => (data HP).completedGroup (fun n q => if n < 2 then
        (data HP).compressedHistory (fun _ => 0) ζ ζ n q else none)
        2 (dyadicSlack 2 i) (.pilotInput ⟨0, HP.k_pos⟩) (request HP)) = some groups ∧
      rowNormPow 4 5 (request HP).source.rate
        (retainedMask threeRoles.source (side 5 0) (data HP).padding [1])
        (retainedMask threeRoles.terminal (side 5 0) (data HP).padding [2, 3])
        (actualNoiseEntry threeRoles.source threeRoles.terminal (side 5 0) (side 5 0)
          (side 5 0) (data HP).padding [1] [2, 3] 0 base
          (firstSignalIncrement (fun p σ x y =>
            ((groups.take p).map (fun T => T σ x y)).sum) 0 (fun _ _ _ _ => 0)) 0 0 1) ≤
        (data HP).initialComputedNormalizedNoise 2 (request HP) threeRoles 0 0 [1] [2, 3] c 1 := by
  dsimp only
  obtain ⟨hd, hroot, _⟩ := positive_direct_precision HP
  let ζ := min HP.η (1 / 10000) / 4
  let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
    (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
    ((data HP).binRate 0)
  let c := (2 : ℝ) ^ ((data HP).requestPrecision 1 Q.direct)
  have hp : 0 ≤ (data HP).requestPrecision 2 (request HP) := by
    rw [(data HP).requestPrecision_grid 2 0 0 (request HP) rfl rfl]
    norm_num [data]
  obtain ⟨groups, hg, hb⟩ := (data HP).initial_compressed_normalized_noise_consumer
    (by norm_num [data]) rfl supportHorizon (fun _ => 0) ζ ζ 2 (by decide)
    (by simp [data]) (request HP) threeRoles 0 0 [1] [2, 3] rfl rfl rfl (by decide)
    (fun bin hb => by
      have hh : bin = 0 ∨ bin = 1 := by simpa [data] using hb
      rcases hh with rfl | rfl <;> decide)
    hp (fun _ _ => 0) (fun _ => rfl) c (by
      intro i bin hb
      dsimp only
      intro hne m hm hlt hpos
      have hbin : bin = 0 := by
        have hh : bin = 0 ∨ bin = 1 := by simpa [data] using hb
        rcases hh with h | h
        · exact h
        · subst bin
          exfalso
          have hscale := (data HP).sampleScale_grid (request HP) 0 1 rfl rfl
          norm_num at hscale
          simp only [show { request HP with usage := (request HP).terminal } = request HP
            from rfl] at hne
          rw [hscale] at hne
          have hz (e : ℕ) : LogSpaceEstimation.lastBudget 2 e (data HP).slack (-4) = 0 := by
            norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff, data]
          simp only [hz] at hne
          exact hne rfl
      subst bin
      have hm1 : m = 1 := by omega
      subst m
      exact ⟨hd, hroot, right_available HP ζ 1 (by decide)⟩)
    (by intro x y; by_cases h : x = y <;> simp [data, base, h])
  exact ⟨groups, hg, hb (side 5 0) (fun _ _ _ _ => 0) 1 (by decide)⟩

-- The same two-atom noise is shared by every prefix. The full factor-28 tail is
-- unconditional and remains nonzero; the geometric bound is uniform in the horizon.
open Cslib.RowCompression NormalizedMoments in
example (m : ℕ) :
    let Z := fun (σ : Fin 2) (_ _ : Unit) => if σ = 0 then (1 : ℝ) else -1
    rowNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
      (fun σ x y => ∑ i ∈ range m, (28 : ℝ) ^ (m - i) *
        (1 / 16 : ℝ) ^ dyadicSlack m i * Z σ x y) ≤ (1792 / 57 : ℝ) ^ 4 := by
  dsimp only
  have h := rowNormPow_sum_le_pow_sum
    (X := fun (_ : Fin 2) (_ : Unit) => True) (by decide : 4 ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 1 * 1) (fun (_ : Fin 2) (_ : Unit) => True)
    (range m) (fun _ σ (_ _ : Unit) => if σ = 0 then (1 : ℝ) else -1)
    (fun i => (28 : ℝ) ^ (m - i) * (1 / 16 : ℝ) ^ dyadicSlack m i) (fun _ => 1)
    (by intros; positivity) (by intros; norm_num)
    (by intros; norm_num [rowNormPow, Fin.sum_univ_two, expect_eq_sum_div_card])
  simp only [mul_one] at h
  exact h.trans (pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity)
    (sum_propagation_mul_sixteenth_le m) 4)

open Cslib.RowCompression NormalizedMoments in
example :
    let Z := fun (σ : Fin 2) (_ _ : Unit) => if σ = 0 then (1 : ℝ) else -1
    rowNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
      (fun σ x y => ∑ i ∈ range 3, (28 : ℝ) ^ (3 - i) *
        (1 / 16 : ℝ) ^ dyadicSlack 3 i * Z σ x y) = (5271 / 1024 : ℝ) ^ 4 := by
  norm_num [rowNormPow, Fin.sum_univ_two, expect_eq_sum_div_card, sum_range_succ,
    dyadicSlack]

end PolynomialBudgetHistory
