/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of allocated initial-pilot calls)
import Complexity.Foundations.Probability.InitialPilotDetector

/-! Actual source-correlated RAW/score calls, including positive allocated walks. -/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace InitialPilotScoreRegression
private def roles : RoleProfile 3 := ⟨0, 1, 2, by decide, by decide, by decide⟩
private def horizon : Horizon 5 := ⟨1, 4, by decide, by decide⟩
private def base : Matrix (ZMod 5) (ZMod 5) ℝ := 1
private def binCutoff : ℝ → ℝ :=
  boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) (fun _ => 1) 1 0 (fun _ => 1)
private lemma binCutoff_base (x y : ZMod 5) : binCutoff (base x y) = base x y := by
  by_cases hxy : x = y
  · subst y
    norm_num [binCutoff, base, boundedRoutedBinCutoff, routedBinCutoff, binWeight,
      polynomialSwitch4_of_ge (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1)]
  · norm_num [binCutoff, base, Matrix.one_apply, hxy, boundedRoutedBinCutoff,
      routedBinCutoff, binWeight]
private def source (σ : Environment 5 3) (x : ZMod 5) : Prop :=
  X roles.source (side 5 1) (CopyPadding.identifier 1 [1]) σ x
private def request (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  ⟨.baseNormalized 0 0, gridChannel 0 1 [1], gridChannel 2 0 [2, 3], gridChannel 2 0 [2, 3]⟩
private lemma admissible (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    Admissible (request HP) := ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩
private lemma large_K (HP : FourthRootHierarchyParams 16 1 16 32 8) : 5 < HP.K := by
  have hg := HP.gate
  have hn : 0 ≤ 32 * (HP.k : ℝ) / HP.η :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) HP.η_pos.le
  have hk : (5 : ℝ) < HP.K := by linarith
  exact_mod_cast hk
private lemma dense (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (σ : Environment 5 3) (x y : ZMod 5) :
    denseChild 1 id (request HP) binCutoff (fun _ => 1) HP.ρ HP.K base σ x y = base x y := by
  have hx := source_nonempty 1 id (request HP) (admissible HP) (by decide)
    Function.injective_id horizon (s := 1) (by decide) rfl x
  rw [denseChild_eq 1 id (request HP) (admissible HP) binCutoff (fun _ => 1) HP.ρ HP.K base
    σ x y hx]
  have hg (T : Finset (ZMod 5)) (z : ZMod 5) :
      rowGate HP.ρ HP.K 1 base T z = 1 := by
    unfold rowGate
    rw [kthLargest_eq_zero_of_card_lt
      ((card_le_univ T).trans_lt (by simpa using large_K HP))]
    exact HP.ρ_one 0 HP.η_pos.le
  have ht (A : FrameChannel 5 4 1) (v : ZMod 5) : splitTerminal 1 id (request HP) A v := by
    change frameRetains 5 4 (semanticSide 5 (rate 0)) A (CopyPadding.identifier 1 [2, 3] v)
    rw [semanticSide_grid, show side 5 0 = 5 by norm_num [side]]
    exact full_retains A _
  have hu (A : FrameChannel 5 4 1) (v : ZMod 5) : splitUsage 1 id (request HP) A v := ht A v
  simp only [denseAtom, ht, ↓reduceIte, atomNormalizer, atomPrep, one_mul,
    hu, filter_true, Fintype.expect_const]
  norm_num only [request, gridChannel, rate, pow_zero, inv_one, one_pow]
  rw [hg]
  norm_num only [min_self, one_mul, div_one]
  norm_num
  exact binCutoff_base x y

private lemma raw_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (σ : Environment 5 3) (x y : ZMod 5) :
    initialPilotRaw HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base σ x y = base x y := by
  unfold initialPilotRaw
  have hr := usageRatio_grid 1 (gridChannel roles.terminal 0 [2, 3]) (request HP)
    0 0 rfl rfl y
  simp only [roles, Nat.max_self] at *
  change rate 0 * HierarchyTask.usageRatio (channels 1) (gridChannel 2 0 [2, 3])
    (request HP) y * denseChild 1 id (request HP) binCutoff (fun _ => 1) HP.ρ HP.K base σ x y = _
  rw [hr, dense]
  norm_num [side, rate]

-- Every finite positive walk computes the lower call; it stays nonconstant on the
-- original environment because source zero extension is part of the actual semantics.
private lemma walk_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (steps : ℕ) (σ : Environment 5 3) (x y : ZMod 5) :
    initialPilotWalk HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base steps σ x y =
      if source σ x then base x y else 0 := by
  unfold initialPilotWalk conditionalWalk
  have ht (τ : Environment 5 3) (w : ZMod 5) :
      Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3]) τ w := by
    simpa only [Y, show side 5 0 = 5 by norm_num [side]] using full_retains (τ roles.terminal) _
  simp only [mem_filter, mem_univ, true_and, ht, and_true]
  change (if _h : source σ x then _ else 0) = _
  split_ifs with hs
  · have he : (fun τ : RetainedPairSlice
        (X roles.source (side 5 1) (CopyPadding.identifier 1 [1]))
        (Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3])) x y =>
        initialPilotRaw HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base τ.val x y) =
          fun _ => base x y := by funext τ; exact raw_eq HP τ.val x y
    rw [he, RotationMap.walk_pow_const]
  · rfl

private lemma score_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (steps : ℕ) (σ : Environment 5 3) (x : ZMod 5) :
    initialPilotScore HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base steps σ x x =
      if source σ x then 1 else 0 := by
  have hδ : HP.δ₁ ≤ 1 := by
    have hθ := HP.θ_lt_θ₂.trans HP.θ₂_lt
    linarith [HP.δ₁_lt]
  have he := walk_eq HP steps σ
  unfold initialPilotScore PilotRowRecipe.score atomPrep
  simp only [he, rowGate, show rate 0 = 1 by norm_num [rate], div_one]
  have hcard : #{w : ZMod 5 | Y roles.terminal (side 5 0)
      (CopyPadding.identifier 1 [2, 3]) σ w} < HP.K :=
    (card_filter_le _ _).trans_lt (by simpa using large_K HP)
  have hrank : kthLargest HP.K
      {w | Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3]) σ w}
      (fun w => if source σ x then base x w else 0) = 0 :=
    kthLargest_eq_zero_of_card_lt hcard _
  rw [hrank]
  simp only [HP.ρ_one 0 HP.η_pos.le, mul_one]
  split_ifs
  · simpa only [base, Matrix.one_apply_eq, div_one] using HP.ϕ_one 1 hδ
  · simpa only [div_one] using HP.ϕ_zero 0 HP.δ₀_pos.le

private def frame : Frame 5 4 1 := Classical.choice inferInstance
private def seed (v : ZMod 5) : Environment 5 3 := fun role =>
  (FrameChannel.evalEquiv (P := 5) (H := 4) (r := 1) (CopyPadding.identifier 1 [1] 0)).symm
    (fun _ => if role = roles.source then v else 0, frame)

private lemma seed_eval (v : ZMod 5) :
    (seed v roles.source).eval (CopyPadding.identifier 1 [1] 0) = fun _ => v := by
  have he := congrArg Prod.fst
    ((FrameChannel.evalEquiv (P := 5) (H := 4) (r := 1)
      (CopyPadding.identifier 1 [1] 0)).apply_symm_apply
      (fun _ => v, frame))
  simpa only [seed, ↓reduceIte, FrameChannel.evalEquiv, Equiv.coe_fn_mk] using he

private lemma seed_agree (v w : ZMod 5) (j : Fin 3) (hj : j ≠ roles.source) :
    seed v j = seed w j := by simp only [seed, hj, ↓reduceIte]

private lemma source_both : source (seed 0) 0 ∧ ¬ source (seed 4) 0 := by
  constructor
  · unfold source X frameRetains
    rw [seed_eval]
    norm_num [show side 5 1 = 3 from by decide, mem_retentionBox]
  · unfold source X frameRetains
    rw [seed_eval]
    norm_num [show side 5 1 = 3 from by decide, mem_retentionBox]
    decide

-- A single source seed controls both actual computed levels. No independent copy of
-- the lower child is used to manufacture this correlation. The exact-mixing case
-- here isolates source support; the general payment does not assume exact mixing.
set_option backward.isDefEq.respectTransparency false in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (L : ℝ) :
    let steps := initialPilotSteps HP L 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base (1 / 4)
    0 < steps ∧ ∃ σ τ : Environment 5 3,
      (∀ j : Fin 3, j ≠ roles.source → σ j = τ j) ∧
      initialPilotWalk HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base steps σ 0 0 = 1 ∧
      initialPilotScore HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base steps σ 0 0 = 1 ∧
      initialPilotWalk HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base steps τ 0 0 = 0 ∧
      initialPilotScore HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base steps τ 0 0 =
        0 := by
  dsimp only
  refine ⟨initialPilotSteps_pos HP L 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
    base _, ?_⟩
  refine ⟨seed 0, seed 4, seed_agree 0 4, ?_⟩
  obtain ⟨hs0, hs4⟩ := source_both
  rw [walk_eq, score_eq, walk_eq, score_eq]
  simp only [hs0, hs4, ↓reduceIte, base, Matrix.one_apply_eq, and_self]

-- A positive tolerance drives the actual two-level computation. There is no error
-- premise for a supplied child. Constants are selected at fixed HP before P/rates.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ε : ℝ, 0 < ε →
    let terminal := Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3])
    let mean := rowSliceMean source terminal
      (initialPilotRaw HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base)
    let steps := initialPilotSteps HP L 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base ε
    rowNormPow 4 5 (rate 1) source terminal (fun σ x y =>
      initialPilotScore HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base steps σ x y -
        PilotRowRecipe.score HP.toHierarchyParams terminal (rate 0) mean σ x y) ≤ ε ^ 4 := by
  obtain ⟨L, hL, ha⟩ := initialPilotScore_allocated HP
  exact ⟨L, hL, fun ε hε => ha 5 3 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base ε hε⟩

-- Here the same fragment targets the actual initial pilot score of a substochastic
-- base matrix, with dense means proved internally and a covering single bin.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ε : ℝ, 0 < ε →
    let terminal := Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3])
    let steps := initialPilotSteps HP L 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base ε
    rowNormPow 4 5 (rate 1) source terminal (fun σ x y =>
      initialPilotScore HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base steps σ x y -
        PilotRowRecipe.score HP.toHierarchyParams terminal (rate 0) base σ x y) ≤ ε ^ 4 := by
  obtain ⟨L, hL, ha⟩ := initialPilotScore_allocated_of_single_bin HP
  have hk : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
  have hd := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
  have hK : 2 * (1 + 32 / HP.η) ≤ HP.K := by linarith [HP.gate]
  refine ⟨L, hL, fun ε hε => ?_⟩
  exact ha 5 3 1 (by decide) roles horizon 0 1 0 (by decide) (by decide)
    [1] [2, 3] binCutoff (fun _ => 1) base (by intros; rfl) HP.η HP.η_pos HP.ρ_one hK
    (by intro x y; simp only [base, Matrix.one_apply]; split_ifs <;> norm_num)
    (by simp [base]) (by intro x y; simpa only [rate, pow_zero, inv_one, one_pow, div_one, one_mul]
      using binCutoff_base x y) ε hε

-- Zero coefficients do not produce a zero-length pseudo-call.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (L : ℝ) :
    0 < initialPilotSteps HP L 1 roles 0 1 0 0 [1] [2, 3] (fun _ => 0)
      (fun _ => 1) (0 : Matrix (ZMod 5) (ZMod 5) ℝ) (1 / 4) :=
  initialPilotSteps_pos HP L 1 roles 0 1 0 0 [1] [2, 3] (fun _ => 0) (fun _ => 1) 0 _

-- Zero base matrices produce a zero computed lower walk and upper score at every
-- finite walk length, rather than merely satisfying an error-bound signature.
private lemma zero_score (HP : FourthRootHierarchyParams 16 1 16 32 8) (steps : ℕ)
    (σ : Environment 5 3) (x y : ZMod 5) :
    initialPilotScore HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      (0 : Matrix (ZMod 5) (ZMod 5) ℝ) steps σ x y = 0 := by
  have hc : binCutoff 0 = 0 := by
    norm_num [binCutoff, boundedRoutedBinCutoff, routedBinCutoff]
  have hr (τ : Environment 5 3) (a b : ZMod 5) :
      initialPilotRaw HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
        (0 : Matrix (ZMod 5) (ZMod 5) ℝ) τ a b = 0 := by
    unfold initialPilotRaw denseChild normalizedRequest
    dsimp only
    split_ifs
    · simp only [DenseRowRecipe.normalized, Matrix.zero_apply, zero_div, hc, zero_mul]
      split_ifs <;> simp only [mul_zero]
    · simp only [mul_zero]
  have hw (a b : ZMod 5) :
      initialPilotWalk HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
        (0 : Matrix (ZMod 5) (ZMod 5) ℝ) steps σ a b = 0 := by
    unfold initialPilotWalk conditionalWalk
    split_ifs
    · simp_rw [hr]
      simp only [← Pi.zero_def, map_zero, Pi.zero_apply]
    · rfl
  unfold initialPilotScore PilotRowRecipe.score atomPrep
  rw [hw, zero_div, HP.ϕ_zero 0 HP.δ₀_pos.le, zero_mul]

-- Signed rank input and empty sets are covered by the reused finite-rank lemma.
example : kthLargest 6 (univ : Finset (ZMod 5)) (fun x => -(x.val : ℝ)) = 0 :=
  kthLargest_eq_zero_of_card_lt (by simp) _
example : kthLargest 1 (∅ : Finset (ZMod 5)) (fun _ => (-7 : ℝ)) = 0 :=
  kthLargest_eq_zero_of_card_lt (by simp) _

-- The old terminal-only child interface cannot represent the ACTUAL allocated score.
-- These two environments agree at every role except the integrated source.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (L : ℝ) :
    let steps := initialPilotSteps HP L 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base (1 / 4)
    ¬ ∃ F : FrameChannel 5 4 1 → ℝ, ∀ σ,
      initialPilotScore HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base steps σ 0 0 =
        F (σ roles.terminal) := by
  intro steps ⟨F, hF⟩
  have h0 := hF (seed 0)
  have h4 := hF (seed 4)
  obtain ⟨hs0, hs4⟩ := source_both
  rw [score_eq, ite_eq_left hs0] at h0
  rw [score_eq, ite_eq_right hs4] at h4
  have ht := seed_agree 0 4 roles.terminal roles.source_terminal.symm
  rw [ht] at h0
  linarith

-- Kernel regression: two original environments, the actual allocated RAW/score,
-- replicated across enough rank entries. This tests source integration, not an
-- injective hierarchy instance or a nonzero residual-mixing error fixture.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (L : ℝ) :
    let steps := initialPilotSteps HP L 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base (1 / 4)
    PilotRowRecipe.sourceDetector HP.toHierarchyParams
      (fun (_ : Bool) (_ : Fin HP.J) => True) (fun (_ : Unit) (_ : Fin HP.J) => True)
      (fun b _ _ _ => initialPilotScore HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff
        (fun _ => 1) base steps (if b then seed 0 else seed 4) 0 0)
      ⟨0, HP.J_pos⟩ = 1 / 2 := by
  intro steps
  have h1 : kthLargest HP.J univ (fun _ : Fin HP.J => (1 : ℝ)) = 1 := by
    apply le_antisymm (kthLargest_le (by norm_num) (fun _ _ => le_rfl))
    apply (le_kthLargest_iff HP.J_pos (by norm_num : (0 : ℝ) < 1)).mpr
    simp
  have h0 : kthLargest HP.J univ (fun _ : Fin HP.J => (0 : ℝ)) = 0 :=
    le_antisymm (kthLargest_le le_rfl (fun _ _ => le_rfl)) kthLargest_nonneg
  obtain ⟨hs0, hs4⟩ := source_both
  norm_num [PilotRowRecipe.sourceDetector, expect_eq_sum_div_card, Fintype.sum_bool,
    score_eq, hs0, hs4, h1, h0]

-- The concrete source-aware initial detector is an actual completed child call,
-- with positive length and its exact width/rate/density payment derived from RAW.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ε : ℝ, 0 < ε →
    let steps := initialPilotSteps HP L 1 roles 0 0 0 0 [1] [2, 3] binCutoff (fun _ => 1) base ε
    0 < steps ∧
    rowNormPow 4 5 (rate 1) source
      (Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3]))
      (fun _ _ y => initialPilotDetector HP 1 roles 0 1 0 0 [1] [2, 3]
        binCutoff (fun _ => 1) base steps y -
        initialTrueDetector HP 1 roles 1 0 [1] [2, 3] base y) ≤ 80 * ε ^ 4 := by
  obtain ⟨L, hL, ha⟩ := initialPilotDetector_allocated HP
  have hk : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
  have hd := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
  have hK : 2 * (1 + 32 / HP.η) ≤ HP.K := by linarith [HP.gate]
  refine ⟨L, hL, fun ε hε => ?_⟩
  have h := ha 5 3 1 (by decide) roles horizon 0 1 0 (by decide) [1] [2, 3]
    binCutoff (fun _ => 1) base (by intros; rfl) HP.η HP.η_pos HP.ρ_one hK
    (by intro x y; simp only [base, Matrix.one_apply]; split_ifs <;> norm_num)
    (by simp [base]) (by intro x y; simpa only [rate, pow_zero, inv_one, one_pow, div_one, one_mul]
      using binCutoff_base x y) 1 (by norm_num)
    (by
      intro y
      have ht : ({t : FrameChannel 5 4 1 | frameRetains 5 4 (side 5 0) t
          (CopyPadding.identifier 1 [2, 3] y)} : Finset _) = univ := by
        apply filter_true_of_mem
        intro t _
        simpa only [show side 5 0 = 5 by norm_num [side]] using full_retains t _
      rw [ht]
      norm_num) ε hε
  norm_num only [rate, pow_zero, pow_one, inv_one, one_pow, mul_one, div_one] at h ⊢
  exact h

-- Changing the actual computed base to zero changes the kernel output from 1/2
-- to zero. All supplied score values still come from completed positive RAW calls.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (L : ℝ) :
    let steps := initialPilotSteps HP L 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      (0 : Matrix (ZMod 5) (ZMod 5) ℝ) (1 / 4)
    0 < steps ∧
    PilotRowRecipe.sourceDetector HP.toHierarchyParams
      (fun (_ : Bool) (_ : Fin HP.J) => True) (fun (_ : Unit) (_ : Fin HP.J) => True)
      (fun b _ _ _ => initialPilotScore HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff
        (fun _ => 1) (0 : Matrix (ZMod 5) (ZMod 5) ℝ) steps
        (if b then seed 0 else seed 4) 0 0)
      ⟨0, HP.J_pos⟩ = 0 := by
  intro steps
  refine ⟨initialPilotSteps_pos HP L 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) 0 _, ?_⟩
  simp only [zero_score, PilotRowRecipe.sourceDetector]
  have hz : kthLargest HP.J univ (fun _ : Fin HP.J => (0 : ℝ)) = 0 :=
    le_antisymm (kthLargest_le le_rfl (fun _ _ => le_rfl)) kthLargest_nonneg
  norm_num [hz]

end InitialPilotScoreRegression
