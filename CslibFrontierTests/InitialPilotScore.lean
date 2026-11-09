/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of allocated initial-pilot calls)
import CslibFrontier.Computability.LogSpaceDerandomization.InitialPilotCompleted
import CslibFrontier.Foundations.Combinatorics.Expander.LowerBound

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
private lemma zero_walk (HP : FourthRootHierarchyParams 16 1 16 32 8) (steps : ℕ)
    (σ : Environment 5 3) (x y : ZMod 5) :
    initialPilotWalk HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
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
  unfold initialPilotWalk conditionalWalk
  split_ifs
  · simp_rw [hr]
    simp only [← Pi.zero_def, map_zero, Pi.zero_apply]
  · rfl

private lemma zero_score (HP : FourthRootHierarchyParams 16 1 16 32 8) (steps : ℕ)
    (σ : Environment 5 3) (x y : ZMod 5) :
    initialPilotScore HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      (0 : Matrix (ZMod 5) (ZMod 5) ℝ) steps σ x y = 0 := by
  have hw := zero_walk HP steps σ
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

set_option backward.isDefEq.respectTransparency false

private lemma large_J (HP : FourthRootHierarchyParams 16 1 16 32 8) : 5 < HP.J := by
  have hk : (1:ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
  have hm : (1:ℝ) ≤ HP.m := by
    have hc := HP.copies
    have hm0 := Nat.cast_nonneg (α := ℝ) HP.m
    rw [div_le_iff₀ (by linarith : (0:ℝ) < HP.m + 1)] at hc
    norm_num only at hc
    linarith
  have hl : (64:ℝ) ≤ 2 * 16 * HP.m * HP.k * (HP.k + 1) := by
    calc
      (64:ℝ) = 2 * 16 * 1 * 1 * (1+1) := by norm_num
      _ ≤ _ := by gcongr
  have hδ : HP.δ₀ < 1 := by
    linarith [HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_lt_θ₂, HP.θ₂_lt]
  have hr := HP.rank
  have hj : (0:ℝ) < HP.J := by exact_mod_cast HP.J_pos
  have hJ : (5:ℝ) < HP.J := by nlinarith [mul_lt_mul_of_pos_right hδ hj]
  exact_mod_cast hJ

-- The actual hierarchy detector is zero on this small-field fixture because its
-- padded rank exceeds the width. No injectivity claim is made for a replicated rank.
private lemma computed_detector_zero (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (hJ : 5 < HP.J) (steps : ℕ) :
    initialPilotDetector HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1) base steps = 0 := by
  unfold initialPilotDetector environmentDetector PilotRowRecipe.sourceDetector
  have hz (S : Finset (ZMod 5)) (f : ZMod 5 → ℝ) : kthLargest HP.J S f = 0 :=
    kthLargest_eq_zero_of_card_lt ((card_le_univ S).trans_lt (by simpa using hJ)) f
  funext y
  simp only [hz, Fintype.expect_const]
  norm_num

private lemma large_Kc (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    5 < ⌈4 * (1 + 32 * HP.R)⌉₊ := by
  have hr := HP.R_rank
  have hj : (1:ℝ) ≤ HP.J := by exact_mod_cast HP.J_pos
  have hc := Nat.le_ceil (4 * (1 + 32 * HP.R))
  norm_num only [one_mul] at hr
  have : (5:ℝ) < ⌈4 * (1 + 32 * HP.R)⌉₊ := by linarith
  exact_mod_cast this

-- Incoming preparation really reads the completed, source-dependent RAW table.
private lemma computed_preparation (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (steps : ℕ) (σ : Environment 5 3) (x y : ZMod 5) :
    initialPilotPreparation HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base steps σ x y = if source σ x then base x y else 0 := by
  have he := walk_eq HP steps σ
  unfold initialPilotPreparation correctionPrep rowGate incomingGate
  simp only [he, show rate 0 = 1 by norm_num [rate], div_one]
  rw [kthLargest_eq_zero_of_card_lt
    ((card_filter_le _ _).trans_lt (by simpa using large_K HP)),
    kthLargest_eq_zero_of_card_lt
      ((card_filter_le _ _).trans_lt (by simpa using large_Kc HP))]
  rw [HP.ρ_one 0 HP.η_pos.le,
    HP.incomingCutoff_one (by rw [HP.τ₀_eq]; norm_num)]
  simp only [mul_one]
  have hθ : HP.θ < 1 := by linarith [HP.θ_lt_θ₂, HP.θ₂_lt]
  by_cases hs : source σ x
  · rw [ite_eq_left hs]
    by_cases hxy : x = y
    · subst y
      simp only [base, Matrix.one_apply_eq]
      exact polynomialPrepCutoff4_eq_one HP.θ_pos (by linarith)
    · simp only [base, Matrix.one_apply_ne hxy]
      exact polynomialPrepCutoff4_eq_zero HP.θ_pos (by linarith [HP.θ_pos])
  · rw [ite_eq_right hs]
    exact polynomialPrepCutoff4_eq_zero HP.θ_pos (by linarith [HP.θ_pos])

private lemma computed_preparation_walk (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (rawSteps prepSteps : ℕ) (σ : Environment 5 3) (x y : ZMod 5) :
    initialPilotPreparationWalk HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base rawSteps prepSteps σ x y = if source σ x then base x y else 0 := by
  unfold initialPilotPreparationWalk conditionalWalk
  have ht (τ : Environment 5 3) (w : ZMod 5) :
      Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3]) τ w := by
    simpa only [Y, show side 5 0 = 5 by norm_num [side]] using full_retains (τ roles.terminal) _
  simp only [mem_filter, mem_univ, true_and, ht, and_true]
  change (if _h : source σ x then _ else 0) = _
  split_ifs with hs
  · have he : (fun τ : RetainedPairSlice
        (X roles.source (side 5 1) (CopyPadding.identifier 1 [1]))
        (Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3])) x y =>
        initialPilotPreparation HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
          base rawSteps τ.val x y) = fun _ => base x y := by
      funext τ
      exact (computed_preparation HP rawSteps τ.val x y).trans
        (ite_eq_left (retainedPairSlice_source _ _ τ))
    rw [he, RotationMap.walk_pow_const]
  · rfl

private lemma event_nonempty {Ω : Type*} [Fintype Ω] (A B : Ω → Prop)
    [DecidablePred A] [DecidablePred B] (σ : Ω) (ha : A σ) (hb : B σ) :
    ({τ | A τ ∧ B τ} : Finset Ω).Nonempty :=
  ⟨σ, mem_filter.mpr ⟨mem_univ _, ha, hb⟩⟩

private lemma retained_mean {Ω V : Type*} [Fintype Ω] (A B : Ω → V → Prop)
    [∀ σ v, Decidable (A σ v)] [∀ σ v, Decidable (B σ v)]
    (C : Matrix V V ℝ) (x y : V)
    (hn : ({σ | A σ x ∧ B σ y} : Finset Ω).Nonempty) :
    rowSliceMean A B (fun σ x y => if A σ x then C x y else 0) x y = C x y := by
  unfold rowSliceMean
  calc
    _ = 𝔼 _σ ∈ ({σ | A σ x ∧ B σ y} : Finset Ω), C x y := by
      apply expect_congr rfl
      intro σ hσ
      exact ite_eq_left (mem_filter.mp hσ).2.1
    _ = C x y := expect_const hn _

private lemma computed_preparation_mean (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (rawSteps prepSteps : ℕ) :
    rowSliceMean (X roles.source (side 5 1) (CopyPadding.identifier 1 [1]))
      (Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3]))
      (initialPilotPreparationWalk HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
        base rawSteps prepSteps) 0 0 = 1 := by
  have ht (σ : Environment 5 3) :
      Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3]) σ 0 := by
    simpa only [Y, show side 5 0 = 5 by norm_num [side]] using
      full_retains (σ roles.terminal) _
  have hn : ({σ : Environment 5 3 | source σ 0 ∧
      Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3]) σ 0} : Finset _).Nonempty :=
    event_nonempty (fun σ => source σ 0) _ (seed 0) source_both.1 (ht _)
  have he : initialPilotPreparationWalk HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff
      (fun _ => 1) base rawSteps prepSteps =
      (fun σ x y => if source σ x then base x y else 0) := by
    funext σ x y
    exact computed_preparation_walk HP rawSteps prepSteps σ x y
  rw [he]
  exact retained_mean (fun σ v => source σ v)
    (Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3])) base 0 0 hn

-- This checks the actual normalized child and its computed conditional normalizer,
-- rather than supplying a preparation value of one to the algorithm.
private lemma computed_normalized (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (rawSteps prepSteps detectorSteps : ℕ) (σ : Environment 5 3) (hs : source σ 0) :
    initialPilotNormalized HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base rawSteps prepSteps detectorSteps σ 0 0 = HP.Q 1 := by
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
    ⟨.row 0 (.pilotNormalized ⟨0, HP.k_pos⟩), gridChannel roles.source 1 [1],
      gridChannel roles.terminal 0 [2, 3], gridChannel roles.terminal 0 [2, 3]⟩
  have hr : Admissible r := ⟨roles.source_terminal, rfl, rfl⟩
  have hm := normalizer_full 1 id r hr
    (initialPilotPreparationWalk HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base rawSteps prepSteps) 0 0
  dsimp only at hm
  have hm' : rowSliceMean (fun σ v => r.source.retains (channels 1) σ (id v))
      (fun σ v => r.usage.retains (channels 1) σ (id v))
      (initialPilotPreparationWalk HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
        base rawSteps prepSteps) 0 0 = 1 := by
    have he : ({σ : Environment 5 3 | r.source.retains (channels 1) σ (id 0) ∧
        r.usage.retains (channels 1) σ (id 0)} : Finset _) =
        ({σ : Environment 5 3 | X roles.source (side 5 1)
          (CopyPadding.identifier 1 [1]) σ 0 ∧
          Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3]) σ 0} : Finset _) := by
      ext σ
      simp only [mem_filter, mem_univ, true_and, r, gridChannel,
        CorrectionRowTask.Channel.retains, channels, semanticSide_grid, X, Y, id_eq]
    unfold rowSliceMean
    rw [he]
    exact computed_preparation_mean HP rawSteps prepSteps
  rw [hm'] at hm
  unfold initialPilotNormalized
  change correctionRequest 1 id r _ _ _ _ _ _ _ _ _ _ σ 0 0 = _
  simp only [correctionRequest, dite_eq_left hr, CorrectionRowRecipe.normalized, hm]
  have ht : coordinate (1 : ZMod 5) r.usage (σ r.terminal.role) (id 0) := by
    change frameRetains 5 4 (semanticSide 5 (rate 0)) _ _
    rw [semanticSide_grid, show side 5 0 = 5 by norm_num [side]]
    exact full_retains _ _
  simp only [Equiv.piSplitAt_apply] at *
  rw [ite_eq_left ht, walk_eq, ite_eq_left hs]
  unfold rowGate incomingGate
  rw [kthLargest_eq_zero_of_card_lt
    ((card_filter_le _ _).trans_lt (by simpa using large_K HP)),
    kthLargest_eq_zero_of_card_lt
      ((card_filter_le _ _).trans_lt (by simpa using large_Kc HP))]
  rw [HP.ρ_one 0 HP.η_pos.le,
    HP.incomingCutoff_one (by rw [HP.τ₀_eq]; norm_num)]
  simp only [initialPilotMaximum, computed_detector_zero HP (large_J HP),
    PilotRowRecipe.maximum, Pi.zero_apply, max_self]
  norm_num only [base, Matrix.one_apply_eq, r, gridChannel, rate, pow_zero, inv_one,
    one_pow, div_one, mul_one, min_self,
    max_eq_right (by norm_num : (1/2:ℝ) ≤ 1), min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
  rw [HP.γ_one 0 (by norm_num), mul_one, HP.toHierarchyParams.atomCutoff_eq (by norm_num)
    (by have := Nat.cast_nonneg (α := ℝ) HP.k; linarith)]

example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (rawSteps prepSteps detectorSteps : ℕ) :
    initialPilotNormalized HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base rawSteps prepSteps detectorSteps (seed 0) 0 0 = HP.Q 1 :=
  computed_normalized HP rawSteps prepSteps detectorSteps (seed 0) source_both.1

-- The completed OUTER walk consumes the actual nested child. Every finite positive
-- allocation has a nonzero correction on the retained slice; this is an exact-mixing
-- fixture with zero detector, not evidence of residual mixing error.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (L ε : ℝ) (hε : 0 < ε) :
    let rawSteps := initialPilotRawSteps HP (1 : ZMod 5) roles 0 1 0 0 [1] [2, 3]
      binCutoff (fun _ => 1) base ε
    let detectorSteps := initialPilotSteps HP L (1 : ZMod 5) roles 0 1 0 0 [1] [2, 3]
      binCutoff (fun _ => 1) base ε
    let outerSteps := initialPilotOuterSteps HP 5 3 1 ε
    0 < rawSteps ∧ 0 < detectorSteps ∧ 0 < outerSteps ∧
    initialPilotCompleted HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base rawSteps 1 detectorSteps outerSteps (seed 0) 0 0 = HP.Q 1 ∧
    0 < initialPilotCompleted HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base rawSteps 1 detectorSteps outerSteps (seed 0) 0 0 := by
  intro rawSteps detectorSteps outerSteps
  have hs : 0 < outerSteps := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  have ht : Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3])
      (seed 0) 0 := by
    simpa only [Y, show side 5 0 = 5 by norm_num [side]] using
      full_retains (seed 0 roles.terminal) _
  have he : initialPilotCompleted HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base rawSteps 1 detectorSteps outerSteps (seed 0) 0 0 = HP.Q 1 := by
    have hc : (fun τ : RetainedPairSlice
        (X roles.source (side 5 1) (CopyPadding.identifier 1 [1]))
        (Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3])) 0 0 =>
        initialPilotNormalized HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
          base rawSteps 1 detectorSteps τ.val 0 0) = fun _ => HP.Q 1 := by
      funext τ
      exact computed_normalized HP rawSteps 1 detectorSteps τ.val
        (retainedPairSlice_source _ _ τ)
    unfold initialPilotCompleted conditionalWalk
    rw [dite_eq_left (mem_filter.mpr ⟨mem_univ _, source_both.1, ht⟩),
      hc, RotationMap.walk_pow_const]
    norm_num [rate]
  have hr := (initialPilotRaw_allocated HP 1 roles 0 1 0 0 [1] [2, 3]
    binCutoff (fun _ => 1) base hε).1
  have hd := initialPilotSteps_pos HP L 1 roles 0 1 0 0 [1] [2, 3]
    binCutoff (fun _ => 1) base ε
  refine ⟨hr, hd, hs, he, ?_⟩
  rw [he]
  linarith [HP.le_Q 1, HP.θ₂_lt]

-- A nonzero upper correction and nonzero genuinely computed preparatory walk.
-- Both lengths are positive and every non-source role is preserved by seed_agree.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (rawSteps prepSteps detectorSteps : ℕ)
    (hr : 0 < rawSteps) (hp : 0 < prepSteps) (hd : 0 < detectorSteps) :
    initialPilotCorrection HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base rawSteps detectorSteps (seed 0) 0 0 = HP.Q 1 ∧
    0 < HP.Q 1 ∧
    initialPilotPreparationWalk HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base rawSteps prepSteps (seed 0) 0 0 = 1 ∧
    initialPilotPreparationWalk HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base rawSteps prepSteps (seed 4) 0 0 = 0 := by
  have _ := hr; have _ := hp; have _ := hd
  have ht : (1:ℝ) ≤ (HP.k:ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) HP.k; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold initialPilotCorrection initialPilotMaximum
    rw [walk_eq, ite_eq_left source_both.1, computed_detector_zero HP (large_J HP)]
    norm_num only [base, Matrix.one_apply_eq, rate, pow_zero, inv_one, one_pow,
      div_one, one_mul, PilotRowRecipe.maximum, Pi.zero_apply, max_self,
      max_eq_right (by norm_num : (0:ℝ) ≤ 0), min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    rw [HP.γ_one 0 (by norm_num), mul_one, HP.toHierarchyParams.atomCutoff_eq (by norm_num) ht]
  · have h := HP.le_Q 1
    have ht := HP.θ₂_lt
    linarith
  · rw [computed_preparation_walk, ite_eq_left source_both.1]
    rfl
  · rw [computed_preparation_walk, ite_eq_right source_both.2]

-- The upper direct correction has the actual zero edge on the rejected source,
-- while the terminal and every spectator agree with the nonzero run.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (rawSteps detectorSteps : ℕ) :
    initialPilotCorrection HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base rawSteps detectorSteps (seed 4) 0 0 = 0 ∧
    ∀ j, j ≠ roles.source → seed 0 j = seed 4 j := by
  constructor
  · unfold initialPilotCorrection
    rw [walk_eq, ite_eq_right source_both.2, zero_div,
      HP.toHierarchyParams.atomCutoff_eq_zero (le_refl 0), mul_zero, zero_mul]
  · exact seed_agree 0 4

-- Zero input still receives a positive genuine RAW allocation and produces a zero
-- upper correction for every source frame, independently of the detector's value.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ε : ℝ) (hε : 0 < ε)
    (detectorSteps : ℕ) (σ : Environment 5 3) (x y : ZMod 5) :
    let steps := initialPilotRawSteps HP (1 : ZMod 5) roles 0 1 0 0 [1] [2, 3]
      binCutoff (fun _ => 1) 0 ε
    0 < steps ∧ initialPilotCorrection HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff
      (fun _ => 1) 0 steps detectorSteps σ x y = 0 := by
  intro steps
  refine ⟨(initialPilotRaw_allocated HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff
    (fun _ => 1) 0 hε).1, ?_⟩
  unfold initialPilotCorrection
  rw [zero_walk, zero_div, HP.toHierarchyParams.atomCutoff_eq_zero (le_refl 0),
    mul_zero, zero_mul]

-- All accuracy hypotheses hold on an actual nonzero base. The returned lengths
-- run the computed algorithm, and the reference is the original canonical pilot.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ε : ℝ) (hε : 0 < ε) :
    ∃ rawSteps detectorSteps : ℕ, 0 < rawSteps ∧ 0 < detectorSteps ∧
    rootDistPow 4 5 (rate 1) source
      (Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3]))
      (initialPilotCorrection HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
        base rawSteps detectorSteps)
      (fun _ x y => pilotCorrection (HP.toHierarchyParams.cutoff (rate 0)) HP.γ
        (columnDetector (canonicalChannel id (rate 0)) (canonicalChannel id (rate 0))
          HP.ϕ HP.ρ HP.J HP.K (rate 0)) base 1 x y) ≤ ε ^ 4 := by
  obtain ⟨L, Lq, Lg, _, _, _, ha⟩ := initialPilotCorrection_accuracy HP
  have hk : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
  have hd := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
  have hK : 2 * (1 + 32 / HP.η) ≤ HP.K := by linarith [HP.gate]
  have hC : ∀ x y, 0 ≤ base x y := by
    intro x y; simp only [base, Matrix.one_apply]; split_ifs <;> norm_num
  have hCf : ∀ x y, base x y ≤ rate 0 := by
    intro x y; simp only [base, Matrix.one_apply]; split_ifs <;> norm_num [rate]
  obtain ⟨hr, hd, he⟩ := ha 5 3 1 (by decide) roles horizon 0 1 0 (by decide) (by decide)
    [1] [2, 3] binCutoff (fun _ => 1) base (by intros; rfl) HP.η HP.η_pos HP.ρ_one hK
    hC (by simp [base])
    (by intro x y; simpa only [rate, pow_zero, inv_one, one_pow, div_one, one_mul]
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
  refine ⟨_, _, hr, hd, ?_⟩
  simp_rw [initialTrueCorrection_eq_canonical HP 1 (by decide) roles 1 0 [1] [2, 3]
    base hC hCf] at he
  exact he

-- The normalized allocation is nonvacuous on the same nonzero base. The reference
-- is the true normalized request; the completed canonical allocation below uses common rates.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ε : ℝ) (hε : 0 < ε) :
    ∃ rawSteps detectorSteps : ℕ, 0 < rawSteps ∧ 0 < detectorSteps ∧
    rootDistPow 4 5 (rate 1) source
      (Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3]))
      (initialPilotNormalized HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
        base rawSteps 1 detectorSteps)
      (correctionRequest 1 id
        ⟨.row 0 (.pilotNormalized ⟨0, HP.k_pos⟩), gridChannel roles.source 1 [1],
          gridChannel roles.terminal 0 [2, 3], gridChannel roles.terminal 0 [2, 3]⟩
        (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
        HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ (fun _ => base)
        (fun σ => correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K
          ⌈4 * (1 + 32 * HP.R)⌉₊ (rate 0) base (polynomialPrepCutoff4 HP.θ) HP.ρ
          {x | source σ x}
          {y | Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3]) σ y})
        (fun _ => PilotRowRecipe.maximum 0 (initialTrueDetector HP 1 roles 1 0 [1] [2, 3] base)))
        ≤ ε ^ 4 := by
  obtain ⟨L, Cr, Cp, Cm, Lp, _, _, _, _, _, ha⟩ := initialPilotNormalized_accuracy HP
  have hk : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
  have hd := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
  have hK : 2 * (1 + 32 / HP.η) ≤ HP.K := by linarith [HP.gate]
  have hC : ∀ x y, 0 ≤ base x y := by
    intro x y; simp only [base, Matrix.one_apply]; split_ifs <;> norm_num
  obtain ⟨hr, hd, he⟩ := ha 5 3 1 (by decide) roles horizon 0 1 0 (by decide) (by decide)
    [1] [2, 3] binCutoff (fun _ => 1) base (by intros; rfl) HP.η HP.η_pos HP.ρ_one hK
    hC (by simp [base])
    (by intro x y; simpa only [rate, pow_zero, inv_one, one_pow, div_one, one_mul]
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
  refine ⟨_, _, hr, hd, ?_⟩
  exact he

-- The completed stochastic accuracy theorem has a concrete nonzero identity-base
-- client. Here all three rates are zero-exponent (full channels); unequal source
-- rates above test the computation separately and are not claimed by this theorem.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ε : ℝ) (hε : 0 < ε) :
    ∃ rawSteps detectorSteps outerSteps : ℕ,
      0 < rawSteps ∧ 0 < detectorSteps ∧ 0 < outerSteps ∧
      rowNormPow 4 5 (rate 0)
        (X roles.source (side 5 0) (CopyPadding.identifier 1 [1]))
        (Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3]))
        (fun σ x y => initialPilotCompleted HP 1 roles 0 0 0 0 [1] [2, 3]
          binCutoff (fun _ => 1) base rawSteps 1 detectorSteps outerSteps σ x y -
          pilotCorrection (HP.toHierarchyParams.cutoff (rate 0)) HP.γ
            (columnDetector (canonicalChannel id (rate 0)) (canonicalChannel id (rate 0))
              HP.ϕ HP.ρ HP.J HP.K (rate 0)) base 1 x y) ≤ ε^4 := by
  have hk : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
  have hd := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
  have hK : 2 * (1 + 32 / HP.η) ≤ HP.K := by linarith [HP.gate]
  have hC : ∀ x y, 0 ≤ base x y := by
    intro x y; simp only [base, Matrix.one_apply]; split_ifs <;> norm_num
  have hCf : ∀ x y, base x y ≤ rate 0 := by
    intro x y; simp only [base, Matrix.one_apply]; split_ifs <;> norm_num [rate]
  obtain ⟨rawSteps, detectorSteps, hr, hd, ho, he⟩ :=
    initialPilotCompleted_accuracy HP 5 3 1 (by decide) roles horizon 0 0 (by decide)
      [1] [2, 3] binCutoff (fun _ => 1) base (by intros; rfl) HP.η HP.η_pos HP.ρ_one hK
      hC (by simp [base]) hCf
      (by intro x y; simpa only [rate, pow_zero, inv_one, one_pow, div_one, one_mul]
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
  exact ⟨rawSteps, detectorSteps, _, hr, hd, ho, he⟩

-- Nonunit matrix units: the joint mean itself is Q(1), while the correction
-- is rate 1 * Q(1). Dropping the literal factor would give the wrong target.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    rate 1 * rowSliceMean
      (X roles.source (side 5 1) (CopyPadding.identifier 1 [1]))
      (Y roles.terminal (side 5 1) (CopyPadding.identifier 1 [2, 3]))
      (initialTrueNormalized HP 1 roles 1 1 [1] [2, 3] ((rate 1) • base)) 0 0 =
        rate 1 * HP.Q 1 := by
  let C : Matrix (ZMod 5) (ZMod 5) ℝ := (rate 1) • base
  have hC : ∀ x y, 0 ≤ C x y := by
    intro x y
    change 0 ≤ rate 1 * (if x = y then 1 else 0)
    split_ifs
    · simpa only [mul_one] using (rate_pos 1).le
    · simp
  have hCf : ∀ x y, C x y ≤ rate 1 := by
    intro x y
    change rate 1 * (if x = y then 1 else 0) ≤ rate 1
    split_ifs <;> nlinarith [rate_pos 1]
  have hC1 : C *ᵥ 1 ≤ 1 := by
    intro x
    norm_num [C, base, smul_mulVec, rate]
  rw [initialTrueNormalized_mean HP 1 (by decide) roles horizon 1 (by decide)
    [1] [2, 3] C hC hC1 hCf]
  have hz : columnDetector (canonicalChannel (id : ZMod 5 → ZMod 5) (rate 1))
      (canonicalChannel id (rate 1)) HP.ϕ HP.ρ HP.J HP.K (rate 1) C = 0 := by
    unfold columnDetector detectorTrial
    have hr (S : Finset (ZMod 5)) (f : ZMod 5 → ℝ) : kthLargest HP.J S f = 0 :=
      kthLargest_eq_zero_of_card_lt
        ((card_le_univ S).trans_lt (by simpa using large_J HP)) f
    funext y
    simp [hr]
  rw [pilotCorrection_succ_apply, pilotMax_succ, pilotMax_zero]
  simp only [pilotInput, pilotCorrection_zero, zero_mul, add_zero, hz,
    Pi.sup_apply, Pi.zero_apply, max_self]
  rw [HP.γ_one 0 (by norm_num), mul_one, HP.toHierarchyParams.cutoff_apply]
  change rate 1 * HP.Q (rate 1 * 1 / rate 1) = _
  rw [mul_one, div_self (rate_pos 1).ne']

-- Zero RAW remains a zero normalized output despite its clipped preparatory denominator.
private lemma zero_normalized (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (rawSteps prepSteps detectorSteps : ℕ) (σ : Environment 5 3) (x y : ZMod 5) :
    initialPilotNormalized HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      0 rawSteps prepSteps detectorSteps σ x y = 0 := by
  unfold initialPilotNormalized correctionRequest
  split_ifs
  · simp only [CorrectionRowRecipe.normalized, zero_walk, zero_div,
      HP.toHierarchyParams.atomCutoff_eq_zero (le_refl 0), zero_mul, zero_div, ite_self]
  · rfl

-- Source rejection is preserved by the outer completion on the same environment.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (rawSteps prepSteps detectorSteps outerSteps : ℕ) :
    initialPilotCompleted HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      base rawSteps prepSteps detectorSteps outerSteps (seed 4) 0 0 = 0 ∧
    ∀ j, j ≠ roles.source → seed 0 j = seed 4 j := by
  refine ⟨?_, seed_agree 0 4⟩
  unfold initialPilotCompleted
  have hx : ¬ X roles.source (side 5 1) (CopyPadding.identifier 1 [1]) (seed 4) 0 :=
    source_both.2
  rw [conditionalWalk_eq_zero_of_not_source
    (X roles.source (side 5 1) (CopyPadding.identifier 1 [1]))
    (Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3])) _ _ _ (seed 4) 0 0 hx,
    mul_zero]

-- Zero remains zero after the actual completed outer walk, including its matrix-unit scale.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (rawSteps prepSteps detectorSteps outerSteps : ℕ) (σ : Environment 5 3) (x y : ZMod 5) :
    initialPilotCompleted HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff (fun _ => 1)
      0 rawSteps prepSteps detectorSteps outerSteps σ x y = 0 := by
  unfold initialPilotCompleted conditionalWalk
  split_ifs
  · have he : initialPilotNormalized HP (1 : ZMod 5) roles 0 1 0 0 [1] [2, 3] binCutoff
        (fun _ => 1) 0 rawSteps prepSteps detectorSteps = fun _ _ _ => 0 := by
      funext τ a b; exact zero_normalized HP rawSteps prepSteps detectorSteps τ a b
    simp only [he, RotationMap.walk_pow_const, mul_zero]
  · exact mul_zero _


-- A bounded PREP input can differ from its walked value even though the joint
-- normalizer is exactly stationary. This complete graph is an exact mixing limit.
private def fullMask (_ : Bool) (_ : Unit) : Prop := True
private abbrev FullSlice := RetainedPairSlice fullMask fullMask () ()
private instance : Nonempty FullSlice := ⟨⟨false, by simp [fullMask]⟩⟩
private def varyingPrep (σ : Bool) (_ _ : Unit) : ℝ := if σ then 1 else 0
private def averagedPrep := conditionalWalk fullMask fullMask
  (fun _ _ => RotationMap.complete FullSlice) (fun _ _ => 1) varyingPrep

private theorem averagedPrep_false : averagedPrep false () () = 1 / 2 := by
  have hw (f : FullSlice → ℝ) (σ : FullSlice) :
      (RotationMap.complete FullSlice).walk f σ = 𝔼 τ : FullSlice, f τ := by
    simp only [RotationMap.walk_apply, RotationMap.neighbor_complete]
  have hh := conditionalWalk_coe fullMask fullMask
    (fun _ _ => RotationMap.complete FullSlice) (fun _ _ => 1) varyingPrep () ()
    (⟨false, by simp [fullMask]⟩ : FullSlice)
  change averagedPrep false () () = _ at hh
  rw [show 2 * (1:ℕ) = 2 by norm_num, pow_two, Module.End.mul_apply, hw] at hh
  simp only [hw, Fintype.expect_const] at hh
  have he := expect_retainedPairSlice fullMask fullMask () ()
    (fun σ => varyingPrep σ () ())
  change (𝔼 τ : FullSlice, varyingPrep τ.val () ()) = _ at he
  rw [he] at hh
  simpa [fullMask, varyingPrep, Finset.expect_eq_sum_div_card] using hh

example : (∀ σ, varyingPrep σ () () ∈ Set.Icc (0:ℝ) 1) ∧
    averagedPrep false () () ≠ varyingPrep false () () ∧
    rowSliceMean fullMask fullMask averagedPrep () () =
      rowSliceMean fullMask fullMask varyingPrep () () := by
  refine ⟨?_, ?_, ?_⟩
  · intro σ
    cases σ <;> norm_num [varyingPrep]
  · rw [averagedPrep_false]
    norm_num [varyingPrep]
  · exact rowSliceMean_conditionalWalk fullMask fullMask
      (fun _ _ => RotationMap.complete FullSlice) (fun _ _ => 1) varyingPrep () ()

end InitialPilotScoreRegression
