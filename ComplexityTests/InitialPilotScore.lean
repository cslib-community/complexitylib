/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of allocated initial-pilot calls)
import Complexity.Foundations.Probability.InitialPilotCompleted
import Complexity.Foundations.Probability.HierarchyCompressedBin
import Complexity.Foundations.Combinatorics.Expander.LowerBound

/-! Actual source-correlated RAW/score calls, including positive allocated walks. -/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace InitialPilotScoreRegression
-- Scalar walk lemmas and row-valued evaluator equations use the two equivalent type spellings.
attribute [local implicit_reducible] Matrix
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
  have he : initialPilotRaw HP 1 roles 0 1 0 0 [1] [2, 3] binCutoff
      (fun _ => 1) base = fun _ => base := by
    funext σ x y
    exact raw_eq HP σ x y
  unfold initialPilotWalk
  rw [he, conditionalWalk_const]
  have ht : Y roles.terminal (side 5 0) (CopyPadding.identifier 1 [2, 3]) σ y := by
    simpa only [Y, show side 5 0 = 5 by norm_num [side]] using
      full_retains (σ roles.terminal) _
  simp only [ht, and_true]
  rfl

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

-- The new shared request evaluator assembles two nonzero half-bins. These use the
-- same original environment, and their sum is completed by its actual H4 graph.
private def budgetData (HP : FourthRootHierarchyParams 16 1 16 32 8) : BudgetData HP 5 where
  padding := 1
  base := base
  bins := {0, 1}
  binRate := fun _ => 1
  cutoff := fun _ d => binCutoff d / 2
  auxiliary := fun _ _ => 1
  slack := 1
  slack_pos := by decide
  rankCharge := 0
  binCap := 1
  binCap_nonneg := zero_le_one
  cutoff_bounds := by
    intro i d
    have h := boundedRoutedBinCutoff_mem_Icc (χ := polynomialSwitch4 (1 / 2) 1)
      (b := fun _ => 1) (cap := 1) (B := 1)
      (by norm_num) (by norm_num) le_rfl
      (monotone_polynomialSwitch4 (by norm_num))
      (fun t ht => polynomialSwitch4_of_le (by norm_num) ht)
      (fun t ht => polynomialSwitch4_of_ge (by norm_num) ht)
      (fun t => ⟨polynomialSwitch4_nonneg _ _ t, polynomialSwitch4_le_one _ _ t⟩)
      (fun _ => zero_lt_one) (fun _ _ _ => le_rfl) (fun _ => by norm_num)
      (fun _ => 1) (fun _ => ⟨zero_le_one, le_rfl⟩) 0 d
    change binCutoff d / 2 ∈ Set.Icc 0 1
    change binCutoff d ∈ Set.Icc 0 1 at h
    constructor <;> linarith [h.1, h.2]

private def budgetRequest (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  { request HP with task := .row 0 (.pilotInput ⟨0, HP.k_pos⟩) }

private lemma dense_half (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (σ : Environment 5 3) (x y : ZMod 5) :
    denseChild 1 id (request HP) (fun d => binCutoff d / 2) (fun _ => 1)
      HP.ρ HP.K base σ x y = base x y / 2 := by
  have he : denseChild 1 id (request HP) (fun d => binCutoff d / 2) (fun _ => 1)
      HP.ρ HP.K base σ x y =
      denseChild 1 id (request HP) binCutoff (fun _ => 1) HP.ρ HP.K base σ x y / 2 := by
    unfold denseChild normalizedRequest DenseRowRecipe.normalized
    dsimp only
    split_ifs <;> ring
  rw [he, dense]

private lemma shared_initial (HP : FourthRootHierarchyParams 16 1 16 32 8) (bin : ℕ) :
    (budgetData HP).initialSample (budgetRequest HP) bin =
      fun _ x y => base x y / 2 := by
  funext σ x y
  let R := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    (budgetRequest HP).source (BudgetData.midpoint (budgetRequest HP))
    (budgetRequest HP).terminal ((budgetData HP).binRate bin)
  have hdir : R.direct = { request HP with task := .baseNormalized 0 bin } := by
    simp only [R, HierarchyTask.rawRequests, budgetRequest, budgetData, request,
      gridChannel, show rate 0 = 1 by norm_num [rate], min_self]
  change 1 * HierarchyTask.usageRatio (channels (1 : ZMod 5))
    (gridChannel 2 0 [2, 3]) R.direct y *
    denseChild 1 id R.direct (fun d => binCutoff d / 2) (fun _ => 1)
      HP.ρ HP.K base σ x y = _
  rw [hdir, denseChild_congr_task]
  have hr : HierarchyTask.usageRatio (k := HP.k) (channels (1 : ZMod 5))
      (gridChannel 2 0 [2, 3]) { request HP with task := .baseNormalized 0 bin } y = 1 := by
    rw [usageRatio_grid (k := HP.k) 1 (gridChannel 2 0 [2, 3])
      { request HP with task := .baseNormalized 0 bin } 0 0 rfl rfl y]
    norm_num [side]
  rw [hr]
  simpa only [one_mul] using dense_half HP σ x y

private lemma shared_positive (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (M : ℕ) (hM : 1 < M) (bin : ℕ) :
    (budgetData HP).positiveSample
      (fun m r => if m < M then (budgetData HP).evaluate m r else none)
      ((budgetData HP).binBudget M bin (budgetRequest HP))
      bin (.pilotInput ⟨0, HP.k_pos⟩) (budgetRequest HP) =
      some (fun _ x y => base x y / 2) := by
  have hm : 0 < (budgetData HP).binBudget M bin (budgetRequest HP) := by
    simpa [BudgetData.binBudget, budgetData, budgetRequest, request, gridChannel,
      LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff, rate] using
      (Nat.sub_pos_of_lt hM)
  rw [BudgetData.positiveSample_initial _ M _ hm
    ((budgetData HP).binBudget_lt (by omega) _ _)]
  change some ((budgetData HP).initialSample (budgetRequest HP) bin) = _
  rw [shared_initial]

private lemma shared_raw (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (M : ℕ) (hM : 1 < M) :
    (budgetData HP).finiteInput
      (fun m r => if m < M then (budgetData HP).evaluate m r else none)
      M (.pilotInput ⟨0, HP.k_pos⟩) (budgetRequest HP) =
      some (fun _ => base) := by
  have hp (l : List ℕ) : l.mapM (fun i => (budgetData HP).positiveSample
      (fun m r => if m < M then (budgetData HP).evaluate m r else none)
      ((budgetData HP).binBudget M i (budgetRequest HP))
      i (.pilotInput ⟨0, HP.k_pos⟩) (budgetRequest HP)) =
      some (l.map (fun _ => fun (_ : Environment 5 3) x y => base x y / 2)) := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.mapM_cons, shared_positive HP M hM i, ih, List.map_cons]
      rfl
  unfold BudgetData.finiteInput
  rw [hp]
  change some (fun σ x y => (((budgetData HP).bins.toList.map
      (fun _ => fun (_ : Environment 5 3) x y => base x y / 2)).map
      (fun A => A σ x y)).sum - 0) = _
  apply congrArg some
  funext σ x y
  simp [budgetData]

private lemma shared_complete_const (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (M : ℕ) (A : Matrix (ZMod 5) (ZMod 5) ℝ) (slack : ℕ := 0) :
    (budgetData HP).complete M (budgetRequest HP) (fun _ => A) slack =
      some (fun σ x y => if source σ x then A x y else 0) := by
  rw [BudgetData.complete_grid _ M _ 0 2 (by decide) 1 0 [1] [2, 3] rfl rfl _ slack]
  apply congrArg some
  funext σ x y
  rw [conditionalWalk_const]
  have ht : Y (2 : Fin 3) (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [2, 3]) σ y := by
    simpa only [Y, show side 5 0 = 5 by norm_num [side]] using full_retains (σ 2) _
  simp only [show (budgetData HP).padding = 1 from rfl, ht, and_true]
  rfl

-- Both half-bins contribute. Their actual shared completion remains nonconstant
-- in the source environment, with no new seed or supplied lower-child function.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ) (hM : 1 < M) :
    ((budgetData HP).finiteInput
      (fun m r => if m < M then (budgetData HP).evaluate m r else none)
      M (.pilotInput ⟨0, HP.k_pos⟩) (budgetRequest HP)).bind
      ((budgetData HP).complete M (budgetRequest HP)) =
      some (fun σ x y => if source σ x then base x y else 0) ∧
    (if source (seed 0) 0 then base 0 0 else 0) ≠
      (if source (seed 4) 0 then base 0 0 else 0) := by
  refine ⟨?_, ?_⟩
  · rw [shared_raw HP M hM, Option.bind_some, shared_complete_const]
  · rw [ite_eq_left source_both.1, ite_eq_right source_both.2]
    norm_num [base]

-- The actual recursive history is sampled at unequal budgets (32 and zero).
-- Adjacent positive budgets (63 and 62) cancel instead of being completed once.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (bin : ℕ) :
    (budgetData HP).pairedSample
      (fun m r => if m < 64 then (budgetData HP).evaluate m r else none)
      64 32 (.pilotInput ⟨0, HP.k_pos⟩) (budgetRequest HP) (some bin) =
      some (fun _ x y => base x y / 2) ∧
    (budgetData HP).pairedSample
      (fun m r => if m < 64 then (budgetData HP).evaluate m r else none)
      64 1 (.pilotInput ⟨0, HP.k_pos⟩) (budgetRequest HP) (some bin) = some 0 := by
  constructor <;>
    rw [BudgetData.pairedSample_initial _ 64 _ (by decide), shared_initial]
  all_goals
    norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
      BudgetData.sampleScale, budgetData, budgetRequest, request, gridChannel, rate]

-- Dense leaf calls at budget zero are explicitly unavailable; the scheduled initial
-- approximation above uses its certified coarse sample bound instead of making that call.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).evaluate 0 (request HP) = none := by
  rw [BudgetData.evaluate_eq]
  rfl

-- The public RAW route keeps the nonconstant completed row after paired scheduling.
private lemma shared_scheduled (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).raw
      (fun m r => if m < 64 then (budgetData HP).evaluate m r else none)
      64 (.pilotInput ⟨0, HP.k_pos⟩) (budgetRequest HP) =
      some (fun σ x y => if source σ x then base x y else 0) := by
  have hs (bin : ℕ) :
      (budgetData HP).sampleScale (budgetRequest HP) (some bin) = 0 := by
    norm_num [BudgetData.sampleScale, budgetData, budgetRequest, request, gridChannel, rate]
  have hc (a b : ℕ) :
      ((if a = 0 then 0 else fun (_ : Environment 5 3) x y => base x y / 2) -
        (if b = 0 then 0 else fun (_ : Environment 5 3) x y => base x y / 2)) =
      fun (_ : Environment 5 3) x y =>
        (if a = 0 then 0 else base x y / 2) - (if b = 0 then 0 else base x y / 2) := by
    funext σ x y
    split_ifs <;> rfl
  have hm (l : List ℕ) (f : ℕ → Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) :
      l.mapM (fun x => some (f x)) = some (l.map f) := List.mapM_pure
  have he : ((budgetData HP).rays (.pilotInput ⟨0, HP.k_pos⟩)).isEmpty = false := by
    simp [BudgetData.rays, budgetData]
  unfold BudgetData.raw BudgetData.completedGroup
  simp only [he]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [BudgetData.rays, List.append_nil, List.mapM_map]
  dsimp only [Function.comp_def]
  simp_rw [BudgetData.pairedSample_initial _ 64 _ (by decide), shared_initial, hs]
  simp_rw [hc]
  simp only [bind, pure]
  simp_rw [hm]
  simp only [Option.bind_some]
  simp_rw [List.map_map]
  dsimp only [Function.comp_def]
  simp_rw [shared_complete_const]
  simp_rw [hm]
  simp only [Option.bind_some]
  norm_num [List.range_succ, Cslib.RowCompression.dyadicSlack, bind, pure, budgetData,
    LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]

-- Group aggregation is performed before its common completion. The two nonzero
-- half-rays combine to the full row at slack 32; the finer slack-1 group cancels.
set_option backward.isDefEq.respectTransparency false in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).completedGroup
      (fun m r => if m < 64 then (budgetData HP).evaluate m r else none)
      64 32 (.pilotInput ⟨0, HP.k_pos⟩) (budgetRequest HP) =
      some (fun σ x y => if source σ x then base x y else 0) ∧
    (budgetData HP).completedGroup
      (fun m r => if m < 64 then (budgetData HP).evaluate m r else none)
      64 1 (.pilotInput ⟨0, HP.k_pos⟩) (budgetRequest HP) = some 0 := by
  have hinput (d : ℕ) : (budgetData HP).initialGroupInput 64 d (budgetRequest HP) =
      fun (_ : Environment 5 3) x y =>
        (if LogSpaceEstimation.lastBudget 64 d 1 0 = 0 then 0 else base x y) -
        (if LogSpaceEstimation.lastBudget 64 (2 * d) 1 0 = 0 then 0 else base x y) := by
    funext σ x y
    simp only [BudgetData.initialGroupInput]
    simp_rw [shared_initial]
    norm_num [BudgetData.sampleScale, budgetData, budgetRequest, request, gridChannel, rate]
    split_ifs <;> ring
  constructor
  all_goals
    rw [BudgetData.completedGroup_initial _ 64 _ (by decide)
      (show (budgetData HP).bins.Nonempty from by simp [budgetData]), hinput]
    norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
  · exact shared_complete_const HP 64 base 32
  · rw [shared_complete_const HP 64 (fun _ _ => 0) 1]
    congr 1
    funext σ x y
    split_ifs <;> rfl

-- This checks the actual routed numerator on a public dense call, including nonconstancy.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).evaluate 1 (request HP) =
      some (.row (fun _ x y => base x y / 2)) ∧
    FourthRootHierarchyParams.NormalizedRow.output (fun d => binCutoff d / 2) HP.ρ
        1 1 1 0 = 1 / 2 ∧
    FourthRootHierarchyParams.NormalizedRow.output (fun d => binCutoff d / 2) HP.ρ
        1 0 1 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BudgetData.evaluate_dense _ 1 0 (by decide) _ rfl]
    congr 2
    funext τ x y
    exact dense_half HP τ x y
  all_goals
    rw [FourthRootHierarchyParams.NormalizedRow.output, HP.ρ_one 0 HP.η_pos.le]
    norm_num [FourthRootHierarchyParams.NormalizedRow.clip,
      show binCutoff 1 = 1 by simpa [base] using binCutoff_base 0 0,
      show binCutoff 0 = 0 by simpa [base, Matrix.one_apply_ne (by decide :
        (0 : ZMod 5) ≠ 1)] using binCutoff_base 0 1]

private def completedTable :
    Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ :=
  fun σ x y => if source σ x then base x y else 0

set_option backward.isDefEq.respectTransparency false in
private lemma prefix_sixtyfour (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).initialPrefixes 64 (budgetRequest HP) =
      some (fun j => if 2 ≤ j then completedTable else 0) := by
  have hinput (d : ℕ) : (budgetData HP).initialGroupInput 64 d (budgetRequest HP) =
      fun (_ : Environment 5 3) x y =>
        (if LogSpaceEstimation.lastBudget 64 d 1 0 = 0 then 0 else base x y) -
        (if LogSpaceEstimation.lastBudget 64 (2 * d) 1 0 = 0 then 0 else base x y) := by
    funext σ x y
    simp only [BudgetData.initialGroupInput]
    simp_rw [shared_initial]
    norm_num [BudgetData.sampleScale, budgetData, budgetRequest, request, gridChannel, rate]
    split_ifs <;> ring
  have hg (d : ℕ) :
      (budgetData HP).completedGroup
        (fun m r => if m ≤ 63 then (budgetData HP).evaluate m r else none)
        64 d (.pilotInput ⟨0, HP.k_pos⟩) (budgetRequest HP) =
      (budgetData HP).complete 64 (budgetRequest HP)
        (fun _ x y =>
          (if LogSpaceEstimation.lastBudget 64 d 1 0 = 0 then 0 else base x y) -
          (if LogSpaceEstimation.lastBudget 64 (2 * d) 1 0 = 0 then 0 else base x y)) d := by
    simpa only [Nat.lt_succ_iff, hinput] using
      BudgetData.completedGroup_initial (budgetData HP) 64 d (by decide)
        (show (budgetData HP).bins.Nonempty from by simp [budgetData]) (budgetRequest HP)
  unfold BudgetData.initialPrefixes
  have hr : { budgetRequest HP with usage := (budgetRequest HP).terminal } =
      budgetRequest HP := rfl
  rw [hr]
  norm_num [List.range_succ, Cslib.RowCompression.dyadicSlack]
  simp only [Nat.lt_succ_iff]
  simp_rw [hg]
  norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
  simp_rw [shared_complete_const]
  simp only [Option.bind_some]
  congr 1
  funext j σ x y
  cases j with
  | zero => simp
  | succ j => cases j with
    | zero => simp
    | succ j =>
      simp only [List.map_cons, List.take_succ_cons, List.sum_cons]
      have hz : (List.take j ([0, 0, 0, 0, 0] : List ℝ)).sum = 0 := by
        apply List.sum_eq_zero
        intro a ha
        have hm := List.mem_of_mem_take ha
        simpa using hm
      simpa [completedTable] using hz

private lemma bin_preparation_one (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (A : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) :
    (budgetData HP).binPreparation 0 (budgetRequest HP) A = fun _ _ _ => 1 := by
  funext σ x y
  unfold BudgetData.binPreparation densePreparation DenseRowRecipe.preparation atomPrep rowGate
  have hz (S : Finset (ZMod 5)) (f : ZMod 5 → ℝ) : kthLargest HP.K S f = 0 :=
    kthLargest_eq_zero_of_card_lt ((card_le_univ S).trans_lt (by simpa using large_K HP)) f
  simp only [budgetData, hz, HP.ρ_one 0 HP.η_pos.le, one_mul]

set_option backward.isDefEq.respectTransparency false in
private lemma compressed_sixtyfour_eq (HP : FourthRootHierarchyParams 16 1 16 32 8) (ζ floor : ℝ) :
    (budgetData HP).compressedBin 64 0 0 ζ floor (budgetRequest HP) =
      some (fun σ x y =>
        let S : Finset (ZMod 5) := univ
        let Δ := fun j z (ν : Fin 2) => if ν = 0 then
          (if j = 1 then completedTable σ x z else 0)
          else if j = 0 then ζ * (if source σ x then 1 else 0) else 0
        let a := Cslib.RowCompression.iterate S
          (NormalizedMoments.compatibleCapacity HP.K 7) (fun _ => HP.K)
          (Cslib.RowCompression.dyadicFloor floor 7) Δ ⟨0, 0⟩ 7
        FourthRootHierarchyParams.NormalizedRow.output (fun d => binCutoff d / 2) HP.ρ ζ
          (a.row y 0) (a.row y 1)
          (Cslib.RowCompression.firstRank S HP.K a.defaultValue a.row)) := by
  unfold BudgetData.compressedBin
  simp only [BudgetData.decodePrefixes]
  have hactive : 0 < (budgetData HP).requestPrecision 64 (budgetRequest HP) := by
    have hlog : Real.logb 2 (rate 1) = -4 := by
      simp only [rate, pow_one]
      rw [Real.logb_pow, Real.logb_inv]
      norm_num
    norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision, budgetData,
      budgetRequest, request, gridChannel, hlog, show rate 0 = 1 by norm_num [rate]]
  have hguard : ¬(64 = 0 ∨ ¬ 0 < (budgetData HP).requestPrecision 64 (budgetRequest HP) ∨
      (budgetRequest HP).terminal.rate ≠ rate 0) := by
    simp only [hactive, not_true_eq_false]
    simp [budgetRequest, request, gridChannel]
  rw [ite_eq_right hguard]
  simp only [prefix_sixtyfour, bind, Option.bind_some]
  simp_rw [bin_preparation_one]
  have hc (d : ℕ) :
      (budgetData HP).complete 64 (budgetRequest HP) (fun _ _ _ => 1) d =
      some (fun σ x _ => if source σ x then 1 else 0) := by
    exact shared_complete_const HP 64 (fun _ _ => 1) d
  norm_num [List.range_succ, Cslib.RowCompression.dyadicSlack, hc, bind, pure]
  funext σ x y
  have ht (z : ZMod 5) : (budgetRequest HP).terminal.retains (channels (1 : ZMod 5)) σ z := by
    simp only [budgetRequest, request, gridChannel, CorrectionRowTask.Channel.retains,
      channels, semanticSide_grid]
    simpa only [show side 5 0 = 5 by norm_num [side]] using full_retains (σ 2) _
  have hset : ({z | (budgetRequest HP).terminal.retains (channels (1 : ZMod 5)) σ z} :
      Finset (ZMod 5)) = univ := by ext z; simp [ht]
  simp only [show (budgetRequest HP).usage = (budgetRequest HP).terminal from rfl,
    show (budgetData HP).padding = 1 from rfl, ht, ↓reduceIte]
  apply congrArg (fun a : Cslib.RowCompression.State (ZMod 5) =>
    FourthRootHierarchyParams.NormalizedRow.output (fun d => binCutoff d / 2) HP.ρ ζ
      (a.row y 0) (a.row y 1) (Cslib.RowCompression.firstRank univ HP.K a.defaultValue a.row))
  apply Cslib.RowCompression.iterate_congr
  intro j hj
  funext z ν
  interval_cases j <;> fin_cases ν <;>
    norm_num [NormalizedMoments.firstSignalIncrement, NormalizedMoments.secondSignalIncrement,
      rate]

private lemma advance_wide (n K : ℕ) (hn : 5 < n) (hK : 5 < K)
    (floor z : ℝ) (hf : 0 ≤ floor) (hz : z ≤ floor)
    (w Δ : ZMod 5 → Fin 2 → ℝ)
    (hsize : ∀ y, 3 * floor ≤ Cslib.RowCompression.entrySize ((w + Δ) y)) :
    Cslib.RowCompression.advance univ n K floor Δ ⟨z, w⟩ = ⟨floor, w + Δ⟩ := by
  have hk (j : ℕ) (hj : 5 < j) (f : ZMod 5 → ℝ) : kthLargest j univ f = 0 :=
    kthLargest_eq_zero_of_card_lt (by simpa using hj) f
  have ht : Cslib.RowCompression.threshold univ n floor z (w + Δ) = floor := by
    simp only [Cslib.RowCompression.threshold, hk n hn, max_eq_left hf, max_eq_right hz]
  have hd : Cslib.RowCompression.newDefault univ n K floor z (w + Δ) = floor := by
    rw [Cslib.RowCompression.newDefault, ht, hk K hK]
    exact max_eq_left ((min_le_left _ _).trans (max_le hz hf))
  unfold Cslib.RowCompression.advance
  congr 1
  funext y
  apply Cslib.RowCompression.update_eq_self_of_three_mul_le
  rw [ht]
  exact hsize y

private def referenceRow (ζ : ℝ) (x : ZMod 5) (j : ℕ) (y : ZMod 5) (ν : Fin 2) : ℝ :=
  if ν = 0 then (if 2 ≤ j then base x y else 0) else if j = 0 then 0 else ζ

private def fixtureIncrement (ζ : ℝ) (x : ZMod 5) (j : ℕ) (y : ZMod 5) (ν : Fin 2) : ℝ :=
  if ν = 0 then (if j = 1 then base x y else 0) else if j = 0 then ζ else 0

private lemma active_iterate (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {ζ : ℝ} (hζ : 0 < ζ) (x : ZMod 5) (j : ℕ) (hj : j ≤ 7) :
    Cslib.RowCompression.iterate univ (NormalizedMoments.compatibleCapacity HP.K 7)
      (fun _ => HP.K) (Cslib.RowCompression.dyadicFloor ζ 7) (fixtureIncrement ζ x) ⟨0, 0⟩ j =
        ⟨if j = 0 then 0 else Cslib.RowCompression.dyadicFloor ζ 7 (j - 1), referenceRow ζ x
        j⟩ := by
  induction j with
  | zero =>
    simp only [Cslib.RowCompression.iterate_zero, ↓reduceIte]
    congr 1
    funext y ν
    fin_cases ν <;> simp [referenceRow]
  | succ j ih =>
    rw [Cslib.RowCompression.iterate_succ, ih (by omega)]
    have hn : 5 < NormalizedMoments.compatibleCapacity HP.K 7 j :=
      (large_K HP).trans_le (NormalizedMoments.compatibleCapacity_bounds HP.K 7 j).1
    have hz : (if j = 0 then 0 else Cslib.RowCompression.dyadicFloor ζ 7 (j - 1)) ≤
        Cslib.RowCompression.dyadicFloor ζ 7 j := by
      by_cases hj0 : j = 0
      · simp only [hj0, ↓reduceIte]
        exact Cslib.RowCompression.dyadicFloor_nonneg hζ.le _ _
      · simp only [hj0, ↓reduceIte]
        have hm := Cslib.RowCompression.dyadicFloor_mul_le_succ hζ.le
          (m := 7) (i := j - 1) (by omega)
        have he : j - 1 + 1 = j := by omega
        rw [he] at hm
        linarith [Cslib.RowCompression.dyadicFloor_nonneg hζ.le 7 (j - 1)]
    have hi (y : ZMod 5) :
        (referenceRow ζ x j + fixtureIncrement ζ x j) y 1 = ζ := by
      by_cases hj0 : j = 0 <;> simp [referenceRow, fixtureIncrement, hj0]
    rw [advance_wide _ _ hn (large_K HP) _ _
      (Cslib.RowCompression.dyadicFloor_nonneg hζ.le _ _) hz _ _ (fun y => ?_)]
    · congr 1
      funext y ν
      fin_cases ν
      · by_cases hj0 : j = 0
        · subst j; simp [referenceRow, fixtureIncrement]
        · by_cases hj1 : j = 1
          · subst j; simp [referenceRow, fixtureIncrement]
          · have hj2 : 2 ≤ j := by omega
            simp [referenceRow, fixtureIncrement, hj1, hj2, show 2 ≤ j + 1 by omega]
      · by_cases hj0 : j = 0 <;> norm_num [referenceRow, fixtureIncrement, hj0]
    · have hb := Cslib.RowCompression.dyadicFloor_le_scale_div hζ.le 7 j
      have hs := Cslib.RowCompression.abs_apply_le_entrySize
        ((referenceRow ζ x j + fixtureIncrement ζ x j) y) 1
      rw [hi, abs_of_pos hζ] at hs
      linarith

private lemma bin_zero {d : ℝ} (hd : d ≤ 1 / 2) : binCutoff d = 0 :=
  boundedRoutedBinCutoff_eq_zero (by norm_num)
    (fun t ht => polynomialSwitch4_of_le (by norm_num) ht)
    (fun _ => zero_lt_one) (fun _ _ _ => le_rfl) hd 0 (fun _ => 1)

set_option backward.isDefEq.respectTransparency false in
private lemma compressed_value (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).compressedBin 64 0 0 (HP.η / 4) (HP.η / 4) (budgetRequest HP) =
      some (fun σ x y => if source σ x then base x y / 2 else 0) := by
  rw [compressed_sixtyfour_eq]
  congr 1
  funext σ x y
  dsimp only
  have hζ : 0 < HP.η / 4 := by linarith [HP.η_pos]
  have hk (f : ZMod 5 → ℝ) : kthLargest HP.K univ f = 0 :=
    kthLargest_eq_zero_of_card_lt (by simpa using large_K HP) f
  by_cases hs : source σ x
  · simp only [completedTable, hs, ↓reduceIte, mul_one]
    let a := Cslib.RowCompression.iterate univ (NormalizedMoments.compatibleCapacity HP.K 7)
      (fun _ => HP.K) (Cslib.RowCompression.dyadicFloor (HP.η / 4) 7)
      (fixtureIncrement (HP.η / 4) x) ⟨0, 0⟩ 7
    change FourthRootHierarchyParams.NormalizedRow.output (fun d => binCutoff d / 2) HP.ρ
      (HP.η / 4) (a.row y 0) (a.row y 1)
      (Cslib.RowCompression.firstRank univ HP.K a.defaultValue a.row) = base x y / 2
    dsimp only [a]
    simp_rw [active_iterate HP hζ x 7 (by decide)]
    have hr : Cslib.RowCompression.dyadicFloor (HP.η / 4) 7 (7 - 1) ≤ HP.η := by
      linarith [Cslib.RowCompression.dyadicFloor_le_scale_div hζ.le 7 (7 - 1), HP.η_pos]
    have hf := Cslib.RowCompression.dyadicFloor_nonneg hζ.le 7 (7 - 1)
    simp only [referenceRow, show (7 : ℕ) ≠ 0 by decide, show 2 ≤ (7 : ℕ) by decide,
      ↓reduceIte, Cslib.RowCompression.firstRank, hk, max_eq_left hf,
      FourthRootHierarchyParams.NormalizedRow.output, HP.ρ_one _ hr,
      FourthRootHierarchyParams.NormalizedRow.clip]
    rw [binCutoff_base]
    norm_num [hζ.ne']
  · simp only [completedTable, hs, ↓reduceIte, mul_zero, ite_self]
    have hsep : 3 * HP.η₂ < (1 / 2 : ℝ) := by
      have ht := HP.θ₂_lt
      norm_num at ht
      linarith [HP.η₂_lt, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_lt_θ₂]
    have hp := Cslib.RowCompression.reference_iterate_output_eq
      (H := FourthRootHierarchyParams.NormalizedRow.output (fun d => binCutoff d / 2) HP.ρ
        (HP.η / 4)) (a := (⟨0, 0⟩ : Cslib.RowCompression.State (ZMod 5)))
      (s := univ) (n := NormalizedMoments.compatibleCapacity HP.K 7)
      (ρ := Cslib.RowCompression.dyadicFloor (HP.η / 4) 7)
      HP.η_pos.le (FourthRootHierarchyParams.NormalizedRow.rank_pos HP)
      (fun _ _ => by dsimp; linarith [HP.η_pos])
      (fun _ _ => by change |(0 : ℝ)| ≤ HP.η; simpa using HP.η_pos.le)
      HP.η_lt_η₂ hsep
      (fun d v q hd => by simp [FourthRootHierarchyParams.NormalizedRow.output, bin_zero hd])
        (fun d v q hq => by simp [FourthRootHierarchyParams.NormalizedRow.output, HP.ρ_zero q hq])
          (fun d v q r hq hr => by
        simp only [FourthRootHierarchyParams.NormalizedRow.output,
          HP.ρ_one q hq.2, HP.ρ_one r hr.2])
      7 (fun j _ => (NormalizedMoments.compatibleCapacity_bounds HP.K 7 j).1)
      (fun j _ => by
        linarith [Cslib.RowCompression.dyadicFloor_le_scale_div hζ.le 7 j, HP.η_pos])
      y (mem_univ y)
    exact hp.trans (by simp [FourthRootHierarchyParams.NormalizedRow.output,
      bin_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)])

-- Compression does not make the uncertified zero/inactive budget boundary available.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ζ floor : ℝ) :
    (budgetData HP).compressedBin 0 0 0 ζ floor (budgetRequest HP) = none ∧
    (budgetData HP).compressedBin 2 0 0 ζ floor (budgetRequest HP) = none := by
  have hlog : Real.logb 2 (rate 1) = -4 := by
    simp only [rate, pow_one]
    rw [Real.logb_pow, Real.logb_inv]
    norm_num
  have hi : ¬ 0 < (budgetData HP).requestPrecision 2 (budgetRequest HP) := by
    norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision, budgetData,
      budgetRequest, request, gridChannel, hlog, show rate 0 = 1 by norm_num [rate]]
  constructor
  · simp only [BudgetData.compressedBin, true_or, ↓reduceIte]
  · simp only [BudgetData.compressedBin, hi, not_false_eq_true, or_true, true_or, ↓reduceIte]

-- Positive floors and actual evaluator history produce a nonconstant compressed row.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).compressedBin 64 0 0 (HP.η / 4) (HP.η / 4) (budgetRequest HP) =
      some (fun σ x y => if source σ x then base x y / 2 else 0) ∧
    (if source (seed 0) 0 then base 0 0 / 2 else 0) ≠
      (if source (seed 4) 0 then base 0 0 / 2 else 0) := by
  refine ⟨compressed_value HP, ?_⟩
  rw [ite_eq_left source_both.1, ite_eq_right source_both.2]
  norm_num [base]

-- The postcompression root error is measured against the actual normalized bin target.
-- The mean agrees on the requested source slice; the inactive source rows stay masked.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ A, (budgetData HP).compressedBin 64 0 0 (HP.η / 4) (HP.η / 4) (budgetRequest HP) = some A ∧
      rootDistPow 4 5 (rate 1) source
        (fun σ y => (request HP).usage.retains (channels (1 : ZMod 5)) σ y)
        A (denseChild 1 id (request HP) (fun d => binCutoff d / 2) (fun _ => 1)
          HP.ρ HP.K base) = 0 ∧
      ∀ σ x, #{y ∈ ({y | (request HP).terminal.retains (channels (1 : ZMod 5)) σ y} :
        Finset (ZMod 5)) | A σ x y ≠ 0} < HP.K := by
  refine ⟨(fun σ x y => if source σ x then base x y / 2 else 0), compressed_value HP, ?_, ?_⟩
  · unfold rootDistPow rowNormPow
    have hz (σ : Environment 5 3) :
        ∑ x ∈ ({x | source σ x} : Finset (ZMod 5)),
          ∑ y ∈ ({y | (request HP).usage.retains (channels (1 : ZMod 5)) σ y} : Finset _),
            |(if source σ x then base x y / 2 else 0) ^ (4⁻¹ : ℝ) -
              denseChild 1 id (request HP) (fun d => binCutoff d / 2) (fun _ => 1)
                HP.ρ HP.K base σ x y ^ (4⁻¹ : ℝ)| ^ 4 = 0 := by
      apply sum_eq_zero
      intro x hx
      apply sum_eq_zero
      intro y _
      rw [ite_eq_left (mem_filter.mp hx).2, dense_half]
      simp
    norm_num only at hz ⊢
    simp only [hz, Fintype.expect_const, mul_zero]
  · have hη₂ : HP.η₂ ≤ (1 / 2 : ℝ) := by
      have ht := HP.θ₂_lt
      norm_num at ht
      linarith [HP.η₂_lt, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_lt_θ₂]
    exact ((budgetData HP).compressedBin_bounds 64 0 0 (HP.η / 4) (HP.η / 4)
      (budgetRequest HP) _ (compressed_value HP) (e := 1 / 2) (g := HP.η₂)
      (by norm_num) hη₂
      (fun d hd => by change binCutoff d / 2 = 0; rw [bin_zero hd, zero_div]) HP.ρ_zero).2.2

-- An empty initial schedule keeps its zero without touching history or validating
-- a graph, including at budget zero. Inactive main/residual guards stay separate.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ({ budgetData HP with bins := ∅ } : BudgetData HP 5).completedGroup
      (fun _ _ => none) 0 1 (.pilotInput ⟨0, HP.k_pos⟩)
      { budgetRequest HP with source := (budgetRequest HP).usage } = some 0 := by
  simp [BudgetData.completedGroup, BudgetData.rays]

-- A concrete active parent budget reaches those two bins through the one evaluator.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).evaluate 64 (budgetRequest HP) =
      some (.row (fun σ x y => if source σ x then base x y else 0)) := by
  have hlog : Real.logb 2 (rate 1) = -4 := by
    simp only [rate, pow_one]
    rw [Real.logb_pow, Real.logb_inv]
    norm_num
  have hactive : 0 < (budgetData HP).requestPrecision 64 (budgetRequest HP) := by
    norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision, budgetData,
      budgetRequest, request, gridChannel, hlog, show rate 0 = 1 by norm_num [rate]]
  have htask : (budgetRequest HP).task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) := rfl
  rw [BudgetData.evaluate_eq]
  simp only [BudgetData.step, htask, hactive, ↓reduceIte]
  rw [shared_scheduled HP]
  rfl

-- Later RAW constructors use the existing schedule and their own positive-precision
-- guards. This equation asserts dispatch, not recursive child availability or accuracy.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (hk : 1 < HP.k) (M : ℕ) :
    let history := fun m r => if m < M then (budgetData HP).evaluate m r else none
    let input := { request HP with task := .row 0 (.input ⟨1, hk⟩) }
    let residual := { request HP with task := .residual 0 }
    (budgetData HP).evaluate M input =
      (if 0 < (budgetData HP).requestPrecision M input then
        ((budgetData HP).raw history M (.input ⟨1, hk⟩) input).map BudgetValue.row
      else none) ∧
    (budgetData HP).evaluate M residual =
      (if 0 < (budgetData HP).requestPrecision M residual then
        ((budgetData HP).raw history M .residual residual).map BudgetValue.row
      else none) := by
  dsimp only
  constructor <;> rw [BudgetData.evaluate_eq] <;> rfl

-- Unsupported cross-stage calls are unavailable rather than placeholder zero outputs.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ) :
    (budgetData HP).evaluate M { request HP with task := .nextMatrix 0 } = none := by
  rw [BudgetData.evaluate_eq]
  rfl

-- Literal bases keep the output shape; row lookup cannot consume a vector zero.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ((budgetData HP).evaluate 0 { request HP with task := .row 0 (.maximum 0) }).bind
      BudgetValue.row? = none := by
  rw [BudgetData.evaluate_maximum_zero _ _ _ rfl]
  rfl

end InitialPilotScoreRegression
