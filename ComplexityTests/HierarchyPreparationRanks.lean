/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of weighted incoming PREP ranks)
import Complexity.Foundations.Probability.HierarchyPreparationRanks
import all ComplexityTests.HierarchyIncomingPreparationBias

/-!
The weighted consumer is exercised on literal successful RAW33/PREP34, with nonconstant
RAW, nonzero canonical identity and positive own error. This half-bin execution is not
an exhaustive polynomial-bin uniform salary witness. The generic half-identity rank
comparison below is independent of width but does not assert execution at growing widths.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open InitialPilotScoreRegression IncomingPreparationBiasRegression
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace PreparationRanksRegression

-- An exact, satisfiable support invariant on a benchmark table, not an invariant
-- inferred for general approximate children. Source and terminal sets stay distinct.
private lemma half_identity_profile {V : Type*} [DecidableEq V]
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {LI Lh Lρ Lτ : ℝ} (hi : 0 ≤ LI) (hh : 0 ≤ Lh) (hr : 0 ≤ Lρ) (ht : 0 ≤ Lτ)
    (hI : ∀ v q v' q', |polynomialAuxCutoff4 HP.θ v q -
      polynomialAuxCutoff4 HP.θ v' q'| ≤ LI * (|v - v'| + |q - q'|))
    (A : Matrix V V ℝ) (S T : Finset V)
    (ha : ∀ z ∈ S, ∀ w, A z w = if z = w then 1 / 2 else 0)
    (x y : V) (hx : x ∈ S) (Kc : ℕ) :
    preparationRankError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
      (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K Kc 1 Lh Lρ Lτ A
      (fun z w => if z = w then 1 else 0) S T x y ≤
      (Lh + Lρ + 2 * Lτ * LI) *
        |A x y - (if x = y then 1 else 0)| := by
  let B : Matrix V V ℝ := fun z w => if z = w then 1 else 0
  have he (z : V) (hz : z ∈ S) (w : V) : |A z w - B z w| ≤ 1 / 2 := by
    rw [ha z hz]
    dsimp only [B]
    split_ifs <;> norm_num
  have hrow (z : V) (hz : z ∈ S) :
      kthLargest 1 T (fun w => |A z w - B z w|) ≤ 1 / 2 :=
    kthLargest_le (by norm_num) (fun w _ => he z hz w)
  have haux (z : V) (hz : z ∈ S) :
      |auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 A T z y -
        auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 B T z y| ≤ LI := by
    have h := auxScore_stability hi hI
      (FourthRootHierarchyParams.NormalizedRow.rank_pos HP) (by norm_num : (0 : ℝ) < 1)
      A B T z y
    apply h.trans
    rw [div_one]
    nlinarith [he z hz y, hrow z hz]
  have hc : kthLargest 1 S (fun z =>
      |auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 A T z y -
        auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 B T z y|) ≤ LI :=
    kthLargest_le hi haux
  have hg0 : 0 ≤ incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
      HP.K Kc 1 A S T y := HP.incomingCutoff_nonneg _
  have hg1 : incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
      HP.K Kc 1 A S T y ≤ 1 := HP.incomingCutoff_le_one _
  have hrow0 : 0 ≤ rowGate HP.ρ HP.K 1 A T x := HP.ρ_nonneg _
  have hrow1 : rowGate HP.ρ HP.K 1 A T x ≤ 1 := HP.ρ_le_one _
  have hb0 : 0 ≤ atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1 B T x y :=
    mul_nonneg (polynomialPrepCutoff4_nonneg _ _) (HP.ρ_nonneg _)
  have hb1 : atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1 B T x y ≤ 1 :=
    (mul_le_mul_of_nonneg_right (polynomialPrepCutoff4_le_one _ _) (HP.ρ_nonneg _)).trans
      (by simpa using HP.ρ_le_one _)
  by_cases hxy : x = y
  · have heq : |A x y - B x y| = 1 / 2 := by rw [ha x hx]; simp [B, hxy]; norm_num
    change preparationRankError _ _ _ _ _ _ _ _ _ _ _ B _ _ _ _ ≤ _
    change _ ≤ (Lh + Lρ + 2 * Lτ * LI) * |A x y - B x y|
    rw [heq]
    unfold preparationRankError
    simp only [div_one]
    have hentry : Lh * |A x y - B x y| * rowGate HP.ρ HP.K 1 A T x *
        incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc 1 A S T y ≤ Lh / 2 := by
      rw [heq]
      calc
        _ ≤ Lh * (1 / 2) * 1 * 1 := by gcongr
        _ = _ := by ring
    have hterminal : Lρ * polynomialPrepCutoff4 HP.θ (B x y) *
        kthLargest 1 T (fun w => |A x w - B x w|) *
        incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc 1 A S T y ≤ Lρ / 2 := by
      calc
        _ ≤ Lρ * 1 * (1 / 2) * 1 := by
          gcongr <;> first
          | exact kthLargest_nonneg
          | exact polynomialPrepCutoff4_le_one _ _
          | exact hrow x hx
        _ = _ := by ring
    have hsource : Lτ * atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1 B T x y *
        kthLargest 1 S (fun z => |auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 A T z y -
          auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 B T z y|) ≤ Lτ * LI := by
      calc
        _ ≤ Lτ * 1 * LI := by
          gcongr
          exact kthLargest_nonneg
        _ = _ := by ring
    linarith
  · have hz : polynomialPrepCutoff4 HP.θ (B x y / 1) = 0 := by
      simp only [B, hxy, ↓reduceIte, zero_div]
      exact polynomialPrepCutoff4_eq_zero HP.θ_pos (by linarith [HP.θ_pos])
    have hz0 : polynomialPrepCutoff4 HP.θ 0 = 0 := by
      simpa only [B, hxy, ↓reduceIte, zero_div] using hz
    simp [preparationRankError, atomPrep, ha x hx, hxy, hz0]


-- A genuinely field-free profile/IH comparison for this executed fixture. The
-- half-identity hypothesis was proved from the returned RAW table, not assumed.
private lemma actual_profile_moment (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (Lh Lρ Lτ : ℝ) (hh : 0 ≤ Lh) (hr : 0 ≤ Lρ) (ht : 0 ≤ Lτ) :
    ∃ LI : ℝ, 0 ≤ LI ∧
    rowNormPow 4 5 (rate 1) source
      (fun σ y => (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ y)
      (fun σ x y => preparationRankError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ 1 Lh Lρ Lτ
        (halfTable σ) base {z | source σ z}
        {w | (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ w} x y) ≤
      (Lh + Lρ + 2 * Lτ * LI) ^ 4 * (81 / 625) := by
  obtain ⟨LI, hi, hI⟩ := HP.auxiliary_stability_constants
  refine ⟨LI, hi, ?_⟩
  rw [← own_moment HP]
  apply rowNormPow_le_mul (by norm_num [rate])
  intro σ x y hx _hy
  have ha (z : ZMod 5) (hz : z ∈ ({z | source σ z} : Finset _)) (w : ZMod 5) :
      halfTable σ z w = if z = w then 1 / 2 else 0 := by
    simp only [halfTable, (mem_filter.mp hz).2, ↓reduceIte, base, Matrix.one_apply]
    split_ifs <;> norm_num
  have h := half_identity_profile HP hi hh hr ht hI (halfTable σ) {z | source σ z}
    {w | (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ w} ha x y
    (mem_filter.mpr ⟨mem_univ _, hx⟩) ⌈4 * (1 + 32 * HP.R)⌉₊
  have hb : (fun z w : ZMod 5 => if z = w then (1 : ℝ) else 0) = base := by
    funext z w; simp only [base, Matrix.one_apply]
  rw [hb] at h
  have hnonneg : 0 ≤ preparationRankError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
      (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ 1 Lh Lρ Lτ
      (halfTable σ) base {z | source σ z}
      {w | (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ w} x y := by
    unfold preparationRankError atomPrep
    have hg : 0 ≤ incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K
        ⌈4 * (1 + 32 * HP.R)⌉₊ 1 (halfTable σ) {z | source σ z}
        {w | (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ w} y :=
      HP.incomingCutoff_nonneg _
    have hrow : 0 ≤ rowGate HP.ρ HP.K 1 (halfTable σ)
        {w | (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ w} x := HP.ρ_nonneg _
    have hbrow : 0 ≤ rowGate HP.ρ HP.K 1 base
        {w | (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ w} x := HP.ρ_nonneg _
    have hterminal : 0 ≤ kthLargest 1
        {w | (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ w}
        (fun w => |halfTable σ x w - base x w|) := kthLargest_nonneg
    have hsource : 0 ≤ kthLargest 1 {z | source σ z} (fun z =>
        |auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 (halfTable σ)
            {w | (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ w} z y -
          auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 base
            {w | (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ w} z y|) :=
      kthLargest_nonneg
    have hp : 0 ≤ polynomialPrepCutoff4 HP.θ (base x y / 1) :=
      polynomialPrepCutoff4_nonneg _ _
    positivity
  rw [abs_of_nonneg hnonneg]
  simpa only [mul_pow, abs_abs, base, Matrix.one_apply] using
    pow_le_pow_left₀ hnonneg h 4

-- This is the actual new consumer, with the successful changed-task child and its
-- positive own precision; canonical input is not replaced by residual zero.
private lemma actual_rank_bias (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Lh Lρ Lτ : ℝ, 0 ≤ Lh ∧ 0 ≤ Lρ ∧ 0 ≤ Lτ ∧
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    rowNormPow 4 5 r.source.rate X U (fun _ x y => rowSliceMean X U completedTable x y -
      rowSliceMean X U (B.incomingPreparation r (fun _ => base)) x y) ≤
    rowNormPow 4 5 r.source.rate X U (fun σ x y =>
      preparationRankError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        r.terminal.rate Lh Lρ Lτ (halfTable σ) base {z | X σ z} {w | U σ w} x y) := by
  obtain ⟨Lh, Lρ, Lτ, hh, hr, ht, h⟩ := BudgetData.evaluate_preparation_rank_bias (HP := HP)
  refine ⟨Lh, Lρ, Lτ, hh, hr, ht, ?_⟩
  have hq : 0 < (halfData HP).requestPrecision 33 (budgetRequest HP) := by
    rw [precision]; norm_num
  have hc := h 5 (halfData HP) 34 true ⟨0, HP.k_pos⟩
    (PreparationExecutionRegression.prepRequest HP) rfl (prep_active HP)
    ((halfData HP).childBudget_lt (by decide)) rfl (rate_pos 1).le (rate_pos 0)
    halfTable completedTable hq (half_evaluated HP) (prep_evaluated HP)
    0 2 (by decide) 1 0 [1] [2, 3] rfl rfl
  simpa only [canonical_zero, Nat.cast_ofNat] using hc

-- The new comparison genuinely improves this actual consumer's allowance: the
-- coefficient is field-free, and it multiplies the literal changed-input allowance.
-- No fixed structural charge or growing-family availability follows from this test.
private lemma actual_fieldfree_bias (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ K : ℝ, 0 ≤ K ∧
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    rowNormPow 4 5 (rate 1) source U (fun _ x y =>
      rowSliceMean source U completedTable x y -
      rowSliceMean source U (B.incomingPreparation r (fun _ => base)) x y) ≤
      K ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision 33 (budgetRequest HP))) ^ 4 := by
  obtain ⟨Lh, Lρ, Lτ, hh, hr, ht, hb⟩ := actual_rank_bias HP
  obtain ⟨LI, hi, hm⟩ := actual_profile_moment HP Lh Lρ Lτ hh hr ht
  refine ⟨Lh + Lρ + 2 * Lτ * LI, by positivity, ?_⟩
  have hX : (fun σ x => (PreparationExecutionRegression.prepRequest HP).source.retains
      (channels (halfData HP).padding) σ x) = source := by
    funext σ x
    simp only [PreparationExecutionRegression.prepRequest, budgetRequest, request,
      gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid,
      source, X, roles, halfData, budgetData]
  simp only [hX] at hb
  have hf : (PreparationExecutionRegression.prepRequest HP).terminal.rate = 1 := by
    norm_num [PreparationExecutionRegression.prepRequest, budgetRequest, request, gridChannel, rate]
  rw [hf] at hb
  apply hb.trans
  apply hm.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by positivity) 4)
  rw [← own_moment HP]
  exact own_accuracy HP

-- The original normalizer/root decoder consumes the improved actual PREP bias.
-- RAW and maximum are fixed, so this is not a recursive parent-success theorem.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    let V := B.incomingPreparation r (fun _ => base)
    let output := fun prep => correctionRequest B.padding id r
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
      halfTable prep (fun _ _ => 0)
    rootDistPow 4 5 (rate 1) source U (output completedTable) (output V) ≤
      C ^ 4 * (K ^ 4 * ((2 : ℝ) ^
        (-B.requestPrecision 33 (budgetRequest HP))) ^ 4) := by
  obtain ⟨C, hC, hc⟩ := BudgetData.correctionRequest_normalizer_root_moment_le (HP := HP)
  obtain ⟨K, hK, hb⟩ := actual_fieldfree_bias HP
  refine ⟨C, K, hC, hK, ?_⟩
  have h := hc 5 (halfData HP) (PreparationExecutionRegression.prepRequest HP)
    (admissible HP) (rate_pos 1).le (rate_pos 0) halfTable completedTable
    ((halfData HP).incomingPreparation (PreparationExecutionRegression.prepRequest HP)
      (fun _ => base)) (fun _ _ => 0)
  have hX : (fun σ x => (PreparationExecutionRegression.prepRequest HP).source.retains
      (channels (halfData HP).padding) σ x) = source := by
    funext σ x
    simp only [PreparationExecutionRegression.prepRequest, budgetRequest, request,
      gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid,
      source, X, roles, halfData, budgetData]
  simp only [hX, Nat.cast_ofNat] at h
  exact h.trans (mul_le_mul_of_nonneg_left hb (pow_nonneg hC 4))

-- Positive own error and nonconstant actual execution are retained in the new test.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (halfData HP).evaluate 33 (budgetRequest HP) = some (.row halfTable) ∧
    (halfData HP).evaluate 34 (PreparationExecutionRegression.prepRequest HP) =
      some (.row completedTable) ∧
    halfTable (seed 0) 0 0 ≠ halfTable (seed 4) 0 0 ∧
    base (0 : ZMod 5) 0 = 1 ∧ 0 < (81 / 625 : ℝ) := by
  refine ⟨half_evaluated HP, prep_evaluated HP, ?_, ?_, by norm_num⟩
  · simp [halfTable, source_both.1, source_both.2, base]
  · simp [base]

end PreparationRanksRegression
