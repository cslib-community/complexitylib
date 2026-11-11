/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.MaxDicut.GoemansWilliamson
import CslibFrontier.Algorithms.Lean.MaxTwoSAT.GoemansWilliamsonMaxTwoSAT
import CslibFrontier.Foundations.Analysis.SpecialFunctions.GoemansWilliamsonDicut
import CslibFrontierTests.GoemansWilliamsonMaxCut
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Checked Goemans–Williamson MAX-2SAT and MAX-DICUT rounding examples

Concrete nonvacuous instantiations of:
- `Real.goemansWilliamsonDicutConstant` (`0.79607 < β < 0.79608`) and Lemma 7.3.2
  (`Real.goemansWilliamsonDicutConstant_mul_add_cos_le`);
- `(Q')`/`(P')` and Boolean MAX-2SAT (`Cslib.Complexity.MaxTwoSAT`) on an unsatisfiable 4-clause
  2-CNF with mixed unit/binary and negated literals (optimal count `3 < 4`);
- `(Q'')`/`(P'')` and unbalanced MAX-DICUT (`β > 0.79607`) on `[(0, 1), (1, 0)]` with asymmetric
  weights `[2, 1]`;
- balanced (Eulerian) MAX-DICUT (`α > 0.87856`) on the directed 3-cycle `0 → 1 → 2 → 0`.
-/

namespace CslibFrontierTests.GoemansWilliamsonExtensions

open MeasureTheory ProbabilityTheory Real Cslib.Logic.PL
open Cslib.Algorithms.Lean.MaxCut
open Cslib.Algorithms.Lean.MaxTwoSAT
open Cslib.Algorithms.Lean.MaxDicut
open scoped RealInnerProductSpace

private abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

private noncomputable def e0 : Vec2 := !₂[1, 0]

private theorem norm_e0 : ‖e0‖ = 1 := by
  rw [norm_eq_sqrt_real_inner, PiLp.inner_apply]
  simp [e0]

private theorem norm_neg_e0 : ‖-e0‖ = 1 := by
  rw [norm_neg, norm_e0]

private theorem inner_e0_e0 : ⟪e0, e0⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_e0, one_pow]

/-! ### Constants and Lemma 7.3.2 -/

example : (0.79607 : ℝ) < goemansWilliamsonDicutConstant ∧
    goemansWilliamsonDicutConstant < 0.79608 :=
  ⟨lt_goemansWilliamsonDicutConstant, goemansWilliamsonDicutConstant_lt⟩

example : goemansWilliamsonDicutConstant ≤ 1 := by
  have hmem : (0, 0, 0) ∈ DicutAngleSet := by
    refine mem_dicutAngleSet_iff.2 ⟨le_rfl, pi_nonneg, le_rfl, pi_nonneg, le_rfl, pi_nonneg,
      by linarith, by linarith, by linarith, by linarith [pi_nonneg]⟩
  have h := goemansWilliamsonDicutConstant_mul_add_cos_le hmem
  norm_num [cos_zero] at h
  exact h

example : (2 * π / 3, 2 * π / 3, 2 * π / 3) ∈ DicutAngleSet ∧
    goemansWilliamsonDicutConstant / 4 *
      (1 + cos (2 * π / 3) + cos (2 * π / 3) + cos (2 * π / 3)) ≤
      1 - (2 * π / 3 + 2 * π / 3 + 2 * π / 3) / (2 * π) := by
  have hpi : 0 < π := pi_pos
  have hmem : (2 * π / 3, 2 * π / 3, 2 * π / 3) ∈ DicutAngleSet :=
    mem_dicutAngleSet_iff.2 ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  exact ⟨hmem, goemansWilliamsonDicutConstant_mul_add_cos_le hmem⟩

example : goemansWilliamsonDicutConstant / 4 *
      (1 + ⟪e0, -e0⟫ + ⟪e0, e0⟫ + ⟪-e0, e0⟫) ≤
      1 - (arccos ⟪e0, -e0⟫ + arccos ⟪e0, e0⟫ + arccos ⟪-e0, e0⟫) / (2 * π) :=
  goemansWilliamsonDicutConstant_mul_add_inner_le norm_e0 norm_neg_e0 norm_e0

/-! ### `(Q')`/`(P')` and Boolean MAX-2SAT (`Cslib.Complexity.MaxTwoSAT`) -/

private def sample2CNF : CNF ℕ :=
  [[(0, true)], [(0, false)], [(0, true), (1, true)], [(0, false), (1, false)]]

private theorem sample2CNF_le2 : ∀ c ∈ sample2CNF, c.length ≤ 2 := by
  intro c hc
  simp only [sample2CNF, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> decide

private theorem sample2CNF_mem_maxTwoSAT :
    (⟨sample2CNF, 3⟩ : Cslib.Complexity.MaxTwoSATInstance) ∈ Cslib.Complexity.MaxTwoSAT := by
  refine Cslib.Complexity.mem_MaxTwoSAT_iff.2 ⟨sample2CNF_le2, fun n => n == 0, ?_⟩
  decide

private theorem sample2CNF_countP_le_three (σ : ℕ → Bool) :
    sample2CNF.countP (Clause.eval σ) ≤ 3 := by
  change (sample2CNF.map (Clause.eval σ)).count true ≤ 3
  have h01 : ∀ b0 b1 : Bool,
      ((sample2CNF.map (Clause.eval (fun n => if n = 0 then b0 else b1))).count true) ≤ 3 := by
    decide
  simpa [sample2CNF, Clause.eval, Literal.eval] using h01 (σ 0) (σ 1)

example : (⟨sample2CNF, 4⟩ : Cslib.Complexity.MaxTwoSATInstance) ∉ Cslib.Complexity.MaxTwoSAT := by
  intro hmem
  obtain ⟨_, σ, h4⟩ := Cslib.Complexity.mem_MaxTwoSAT_iff.1 hmem
  have h3 := sample2CNF_countP_le_three σ
  omega

private noncomputable def satOptVec : Option ℕ → Vec2
  | none => e0
  | some 0 => e0
  | some _ => -e0

private theorem norm_satOptVec (o : Option ℕ) : ‖satOptVec o‖ = 1 := by
  rcases o with _ | n
  · exact norm_e0
  · cases n with
    | zero => exact norm_e0
    | succ _ => exact norm_neg_e0

private theorem satSdpValue_sample2CNF_eq (v : Option ℕ → Vec2) :
    satSdpValue (fun i : Fin sample2CNF.length => sample2CNF[i]) (fun _ => 1) v =
      2 + (1 - ⟪v (some 0), v (some 1)⟫) / 2 := by
  unfold satSdpValue
  change (∑ j : Fin 4, (1 : ℝ) * satSdpClause v sample2CNF[j]) = _
  rw [Fin.sum_univ_four]
  simp only [one_mul]
  change satSdpClause v [(0, true)] + satSdpClause v [(0, false)] +
      satSdpClause v [(0, true), (1, true)] + satSdpClause v [(0, false), (1, false)] = _
  simp only [satSdpClause, litVector, ↓reduceIte, Bool.false_eq_true, inner_neg_left,
    inner_neg_right, neg_neg]
  ring

private theorem isMaxOn_satOptVec :
    IsMaxOn (satSdpValue (fun i : Fin sample2CNF.length => sample2CNF[i]) (fun _ => 1))
      {v' | ∀ o, ‖v' o‖ = 1} satOptVec := by
  rw [isMaxOn_iff]
  intro v' hv'
  rw [satSdpValue_sample2CNF_eq, satSdpValue_sample2CNF_eq]
  have hopt_val : ⟪satOptVec (some 0), satOptVec (some 1)⟫ = -1 := by
    simp only [satOptVec, inner_neg_right, inner_e0_e0]
  have hbound : -1 ≤ ⟪v' (some 0), v' (some 1)⟫ := by
    have h := abs_real_inner_le_norm (v' (some 0)) (v' (some 1))
    rw [hv' (some 0), hv' (some 1), mul_one, abs_le] at h
    exact h.1
  linarith

example :
    (0.87856 : ℝ) * 3 <
      ∫ r : Vec2, (sample2CNF.countP (Clause.eval (satHyperplaneAssignment satOptVec r)) : ℝ)
        ∂stdGaussian Vec2 ∧
    (∃ r : Vec2, ∀ σ : ℕ → Bool,
      goemansWilliamsonConstant * satValue (fun i : Fin sample2CNF.length => sample2CNF[i])
          (fun _ => 1) σ ≤
        satValue (fun i : Fin sample2CNF.length => sample2CNF[i]) (fun _ => 1)
          (satHyperplaneAssignment satOptVec r)) ∧
    (∃ v : Option ℕ → Vec2, (∀ o, ‖v o‖ = 1) ∧
      IsMaxOn (satSdpValue (fun i : Fin sample2CNF.length => sample2CNF[i]) (fun _ => 1))
        {v' | ∀ o, ‖v' o‖ = 1} v) := by
  have hint := goemansWilliamsonConstant_mul_target_le_integral_of_mem
    sample2CNF_mem_maxTwoSAT norm_satOptVec (ε := 0)
    (fun v' hv' => by simpa only [add_zero] using isMaxOn_iff.1 isMaxOn_satOptVec v' hv')
  rw [sub_zero] at hint
  have hlt : (0.87856 : ℝ) * 3 < goemansWilliamsonConstant * ((3 : ℕ) : ℝ) := by
    have h := lt_goemansWilliamsonConstant
    norm_num at h ⊢
    linarith
  have hforall := exists_forall_goemansWilliamsonConstant_mul_sub_le
    (fun i : Fin sample2CNF.length => sample2CNF[i])
    (fun i => sample2CNF_le2 _ (List.getElem_mem i.2)) (fun _ => zero_le_one)
    norm_satOptVec (ε := 0)
    (fun v' hv' => by simpa only [add_zero] using isMaxOn_iff.1 isMaxOn_satOptVec v' hv')
  simp only [sub_zero] at hforall
  exact ⟨hlt.trans_le hint, hforall,
    exists_isMaxOn_satSdpValue (fun i : Fin sample2CNF.length => sample2CNF[i]) (fun _ => 1)⟩

example :
    (∀ side : Fin 2 → Bool,
      goemansWilliamsonConstant *
          signedCutValue (fun _ : Fin 1 => (0, 1)) (fun _ => 1) (fun _ => 1) side ≤
        ∫ r : Vec2, signedCutValue (fun _ : Fin 1 => (0, 1)) (fun _ => 1) (fun _ => 1)
          (hyperplaneSide (fun _ : Fin 2 => e0) r) ∂stdGaussian Vec2) ∧
    (∃ v : Fin 2 → Vec2, (∀ i, ‖v i‖ = 1) ∧
      IsMaxOn (signedSdpValue (fun _ : Fin 1 => (0, 1)) (fun _ => 1) (fun _ => 1))
        {v' | ∀ i, ‖v' i‖ = 1} v) := by
  let v₀ : Fin 2 → Vec2 := fun _ => e0
  have hv₀ : ∀ i, ‖v₀ i‖ = 1 := fun _ => norm_e0
  have hopt : IsMaxOn (signedSdpValue (fun _ : Fin 1 => (0, 1)) (fun _ => 1) (fun _ => 1))
      {v' | ∀ i, ‖v' i‖ = 1} v₀ := by
    rw [isMaxOn_iff]
    intro v' hv'
    simp only [signedSdpValue, Fin.sum_univ_one]
    have h1 := abs_real_inner_le_norm (v' 0) (v' 1)
    have h2 : ⟪v₀ 0, v₀ 1⟫ = 1 := inner_e0_e0
    rw [hv' 0, hv' 1, mul_one, abs_le] at h1
    linarith
  exact ⟨fun side => goemansWilliamsonConstant_mul_signedCutValue_le_integral
      (fun _ : Fin 1 => (0, 1)) (fun _ => zero_le_one) (fun _ => zero_le_one) hv₀ hopt side,
    exists_isMaxOn_signedSdpValue (fun _ : Fin 1 => (0, 1)) (fun _ => 1) (fun _ => 1)⟩

/-! ### `(Q'')`/`(P'')` and weighted MAX-DICUT (unbalanced & balanced 3-cycle) -/

private def asymEnds : Fin 2 → Fin 2 × Fin 2 := ![(0, 1), (1, 0)]
private noncomputable def asymWeights : Fin 2 → ℝ := ![2, 1]

private theorem asymWeights_nonneg (e : Fin 2) : 0 ≤ asymWeights e := by
  fin_cases e <;> simp [asymWeights]

private noncomputable def asymOptVec : Option (Fin 2) → Vec2
  | none => e0
  | some 0 => e0
  | some 1 => -e0

private theorem norm_asymOptVec (o : Option (Fin 2)) : ‖asymOptVec o‖ = 1 := by
  rcases o with _ | x
  · exact norm_e0
  · fin_cases x <;> [exact norm_e0; exact norm_neg_e0]

private theorem isMaxOn_asymOptVec :
    IsMaxOn (dicutSdpValue asymEnds asymWeights) {v' | ∀ o, ‖v' o‖ = 1} asymOptVec := by
  rw [isMaxOn_iff]
  intro v' hv'
  have hmax : dicutSdpValue asymEnds asymWeights v' ≤ 2 := by
    unfold dicutSdpValue asymEnds asymWeights
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h0 : -1 ≤ ⟪v' (some 0), v' none⟫ ∧ ⟪v' (some 0), v' none⟫ ≤ 1 := by
      have h := abs_real_inner_le_norm (v' (some 0)) (v' none)
      rwa [hv' _, hv' _, mul_one, abs_le] at h
    have h1 : -1 ≤ ⟪v' (some 1), v' none⟫ ∧ ⟪v' (some 1), v' none⟫ ≤ 1 := by
      have h := abs_real_inner_le_norm (v' (some 1)) (v' none)
      rwa [hv' _, hv' _, mul_one, abs_le] at h
    have h01 : -1 ≤ ⟪v' (some 0), v' (some 1)⟫ ∧ ⟪v' (some 0), v' (some 1)⟫ ≤ 1 := by
      have h := abs_real_inner_le_norm (v' (some 0)) (v' (some 1))
      rwa [hv' _, hv' _, mul_one, abs_le] at h
    have h10 : ⟪v' (some 1), v' (some 0)⟫ = ⟪v' (some 0), v' (some 1)⟫ := real_inner_comm _ _
    linarith
  have hval : dicutSdpValue asymEnds asymWeights asymOptVec = 2 := by
    unfold dicutSdpValue asymEnds asymWeights asymOptVec
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, inner_neg_left,
      inner_neg_right, inner_e0_e0]
    norm_num
  exact hmax.trans_eq hval.symm

example :
    (0.79607 : ℝ) * 2 <
      ∫ r : Vec2, dicutValue asymEnds asymWeights (dicutHyperplaneSet asymOptVec r)
        ∂stdGaussian Vec2 ∧
    (∃ r : Vec2, ∀ S : Fin 2 → Bool,
      goemansWilliamsonDicutConstant * dicutValue asymEnds asymWeights S ≤
        dicutValue asymEnds asymWeights (dicutHyperplaneSet asymOptVec r)) ∧
    (∃ v : Option (Fin 2) → Vec2, (∀ o, ‖v o‖ = 1) ∧
      IsMaxOn (dicutSdpValue asymEnds asymWeights) {v' | ∀ o, ‖v' o‖ = 1} v) := by
  have hint := goemansWilliamsonDicutConstant_mul_dicutValue_le_integral asymEnds
    asymWeights_nonneg norm_asymOptVec isMaxOn_asymOptVec (fun i => i == 0)
  have hval : dicutValue asymEnds asymWeights (fun i : Fin 2 => i == 0) = 2 := by
    simp [dicutValue, asymEnds, asymWeights]
  rw [hval] at hint
  have hlt : (0.79607 : ℝ) * 2 < goemansWilliamsonDicutConstant * 2 := by
    linarith [lt_goemansWilliamsonDicutConstant]
  have hforall := exists_forall_goemansWilliamsonDicutConstant_mul_sub_le asymEnds
    asymWeights_nonneg norm_asymOptVec (ε := 0)
    (fun v' hv' => by simpa only [add_zero] using isMaxOn_iff.1 isMaxOn_asymOptVec v' hv')
  simp only [sub_zero] at hforall
  exact ⟨hlt.trans_le hint, hforall, exists_isMaxOn_dicutSdpValue asymEnds asymWeights⟩

/-! ### Balanced (Eulerian) 3-cycle MAX-DICUT (`α > 0.87856`) -/

section BalancedTriangle

open GoemansWilliamsonMaxCut (tri triEnds triW norm_tri isMaxOn_tri)

private noncomputable def cycle3OptVec : Option (Fin 3) → Vec2
  | none => e0
  | some i => tri i

private theorem norm_cycle3OptVec (o : Option (Fin 3)) : ‖cycle3OptVec o‖ = 1 := by
  rcases o with _ | i
  · exact norm_e0
  · exact norm_tri i

private theorem isBalancedDigraph_cycle3 : IsBalancedDigraph triEnds triW := by
  refine isBalancedDigraph_of_outdeg_eq_indeg fun x => ?_
  fin_cases x <;> simp [triEnds, triW, Fin.sum_univ_three]

private theorem isMaxOn_cycle3OptVec :
    IsMaxOn (dicutSdpValue triEnds triW) {v' | ∀ o, ‖v' o‖ = 1} cycle3OptVec := by
  rw [isMaxOn_iff]
  intro v' hv'
  have h1 : 2 * dicutSdpValue triEnds triW v' = sdpValue triEnds triW (fun x => v' (some x)) :=
    two_mul_dicutSdpValue_eq_sdpValue_of_isBalancedDigraph isBalancedDigraph_cycle3 v'
  have h2 : 2 * dicutSdpValue triEnds triW cycle3OptVec = sdpValue triEnds triW tri :=
    two_mul_dicutSdpValue_eq_sdpValue_of_isBalancedDigraph isBalancedDigraph_cycle3 cycle3OptVec
  have hmax : sdpValue triEnds triW (fun x => v' (some x)) ≤ sdpValue triEnds triW tri :=
    isMaxOn_iff.1 isMaxOn_tri (fun x => v' (some x)) fun x => hv' (some x)
  linarith

example :
    (0.87856 : ℝ) <
      ∫ r : Vec2, dicutValue triEnds triW (dicutHyperplaneSet cycle3OptVec r) ∂stdGaussian Vec2 ∧
    goemansWilliamsonDicutConstant < 0.79608 := by
  have hint := goemansWilliamsonConstant_mul_sub_le_integral_of_isBalancedDigraph triEnds
    (fun _ => zero_le_one) (w := triW) isBalancedDigraph_cycle3 norm_cycle3OptVec (ε := 0)
    (fun v' hv' => by simpa only [add_zero] using isMaxOn_iff.1 isMaxOn_cycle3OptVec v' hv')
    (fun x => x == 0)
  have hval : dicutValue triEnds triW (fun x : Fin 3 => x == 0) = 1 := by
    unfold dicutValue triEnds triW
    rw [Fin.sum_univ_three]
    norm_num
  rw [hval, sub_zero, mul_one] at hint
  exact ⟨lt_goemansWilliamsonConstant.trans_le hint, goemansWilliamsonDicutConstant_lt⟩

end BalancedTriangle

/-! ### `(Q'')`/`(P'')` triple rounding instantiation -/

example :
    (∀ v : Fin 3 → Vec2, (∀ i, ‖v i‖ = 1) →
      goemansWilliamsonDicutConstant *
          tripleSdpValue (fun _ : Fin 1 => (0, 1, 2)) (fun _ => 1) (fun _ => 1) v ≤
        ∫ r : Vec2, tripleCutValue (fun _ : Fin 1 => (0, 1, 2)) (fun _ => 1) (fun _ => 1)
          (hyperplaneSide v r) ∂stdGaussian Vec2) ∧
    (∃ v : Fin 3 → Vec2, (∀ i, ‖v i‖ = 1) ∧
      IsMaxOn (tripleSdpValue (fun _ : Fin 1 => (0, 1, 2)) (fun _ => 1) (fun _ => 1))
        {v' | ∀ i, ‖v' i‖ = 1} v) :=
  ⟨fun _ hv => goemansWilliamsonDicutConstant_mul_tripleSdpValue_le_integral
      (fun _ : Fin 1 => (0, 1, 2)) (fun _ => zero_le_one) (fun _ => zero_le_one) hv,
    exists_isMaxOn_tripleSdpValue (fun _ : Fin 1 => (0, 1, 2)) (fun _ => 1) (fun _ => 1)⟩

end CslibFrontierTests.GoemansWilliamsonExtensions
