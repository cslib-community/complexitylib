/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module

import Complexity.Foundations.Probability.HierarchyTasks
import all Complexity.Foundations.Probability.DetectedHierarchy
import all Complexity.Foundations.LinearAlgebra.Matrix.CorrectionHierarchy
import Mathlib.Tactic.FinCases

/-!
# Cross-stage hierarchy task regression

The actual hierarchy starts from a nonzero three-vertex forward path. Full channels at stage
zero supply its first-stage invariant. The reward supported at the first original vertex remains
nonconstant after two stages. Primitive sampling data are constructed at every stage; local
preparation/normalization and both cross-stage calls are exercised on the same hierarchy.
-/

-- Radix domains at stage zero reduce through the natural-power instance.
set_option backward.isDefEq.respectTransparency false

-- This regression module deliberately exports no library API.
set_option linter.privateModule false

namespace ComplexityTests.HierarchyTasks

open Finset Matrix Matrix.HierarchyParams
open scoped BigOperators

private abbrev full {α V : Type*} (_ : α) (_ : V) : Prop := True
private abbrev hit {V : Type*} (t : Bool) (_ : V) : Prop := t = true

private abbrev V (P : HierarchyParams 2 1 1 1 0) (l : ℕ) := Fin (3 * (P.m + 1) ^ l)

private noncomputable def C (P : HierarchyParams 2 1 1 1 0) :
    Matrix (V P 0) (V P 0) ℝ :=
  of fun x y => if x.val + 1 = y.val then 1 / 2 else 0

private theorem C_upper (P : HierarchyParams 2 1 1 1 0) : (C P).IsStrictUpperTriangular := by
  intro x y h
  simp only [C, of_apply, ite_eq_right_iff]
  intro hxy
  exact (h (Fin.lt_def.mpr (by omega))).elim

private theorem C_nonneg (P : HierarchyParams 2 1 1 1 0) (x y : V P 0) : 0 ≤ C P x y := by
  simp only [C, of_apply]
  split_ifs <;> norm_num

private theorem C_row (P : HierarchyParams 2 1 1 1 0) : C P *ᵥ 1 ≤ 1 := by
  intro x
  simp only [C, mulVec, dotProduct, of_apply, Pi.one_apply, mul_one]
  change (∑ y : Fin 3, if x.val + 1 = y.val then (1 / 2 : ℝ) else 0) ≤ 1
  fin_cases x <;> norm_num [Fin.sum_univ_three]

private theorem channels {V : Type*} : Cslib.Probability.RetentionChannels
    (full (α := Unit) (V := V)) (full (α := Unit)) 1 1 1 1 1 0 where
  dens_X _ := by simp [full]
  dens_Y _ := by simp [full]
  lower := by norm_num
  upper := by norm_num
  pair _ _ _ := by simp [full]
  tail T _ := by
    have hempty : ({s : Unit | 2 * (#{x ∈ T | full s x} : ℝ) < #T * 1} : Finset Unit) = ∅ := by
      ext s
      simp only [full, filter_true, mul_one, mem_filter, mem_univ, true_and,
        notMem_empty, iff_false, not_lt]
      linarith [Nat.cast_nonneg (α := ℝ) #T]
    rw [hempty]
    norm_num

private abbrev copies (P : HierarchyParams 2 1 1 1 0) := radixCopyEquiv 3 P.m
private noncomputable abbrev H (P : HierarchyParams 2 1 1 1 0) :=
  hierarchy P (V := V P) (copies P) (fun _ => full (α := Unit)) (fun _ => full (α := Unit)) (C P)
private noncomputable abbrev E (P : HierarchyParams 2 1 1 1 0) :=
  hierarchyCorrection P (V := V P) (copies P)
    (fun _ => full (α := Unit)) (fun _ => full (α := Unit)) (C P)
private noncomputable abbrev Pr (P : HierarchyParams 2 1 1 1 0) :=
  hierarchyProj P (V := V P) (copies P)
    (fun _ => full (α := Unit)) (fun _ => full (α := Unit)) (C P)
private noncomputable abbrev W (P : HierarchyParams 2 1 1 1 0) (l : ℕ) :=
  rewardTransport (Pr P) (E P) l *ᵥ (fun x => if x = 0 then 1 else 0)

-- This primitive contract works for every actual hierarchy matrix and positive stage rate.
-- Its generous finite ranks are regression parameters, not uniform/native resource bounds.
private noncomputable def sampling (P : HierarchyParams 2 1 1 1 0) (l : ℕ) :
    P.CorrectionSampling (full (α := Unit)) (full (α := Unit)) (full (α := Unit))
      (full (α := Bool)) hit ((2 : ℝ)⁻¹ ^ l) (H P l) (P.k - 1) where
  I := fun _ _ => 0
  τ := fun _ => 1
  h := fun _ => 1
  ρ := fun _ => 1
  K := ⌈4 * (1 + (((2 : ℝ)⁻¹ ^ l)⁻¹) * ((P.k - 1 : ℕ) + 1))⌉₊
  Kc := 4 * (1 + Fintype.card (V P l))
  η := 1
  τ₀ := 0
  e := 0
  c := ((2 : ℝ)⁻¹ ^ l)⁻¹
  p := 1
  R := Fintype.card (V P l)
  π := 1 / 2
  π_pos := by norm_num
  density _ := by norm_num [hit, filter_eq', dens_eq_card_div_card]
  Q_support _ _ := rfl
  ρ_nonneg _ := zero_le_one
  ρ_le_one _ := le_rfl
  η_pos := one_pos
  ρ_one _ _ := rfl
  τ_nonneg _ := zero_le_one
  τ_le_one _ := le_rfl
  τ₀_nonneg := le_rfl
  τ_one _ _ := rfl
  I_zero _ _ _ := rfl
  c_nonneg := by positivity
  row_rank := by
    simpa only [div_one] using Nat.le_ceil
      (4 * (1 + (((2 : ℝ)⁻¹ ^ l)⁻¹) * ((P.k - 1 : ℕ) + 1)))
  terminal_pair _ _ _ := by simp [full, hit]
  p_nonneg := zero_le_one
  source_pair _ _ _ := by simp [full]
  incoming_count z _ := by
    simpa only [one_mul] using
      (show (#({w : V P l | 0 <
          P.correctionInput (full (α := Unit)) (full (α := Unit))
            ((2 : ℝ)⁻¹ ^ l) (H P l) (P.k - 1) w z / ((2 : ℝ)⁻¹ ^ l)} :
          Finset (V P l)) : ℝ) ≤ Fintype.card (V P l) by
        exact_mod_cast card_le_univ _)
  incoming_rank := by push_cast; rfl

private noncomputable abbrev value (P : HierarchyParams 2 1 1 1 0) :=
  hierarchyTaskValue P (V := V P) (copies P)
    (fun _ => full (α := Unit)) (fun _ => full (α := Unit)) (C P)
    (fun x => if x = 0 then 1 else 0) (fun _ => full (α := Unit))
    (fun _ => full (α := Bool)) (fun _ => hit) (sampling P)

private theorem invariant_one (P : HierarchyParams 2 1 1 1 0) :
    (H P 1).IsStrictUpperTriangular ∧ (∀ x y, 0 ≤ H P 1 x y) ∧
      H P 1 *ᵥ 1 ≤ 1 ∧ ∀ x y, H P 1 x y ≤ (2 : ℝ)⁻¹ ^ 1 := by
  apply hierarchy_invariant (π := fun _ => 1)
    (fun l _ _ h => radixCopyEquiv_lt 3 P.m l h) (by norm_num) one_pos
    (C_upper P) (C_nonneg P) (C_row P) 1
  intro j hj
  obtain rfl : j = 0 := by omega
  simpa only [pow_zero] using (channels (V := V P 0))

private theorem E0_zero (P : HierarchyParams 2 1 1 1 0) (x : V P 0) : E P 0 x 0 = 0 := by
  have htri := (P.isCorrectionSeq_correctionIter (X := full (α := Unit))
    (Y := full (α := Unit)) one_pos (C_nonneg P)).isStrictUpperTriangular (C_upper P) P.k
  change P.correction (full (α := Unit)) (full (α := Unit)) ((2 : ℝ)⁻¹ ^ 0) (C P) x 0 = 0
  rw [← P.correctionIter_last]
  exact htri (by change ¬ x.val < 0; omega)

private theorem W1_eq (P : HierarchyParams 2 1 1 1 0) (a : V P 1) :
    W P 1 a = P.weight (full (α := Unit)) (full (α := Unit)) 1 (C P)
      (ofLex (copies P 0 a)).2 (ofLex (copies P 0 a)).1 *
        (if (ofLex (copies P 0 a)).1 = 0 then 1 else 0) := by
  rw [W, rewardTransport_succ_mulVec, hierarchyProj_mulVec]
  simp only [rewardTransport, one_mulVec, mulVec, dotProduct, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, ite_true, E0_zero, Pi.add_apply, add_zero, hierarchy, pow_zero]

private theorem W1_nonneg (P : HierarchyParams 2 1 1 1 0) (a : V P 1) : 0 ≤ W P 1 a := by
  rw [W1_eq]
  exact mul_nonneg (P.weight_nonneg _ _) (by split_ifs <;> norm_num)

private abbrev primary (P : HierarchyParams 2 1 1 1 0) (x : V P 0) (l : ℕ) :=
  primaryCopy P (V := V P) (copies P) x l

private theorem W1_primary (P : HierarchyParams 2 1 1 1 0) (x : V P 0) :
    W P 1 (primary P x 1) = if x = 0 then 1 else 0 := by
  rw [W1_eq]
  simp only [primary, primaryCopy, Equiv.apply_symm_apply, ofLex_toLex]
  rw [P.weight_eq]
  simp [detectorWeight]

-- A nonzero forward path with a nonconstant reward after TWO actual copy/correction stages.
-- The source reward is supported at 0, so its zero at the later parent 2 is preserved by
-- strict forwardness. At parent 0 the direct inherited term remains at least one.
private theorem two_stage_nonconstant (P : HierarchyParams 2 1 1 1 0) :
    1 ≤ W P 2 (primary P 0 2) ∧ W P 2 (primary P 2 2) = 0 := by
  have hinv := invariant_one P
  have hf : 0 < (2 : ℝ)⁻¹ ^ 1 := by norm_num
  have hseq := P.isCorrectionSeq_correctionIter (X := full (α := Unit))
    (Y := full (α := Unit)) hf hinv.2.1
  have htri : (E P 1).IsStrictUpperTriangular := by
    rw [E, hierarchyCorrection_eq, ← P.correctionIter_last]
    exact hseq.isStrictUpperTriangular hinv.1 P.k
  have hE0 (x y : V P 1) : 0 ≤ E P 1 x y := by
    rw [E, hierarchyCorrection_eq, ← P.correctionIter_last]
    exact hseq.nonneg P.k x y
  have hstep (x : V P 0) :
      W P 2 (primary P x 2) =
        W P 1 (primary P x 1) + (E P 1 *ᵥ W P 1) (primary P x 1) := by
    rw [W, rewardTransport_succ_mulVec, hierarchyProj_mulVec]
    simp [primary, primaryCopy, P.weight_eq, detectorWeight]
  constructor
  · rw [hstep, W1_primary]
    have := mulVec_nonneg hE0 (W1_nonneg P) (primary P 0 1)
    norm_num at *
    linarith
  · rw [hstep, W1_primary]
    norm_num only [show (2 : V P 0) ≠ 0 by norm_num [V, Fin.ext_iff], ite_false, zero_add]
    change ∑ y, E P 1 (primary P 2 1) y * W P 1 y = 0
    apply sum_eq_zero
    intro y _
    by_cases hy : (ofLex (copies P 0 y)).1 = 0
    · have hlt : y < primary P 2 1 := by
        apply radixCopyEquiv_lt 3 P.m 0
        change copies P 0 y < copies P 0 ((copies P 0).symm (toLex (2, 0)))
        rw [Equiv.apply_symm_apply]
        have hh : (ofLex (copies P 0 y)).1 < (2 : V P 0) := by
          rw [hy]
          norm_num [V, Fin.lt_def]
        exact Prod.Lex.left _ _ hh
      exact mul_eq_zero_of_left (htri (not_lt_of_ge hlt.le)) _
    · rw [W1_eq]
      simp only [hy, ite_false, mul_zero]

-- An actual parameter witness makes the two-stage nonconstant task client nonvacuous.
example : ∃ P : HierarchyParams 2 1 1 1 0,
    1 ≤ value P (.row 2 .previousReward) (primary P 0 2) ∧
      value P (.row 2 .previousReward) (primary P 2 2) = 0 ∧ C P 0 1 = 1 / 2 := by
  obtain ⟨P⟩ := HierarchyParams.nonempty (q := 2) (cπ := 1) (Cπ := 1)
    (Cpair := 1) (Cvar := 0) (by norm_num) one_pos
  exact ⟨P, (two_stage_nonconstant P).1, (two_stage_nonconstant P).2, by norm_num [C, V]⟩

-- The two former leaves now call actual earlier constructors in the same global order.
example (P : HierarchyParams 2 1 1 1 0) :
    value P (.row 2 .base) = value P (.nextMatrix 1) :=
  hierarchyTask_base_succ _ _ _ _ _ _ _ _ _ _ 1

example (P : HierarchyParams 2 1 1 1 0) :
    value P (.row 2 .previousReward) =
      fun a => value P (.row 1 (.projectedReward (Fin.last P.k))) (copies P 1 a) :=
  hierarchyTask_previousReward_succ _ _ _ _ _ _ _ _ _ _ 1

-- Preparation and normalization are real local calls at both stages of that same client.
example (P : HierarchyParams 2 1 1 1 0) (hk : 0 < P.k) (l : Fin 2) :
    value P (.row l (.normalized ⟨P.k - 1, by omega⟩)) =
      (sampling P l).normalizedRecipe
        (value P (.row l (.input ⟨P.k - 1, by omega⟩)))
        ((sampling P l).preparationRecipe
          (value P (.row l (.input ⟨P.k - 1, by omega⟩))))
        (value P (.row l (.maximum (Fin.last P.k)))) := rfl

-- The second-stage stochastic reward consumes the preceding projected reward, with
-- true-model bounds derived from the first-stage hierarchy invariant.
example (P : HierarchyParams 2 1 1 1 0) (hk : 0 < P.k) (a : V P 2) :
    (𝔼 σ ∈ (univ : Finset Unit) ×ˢ (univ : Finset Bool),
      (sampling P 1).projectedRewardRecipe
        (fun b => value P (.row 0 (.projectedReward (Fin.last P.k))) (copies P 0 b))
        σ (copies P 1 a)) = value P (.row 2 .previousReward) a := by
  simpa only [full, filter_true] using
    expect_hierarchyTaskReward_crossStage P (V := V P) (copies P)
      (fun _ => full (α := Unit)) (fun _ => full (α := Unit)) (C P)
      (fun x => if x = 0 then 1 else 0) (fun _ => full (α := Unit))
      (fun _ => full (α := Bool)) (fun _ => hit) (sampling P) 0 (by omega)
      (fun l _ _ h => radixCopyEquiv_lt 3 P.m l h) (by norm_num) one_pos
      (C_upper P) (C_nonneg P) (C_row P) (π := fun _ => 1)
      (fun j hj => by
        obtain rfl : j = 0 := by omega
        simpa only [pow_zero] using (channels (V := V P 0)))
      a (by simp [full])

-- Zero stages and zero local corrections remain literal bases.
example (P : HierarchyParams 2 1 1 1 0) : value P (.row 0 .base) = C P :=
  hierarchyTask_base_zero _ _ _ _ _ _ _ _ _ _

example (P : HierarchyParams 2 1 1 1 0) (l : ℕ) :
    value P (.row l (.correction 0)) = 0 := by
  simp [value, hierarchyTaskValue, HierarchyParams.CorrectionSampling.value,
    HierarchyParams.correctionIter, cutoffCorrectionIter]

-- A zero-iteration stage still has a finite decreasing cross-stage call graph.
example : (HierarchyTask.nextMatrix (k := 0) 4).rank <
    (HierarchyTask.row (k := 0) 5 .base).rank :=
  HierarchyTask.rank_lt_of_dependency (.base 4)

end ComplexityTests.HierarchyTasks
