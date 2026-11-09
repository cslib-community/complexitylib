/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module

import CslibFrontier.Computability.LogSpaceDerandomization.RootMetric.ConditionalWalk
import CslibFrontier.Computability.LogSpaceDerandomization.SignedResidualBins
import all CslibFrontier.Computability.LogSpaceDerandomization.DetectedHierarchy
import all CslibFrontier.Computability.LogSpaceDerandomization.CorrectionHierarchy
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

namespace CslibFrontierTests.HierarchyTasks

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

-- The new routed residual client uses the same nonconstant two-stage hierarchy above.
-- A generous finite gate instance isolates routing/normalization from native rank budgets.
private noncomputable def denseLaws {W : Type*} [Fintype W] (k : ℝ → ℝ)
    (b M : ℝ) (hb : 0 < b) :
    DenseSamplingLaws (full (α := Bool) (V := W)) full hit k b M where
  h := fun _ => 1
  ρ := fun _ => 1
  K := ⌈2 * (1 + b⁻¹ * M)⌉₊
  η := 1
  c := b⁻¹
  usage_subset _ _ _ := trivial
  usage_nonempty _ := by simp [hit, filter_eq']
  support _ _ := rfl
  gate_nonneg _ := zero_le_one
  gate_le_one _ := le_rfl
  η_pos := one_pos
  gate_one _ _ := rfl
  c_nonneg := inv_nonneg.mpr hb.le
  rank_bound := by simpa only [div_one] using Nat.le_ceil (2 * (1 + b⁻¹ * M))
  pair _ _ _ := by simp [hit, full, inv_mul_cancel₀ hb.ne']

private noncomputable abbrev D (P : HierarchyParams 2 1 1 1 0) :=
  hierarchyResidual P (V := V P) (copies P)
    (fun _ => full (α := Unit)) (fun _ => full (α := Unit)) (C P) 1

private theorem D_nonneg (P : HierarchyParams 2 1 1 1 0) (x y : V P 1) : 0 ≤ D P x y :=
  P.residual_nonneg (by norm_num) (invariant_one P).2.1 x y

-- All row-mass bounds are derived from the actual residual; no mean is supplied as data.
private noncomputable def mass (P : HierarchyParams 2 1 1 1 0) : ℝ := ∑ x, ∑ y, D P x y
private theorem D_mass (P : HierarchyParams 2 1 1 1 0) (x : V P 1) :
    ∑ y, D P x y ≤ mass P :=
  single_le_sum (fun w _ => sum_nonneg (fun y _ => D_nonneg P w y)) (mem_univ x)

-- A fixed-symbol residual bin at stage one is averaged to the actual stage TWO matrix.
-- This is the complete direct/routed client; the separate residual raw estimator is still open.
example (P : HierarchyParams 2 1 1 1 0) (a d : V P 2) :
    let b : ℕ → ℝ := fun _ => if D P (ofLex (copies P 1 a)).1 (ofLex (copies P 1 d)).1 = 0
      then 1 else D P (ofLex (copies P 1 a)).1 (ofLex (copies P 1 d)).1
    let A := fun (j : Fin (P.m + 1)) i => denseLaws (W := V P 1)
      (routedBinCutoff (fun _ => 1) b i
        (fun w => copyFraction (P.copyCutoff ((2 : ℝ)⁻¹ ^ 1)) P.m w j)) (b i) (mass P)
        (by
          dsimp only [b]
          split_ifs with h
          · norm_num
          · exact lt_of_le_of_ne (D_nonneg P _ _) (Ne.symm h))
    (∑ i ∈ range 1, P.weight (full (α := Unit)) (full (α := Unit)) ((2 : ℝ)⁻¹ ^ 1) (H P 1)
      (ofLex (copies P 1 a)).2 (ofLex (copies P 1 a)).1 *
      (𝔼 s ∈ (univ : Finset Bool), (A (ofLex (copies P 1 d)).2 i).direct (D P) s
        (ofLex (copies P 1 a)).1 (ofLex (copies P 1 d)).1)) = H P 2 a d := by
  dsimp only
  have hb : ∀ i : ℕ, 0 < (if D P (ofLex (copies P 1 a)).1 (ofLex (copies P 1 d)).1 = 0
      then 1 else D P (ofLex (copies P 1 a)).1 (ofLex (copies P 1 d)).1 : ℝ) := by
    intro i
    split_ifs with h
    · norm_num
    · exact lt_of_le_of_ne (D_nonneg P _ _) (Ne.symm h)
  simpa only [full, filter_true, Nat.reduceAdd] using
    sum_expect_hierarchy_routed_bins P (V := V P) (copies P)
      (fun _ => full (α := Unit)) (fun _ => full (α := Unit)) (C P) 1 0
      (fun _ => 1) _ hb (fun _ _ => rfl) (fun _ => full) (fun _ => full)
      (fun _ => hit) a d (mass P)
      (fun j i => denseLaws _ _ _ (hb i)) (D_nonneg P) (D_mass P)
      (by
        change D P _ _ = 0 ∨ (if D P _ _ = 0 then 1 else D P _ _) ≤ D P _ _
        split_ifs with h
        · exact Or.inl h
        · exact Or.inr le_rfl)

-- Two native copy symbols are appended before the inherited suffix, rather than after it.
example : CopyPadding.identifier (2 : ZMod 17) [1, 0, 1] 1 = 13 := by decide
example : CopyPadding.identifier (2 : ZMod 17) [0, 1, 1] 1 = 11 := by decide

private noncomputable def src : CorrectionRowTask.Channel (Fin 3) (List ℕ) := ⟨0, 1 / 16, [7]⟩
private noncomputable def mid : CorrectionRowTask.Channel (Fin 3) (List ℕ) := ⟨1, 1 / 2, [8]⟩
private noncomputable def dst : CorrectionRowTask.Channel (Fin 3) (List ℕ) := ⟨2, 1 / 4, [9]⟩

-- Distinct roles/rates, a fine usage slice, and genuine midpoint source release.
example : HierarchyTask.binCopyRequests (k := 0) 1 src mid dst (1 / 8) 2 3 =
    [⟨.row 1 .base, ⟨0, 1 / 16, [2, 7]⟩, ⟨2, 1 / 8, [3, 9]⟩, ⟨2, 1 / 8, [3, 9]⟩⟩,
     ⟨.row 1 (.correction 0), ⟨0, 1 / 16, [2, 7]⟩, mid, mid⟩,
     ⟨.row 1 .base, mid, ⟨2, 1 / 8, [3, 9]⟩, ⟨2, 1 / 8, [3, 9]⟩⟩,
     ⟨.row 1 .weights, ⟨0, 1 / 2, [2, 7]⟩, ⟨2, 1 / 8, [3, 9]⟩, ⟨2, 1 / 8, [3, 9]⟩⟩] := by
  norm_num [HierarchyTask.binCopyRequests, HierarchyTask.copyRequests,
    CorrectionRowTask.Channel.throughCopy, src, mid, dst]

-- A zero entry is reconstructed even when every positive scale exceeds it.
example : (∑ i ∈ range 4, (1 / 2 : ℝ) * routedBinCutoff (fun t => min 1 t)
    (fun _ => 1 / 2) i (fun w => copyFraction (fun t => min 1 t) 2 w 1) (0 / (1 / 2))) = 0 := by
  simpa using sum_routedBinCutoff (χ := fun t => min 1 t)
    (route := fun w => copyFraction (fun t => min 1 t) 2 w 1) (b := fun _ => 1 / 2) 3
    (by norm_num) (by intro t ht; exact min_eq_left ht) (w := 0) (Or.inl rfl)

-- Two adjacent bins both contribute at an interior switch value, with nonprimary routing.
example : (∑ i ∈ range 3, ((1 / 2 : ℝ) ^ i) *
    routedBinCutoff (fun t => min 1 (max 0 (2 * t - 1))) (fun i => (1 / 2 : ℝ) ^ i) i
      (fun w => copyFraction (fun _ => 1) 1 w 1) ((3 / 8) / ((1 / 2 : ℝ) ^ i))) = 3 / 16 := by
  norm_num [sum_range_succ, routedBinCutoff, Cslib.binWeight, copyFraction]

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private def padded (x : Fin 3) : ZMod 17 := CopyPadding.identifier 2 [1, 0] x
private theorem padded_injective : Function.Injective padded := by
  apply (CopyPadding.identifier_injective (by decide : (2 : ZMod 17) ≠ 0) [1, 0]).comp
  decide

private noncomputable def affineBin : DenseSamplingLaws
    (fun s v => Cslib.Probability.affineRetains 17 1 9 s (padded v))
    (fun s v => Cslib.Probability.affineRetains 17 1 7 s (padded v))
    (fun s v => Cslib.Probability.affineRetains 17 1 3 s (padded v))
    (routedBinCutoff (fun d => min 1 (max 0 d)) (fun _ => 1 / 2) 0
      (fun w => copyFraction (fun _ => 1) 1 w 1)) (1 / 2) 1 := by
  have hceil : ⌈(17 : ℝ) * (1 / 2)⌉₊ = 9 :=
    (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  norm_num only [mul_one_div] at hceil
  simpa only [Nat.cast_ofNat, mul_one_div, hceil, pow_one] using
    (DenseSamplingLaws.ofAffine (H := 1) padded_injective (a := 1 / 2)
      (by norm_num) (by norm_num) (Lt := 3) (La := 7)
      (by norm_num) (by norm_num only [Nat.cast_ofNat]; rw [hceil]; norm_num) (by norm_num)
      (routedBinCutoff (fun d => min 1 (max 0 d)) (fun _ => 1 / 2) 0
        (fun w => copyFraction (fun _ => 1) 1 w 1)) (fun _ => 1) (fun _ => 1) 6 1 1
      (fun _ _ => rfl) (fun _ => zero_le_one) (fun _ => le_rfl) one_pos
      (fun _ _ => rfl) (by norm_num))

private noncomputable def affineInput : Matrix (Fin 3) (Fin 3) ℝ :=
  of fun x y => if x = 0 ∧ y = 1 then 1 / 2 else 0

private theorem affineInput_nonneg (x y : Fin 3) : 0 ≤ affineInput x y := by
  simp only [affineInput, of_apply]
  split_ifs <;> norm_num

private theorem affineInput_mass (x : Fin 3) : ∑ y, affineInput x y ≤ 1 := by
  fin_cases x <;> norm_num [affineInput, Fin.sum_univ_three]

-- Real two-rate affine channels, with a two-symbol native suffix: nonzero routing to copy 1.
example : (𝔼 s ∈ ({s | Cslib.Probability.affineRetains 17 1 7 s (padded 1)} : Finset _),
    affineBin.direct affineInput s 0 1) = 1 / 4 := by
  rw [affineBin.expect_direct (by norm_num) affineInput_nonneg affineInput_mass]
  norm_num [affineInput, routedBinCutoff, Cslib.binWeight, copyFraction]

-- The same whole table also has a true zero entry; the source/endpoint are arguments.
example : (𝔼 s ∈ ({s | Cslib.Probability.affineRetains 17 1 7 s (padded 0)} : Finset _),
    affineBin.direct affineInput s 1 0) = 0 := by
  rw [affineBin.expect_direct (by norm_num) affineInput_nonneg affineInput_mass]
  norm_num [affineInput, routedBinCutoff, Cslib.binWeight, copyFraction]

-- Bounded stochastic preparation and normalization of the actual stage-one residual.
-- This feeds the same hierarchy used above to construct stage TWO; no residual/mass
-- certificate is postulated. The fixed top scale is one and all zero entries are covered.
example (P : HierarchyParams 2 1 1 1 0) (i : ℕ) (x y : V P 1) :
    let b : ℕ → ℝ := fun j => (1 / 2) ^ j
    let r := fun w => copyFraction (P.copyCutoff ((2 : ℝ)⁻¹ ^ 1)) P.m w 0
    let A := denseLaws (W := V P 1)
      (boundedRoutedBinCutoff (fun d => min 1 (max 0 (2 * d - 1))) b
        ((P.k : ℝ) + 2) i r) (b i) 1 (by positivity)
    let base := fun _ : Unit × Bool => H P 1
    let corr := fun _ : Unit × Bool =>
      P.correction (full (α := Unit)) (full (α := Unit)) ((2 : ℝ)⁻¹ ^ 1) (H P 1)
    let prep := ResidualBinTask.value (fun d => min 1 (max 0 (2 * d - 1))) b
      ((P.k : ℝ) + 2) i r A.h A.ρ A.K full full hit base corr corr base base .preparation
    (𝔼 σ ∈ (univ : Finset Unit) ×ˢ (univ : Finset Bool),
      (b i * ((dens (univ : Finset Bool) : ℝ) / dens {s | hit s y})) *
        ResidualBinTask.value (fun d => min 1 (max 0 (2 * d - 1))) b
          ((P.k : ℝ) + 2) i r A.h A.ρ A.K full full hit base corr corr base prep
            .normalized σ x y) =
      b i * routedBinCutoff (fun d => min 1 (max 0 (2 * d - 1))) b i r (D P x y / b i) := by
  dsimp only
  simpa only [full, filter_true] using
    ResidualBinTask.expect_value_true P (full (α := Unit)) (full (α := Unit)) (H P 1)
      (by norm_num) (by norm_num) (invariant_one P).2.1 (invariant_one P).2.2.2
      (invariant_one P).2.2.1 (fun d => min 1 (max 0 (2 * d - 1)))
      (fun j => (1 / 2 : ℝ) ^ j) (fun _ => by positivity) (by norm_num) i
      (fun w => copyFraction (P.copyCutoff ((2 : ℝ)⁻¹ ^ 1)) P.m w 0)
      (full (α := Unit)) (full (α := Bool)) full hit (denseLaws _ _ _ (by positivity))
      x y (by simp [full])

-- Negative correction is sampled with its OWN terminal usage slice, not the midpoint factor.
example (P : HierarchyParams 2 1 1 1 0) (x y : V P 1) :
    (𝔼 σ ∈ (univ : Finset Unit) ×ˢ (univ : Finset Bool),
      CorrectionSampling.negativeRecipe (f := (2 : ℝ)⁻¹ ^ 1) full hit
        (sampling P 1).atom σ x y) =
      -P.correctionIter (full (α := Unit)) (full (α := Unit))
        ((2 : ℝ)⁻¹ ^ 1) (H P 1) ((P.k - 1) + 1) x y := by
  simpa only [full, filter_true] using (sampling P 1).expect_negativeRecipe
    (Ya := full) (by norm_num) (invariant_one P).2.1 (invariant_one P).2.2.1
    (fun _ _ _ => trivial) x y (by simp [full])

-- The actual signed sampler on the same multi-stage hierarchy recovers D, including -E.
example (P : HierarchyParams 2 1 1 1 0) (hkpos : 0 < P.k) (x y : V P 1) :
    let B := denseLaws (W := V P 1) id 1 1 (by norm_num)
    (𝔼 draw ∈ ((univ : Finset Unit) ×ˢ (univ : Finset Bool)) ×ˢ (univ : Finset Bool),
      (sampling P 1).residualSample full hit hit 1 (sampling P 1).atom
        (B.atom (H P 1)) (sampling P 1).atom draw x y) = D P x y := by
  dsimp only
  have hm := (sampling P 1).expect_residualSample
    (denseLaws (W := V P 1) id 1 1 (by norm_num)) (sampling P 1)
    (by norm_num) (by norm_num) (invariant_one P).2.1 (invariant_one P).2.2.1
    (fun _ _ _ => trivial) x y (by simp [full])
  have hk : P.k - 1 + 1 = P.k := by omega
  simp only [full, filter_true, hk, P.correctionIter_last, id_eq, div_one, one_mul] at hm
  rw [hm]
  change _ = P.residual (full (α := Unit)) (full (α := Unit))
    ((2 : ℝ)⁻¹ ^ 1) (H P 1) x y
  rw [P.residual_eq]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply]
  ring

-- Negative and midpoint calls preserve different endpoint roles and usage slices.
example : HierarchyTask.residualRequests (k := 0) 1 src mid dst (1 / 8) =
    [⟨.row 1 .base, src, ⟨2, 1 / 8, [9]⟩, ⟨2, 1 / 8, [9]⟩⟩,
     ⟨.row 1 (.correction 0), src, mid, mid⟩,
     ⟨.row 1 .base, mid, ⟨2, 1 / 8, [9]⟩, ⟨2, 1 / 8, [9]⟩⟩,
     ⟨.row 1 (.correction 0), src, ⟨2, 1 / 2, [9]⟩, dst⟩] := by
  norm_num [HierarchyTask.residualRequests, src, mid, dst]

-- A completed raw child is a genuine conditional-walk average. The existing hierarchy
-- evaluator must read it before applying the nonlinear preparation gate.
open Cslib in
private def rawGraph (P : HierarchyParams 2 1 1 1 0) (x y : V P 0) :
    RotationMap (RetainedPairSlice (full (α := Bool)) full x y) Bool :=
  ⟨fun p => (⟨p.2, by simp [full]⟩, p.1.val), by
    intro p
    rcases p with ⟨⟨v, hv⟩, d⟩
    rfl⟩

open Cslib in
private noncomputable def rawWalk (P : HierarchyParams 2 1 1 1 0) :
    Bool → Matrix (V P 0) (V P 0) ℝ :=
  conditionalWalk (full (α := Bool)) full (rawGraph P) (fun _ _ => 1)
    (fun b x y => if b then C P x y else 0)

open Cslib in
private lemma rawWalk_eq (P : HierarchyParams 2 1 1 1 0) (b : Bool) (x y : V P 0) :
    rawWalk P b x y = C P x y / 2 := by
  norm_num [rawWalk, conditionalWalk, full, pow_succ, Module.End.mul_apply,
    RotationMap.walk_apply, RotationMap.neighbor, rawGraph,
    Fintype.expect_eq_sum_div_card, Fintype.sum_bool, smul_eq_mul, div_eq_mul_inv, mul_comm]
  change (1 / 2 : ℚ) • (C P x y) = (1 / 2 : ℝ) * C P x y
  norm_num [Rat.smul_def]

example (P : HierarchyParams 2 1 1 1 0) (b : Bool) :
    let child := Function.update (value P) (.residual 0) (rawWalk P b)
    let B : DenseBinRecipe := ⟨id, fun _ => 1, 1, id, id, fun _ => 1, 1⟩
    hierarchyTaskRecipe P (copies P) (fun _ => full) (fun _ => full) (C P)
      (fun x => if x = 0 then 1 else 0) (fun _ => full) (fun _ => full) (fun _ => hit)
      (sampling P) child (.residualPreparation 0 0) B ((), true) 0 1 = 1 / 4 ∧
    hierarchyTaskRecipe P (copies P) (fun _ => full) (fun _ => full) (C P)
      (fun x => if x = 0 then 1 else 0) (fun _ => full) (fun _ => full) (fun _ => hit)
      (sampling P) child (.residualPreparation 0 0) B ((), true) 0 0 = 0 := by
  dsimp only
  have he := hierarchyTaskRecipe_residualPreparation P (copies P)
    (fun _ => full) (fun _ => full) (C P) (fun x => if x = 0 then 1 else 0)
    (fun _ => full) (fun _ => full) (fun _ => hit) (sampling P)
    (fun b => Function.update (value P) (.residual 0) (rawWalk P b)) 0 0
    (rawWalk P) (by intro b; simp)
    (⟨id, fun _ => 1, 1, id, id, fun _ => 1, 1⟩ : DenseBinRecipe) b ((), true)
  rw [he]
  norm_num [DenseRowRecipe.preparation, atomPrep, rowGate, rawWalk_eq, C, V]

end CslibFrontierTests.HierarchyTasks
