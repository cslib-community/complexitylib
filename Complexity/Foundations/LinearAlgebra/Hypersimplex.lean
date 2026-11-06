/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Box
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

/-!
# The hypersimplex as a convex hull

The real unit box with integral prescribed mass is the convex hull of the
indicator vectors of subsets of that cardinality. This supplies the exact
relaxation representation used by [XuGaoHu2027], Section 5.1.
-/

public section

namespace Cslib

open Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Unit-box weights of a prescribed integral mass. -/
@[expose] def hypersimplex (m : ℕ) : Set (ι → ℝ) :=
  {w | (∀ i, w i ∈ Icc (0 : ℝ) 1) ∧ ∑ i, w i = m}

open Classical in
/-- Indicator vectors of all subsets of the prescribed cardinality. -/
@[expose] def subsetIndicators (m : ℕ) : Set (ι → ℝ) :=
  {w | ∃ s : Finset ι, s.card = m ∧ w = fun i => if i ∈ s then 1 else 0}

/-- The fixed-mass box is compact. -/
theorem isCompact_hypersimplex (m : ℕ) : IsCompact (hypersimplex (ι := ι) m) := by
  have heq : hypersimplex (ι := ι) m = Icc (0 : ι → ℝ) 1 ∩ {w | ∑ i, w i = (m : ℝ)} := by
    ext w
    simp only [hypersimplex, mem_ofPred_eq, mem_inter_iff, mem_Icc, Pi.le_def]
    aesop
  rw [heq]
  exact isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)

/-- The fixed-mass box is convex. -/
theorem convex_hypersimplex (m : ℕ) : Convex ℝ (hypersimplex (ι := ι) m) := by
  intro u hu v hv a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · change 0 ≤ a * u i + b * v i ∧ a * u i + b * v i ≤ 1
    constructor
    · exact add_nonneg (mul_nonneg ha (hu.1 i).1) (mul_nonneg hb (hv.1 i).1)
    · nlinarith [mul_le_mul_of_nonneg_left (hu.1 i).2 ha,
        mul_le_mul_of_nonneg_left (hv.1 i).2 hb]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hu.2, hv.2]
    nlinarith

open Classical in
/-- An integral-mass box vector cannot have exactly one fractional coordinate. -/
theorem integral_of_fractional_card_le_one (m : ℕ) (w : ι → ℝ)
    (hw : w ∈ hypersimplex m)
    (hc : (Finset.univ.filter fun i => 0 < w i ∧ w i < 1).card ≤ 1) :
    ∀ i, w i = 0 ∨ w i = 1 := by
  classical
  intro i
  by_contra hn
  have hwi : 0 < w i ∧ w i < 1 := by
    have hb := hw.1 i
    have hz : w i ≠ 0 := fun h => hn (Or.inl h)
    have ho : w i ≠ 1 := fun h => hn (Or.inr h)
    exact ⟨lt_of_le_of_ne hb.1 (Ne.symm hz), lt_of_le_of_ne hb.2 ho⟩
  let s := Finset.univ.filter fun j => w j = 1
  have hterm (j : ι) : w j = (if j ∈ s then 1 else 0) + if j = i then w i else 0 := by
    by_cases hj : j = i
    · subst j
      simp [s, ne_of_lt hwi.2]
    · have hnf : ¬ (0 < w j ∧ w j < 1) := by
        intro hf
        have he := Finset.card_le_one.mp hc j (by simp [hf]) i (by simp [hwi])
        exact hj he
      have hb := hw.1 j
      have he : w j = 0 ∨ w j = 1 := by
        by_cases hz : w j = 0
        · exact Or.inl hz
        · right
          have hp : 0 < w j := lt_of_le_of_ne hb.1 (Ne.symm hz)
          exact le_antisymm hb.2 (not_lt.mp fun hl => hnf ⟨hp, hl⟩)
      rcases he with he | he <;> simp [s, he, hj]
  have hm : (m : ℝ) = s.card + w i := by
    rw [← hw.2]
    calc
      (∑ j, w j) = ∑ j, ((if j ∈ s then 1 else 0) + if j = i then w i else 0) :=
        Finset.sum_congr rfl fun j _ => hterm j
      _ = _ := by simp [Finset.sum_add_distrib]
  have hlo : s.card < m := by exact_mod_cast (show (s.card : ℝ) < m by linarith)
  have hhi : m < s.card + 1 := by exact_mod_cast (show (m : ℝ) < (s.card : ℝ) + 1 by linarith)
  omega

private theorem extreme_integral (m : ℕ) (w : ι → ℝ)
    (hw : w ∈ (hypersimplex m).extremePoints ℝ) : ∀ i, w i = 0 ∨ w i = 1 := by
  classical
  let a : ι → Fin 1 → ℝ := fun _ _ => 1
  have heq : hypersimplex (ι := ι) m =
      {u | (∀ i, u i ∈ Icc (0 : ℝ) 1) ∧ ∑ i, u i • a i = fun _ => (m : ℝ)} := by
    ext u
    simp only [hypersimplex, mem_ofPred_eq, funext_iff, Finset.sum_apply,
      Pi.smul_apply, a, smul_eq_mul, mul_one, forall_const]
  have hi := linearIndependent_fractional_of_extreme a (fun _ => (m : ℝ)) w (heq ▸ hw)
  have hc : (Finset.univ.filter fun i => 0 < w i ∧ w i < 1).card ≤ 1 := by
    simpa only [Fintype.card_subtype, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] using hi.fintype_card_le_finrank
  exact integral_of_fractional_card_le_one m w hw.1 hc

/-- Exact convex-hull representation, including empty and full cardinalities. -/
theorem hypersimplex_eq_convexHull (m : ℕ) :
    hypersimplex (ι := ι) m = convexHull ℝ (subsetIndicators m) := by
  classical
  have hv : subsetIndicators (ι := ι) m ⊆ hypersimplex m := by
    rintro w ⟨s, hs, rfl⟩
    exact ⟨fun i => by dsimp only; split_ifs <;> norm_num, by simp [hs]⟩
  apply Subset.antisymm
  · rw [← closure_convexHull_extremePoints (isCompact_hypersimplex (ι := ι) m)
      (convex_hypersimplex m)]
    apply closure_minimal
    · apply convexHull_mono
      intro w hw
      let s := Finset.univ.filter fun i => w i = 1
      have he : w = fun i => if i ∈ s then 1 else 0 := by
        funext i
        rcases extreme_integral m w hw i with hi | hi <;> simp [s, hi]
      refine ⟨s, ?_, he⟩
      have hm := hw.1.2
      rw [he] at hm
      simpa using hm
    · apply Set.Finite.isClosed_convexHull ℝ
      have hf : (Set.range (fun s : Finset ι => (fun i => if i ∈ s then (1 : ℝ) else 0))).Finite :=
        Set.finite_range _
      apply hf.subset
      rintro w ⟨s, _, rfl⟩
      exact ⟨s, rfl⟩
  · exact convexHull_min hv (convex_hypersimplex m)

open Classical in
/-- A box vector of integral mass with at most two fractional coordinates is
integral or is an interior interpolation of two subsets differing by one swap. -/
theorem hypersimplex_indicator_or_swap (m : ℕ) (w : ι → ℝ)
    (hw : w ∈ hypersimplex m)
    (hc : (Finset.univ.filter fun i => 0 < w i ∧ w i < 1).card ≤ 2) :
    (∀ i, w i = 0 ∨ w i = 1) ∨
      ∃ (R : Finset ι) (i j : ι) (t : ℝ), i ≠ j ∧ i ∉ R ∧ j ∉ R ∧
        R.card + 1 = m ∧ 0 < t ∧ t < 1 ∧
        ∀ k, w k = if k ∈ R then 1 else if k = i then 1 - t else if k = j then t else 0 := by
  classical
  by_cases hint : ∀ i, w i = 0 ∨ w i = 1
  · exact Or.inl hint
  right
  have hnot : ¬ (Finset.univ.filter fun i => 0 < w i ∧ w i < 1).card ≤ 1 :=
    fun h => hint (integral_of_fractional_card_le_one m w hw h)
  have htwo : (Finset.univ.filter fun i => 0 < w i ∧ w i < 1).card = 2 := by omega
  obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp htwo
  have hwi : 0 < w i ∧ w i < 1 := by
    have : i ∈ Finset.univ.filter fun k => 0 < w k ∧ w k < 1 := by rw [he]; simp
    exact (Finset.mem_filter.mp this).2
  have hwj : 0 < w j ∧ w j < 1 := by
    have : j ∈ Finset.univ.filter fun k => 0 < w k ∧ w k < 1 := by rw [he]; simp
    exact (Finset.mem_filter.mp this).2
  let R := Finset.univ.filter fun k => w k = 1
  have hiR : i ∉ R := by simp [R, ne_of_lt hwi.2]
  have hjR : j ∉ R := by simp [R, ne_of_lt hwj.2]
  have hother (k : ι) (hki : k ≠ i) (hkj : k ≠ j) : w k = 0 ∨ w k = 1 := by
    have hnf : ¬ (0 < w k ∧ w k < 1) := by
      intro hk
      have : k ∈ Finset.univ.filter fun k => 0 < w k ∧ w k < 1 := by simp [hk]
      rw [he] at this
      simp [hki, hkj] at this
    have hb := hw.1 k
    by_cases hz : w k = 0
    · exact Or.inl hz
    · exact Or.inr (le_antisymm hb.2 (not_lt.mp fun h => hnf
        ⟨lt_of_le_of_ne hb.1 (Ne.symm hz), h⟩))
  have hterm (k : ι) : w k = (if k ∈ R then 1 else 0) +
      (if k = i then w i else 0) + (if k = j then w j else 0) := by
    by_cases hki : k = i
    · subst k; simp [hiR, hij]
    · by_cases hkj : k = j
      · subst k; simp [hjR, hij.symm]
      · rcases hother k hki hkj with hk | hk <;> simp [R, hk, hki, hkj]
  have hmR : (m : ℝ) = R.card + w i + w j := by
    rw [← hw.2]
    calc
      (∑ k, w k) = ∑ k, ((if k ∈ R then 1 else 0) +
        (if k = i then w i else 0) + (if k = j then w j else 0)) :=
          Finset.sum_congr rfl fun k _ => hterm k
      _ = _ := by simp [Finset.sum_add_distrib]
  have hlo : R.card < m := by exact_mod_cast (show (R.card : ℝ) < m by linarith)
  have hhi : m < R.card + 2 := by exact_mod_cast (show (m : ℝ) < (R.card : ℝ) + 2 by linarith)
  have hcard : R.card + 1 = m := by omega
  have hsum : w i + w j = 1 := by
    have hh : (R.card : ℝ) + 1 = m := by exact_mod_cast hcard
    linarith
  refine ⟨R, i, j, w j, hij, hiR, hjR, hcard, hwj.1, hwj.2, fun k => ?_⟩
  by_cases hki : k = i
  · subst k; simp [hiR]; linarith
  · by_cases hkj : k = j
    · subst k; simp [hjR, hij.symm]
    · rcases hother k hki hkj with hk | hk <;> simp [R, hk, hki, hkj]

end Cslib
