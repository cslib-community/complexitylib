/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Majority votes over a uniform sample space at arbitrary advantage

Generalizes `Cslib.card_filter_card_filter_le_le` (the `(8 / 9) ^ r` bound for advantage `2 / 3`)
to any error fraction `ε < 1 / 2`, deriving the counting bound directly from the `PMF` majority
tail bound `Cslib.Probability.PMF.iid_card_ge_le`.

## Main results

* `Cslib.card_filter_card_filter_le_of_err_lt_half`: if at least `(1 - ε) * |Ω|` elements of `Ω`
  lie in `G` (`0 ≤ ε < 1 / 2`), at most a `(4 * ε * (1 - ε)) ^ r` fraction of `2 r`-tuples over `Ω`
  have at most `r` entries in `G`.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 7.4][AroraBarak09]
-/

public section

namespace Cslib

/-- **Majority-vote counting bound for any advantage `ε < 1 / 2`.** If at least `(1 - ε) * |Ω|`
elements of `Ω` lie in `G` (`0 ≤ ε < 1 / 2`), then among the `2 r`-tuples over `Ω`, those with at
most `r` entries in `G` make up at most a `(4 * ε * (1 - ε)) ^ r` fraction. -/
theorem card_filter_card_filter_le_of_err_lt_half {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (G : Finset Ω) {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε < 1 / 2)
    (hG : (1 - ε) * (Fintype.card Ω : ℝ) ≤ G.card) (r : ℕ) :
    ((Finset.univ.filter fun ω : Fin (2 * r) → Ω =>
      (Finset.univ.filter fun i => ω i ∈ G).card ≤ r).card : ℝ) ≤
      (4 * ε * (1 - ε)) ^ r * (Fintype.card Ω : ℝ) ^ (2 * r) := by
  rcases r.eq_zero_or_pos with rfl | hr_pos
  · have hcard : (Finset.univ.filter fun ω : Fin (2 * 0) → Ω =>
        (Finset.univ.filter fun i => ω i ∈ G).card ≤ 0).card ≤ 1 :=
      (Finset.card_filter_le _ _).trans (by simp)
    simp only [Nat.mul_zero, pow_zero, mul_one]
    exact_mod_cast hcard
  rcases isEmpty_or_nonempty Ω with hEmpty | hNonempty
  · have : IsEmpty (Fin (2 * r) → Ω) := ⟨fun f => hEmpty.false (f ⟨0, by omega⟩)⟩
    have hcard0 : (Finset.univ.filter fun ω : Fin (2 * r) → Ω =>
        (Finset.univ.filter fun i => ω i ∈ G).card ≤ r).card = 0 :=
      Nat.eq_zero_of_le_zero ((Finset.card_filter_le _ _).trans (by simp))
    rw [hcard0, Nat.cast_zero]
    exact mul_nonneg (pow_nonneg (by nlinarith) r) (by positivity)
  classical
  set N := Fintype.card Ω
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos
  let bad : Ω → Bool := fun x => decide (x ∉ G)
  have hq_eq : (((Probability.PMF.uniformOfFintype Ω).map bad) true).toReal =
      ((Finset.univ.filter (· ∉ G)).card : ℝ) / N := by
    have h1 : ((Probability.PMF.uniformOfFintype Ω).map bad) true =
        (Probability.PMF.uniformOfFintype Ω).toOuterMeasure {x | x ∉ G} := by
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
      congr 1
      ext x
      simp [bad]
    rw [h1, Probability.PMF.toOuterMeasure_uniformOfFintype_toReal]
    rfl
  have hcard_compl : (Finset.univ.filter (· ∉ G)).card + G.card = N := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Ω)) (· ∈ G)
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ] at h
    omega
  have hq_le : (((Probability.PMF.uniformOfFintype Ω).map bad) true).toReal ≤ ε := by
    rw [hq_eq, div_le_iff₀ hN_pos]
    have hcomplR : ((Finset.univ.filter (· ∉ G)).card : ℝ) + G.card = N := by
      exact_mod_cast hcard_compl
    linarith
  have hiid := Probability.PMF.iid_card_ge_le hq_le hε₁.le r
  rw [Probability.PMF.iid_map, Probability.PMF.iid_uniformOfFintype,
    PMF.toOuterMeasure_map_apply, Probability.PMF.toOuterMeasure_uniformOfFintype_toReal] at hiid
  have hcard_fun : (Fintype.card (Fin (2 * r) → Ω) : ℝ) = (N : ℝ) ^ (2 * r) := by
    simp [Fintype.card_fin, N]
  rw [hcard_fun, div_le_iff₀ (pow_pos hN_pos (2 * r))] at hiid
  have hfilter_eq : (Finset.univ.filter fun ω : Fin (2 * r) → Ω =>
      ω ∈ (fun ω i => bad (ω i)) ⁻¹'
        {v : Fin (2 * r) → Bool | r ≤ (Finset.univ.filter fun i => v i = true).card}) =
      Finset.univ.filter (fun ω : Fin (2 * r) → Ω =>
        (Finset.univ.filter fun i => ω i ∈ G).card ≤ r) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_preimage, Set.mem_ofPred_eq,
      bad, decide_eq_true_eq]
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 * r)))) (fun i => ω i ∈ G)
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    omega
  rwa [hfilter_eq] at hiid

end Cslib
