/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Combinatorics.CentralBinomial
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hypergeometric Intersection Sizes and Tail Counting

Cardinality decomposition of subsets intersecting a fixed subset in exactly or at least `g`
elements, with upper bounds on large intersections and base-2 logarithm gap estimates
([LiLiangYuZhou2023], Section 4.3, Claim 4.6 and Eq. (7), p. 19 / PDF p. 20).

## Main results

* `Cslib.card_inter_filter_powersetCard`: number of `m`-subsets intersecting `A` in exactly `g`.
* `Cslib.card_filter_powersetCard_inter_ge`: sum decomposition over `j ∈ [k, m]`.
* `Cslib.card_filter_powersetCard_inter_ge_half_le`: bound for `m / 2 ≤ |A ∩ B|`.
* `Cslib.quarter_mul_logb_le_logb_powersetCard_sub_nbr`: Claim 4.6 log gap `≥ (1 / 4) * m * log₂ F`.
-/

public section

namespace Cslib

/-- Exact cardinality of `{B ∈ R.powersetCard m | (A ∩ B).card = g}` for `A ⊆ R` with `A.card = m`
([LiLiangYuZhou2023], Section 4.3, Claim 4.6, p. 19 / PDF p. 20). -/
theorem card_inter_filter_powersetCard {α : Type*} [DecidableEq α]
    {R A : Finset α} {m g : ℕ} (hsub : A ⊆ R) (hA : A.card = m) :
    ((R.powersetCard m).filter fun B => (A ∩ B).card = g).card =
      m.choose g * (R.card - m).choose (m - g) := by
  by_cases hg : g ≤ m
  · have hbij : ((R.powersetCard m).filter fun B => (A ∩ B).card = g).card =
        (A.powersetCard g ×ˢ (R \ A).powersetCard (m - g)).card := by
      refine Finset.card_bij (fun B _ => (A ∩ B, B \ A)) ?_ ?_ ?_
      · intro B hB; simp only [Finset.mem_filter, Finset.mem_powersetCard] at hB
        obtain ⟨⟨hBR, hBm⟩, hgB⟩ := hB
        have hdisj : Disjoint (A ∩ B) (B \ A) := Finset.disjoint_left.mpr fun _ hx₁ hx₂ =>
          (Finset.mem_sdiff.mp hx₂).2 (Finset.mem_inter.mp hx₁).1
        have hunion : (A ∩ B) ∪ (B \ A) = B := by
          ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
        have hsum := Finset.card_union_of_disjoint hdisj; rw [hunion, hBm, hgB] at hsum
        simp only [Finset.mem_product, Finset.mem_powersetCard]
        exact ⟨⟨Finset.inter_subset_left, hgB⟩,
          ⟨fun x hx => Finset.mem_sdiff.mpr ⟨hBR (Finset.mem_sdiff.mp hx).1,
            (Finset.mem_sdiff.mp hx).2⟩, by omega⟩⟩
      · intro B₁ _ B₂ _ heq; rcases Prod.mk.inj heq with ⟨hP, hQ⟩
        ext x; have h₁ : x ∈ B₁ ↔ x ∈ (A ∩ B₁) ∪ (B₁ \ A) := by
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
        have h₂ : x ∈ B₂ ↔ x ∈ (A ∩ B₂) ∪ (B₂ \ A) := by
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
        rw [h₁, h₂, hP, hQ]
      · rintro ⟨P, Q⟩ hmem; simp only [Finset.mem_product, Finset.mem_powersetCard] at hmem
        obtain ⟨⟨hPA, hPc⟩, ⟨hQR, hQc⟩⟩ := hmem
        have hdisj : Disjoint P Q :=
          Finset.disjoint_left.mpr fun _ hx₁ hx₂ => (Finset.mem_sdiff.mp (hQR hx₂)).2 (hPA hx₁)
        have hi : A ∩ (P ∪ Q) = P := by
          ext x; simp only [Finset.mem_inter, Finset.mem_union]
          exact ⟨fun ⟨hxA, hxU⟩ => hxU.elim id fun hxQ =>
            False.elim ((Finset.mem_sdiff.mp (hQR hxQ)).2 hxA), fun hxP => ⟨hPA hxP, Or.inl hxP⟩⟩
        have hs : (P ∪ Q) \ A = Q := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
          exact ⟨fun ⟨hxU, hnA⟩ => hxU.elim (fun hxP => (hnA (hPA hxP)).elim) id,
            fun hxQ => ⟨Or.inr hxQ, (Finset.mem_sdiff.mp (hQR hxQ)).2⟩⟩
        exact ⟨P ∪ Q, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
          ⟨Finset.union_subset (hPA.trans hsub) (hQR.trans Finset.sdiff_subset),
            by rw [Finset.card_union_of_disjoint hdisj, hPc, hQc]; omega⟩, by rw [hi, hPc]⟩,
          Prod.ext hi hs⟩
    rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hA]
  · rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro B _; have := Finset.card_le_card (Finset.inter_subset_left (s₁ := A) (s₂ := B)); omega

/-- Exact cardinality decomposition of `{B ∈ R.powersetCard m | k ≤ (A ∩ B).card}` for `A ⊆ R`
with `A.card = m` ([LiLiangYuZhou2023], Section 4.3, Claim 4.6, p. 19 / PDF p. 20). -/
theorem card_filter_powersetCard_inter_ge {α : Type*} [DecidableEq α]
    {R A : Finset α} {m k : ℕ} (hsub : A ⊆ R) (hA : A.card = m) :
    ((R.powersetCard m).filter fun B => k ≤ (A ∩ B).card).card =
      ∑ j ∈ Finset.Icc k m, m.choose j * (R.card - m).choose (m - j) := by
  have heq : (R.powersetCard m).filter (fun B => k ≤ (A ∩ B).card) =
      (Finset.Icc k m).biUnion fun j => (R.powersetCard m).filter fun B => (A ∩ B).card = j := by
    ext B; simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc]
    refine ⟨fun ⟨hB, hkB⟩ => ⟨(A ∩ B).card, ⟨hkB,
      hA ▸ Finset.card_le_card Finset.inter_subset_left⟩, hB, rfl⟩, ?_⟩
    rintro ⟨j, ⟨hkj, _⟩, hB, rfl⟩; exact ⟨hB, hkj⟩
  rw [heq, Finset.card_biUnion (fun i _ j _ hij => Finset.disjoint_filter.mpr fun _ _ hi hj =>
    hij (hi.symm.trans hj))]
  exact Finset.sum_congr rfl fun j _ => card_inter_filter_powersetCard hsub hA

/-- Upper bound on `|F_nbr|` ([LiLiangYuZhou2023], Section 4.3, Claim 4.6, p. 19 / PDF p. 20). -/
theorem card_filter_powersetCard_inter_ge_half_le {α : Type*} [DecidableEq α]
    {R A : Finset α} {m F : ℕ} (hm_even : 2 ∣ m) (hm : 2 ≤ m) (hF : 2 ≤ F)
    (hsub : A ⊆ R) (hA : A.card = m) (hR : R.card ≤ F * m) :
    ((R.powersetCard m).filter fun B => m / 2 ≤ (A ∩ B).card).card ≤
      m * m.choose (m / 2) * (F * m).choose (m / 2) := by
  rw [card_filter_powersetCard_inter_ge hsub hA]
  have h2m_le : 2 * m ≤ F * m := Nat.mul_le_mul_right m hF
  have hterm : ∀ j ∈ Finset.Icc (m / 2) m,
      m.choose j * (R.card - m).choose (m - j) ≤ m.choose (m / 2) * (F * m).choose (m / 2) := by
    intro j hj; rw [Finset.mem_Icc] at hj
    have hmj_le : m - j ≤ m / 2 := by obtain ⟨mh, rfl⟩ := hm_even; omega
    exact Nat.mul_le_mul (Nat.choose_le_middle j m)
      ((Nat.choose_le_choose (m - j) ((Nat.sub_le _ _).trans hR)).trans
        (choose_le_choose_of_le_of_le_half hmj_le (by omega)))
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, smul_eq_mul, Nat.card_Icc, mul_assoc]
  exact Nat.mul_le_mul_right _ (by omega)

/-- Section 4.3 Claim 4.6 ([LiLiangYuZhou2023], Section 4.3, Claim 4.6 and Eq. (7), p. 19 /
PDF p. 20): `log₂ |F_all| - log₂ |F_nbr| ≥ (1 / 4) * m * log₂ F`. -/
theorem quarter_mul_logb_le_logb_powersetCard_sub_nbr {α : Type*} [DecidableEq α]
    {R A : Finset α} {m F : ℕ} (hm_even : 2 ∣ m) (hm : 2 ≤ m) (hF_even : 2 ∣ F) (hF : 2 ^ 20 ≤ F)
    (hsub : A ⊆ R) (hA : A.card = m) (hR_lo : (F / 2) * m ≤ R.card) (hR_hi : R.card ≤ F * m) :
    (1 / 4 : ℝ) * (m : ℝ) * Real.logb 2 F ≤
      Real.logb 2 (R.powersetCard m).card -
        Real.logb 2 ((R.powersetCard m).filter fun B => m / 2 ≤ (A ∩ B).card).card := by
  have hm_le_Fm : m ≤ F * m := le_mul_of_one_le_left (Nat.zero_le m) (by omega)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hall_ge : (m : ℝ) * Real.logb 2 F - (m : ℝ) ≤ Real.logb 2 (R.powersetCard m).card := by
    rw [Finset.card_powersetCard]
    have h1 := mul_logb_div_le_logb_choose (by omega)
      ((Nat.le_mul_of_pos_left m (by omega : 0 < F / 2)).trans hR_lo)
    have hdiv_ge : (F : ℝ) / 2 ≤ (R.card : ℝ) / (m : ℝ) := by
      obtain ⟨q, hq⟩ := hF_even
      have hFh : ((F / 2 : ℕ) : ℝ) = (F : ℝ) / 2 := by
        rw [hq, Nat.mul_div_cancel_left q (by omega)]; push_cast; ring
      rw [← hFh, le_div_iff₀ hm_pos]; exact_mod_cast hR_lo
    have hlog_ge := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hdiv_ge
    rw [Real.logb_div (by positivity) (by norm_num),
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hlog_ge; nlinarith
  set nbr := (R.powersetCard m).filter fun B => m / 2 ≤ (A ∩ B).card
  have hnbr_pos : (0 : ℝ) < (nbr.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr
    ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hA⟩,
      by rw [Finset.inter_self, hA]; exact Nat.div_le_self m 2⟩⟩)
  have hhalf_le_Fm : m / 2 ≤ F * m := (Nat.div_le_self m 2).trans hm_le_Fm
  have hprod_pos : (0 : ℝ) < ((F * m).choose (m / 2) : ℝ) := by
    exact_mod_cast Nat.choose_pos hhalf_le_Fm
  have hnbr_real : (nbr.card : ℝ) ≤ (2 : ℝ) ^ (2 * m) * ((F * m).choose (m / 2) : ℝ) := by
    exact_mod_cast ((card_filter_powersetCard_inter_ge_half_le hm_even hm (by omega) hsub hA
      hR_hi).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul Nat.lt_two_pow_self.le
      (Nat.choose_le_two_pow m (m / 2))))).trans_eq (by rw [← pow_add, two_mul])
  have hlog_nbr1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hnbr_pos hnbr_real
  rw [Real.logb_mul (by positivity) hprod_pos.ne', Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one, Nat.cast_mul,
    Nat.cast_ofNat] at hlog_nbr1
  obtain ⟨m_half, hm_eq⟩ := hm_even
  have hm_half_real : ((m / 2 : ℕ) : ℝ) = (m : ℝ) / 2 := by
    rw [hm_eq, Nat.mul_div_cancel_left m_half (by omega)]; push_cast; ring
  have hlog_fm := logb_choose_le_mul_logb_exp_mul_div hhalf_le_Fm
  rw [show Real.exp 1 * ((F * m : ℕ) : ℝ) / ((m / 2 : ℕ) : ℝ) = 2 * Real.exp 1 * (F : ℝ) by
    rw [hm_half_real, Nat.cast_mul]; field_simp, hm_half_real] at hlog_fm
  have hF_pos : (0 : ℝ) < (F : ℝ) := by exact_mod_cast (show 0 < F by omega)
  have hlog_2eF : Real.logb 2 (2 * Real.exp 1 * (F : ℝ)) ≤ 3 + Real.logb 2 F := by
    rw [Real.logb_mul (by positivity) hF_pos.ne']
    have h2 : Real.logb 2 (2 * Real.exp 1) ≤ 3 :=
      (Real.logb_le_iff_le_rpow (by norm_num) (by positivity)).mpr
        (by have := Real.exp_one_lt_d9; norm_num; linarith)
    linarith
  have hlogF_ge : (20 : ℝ) ≤ Real.logb 2 F := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hF_pos,
      show (2 : ℝ) ^ (20 : ℝ) = ((2 ^ 20 : ℕ) : ℝ) by norm_num]; exact_mod_cast hF
  nlinarith

end Cslib
