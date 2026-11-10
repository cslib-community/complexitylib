/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Spread.Talagrand
import CslibFrontier.Probability.Minimax
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Coin

/-!
# Finite minimax duality for spread laws

Normalize an arbitrary law by its largest containment moment, putting the missing mass at the
empty set. The resulting law is spread. Finite minimax then turns bounds under every spread law
into a single majorizing probability witness. This realizes the converse of the elementary
Fubini implication without assuming a separation or fractional-cover contract.

## Main results

* `exists_coverScore_majorant`: a probability witness from all spread-law bounds.
* `conjecture711At_of_conjecture78At`: the source converse at the same constant.
* `conjecture78_iff_conjecture711`: the two source assertions are equivalent.

## References

[Talagrand2010Small], proof that Conjecture 7.8 implies 7.11, author PDF pp.10–11.
The proof below uses the existing finite minimax theorem in place of its separation formulation.
-/

public section
namespace Cslib.Probability.Spread
open Finset
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def dilute (ν : PMF (Finset ι)) (r : Set.Icc (0 : ℝ) 1) : PMF (Finset ι) :=
  (PMF.coin r).bind fun b => if b then ν else PMF.pure ∅

omit [DecidableEq ι] in
private theorem dilute_mean (ν : PMF (Finset ι)) (r : Set.Icc (0 : ℝ) 1) (f : Finset ι → ℝ) :
    (∑ J, (dilute ν r J).toReal * f J) =
      (r : ℝ) * (∑ J, (ν J).toReal * f J) + (1 - r) * f ∅ := by
  classical
  rw [dilute, PMF.sum_bind_mul]
  simp [PMF.coin_apply_toReal, PMF.pure_apply, apply_ite, ite_mul]

/-- Bounds on a nonnegative score against every spread law produce a majorizing probability
witness. The input is an actual universal moment bound, not an assumed duality principle. -/
theorem exists_coverScore_majorant {q b : ℝ} (hq : 0 < q) (f : Finset ι → ℝ)
    (hf : ∀ J, 0 ≤ f J)
    (h : ∀ ν : PMF (Finset ι), IsSpreadLaw q ν → ∑ J, (ν J).toReal * f J ≤ b) :
    ∃ η : PMF (Finset ι), ∀ J, f J ≤ b * coverScore q η J := by
  classical
  obtain ⟨η, hη⟩ := PMF.exists_forall_sum_mul_le
    (fun I J : Finset ι => f J - b * upperKernel q I J) (ε := 0) (fun ν => by
      let moment (I : Finset ι) := ∑ J, (ν J).toReal * upperKernel q I J
      obtain ⟨I, _, hI⟩ := exists_max_image univ moment univ_nonempty
      let m := moment I
      have hm : 1 ≤ m := by
        have hh := hI ∅ (mem_univ ∅)
        simpa only [moment, upperKernel_empty, mul_one, PMF.sum_toReal] using hh
      have hm0 : 0 < m := by linarith
      let r : Set.Icc (0 : ℝ) 1 := ⟨1 / m, by
        constructor
        · positivity
        · exact (div_le_one hm0).mpr hm⟩
      let μ := dilute ν r
      have hμ : IsSpreadLaw q μ := (isSpreadLaw_iff_kernel hq μ).mpr fun K => by
        by_cases hK : K = ∅
        · subst K
          simp only [upperKernel_empty, mul_one, PMF.sum_toReal, le_refl]
        · have he : upperKernel q K ∅ = 0 := by simp [upperKernel, hK]
          calc (∑ J, (μ J).toReal * upperKernel q K J) = (1 / m) * moment K := by
                simp only [μ, dilute_mean, he, mul_zero, add_zero, r, moment]
            _ ≤ (1 / m) * m := mul_le_mul_of_nonneg_left (hI K (mem_univ K))
                (by positivity)
            _ = 1 := by field_simp
      have hμf := h μ hμ
      rw [dilute_mean] at hμf
      have hlow : 0 ≤ (1 - (r : ℝ)) * f ∅ := mul_nonneg (sub_nonneg.mpr r.2.2) (hf ∅)
      have hdiv : (∑ J, (ν J).toReal * f J) / m ≤ b := by
        have hh : (r : ℝ) * (∑ J, (ν J).toReal * f J) ≤ b := by linarith
        simpa only [r, one_div, div_eq_mul_inv, mul_comm, one_mul] using hh
      refine ⟨I, ?_⟩
      have hb := (div_le_iff₀ hm0).mp hdiv
      calc _ = (∑ J, (ν J).toReal * f J) - b * m := by
            simp only [mul_sub, sum_sub_distrib, m, moment, mul_sum]
            congr 1
            apply sum_congr rfl
            intro J _
            ring
        _ ≤ 0 := sub_nonpos.mpr hb)
  refine ⟨η, fun J => ?_⟩
  have he : (∑ I, (η I).toReal * (f J - b * upperKernel q I J)) =
      f J - b * coverScore q η J := by
    simpa only [sub_eq_add_neg, neg_mul, coverScore] using
      PMF.sum_affine η (f J) (-b) (fun I => upperKernel q I J)
  have hh := hη J
  rw [he] at hh
  exact sub_nonpos.mp hh

/-- The source's separation direction, with all finite witnesses constructed by minimax. -/
theorem conjecture711At_of_conjecture78At {α : ℝ} (hα : 0 < α) (hα' : α < 1)
    (h : Conjecture78At α) : Conjecture711At α := by
  intro n p hp hp' A hA
  exact exists_coverScore_majorant (mul_pos hα hp) (theta α A)
    (theta_nonneg hα.le hα'.le A) (fun ν hν => h n p hp hp' ν hν A hA)

/-- Talagrand's Conjectures 7.8 and 7.11 have the same universal-constant content. -/
theorem conjecture78_iff_conjecture711 : Conjecture78 ↔ Conjecture711 := by
  refine ⟨?_, conjecture78_of_conjecture711⟩
  rintro ⟨α, hα, hα', h⟩
  exact ⟨α, hα, hα', conjecture711At_of_conjecture78At hα hα' h⟩

end Cslib.Probability.Spread
