/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Divergence
public import CslibFrontier.Probability.Product
import Mathlib.Tactic

/-!
# Relative entropy of independent finite samples

The actual finite-product PMF has relative entropy equal to the sum of the
coordinate relative entropies. The full-support version suffices for binary
statistical testing families, without any assumed product-divergence bound.

## Main results

* `Cslib.Probability.PMF.toReal_klDiv_pi`: additivity for full-support finite products.
-/

public section
noncomputable section
open MeasureTheory InformationTheory Finset
namespace Cslib.Probability.PMF
variable {ι α : Type*} [Fintype ι] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

omit [Fintype α] in
/-- Relative entropy in nats is additive over actual independent finite samples.
Both distributions have full support; no conclusion about singular laws is needed. -/
theorem toReal_klDiv_pi [Finite α] (p q : ι → PMF α)
    (hp : ∀ i a, p i a ≠ 0) (hq : ∀ i a, q i a ≠ 0) :
    (klDiv (pi p).toMeasure (pi q).toMeasure).toReal =
      ∑ i, (klDiv (p i).toMeasure (q i).toMeasure).toReal := by
  classical
  let := Fintype.ofFinite α
  have hs (i : ι) : (p i).support ⊆ (q i).support :=
    fun a _ => (PMF.mem_support_iff _ _).mpr (hq i a)
  have hsp : (pi p).support ⊆ (pi q).support := by
    intro z _
    exact (mem_support_pi_iff q z).mpr fun i => (PMF.mem_support_iff _ _).mpr (hq i _)
  rw [toReal_klDiv_toMeasure hsp]
  simp_rw [toReal_klDiv_toMeasure (hs _)]
  have hlog (z : ι → α) :
      Real.log (((pi p) z).toReal / ((pi q) z).toReal) =
        ∑ i, Real.log ((p i (z i)).toReal / (q i (z i)).toReal) := by
    simp only [pi_apply, ENNReal.toReal_prod, ← prod_div_distrib]
    exact Real.log_prod (fun i _ => div_ne_zero
      (ENNReal.toReal_ne_zero.mpr ⟨hp i _, (p i).apply_ne_top _⟩)
      (ENNReal.toReal_ne_zero.mpr ⟨hq i _, (q i).apply_ne_top _⟩))
  simp_rw [hlog]
  exact sum_pi_mul_sum p (fun i a => Real.log ((p i a).toReal / (q i a).toReal))

/-- The elementary KL-to-Pearson bound for full-support finite distributions. -/
theorem toReal_klDiv_le_pearson (p q : PMF α)
    (hp : ∀ a, p a ≠ 0) (hq : ∀ a, q a ≠ 0) :
    (klDiv p.toMeasure q.toMeasure).toReal ≤
      ∑ a, ((p a).toReal - (q a).toReal) ^ 2 / (q a).toReal := by
  classical
  have hqp (a : α) : 0 < (q a).toReal :=
    ENNReal.toReal_pos (hq a) (q.apply_ne_top a)
  have hpp (a : α) : 0 < (p a).toReal :=
    ENNReal.toReal_pos (hp a) (p.apply_ne_top a)
  rw [toReal_klDiv_toMeasure (fun a _ => (PMF.mem_support_iff q a).mpr (hq a))]
  calc (∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)) ≤
      ∑ a, (p a).toReal * ((p a).toReal / (q a).toReal - 1) := by
         apply sum_le_sum
         intro a _
         exact mul_le_mul_of_nonneg_left
           (Real.log_le_sub_one_of_pos (div_pos (hpp a) (hqp a))) (hpp a).le
       _ = ∑ a, (((p a).toReal - (q a).toReal) ^ 2 / (q a).toReal +
           ((p a).toReal - (q a).toReal)) := by
         apply sum_congr rfl
         intro a _
         field_simp [(hqp a).ne']
         ring
       _ = _ := by rw [sum_add_distrib, sum_sub_distrib, sum_toReal, sum_toReal]; ring

end Cslib.Probability.PMF
