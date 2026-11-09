/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/StatisticalDistance.lean`)

public import CslibFrontier.Probability.StatisticalDistance.Coupling
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map

/-!
# Optimal couplings

On a finite type, two distributions have a coupling whose disagreement probability equals their
statistical distance (`Cslib.Probability.PMF.exists_coupling_toReal_eq_dist`). Together with the
coupling inequality `Cslib.Probability.PMF.CoupledWithin.dist_le` this characterizes statistical
distance as the minimum disagreement probability over all couplings. The coupling puts
`min (μ a) (ν a)` on each diagonal point `(a, a)` and spreads the excesses `μ - ν` and `ν - μ`
independently over the off-diagonal.

As a consequence, running a common kernel `K` from two coupled distributions moves them at most
the disagreement probability times the largest distance between two rows of `K`
(`Cslib.Probability.PMF.CoupledWithin.dist_bind_le`). With an optimal coupling this gives
`dist (μ.bind K) (ν.bind K) ≤ dist μ ν * D`, the step behind the submultiplicativity of the
pairwise distance of a Markov chain.

## Main results

* `Cslib.Probability.PMF.exists_coupling_toReal_eq_dist`: an optimal coupling exists.
* `Cslib.Probability.PMF.coupledWithin_dist`: two distributions are coupled within their
  statistical distance.
* `Cslib.Probability.PMF.CoupledWithin.dist_bind_le`: contraction of a common kernel through a
  coupling.
* `Cslib.Probability.PMF.dist_bind_le_mul`: contraction through an optimal coupling.

## References

* [LevinPeres2017], Proposition 4.7 and Remark 4.8 (optimal coupling).
-/

public section

open scoped ENNReal Cslib.Probability.PMF

namespace Cslib.Probability.PMF

variable {α β : Type*}

private theorem sum_coe_eq_one [Fintype α] (μ : PMF α) : ∑ a, μ a = 1 := by
  simpa [tsum_fintype] using μ.tsum_coe

/-- **Optimal coupling** ([LevinPeres2017], Proposition 4.7 and Remark 4.8). On a finite
type, two distributions have a coupling whose disagreement probability is exactly their
statistical distance. -/
theorem exists_coupling_toReal_eq_dist [Fintype α] (μ ν : PMF α) :
    ∃ ω : PMF (α × α), ω.map Prod.fst = μ ∧ ω.map Prod.snd = ν ∧
      (ω.toOuterMeasure {p | p.1 ≠ p.2}).toReal = dist μ ν := by
  classical
  set e : α → ℝ≥0∞ := fun a => μ a - ν a with he_def
  set f : α → ℝ≥0∞ := fun a => ν a - μ a with hf_def
  set m : α → ℝ≥0∞ := fun a => min (μ a) (ν a) with hm_def
  set δ : ℝ≥0∞ := ∑ a, e a with hδ_def
  have hμsplit (a : α) : μ a = e a + m a := tsub_add_min.symm
  have hνsplit (a : α) : ν a = f a + m a := by
    simp only [hf_def, hm_def, min_comm (μ a)]
    exact tsub_add_min.symm
  have hm_ne_top : ∑ a, m a ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [sum_coe_eq_one μ]; exact ENNReal.one_ne_top)
      (Finset.sum_le_sum fun a _ => min_le_left _ _)
  have hδf : ∑ a, f a = δ := by
    have h1 : δ + ∑ a, m a = 1 := by
      rw [← sum_coe_eq_one μ, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => (hμsplit a).symm
    have h2 : ∑ a, f a + ∑ a, m a = 1 := by
      rw [← sum_coe_eq_one ν, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => (hνsplit a).symm
    exact (ENNReal.add_left_inj hm_ne_top).mp (h2.trans h1.symm)
  have hδ_ne_top : δ ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [sum_coe_eq_one μ]; exact ENNReal.one_ne_top)
      (Finset.sum_le_sum fun a _ => tsub_le_self)
  have hcancel (x : ℝ≥0∞) (hx : δ = 0 → x = 0) : x * δ * δ⁻¹ = x := by
    by_cases hδ : δ = 0
    · simp [hx hδ]
    · rw [mul_assoc, ENNReal.mul_inv_cancel hδ hδ_ne_top, mul_one]
  have he_zero (h : δ = 0) (a : α) : e a = 0 :=
    (Finset.sum_eq_zero_iff.mp h) a (Finset.mem_univ a)
  have hf_zero (h : δ = 0) (a : α) : f a = 0 :=
    (Finset.sum_eq_zero_iff.mp (hδf.trans h)) a (Finset.mem_univ a)
  have hef (a : α) : e a * f a = 0 := by
    rcases le_total (μ a) (ν a) with h | h
    · simp [he_def, tsub_eq_zero_of_le h]
    · simp [hf_def, tsub_eq_zero_of_le h]
  let w : α × α → ℝ≥0∞ := fun p =>
    (if p.1 = p.2 then m p.1 else 0) + e p.1 * f p.2 * δ⁻¹
  have hrow (a : α) : ∑ b, w (a, b) = μ a := by
    simp only [w, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      ← Finset.sum_mul, ← Finset.mul_sum, hδf]
    rw [hcancel _ fun h => he_zero h a, add_comm, ← hμsplit]
  have hcol (b : α) : ∑ a, w (a, b) = ν b := by
    simp only [w, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      ← Finset.sum_mul]
    rw [← hδ_def, mul_comm δ, hcancel _ fun h => hf_zero h b, add_comm, ← hνsplit]
  have htotal : ∑ p, w p = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [hrow]
    exact sum_coe_eq_one μ
  let ω : PMF (α × α) := PMF.ofFintype w htotal
  refine ⟨ω, ?_, ?_, ?_⟩
  · ext a
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [ω, PMF.ofFintype_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact hrow a
  · ext b
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
    simp only [ω, PMF.ofFintype_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact hcol b
  · have hind (p : α × α) :
        Set.indicator {p : α × α | p.1 ≠ p.2} ω p = e p.1 * f p.2 * δ⁻¹ := by
      by_cases hp : p.1 = p.2
      · rw [Set.indicator_of_notMem (by simpa using hp), hp, hef, zero_mul]
      · rw [Set.indicator_of_mem hp]
        simp only [ω, PMF.ofFintype_apply, w, hp, ite_false, zero_add]
    have hδω : ω.toOuterMeasure {p | p.1 ≠ p.2} = δ := by
      rw [PMF.toOuterMeasure_apply, tsum_fintype]
      simp only [hind]
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ← Finset.sum_mul, hδf]
      rw [← hδ_def]
      exact hcancel δ id
    rw [hδω, dist_eq_sum_filter_lt, Finset.sum_filter, hδ_def,
      ENNReal.toReal_sum fun a _ => ne_top_of_le_ne_top (μ.apply_ne_top a) tsub_le_self]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · exact ENNReal.toReal_sub_of_le
        ((ENNReal.toReal_le_toReal (ν.apply_ne_top a) (μ.apply_ne_top a)).mp h.le)
        (μ.apply_ne_top a)
    · rw [tsub_eq_zero_of_le
        ((ENNReal.toReal_le_toReal (μ.apply_ne_top a) (ν.apply_ne_top a)).mp (not_lt.mp h)),
        ENNReal.toReal_zero]

/-- Two distributions on a finite type are coupled within their statistical distance. -/
theorem coupledWithin_dist [Fintype α] (μ ν : PMF α) :
    CoupledWithin μ ν (ENNReal.ofReal (dist μ ν)) := by
  obtain ⟨ω, h1, h2, h3⟩ := exists_coupling_toReal_eq_dist μ ν
  exact ⟨ω, h1, h2, by rw [← h3, ENNReal.ofReal_toReal (toOuterMeasure_ne_top _ _)]⟩

/-- Running a common kernel `K` from two distributions coupled within `ε` moves them at most
`ε * D`, where `D` bounds the distance between any two rows of `K`. -/
theorem CoupledWithin.dist_bind_le [Finite α] [Fintype β] {μ ν : PMF α} {ε : ℝ≥0∞}
    (h : CoupledWithin μ ν ε) (hε : ε ≠ ⊤) (K : α → PMF β) {D : ℝ}
    (hD : ∀ x y, dist (K x) (K y) ≤ D) :
    dist (μ.bind K) (ν.bind K) ≤ ε.toReal * D := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨ω, rfl, rfl, hω⟩ := h
  have hD0 : 0 ≤ D := by
    obtain ⟨a, -⟩ := ω.support_nonempty
    simpa using hD a.1 a.1
  have hpair (g : α × α → α) :
      (ω.bind fun p => (K (g p)).map (p, ·)).map Prod.snd = ω.bind (K ∘ g) := by
    rw [PMF.map_bind]
    exact congrArg ω.bind (funext fun p => (PMF.map_comp _ _ _).trans (PMF.map_id _))
  rw [PMF.bind_map, PMF.bind_map, ← hpair Prod.fst, ← hpair Prod.snd]
  refine (dist_map_le _ _ _).trans ?_
  rw [dist_bind_pair]
  calc ∑ p, (ω p).toReal * dist (K p.1) (K p.2)
      ≤ ∑ p, (if p ∈ {p : α × α | p.1 ≠ p.2} then (ω p).toReal else 0) * D := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hp : p.1 = p.2
        · simp [hp]
        · simpa [hp] using mul_le_mul_of_nonneg_left (hD p.1 p.2) ENNReal.toReal_nonneg
    _ = (ω.toOuterMeasure {p | p.1 ≠ p.2}).toReal * D := by
        rw [toOuterMeasure_apply_toReal, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by split_ifs <;> rfl
    _ ≤ ε.toReal * D := by gcongr

/-- Running a common kernel `K` moves two distributions at most their statistical distance times
the largest distance `D` between two rows of `K`. -/
theorem dist_bind_le_mul [Fintype α] [Fintype β] (μ ν : PMF α) (K : α → PMF β) {D : ℝ}
    (hD : ∀ x y, dist (K x) (K y) ≤ D) :
    dist (μ.bind K) (ν.bind K) ≤ dist μ ν * D := by
  have h := (coupledWithin_dist μ ν).dist_bind_le ENNReal.ofReal_ne_top K hD
  rwa [ENNReal.toReal_ofReal dist_nonneg] at h

end Cslib.Probability.PMF
