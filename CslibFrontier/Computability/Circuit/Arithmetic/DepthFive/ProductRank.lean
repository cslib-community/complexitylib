/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Params
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.RankMeasure
import CslibFrontier.Foundations.Data.Nat.Choose.Multichoose

/-!
# The rank measure of a product of homogeneous polynomials

Let `Q j` be homogeneous polynomials whose degrees `e j` add up to `n`. The component of
bidegree `(k, m)` of their product is a sum, over the ways to choose a bidegree `(f j, e j - f j)`
for each factor, of the products of the components of these bidegrees. For one choice, the
factors with `f j > λ e j` are applied first. Their operator maps the slice of bidegree `(a, b)`
to a slice of bidegree `(a - I, b + J)`, whose dimension is at most
`2 D ∏ j, q ^ |f j - λ e j|`. Summing over the choices gives
`R (∏ j, Q j) ≤ 2 D ∏ j, H (e j)`, the product-rank lemma of
[OpenAI, §3][OpenAI2026DepthFive].

## Main results

* `Cslib.Circuits.DepthFive.Params.Good.multichoose_mul_le`: the dimension of an intermediate
  slice.
* `Cslib.Circuits.DepthFive.rankMeasure_prod_le`: the rank measure of a product.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §3 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.DepthFive

open MvPolynomial Finset Params

variable {p : Params}

/-- The slice of bidegree `(a - i, b + j)` has dimension at most `2 D α ^ (i - ρ j)`. -/
theorem Params.Good.multichoose_mul_le (hp : p.Good) {i j : ℕ} (hi : i ≤ p.k) :
    (p.v.multichoose (p.a - i) * p.u.multichoose (p.b + j) : ℝ) ≤
      2 * p.D * p.α ^ ((i : ℝ) - p.ρ * j) := by
  obtain ⟨v', hv'⟩ := Nat.exists_eq_succ_of_ne_zero hp.v_pos.ne'
  have hv : (p.v : ℝ) = v' + 1 := by exact_mod_cast hv'
  have ha : (0 : ℝ) < p.a := by exact_mod_cast hp.a_pos
  have hb : (0 : ℝ) < p.b := by exact_mod_cast hp.b_pos
  have hu : (0 : ℝ) < p.u := by exact_mod_cast hp.u_pos
  have hα := hp.α_pos
  have hA : (p.v.multichoose (p.a - i) : ℝ) * (p.a + v') ^ i ≤
      p.v.multichoose p.a * p.a ^ i := by
    rw [hv']
    exact_mod_cast Nat.multichoose_succ_sub_mul_pow_le v' (hi.trans hp.k_le_a)
  have hB : (p.u.multichoose (p.b + j) : ℝ) * p.b ^ j ≤
      p.u.multichoose p.b * (p.b + p.u) ^ j := by
    exact_mod_cast Nat.multichoose_add_mul_pow_le p.u p.b j
  have hi' : (i : ℝ) * 2 ≤ p.a + v' + 1 := by
    have h : i * 2 ≤ p.a := by have := hp.four_n_le_a; have := p.hkm; lia
    have h' : ((i * 2 : ℕ) : ℝ) ≤ p.a := by exact_mod_cast h
    push_cast at h'
    linarith [v'.cast_nonneg (α := ℝ)]
  have hW : (p.a + v' + 1 : ℝ) ^ i ≤ 2 * (p.a + v') ^ i := by
    have h := one_add_mul_le_pow (a := -1 / (p.a + v' + 1 : ℝ))
      (by rw [le_div_iff₀ (by positivity)]; linarith) i
    have h1 : 1 + -1 / (p.a + v' + 1 : ℝ) = (p.a + v') / (p.a + v' + 1) := by
      field_simp; ring
    have h2 : -1 / 2 ≤ (i : ℝ) * (-1 / (p.a + v' + 1)) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]; linarith
    rw [h1, div_pow, le_div_iff₀ (by positivity)] at h
    nlinarith [pow_pos (show (0 : ℝ) < p.a + v' + 1 by positivity) i]
  have hX : (p.v.multichoose (p.a - i) : ℝ) ≤ 2 * p.v.multichoose p.a * p.α ^ i := by
    rw [α, hv, div_pow, ← add_assoc, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg (α := ℝ) (p.v.multichoose (p.a - i)))]
  have hY : (p.u.multichoose (p.b + j) : ℝ) * (p.α ^ p.ρ) ^ j ≤ p.u.multichoose p.b :=
    calc (p.u.multichoose (p.b + j) : ℝ) * (p.α ^ p.ρ) ^ j
        ≤ p.u.multichoose (p.b + j) * p.β ^ j :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Real.rpow_nonneg hα.le _) hp.α_rpow_le_β j) (Nat.cast_nonneg _)
      _ = p.u.multichoose (p.b + j) * p.b ^ j / (p.b + p.u) ^ j := by
          rw [β, div_pow, mul_div_assoc]
      _ ≤ p.u.multichoose p.b := by rwa [div_le_iff₀ (by positivity)]
  rw [Real.rpow_sub hα, Real.rpow_natCast, Real.rpow_mul hα.le, Real.rpow_natCast,
    mul_div_assoc', le_div_iff₀ (pow_pos (Real.rpow_pos_of_pos hα _) j)]
  calc (p.v.multichoose (p.a - i) : ℝ) * p.u.multichoose (p.b + j) * (p.α ^ p.ρ) ^ j
      = p.v.multichoose (p.a - i) * (p.u.multichoose (p.b + j) * (p.α ^ p.ρ) ^ j) := by ring
    _ ≤ 2 * p.v.multichoose p.a * p.α ^ i * p.u.multichoose p.b :=
        mul_le_mul hX hY (by positivity) (by positivity)
    _ = 2 * p.D * p.α ^ i := by simp only [D]; push_cast; ring

variable {K σ ι : Type*} [Field K] [Fintype σ] {s : σ → Prop} [DecidablePred s] [Fintype ι]

/-- The contribution of one choice of bidegrees `(f j, e j - f j)` for the factors. -/
private theorem rankMeasure_prod_component_le (hp : p.Good)
    (hv : Fintype.card {i // s i} = p.v) (hu : Fintype.card {i // ¬ s i} = p.u)
    {P : ι → MvPolynomial σ K} {e f : ι → ℕ} (hf : ∀ j, f j ≤ e j)
    (hP : ∀ j, (P j).IsWeightedHomogeneous (bidegWeight s) (f j, e j - f j))
    (he : ∑ j, e j = p.n) :
    (rankMeasure s (p.k, p.m) (p.a, p.b) (∏ j, P j) : ℝ) ≤
      2 * p.D * ∏ j, p.q ^ |(f j : ℝ) - p.lam * e j| := by
  classical
  have hq := hp.q_pos
  have hPall := IsWeightedHomogeneous.prod univ P _ fun j _ => hP j
  by_cases h : ∑ j, (f j, e j - f j) = (p.k, p.m)
  swap
  · rw [rankMeasure_eq_zero_of_ne hPall h, Nat.cast_zero]
    positivity
  have hk : ∑ j, f j = p.k := by simpa [Prod.fst_sum] using congrArg Prod.fst h
  let T := univ.filter fun j => p.lam * e j < f j
  have hPT : (∏ j ∈ T, P j).IsWeightedHomogeneous (bidegWeight s)
      (∑ j ∈ T, f j, ∑ j ∈ T, (e j - f j)) := by
    have := IsWeightedHomogeneous.prod T P _ fun j _ => hP j
    rwa [show ∑ j ∈ T, (f j, e j - f j) = (∑ j ∈ T, f j, ∑ j ∈ T, (e j - f j)) from
      Prod.ext Prod.fst_sum Prod.snd_sum] at this
  have hI : ∑ j ∈ T, f j ≤ p.k := hk ▸ sum_le_sum_of_subset (subset_univ T)
  have hrank : rankMeasure s (p.k, p.m) (p.a, p.b) (∏ j, P j) ≤
      p.v.multichoose (p.a - ∑ j ∈ T, f j) * p.u.multichoose (p.b + ∑ j ∈ T, (e j - f j)) := by
    rw [h] at hPall
    rw [← prod_filter_mul_prod_filter_not univ (fun j => p.lam * e j < f j), mul_comm] at hPall ⊢
    rw [← hv, ← hu, ← finrank_bihomogeneous (R := K)]
    exact rankMeasure_mul_le hPall hPT (hI.trans hp.k_le_a)
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast hp.n_pos.ne'
  have hm : (p.m : ℝ) ≠ 0 := by exact_mod_cast hp.m_pos.ne'
  have hρ : (1 + p.ρ) * p.lam = p.ρ := by
    have : (p.n : ℝ) = p.k + p.m := by exact_mod_cast p.hkm.symm
    rw [ρ, lam, this]
    field_simp
    ring
  have h0 : ∑ j, ((f j : ℝ) - p.lam * e j) = 0 := by
    rw [sum_sub_distrib, ← mul_sum, ← Nat.cast_sum, ← Nat.cast_sum, hk, he, lam,
      div_mul_cancel₀ _ hn, sub_self]
  have habs : ∑ j, |(f j : ℝ) - p.lam * e j| = 2 * ∑ j ∈ T, ((f j : ℝ) - p.lam * e j) := by
    have h1 : ∀ j, |(f j : ℝ) - p.lam * e j| =
        2 * (if p.lam * e j < f j then (f j : ℝ) - p.lam * e j else 0) -
          ((f j : ℝ) - p.lam * e j) := by
      intro j
      split_ifs with hj
      · rw [abs_of_pos (sub_pos.2 hj)]; ring
      · rw [abs_of_nonpos (sub_nonpos.2 (not_lt.1 hj))]; ring
    simp only [h1]
    rw [sum_sub_distrib, h0, sub_zero, ← mul_sum, sum_filter]
  have hexp : ((∑ j ∈ T, f j : ℕ) : ℝ) - p.ρ * (∑ j ∈ T, (e j - f j) : ℕ) =
      (1 + p.ρ) / 2 * ∑ j, |(f j : ℝ) - p.lam * e j| := by
    rw [habs, Nat.cast_sum, Nat.cast_sum, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [Nat.cast_sub (hf j)]
    linear_combination (e j : ℝ) * hρ
  calc (rankMeasure s (p.k, p.m) (p.a, p.b) (∏ j, P j) : ℝ)
      ≤ p.v.multichoose (p.a - ∑ j ∈ T, f j) *
          p.u.multichoose (p.b + ∑ j ∈ T, (e j - f j)) := by exact_mod_cast hrank
    _ ≤ 2 * p.D * p.α ^ (((∑ j ∈ T, f j : ℕ) : ℝ) - p.ρ * (∑ j ∈ T, (e j - f j) : ℕ)) :=
        hp.multichoose_mul_le hI
    _ = 2 * p.D * ∏ j, p.q ^ |(f j : ℝ) - p.lam * e j| := by
        rw [← Real.rpow_sum_of_pos hq, q, ← Real.rpow_mul hp.α_pos.le, hexp]

/-- The rank measure of a product of homogeneous polynomials whose degrees add up to `n` is at
most `2 D ∏ j, H (e j)`. -/
theorem rankMeasure_prod_le (hp : p.Good) (hv : Fintype.card {i // s i} = p.v)
    (hu : Fintype.card {i // ¬ s i} = p.u) {Q : ι → MvPolynomial σ K} {e : ι → ℕ}
    (hQ : ∀ j, (Q j).IsHomogeneous (e j)) (he : ∑ j, e j = p.n) :
    (rankMeasure s (p.k, p.m) (p.a, p.b) (∏ j, Q j) : ℝ) ≤ 2 * p.D * ∏ j, p.H (e j) := by
  classical
  have hprod : ∏ j, Q j = ∑ f ∈ Fintype.piFinset fun j => range (e j + 1),
      ∏ j, weightedHomogeneousComponent (bidegWeight s) (f j, e j - f j) (Q j) :=
    (prod_congr rfl fun j _ => (hQ j).eq_sum_bidegree_component).trans (prod_univ_sum _ _)
  rw [hprod, show ∏ j, p.H (e j) = _ from prod_univ_sum _ _, mul_sum]
  refine (Nat.cast_le.2 (rankMeasure_sum_le _ _)).trans ?_
  rw [Nat.cast_sum]
  exact sum_le_sum fun f hf => rankMeasure_prod_component_le hp hv hu
    (fun j => Nat.lt_succ_iff.1 (mem_range.1 (Fintype.mem_piFinset.1 hf j)))
    (fun j => weightedHomogeneousComponent_isWeightedHomogeneous ..) he

end Cslib.Circuits.DepthFive
