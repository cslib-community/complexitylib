/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Schedule

/-!
# The weight of an interval of layers

In the sum over type words, a layer of type `𝒟` has weight `α⁻¹` when it is differentiated and
`β` when it is multiplied [OpenAI, §5][OpenAI2026DepthFive]. Since `β` is close to `α ^ ρ`, the
weight of an interval of layers is governed by its discrepancy in the balanced schedule, and it
is at most `2 * n`.

## Main definitions

* `Params.layerWeight`: the weight of a layer of type `𝒟`.

## Main results

* `Params.prod_layerWeight_le`: the layer weights of an interval multiply to at most
  `(2 * √n) ^ 2`.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §5 (unrefereed preprint)
-/

@[expose] public section

namespace Cslib.Circuits.DepthFive.Params

variable {p : Params}

/-- Whether the layer with index `t` is differentiated. -/
abbrev isVNat (p : Params) (t : ℕ) : Prop := ∃ r < p.k, t = 2 * r + r * p.s / p.k

/-- The weight of a layer of type `𝒟`. -/
noncomputable def layerWeight (p : Params) (t : ℕ) : ℝ :=
  if p.isVNat t then p.α⁻¹ else p.β

theorem layerWeight_val (t : Fin p.n) :
    p.layerWeight t = if p.isV t then p.α⁻¹ else p.β := by
  simp [layerWeight, isV]

/-- The layer weights of an interval multiply to at most `2 * n`, by the discrepancy bound. -/
theorem prod_layerWeight_le (hp : p.Good) (i : ℕ) {j : ℕ} (hj : j ≤ p.n) :
    ∏ t ∈ Finset.Ico i j, p.layerWeight t ≤ (2 * √(p.n : ℝ)) ^ 2 := by
  have hIco : Finset.Ico i j = (Finset.range p.n).filter fun t => i ≤ t ∧ t < j := by
    ext t; simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]; omega
  rw [hIco, Finset.prod_filter,
    ← Fin.prod_univ_eq_prod_range fun t => if i ≤ t ∧ t < j then p.layerWeight t else 1]
  have hsplit (t : Fin p.n) : (if i ≤ (t : ℕ) ∧ (t : ℕ) < j then p.layerWeight t else 1) =
      (if (i ≤ (t : ℕ) ∧ (t : ℕ) < j) ∧ p.isV t then p.α⁻¹ else 1) *
        if (i ≤ (t : ℕ) ∧ (t : ℕ) < j) ∧ ¬ p.isV t then p.β else 1 := by
    rw [layerWeight_val]
    by_cases h : i ≤ (t : ℕ) ∧ (t : ℕ) < j <;> cases p.isV t <;> simp [h]
  rw [Finset.prod_congr rfl fun t _ => hsplit t, Finset.prod_mul_distrib, ← Finset.prod_filter,
    ← Finset.prod_filter, Finset.prod_const, Finset.prod_const]
  have hd := discrepancy_le (p := p) i j
  set a := (Finset.univ.filter fun t : Fin p.n => (i ≤ t ∧ (t : ℕ) < j) ∧ p.isV t).card
  set u := (Finset.univ.filter fun t : Fin p.n => (i ≤ t ∧ (t : ℕ) < j) ∧ ¬ p.isV t).card
  have hα := hp.α_pos
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have h₁ : p.α ^ (p.ρ * u - a) ≤ p.n :=
    calc p.α ^ (p.ρ * u - a) ≤ p.α ^ (-(1 + p.ρ)) :=
          Real.rpow_le_rpow_of_exponent_ge hα hp.α_lt_one.le (by linarith)
      _ = p.α⁻¹ ^ (1 + p.ρ) := by rw [Real.inv_rpow hα.le, Real.rpow_neg hα.le]
      _ ≤ √(p.n : ℝ) ^ (1 + p.ρ) :=
          Real.rpow_le_rpow (inv_nonneg.2 hα.le) hp.inv_α_le (by linarith [hp.ρ_pos])
      _ ≤ √(p.n : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hp.one_le_sqrt (by linarith [hp.ρ_lt_one])
      _ = p.n := by rw [Real.rpow_two, Real.sq_sqrt hn]
  have h₂ : Real.exp (2 / p.b) ^ u ≤ 2 := by
    have hb : (0 : ℝ) < p.b := by exact_mod_cast hp.b_pos
    have hu : (u : ℝ) ≤ p.n := by
      exact_mod_cast (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
    have h4 : 4 * (p.n : ℝ) ≤ p.b := by exact_mod_cast hp.four_n_le_b
    have hle : (u : ℝ) * (2 / p.b) ≤ 1 / 2 := by
      rw [mul_div_assoc', div_le_iff₀ hb]; linarith
    have hhalf : (2 : ℝ)⁻¹ ≤ Real.exp (-(1 / 2)) := by
      have := Real.add_one_le_exp (-(1 / 2) : ℝ); linarith
    rw [← Real.exp_nat_mul]
    refine (Real.exp_le_exp.2 hle).trans ?_
    rw [← inv_inv (Real.exp (1 / 2)), ← Real.exp_neg]
    exact inv_le_of_inv_le₀ two_pos hhalf
  calc p.α⁻¹ ^ a * p.β ^ u ≤ p.α⁻¹ ^ a * (p.α ^ p.ρ * Real.exp (2 / p.b)) ^ u := by
        gcongr
        · exact hp.β_pos.le
        · exact hp.β_le_α_rpow
    _ = p.α ^ (p.ρ * u - a) * Real.exp (2 / p.b) ^ u := by
        rw [mul_pow, ← Real.rpow_mul_natCast hα.le, Real.rpow_sub hα, Real.rpow_natCast, inv_pow]
        ring
    _ ≤ p.n * 2 := mul_le_mul h₁ h₂ (by positivity) hn
    _ ≤ (2 * √(p.n : ℝ)) ^ 2 := by rw [mul_pow, Real.sq_sqrt hn]; linarith

end Cslib.Circuits.DepthFive.Params
