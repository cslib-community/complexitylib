/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.SliceSum
import CslibFrontier.Foundations.Combinatorics.CompositionMomentLinear

/-!
# The first trace moment of iterated matrix multiplication

Let `F` be the matrix `pathMatrix` of the operator of `IMM_{n,n}` in the normalized monomial
bases. Different paths map a basis vector to different basis vectors, so the trace of `Fᵀ * F`
is the sum, over the paths `P` and the exponent vectors `M` of bidegree `(a, b)`, of the squared
coefficient `Path.coeff P M`. This coefficient is a product of `k` exponents of differentiated
variables and of `m` successors of exponents of multiplied variables. The lower comparison for
weak compositions gives

`tr (Fᵀ * F) ≥ D * n ^ (n - 1) * μ * exp (-(3 / 2) / √n)`, where `μ = (a / v) ^ k * (1 + b / u) ^ m`

is the corresponding moment of independent geometric variables
[OpenAI, §4][OpenAI2026DepthFive].

## Main definitions

* `Params.μ`: the geometric moment `(a / v) ^ k * (1 + b / u) ^ m`.

## Main results

* `sum_coeff_le_trace`: the first trace is at least the sum of the squared coefficients.
* `first_trace_ge`: the lower bound for the first trace.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §4 (unrefereed preprint)
-/

@[expose] public section

open MvPolynomial Finsupp
open scoped Matrix

namespace Cslib.Circuits.DepthFive

/-- The moment `μ = (a / v) ^ k * (1 + b / u) ^ m` of a path coefficient under independent
geometric exponents of means `a / v` and `b / u`. -/
noncomputable def Params.μ (p : Params) : ℝ :=
  ((p.a : ℝ) / p.v) ^ p.k * (1 + (p.b : ℝ) / p.u) ^ p.m

variable {p : Params} [NeZero p.n]

/-- The first trace is at least the sum of the squared path coefficients. -/
theorem sum_coeff_le_trace (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k) :
    ∑ P : Path p.n, ∑ M : Slice p (p.a, p.b), (P.coeff p M.1 : ℝ) ≤
      ((pathMatrix p)ᵀ * pathMatrix p).trace := by
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    pathMatrix, Matrix.of_apply, pathEntry]
  refine Finset.sum_le_sum fun M _ => ?_
  have hsq (N : Slice p (p.a - p.k, p.b + p.m)) :
      ∑ P : Path p.n, (if N.1 + P.vPart p = M.1 + P.uPart p then (P.coeff p M.1 : ℝ) else 0) ≤
        (∑ P : Path p.n, if N.1 + P.vPart p = M.1 + P.uPart p then √(P.coeff p M.1) else 0) *
          ∑ P : Path p.n, if N.1 + P.vPart p = M.1 + P.uPart p then √(P.coeff p M.1) else 0 := by
    rw [← sq]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun P _ => ?_))
      (Finset.sum_sq_le_sq_sum_of_nonneg fun P _ => by split_ifs <;> positivity)
    split_ifs
    · rw [Real.sq_sqrt (Nat.cast_nonneg _)]
    · rw [sq, mul_zero]
  refine le_trans ?_ (Finset.sum_le_sum fun N _ => hsq N)
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun P _ => ?_
  by_cases h0 : P.coeff p M.1 = 0
  · rw [h0, Nat.cast_zero]
    exact Finset.sum_nonneg fun N _ => by split_ifs <;> rfl
  have hle := P.vPart_le (left_ne_zero_of_mul (P.coeff_eq_mul M.1 ▸ h0))
  have hN : M.1 - P.vPart p + P.uPart p + P.vPart p = M.1 + P.uPart p := by
    rw [add_right_comm, tsub_add_cancel_of_le hle]
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun N : Slice p _ =>
      if N.1 + P.vPart p = M.1 + P.uPart p then (P.coeff p M.1 : ℝ) else 0)
    (fun N _ => by split_ifs <;> positivity)
    (Finset.mem_univ ⟨_, P.weight_of_add_vPart_eq hcard hN M.2⟩))
  exact (ite_eq_left hN).symm

/-- The lower comparison for the product of the exponents, shifted by `ε`, of the edges of a path
in the layers satisfying `q`, over the weak compositions into the variables of these layers. -/
private theorem le_sum_prod_edge (P : Path p.n) (q : Fin p.n → Prop) [DecidablePred q]
    (S : Finset (Fin p.n × Fin p.n × Fin p.n)) (hSq : S = Finset.univ.filter fun x => q x.1)
    (hS : S.Nonempty) (ε t : ℕ) (h : 2 * (Finset.univ.filter q).card ≤ t) :
    Real.exp (-(((Finset.univ.filter q).card : ℝ) ^ 2 / t) -
        ((Finset.univ.filter q).card : ℝ) ^ 2 / (2 * S.card)) *
      ((S.card).multichoose t * ((t : ℝ) / S.card + ε) ^ (Finset.univ.filter q).card) ≤
      ((∑ x ∈ S.finsuppAntidiag t, ∏ s with q s, (x (P.edge s) + ε) : ℕ) : ℝ) := by
  subst hSq
  have hcard : ((Finset.univ.filter fun x : Fin p.n × Fin p.n × Fin p.n => q x.1).filter
      fun c => (if c = P.edge c.1 then 1 else 0) ≠ 0).card = (Finset.univ.filter q).card := by
    rw [Finset.card_filter, Finset.card_eq_sum_ones,
      ← sum_ite_section q P.edge (fun _ => rfl) fun _ _ => 1]
    exact Finset.sum_congr rfl fun c _ => by split_ifs <;> first | rfl | omega
  have key := Finset.le_sum_finsuppAntidiag_prod_linear hS t
    (fun c => if c = P.edge c.1 then 1 else 0) (fun c => if c = P.edge c.1 then ε else 1)
    (by rw [hcard]; exact h)
  rw [hcard] at key
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · congr 2
    rw [← Finset.prod_const, ← prod_ite_section q P.edge (fun _ => rfl) fun _ _ =>
      (t : ℝ) / (Finset.univ.filter fun x : Fin p.n × Fin p.n × Fin p.n => q x.1).card + ε]
    exact Finset.prod_congr rfl fun c _ => by split_ifs <;> simp
  · congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← prod_ite_section q P.edge (fun _ => rfl) fun _ c => x c + ε]
    exact Finset.prod_congr rfl fun c _ => by split_ifs <;> simp

omit [NeZero p.n] in
/-- The loss of the lower comparison for the first trace is of order `1 / √n`. -/
private theorem Params.Good.loss_le (hp : p.Good) :
    (p.k : ℝ) ^ 2 / p.a + (p.k : ℝ) ^ 2 / (2 * p.v) + ((p.m : ℝ) ^ 2 / p.b +
      (p.m : ℝ) ^ 2 / (2 * p.u)) ≤ 3 / 2 / √(p.n : ℝ) := by
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast hp.n_pos
  have hk : (0 : ℝ) < p.k := by exact_mod_cast hp.k_pos
  have hm : (0 : ℝ) < p.m := by exact_mod_cast hp.m_pos
  have ha : (0 : ℝ) < p.a := by exact_mod_cast hp.a_pos
  have hb : (0 : ℝ) < p.b := by exact_mod_cast hp.b_pos
  have hv : (p.v : ℝ) = p.k * (p.n : ℝ) ^ 2 := by rw [Params.v]; push_cast; ring
  have hu : (p.u : ℝ) = p.m * (p.n : ℝ) ^ 2 := by rw [Params.u]; push_cast; ring
  have hkm : (p.k : ℝ) + p.m = p.n := by exact_mod_cast p.hkm
  have hr : (1 : ℝ) ≤ √(p.n : ℝ) := Real.one_le_sqrt.2 hn
  have hr2 : √(p.n : ℝ) ^ 2 = p.n := Real.sq_sqrt (by positivity)
  have hva : (p.v : ℝ) ≤ p.a * √(p.n : ℝ) := by
    have h := hp.α_ge
    rw [Params.α, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)] at h
    have : (0 : ℝ) ≤ p.a := ha.le
    linarith
  have hub : (p.u : ℝ) ≤ p.b * √(p.n : ℝ) := by
    have h : (√(p.n : ℝ))⁻¹ ≤ p.β := hp.α_ge.trans (le_trans (by
      simpa using Real.rpow_le_rpow_of_exponent_ge hp.α_pos hp.α_lt_one.le hp.ρ_lt_one.le)
      hp.α_rpow_le_β)
    rw [Params.β, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)] at h
    have : (0 : ℝ) ≤ p.b := hb.le
    linarith
  have h₁ : (p.k : ℝ) ^ 2 / p.a ≤ p.k * √(p.n : ℝ) / (p.n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ ha (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hva hk.le]
  have h₂ : (p.m : ℝ) ^ 2 / p.b ≤ p.m * √(p.n : ℝ) / (p.n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hb (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hub hm.le]
  have h₃ : (p.k : ℝ) ^ 2 / (2 * p.v) = p.k / (2 * (p.n : ℝ) ^ 2) := by
    rw [hv]; field_simp
  have h₄ : (p.m : ℝ) ^ 2 / (2 * p.u) = p.m / (2 * (p.n : ℝ) ^ 2) := by
    rw [hu]; field_simp
  have h₅ : (p.k : ℝ) * √(p.n : ℝ) / (p.n : ℝ) ^ 2 + p.k / (2 * (p.n : ℝ) ^ 2) +
      (p.m * √(p.n : ℝ) / (p.n : ℝ) ^ 2 + p.m / (2 * (p.n : ℝ) ^ 2)) =
      (√(p.n : ℝ) + 1 / 2) / √(p.n : ℝ) ^ 2 := by
    rw [hr2, ← hkm]; field_simp
  have h₆ : (√(p.n : ℝ) + 1 / 2) / √(p.n : ℝ) ^ 2 ≤ 3 / 2 / √(p.n : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **The first trace.** The trace of `Fᵀ * F` is at least
`D * n ^ (n - 1) * μ * exp (-(3 / 2) / √n)`. -/
theorem first_trace_ge (hp : p.Good)
    (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k) :
    p.D * (p.n : ℝ) ^ (p.n - 1) * p.μ * Real.exp (-(3 / 2) / √(p.n : ℝ)) ≤
      ((pathMatrix p)ᵀ * pathMatrix p).trace := by
  have hm : (Finset.univ.filter fun t => ¬ p.isV t).card = p.m := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p.n)))
      (fun t => p.isV t)
    have := p.hkm
    rw [hcard, Finset.card_univ, Fintype.card_fin] at h
    omega
  have hSV : p.varV.Nonempty := Finset.card_pos.1 (card_varV hcard ▸ hp.v_pos)
  have hSU : p.varU.Nonempty := Finset.card_pos.1 (card_varU hcard ▸ hp.u_pos)
  have hkn : p.k ≤ p.n := by have := p.hkm; omega
  have hmn : p.m ≤ p.n := by have := p.hkm; omega
  refine le_trans ?_ (sum_coeff_le_trace hcard)
  have hP (P : Path p.n) :
      Real.exp (-((p.k : ℝ) ^ 2 / p.a) - (p.k : ℝ) ^ 2 / (2 * p.v)) *
          (p.v.multichoose p.a * ((p.a : ℝ) / p.v) ^ p.k) *
        (Real.exp (-((p.m : ℝ) ^ 2 / p.b) - (p.m : ℝ) ^ 2 / (2 * p.u)) *
          (p.u.multichoose p.b * ((p.b : ℝ) / p.u + 1) ^ p.m)) ≤
        ∑ M : Slice p (p.a, p.b), (P.coeff p M.1 : ℝ) := by
    have hV := le_sum_prod_edge P (fun t => p.isV t) p.varV rfl hSV 0 p.a
      (by rw [hcard]; have := hp.four_n_le_a; omega)
    have hU := le_sum_prod_edge P (fun t => ¬ p.isV t) p.varU rfl hSU 1 p.b
      (by rw [hm]; have := hp.four_n_le_b; omega)
    rw [hcard, card_varV hcard] at hV
    rw [hm, card_varU hcard] at hU
    simp only [Nat.cast_zero, add_zero, Nat.cast_one] at hV hU
    refine (mul_le_mul hV hU (by positivity) (Nat.cast_nonneg _)).trans (le_of_eq ?_)
    rw [← Nat.cast_mul, ← sum_slice_mul p.a p.b
      (fun x => ∏ s with p.isV s, x (P.edge s)) (fun y => ∏ s with ¬ p.isV s, (y (P.edge s) + 1))
      (fun x y h => Finset.prod_congr rfl fun s hs => h _ (Finset.mem_filter.1 hs).2)
      (fun x y h => Finset.prod_congr rfl fun s hs =>
        congrArg (· + 1) (h (P.edge s) (Finset.mem_filter.1 hs).2)),
      Nat.cast_sum]
    exact Finset.sum_congr rfl fun M _ => by rw [P.coeff_eq_mul]
  refine le_trans ?_ (Finset.sum_le_sum fun P _ => hP P)
  rw [Finset.sum_const, Finset.card_univ, card_path, nsmul_eq_mul, Nat.cast_pow]
  have hloss : Real.exp (-(3 / 2) / √(p.n : ℝ)) ≤
      Real.exp (-((p.k : ℝ) ^ 2 / p.a) - (p.k : ℝ) ^ 2 / (2 * p.v)) *
        Real.exp (-((p.m : ℝ) ^ 2 / p.b) - (p.m : ℝ) ^ 2 / (2 * p.u)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := hp.loss_le
    rw [neg_div]
    linarith
  calc p.D * (p.n : ℝ) ^ (p.n - 1) * p.μ * Real.exp (-(3 / 2) / √(p.n : ℝ))
      ≤ p.D * (p.n : ℝ) ^ (p.n - 1) * p.μ *
          (Real.exp (-((p.k : ℝ) ^ 2 / p.a) - (p.k : ℝ) ^ 2 / (2 * p.v)) *
            Real.exp (-((p.m : ℝ) ^ 2 / p.b) - (p.m : ℝ) ^ 2 / (2 * p.u))) := by
        refine mul_le_mul_of_nonneg_left hloss ?_
        rw [Params.μ]
        positivity
    _ = _ := by
        rw [Params.D, Params.μ]
        push_cast
        ring

end Cslib.Circuits.DepthFive
