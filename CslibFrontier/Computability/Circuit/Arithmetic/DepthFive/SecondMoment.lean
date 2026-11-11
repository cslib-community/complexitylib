/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.FirstMoment
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.FourPath
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.WordSum
import CslibFrontier.Foundations.Combinatorics.CompositionMomentLinear

/-!
# The second trace moment of iterated matrix multiplication

Let `F` be the matrix `pathMatrix` of the operator of `IMM_{n,n}` in the normalized monomial
bases. The four-path bound `second_trace_le_sum_local` writes the trace of
`(Fᵀ * F) * (Fᵀ * F)` as a sum over four paths of a product of local polynomials in the
exponents. The upper comparison for weak compositions replaces every local polynomial by its
moment under independent geometric exponents, `Quad.weight`: after division by `(a / v) ^ 2` in
a differentiated layer and by `(1 + b / u) ^ 2` in a multiplied layer, this is

* `1 + α⁻¹` or `1` in a differentiated layer of type `𝒩`, as the edges of `P` and `R` agree or
  not, and `α⁻¹` of type `𝒟`;
* `1 + β` or `1` in a multiplied layer of type `𝒩`, and `β` of type `𝒟`.

Summing over the four paths of every type word with `sum_quad_le` gives the moment reduction
[OpenAI, §4][OpenAI2026DepthFive]

`tr ((Fᵀ * F) * (Fᵀ * F)) ≤ D * n ^ (2 * (n - 1)) * μ ^ 2 * (1 + β) ^ m * ∑ τ, wordWeight τ`.

## Main definitions

* `Quad.weight`: the geometric moment of the local polynomial of a layer.

## Main results

* `sum_local_le`: the occupation comparison for the product of the local polynomials.
* `second_trace_le`: the moment reduction.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §4 (unrefereed preprint)
-/

@[expose] public section

open Finsupp
open scoped Matrix

namespace Cslib.Circuits.DepthFive

variable {p : Params} [NeZero p.n]

variable (p) in
/-- The moment of the local polynomial of a layer of type `τ` under independent geometric
exponents of means `a / v` and `b / u`. -/
noncomputable def Quad.weight (W : Quad p.n) (τ : Bool) (t : Fin p.n) : ℝ :=
  if p.isV t then ((p.a : ℝ) / p.v) ^ 2 *
    (if τ then p.α⁻¹ else 1 + p.α⁻¹ * if W.P.edge t = W.R.edge t then 1 else 0)
  else (1 + (p.b : ℝ) / p.u) ^ 2 *
    (if τ then p.β else 1 + p.β * if W.P.edge t = W.R.edge t then 1 else 0)

omit [NeZero p.n] in
/-- The upper comparison for a product over the layers satisfying `q` of two shifted exponents
of variables of the layer. -/
private theorem sum_prod_two_le (q : Fin p.n → Prop) [DecidablePred q]
    (S : Finset (Fin p.n × Fin p.n × Fin p.n)) (hSq : S = Finset.univ.filter fun x => q x.1)
    (hS : S.Nonempty) (c₁ c₂ : Fin p.n → Fin p.n × Fin p.n × Fin p.n) (h₁ : ∀ t, (c₁ t).1 = t)
    (h₂ : ∀ t, (c₂ t).1 = t) (e₁ e₂ : Fin p.n → ℕ) (t : ℕ) (ht : 0 < t) :
    ((∑ x ∈ S.finsuppAntidiag t, ∏ s with q s, (x (c₁ s) + e₁ s) * (x (c₂ s) + e₂ s) : ℕ) : ℝ) ≤
      (S.card).multichoose t * ∏ s with q s,
        (((t : ℝ) / S.card + e₁ s) * ((t : ℝ) / S.card + e₂ s) +
          if c₁ s = c₂ s then ((t : ℝ) / S.card) ^ 2 + (t : ℝ) / S.card else 0) := by
  subst hSq
  have hG : (0 : ℝ) < (t : ℝ) / (Finset.univ.filter fun x : Fin p.n × Fin p.n × Fin p.n =>
      q x.1).card := div_pos (by exact_mod_cast ht) (by exact_mod_cast hS.card_pos)
  have key := Finset.sum_finsuppAntidiag_prod_linear_mul_linear_le hS t
    (fun c => if c = c₁ c.1 then 1 else 0) (fun c => if c = c₁ c.1 then e₁ c.1 else 1)
    (fun c => if c = c₂ c.1 then 1 else 0) (fun c => if c = c₂ c.1 then e₂ c.1 else 1)
  set G : ℝ := (t : ℝ) / (Finset.univ.filter fun x : Fin p.n × Fin p.n × Fin p.n => q x.1).card
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← prod_ite_section q c₁ h₁ fun s c => x c + e₁ s,
      ← prod_ite_section q c₂ h₂ fun s c => x c + e₂ s]
    congr 1 <;> exact Finset.prod_congr rfl fun c _ => by split_ifs <;> simp
  · congr 1
    have hprod : ∏ s with q s, ((G + e₁ s) * (G + e₂ s) +
        if c₁ s = c₂ s then G ^ 2 + G else 0) =
        (∏ s with q s, (G + e₁ s)) * ∏ s with q s, (G + e₂ s) *
          (1 + if c₁ s = c₂ s then (G ^ 2 + G) / ((G + e₁ s) * (G + e₂ s)) else 0) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hpos₁ : G + e₁ s ≠ 0 := by positivity
      have hpos₂ : G + e₂ s ≠ 0 := by positivity
      split_ifs
      · field_simp
      · ring
    rw [hprod, ← prod_ite_section q c₁ h₁ fun s _ => G + e₁ s,
      ← prod_ite_section q c₂ h₂ fun s _ => (G + e₂ s) *
        (1 + if c₁ s = c₂ s then (G ^ 2 + G) / ((G + e₁ s) * (G + e₂ s)) else 0),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun c _ => ?_
    have h12 : c = c₁ c.1 → c = c₂ c.1 → c₁ c.1 = c₂ c.1 := fun a b => a.symm.trans b
    have h21 : c = c₂ c.1 → c₁ c.1 = c₂ c.1 → c = c₁ c.1 := fun a b => a.trans b.symm
    have hpos₁ : G + e₁ c.1 ≠ 0 := by positivity
    have hpos₂ : G + e₂ c.1 ≠ 0 := by positivity
    split_ifs <;> first | (exfalso; tauto) | (push_cast; field_simp; ring) |
      (push_cast; field_simp)

theorem Quad.weight_nonneg (hp : p.Good) (W : Quad p.n) (τ : Bool) (t : Fin p.n) :
    0 ≤ W.weight p τ t := by
  have := hp.α_pos
  have := hp.β_pos
  rw [Quad.weight]
  split_ifs <;> positivity

/-- The moment of the local polynomial of a differentiated layer. -/
private theorem weight_of_isV (hp : p.Good) (W : Quad p.n) {s : Fin p.n} (hs : p.isV s) :
    ((p.a : ℝ) / p.v + ((if p.isV s then 0 else 1 : ℕ) : ℝ)) * ((p.a : ℝ) / p.v + W.shift p s) +
        (if W.1.1.edge s = W.mate s then ((p.a : ℝ) / p.v) ^ 2 + (p.a : ℝ) / p.v else 0) =
      W.weight p (W.type s) s := by
  have ha : (0 : ℝ) < p.a := by exact_mod_cast hp.a_pos
  have hv : (0 : ℝ) < p.v := by exact_mod_cast hp.v_pos
  have hα : p.α⁻¹ = 1 + (p.v : ℝ) / p.a := by rw [Params.α, inv_div]; field_simp
  by_cases hpq : W.1.1.edge s = W.1.2.edge s
  · simp only [Quad.weight, Quad.type, Quad.mate, Quad.shift, hs, hpq, hα, ne_eq,
      not_true_eq_false, decide_false, ite_true, Nat.cast_zero, add_zero, Bool.false_eq_true,
      ite_false, mul_ite, mul_one, mul_zero]
    split_ifs
    · field_simp
    · ring
  · simp only [Quad.weight, Quad.type, Quad.mate, Quad.shift, hs, hpq, hα, ne_eq,
      not_false_eq_true, decide_true, iff_true, ite_true, ite_false, Nat.cast_zero, add_zero,
      Nat.cast_one]
    field_simp

/-- The moment of the local polynomial of a multiplied layer. -/
private theorem weight_of_not_isV (hp : p.Good) (W : Quad p.n) {s : Fin p.n} (hs : ¬ p.isV s) :
    ((p.b : ℝ) / p.u + ((if p.isV s then 0 else 1 : ℕ) : ℝ)) * ((p.b : ℝ) / p.u + W.shift p s) +
        (if W.1.1.edge s = W.mate s then ((p.b : ℝ) / p.u) ^ 2 + (p.b : ℝ) / p.u else 0) =
      W.weight p (W.type s) s := by
  have hb : (0 : ℝ) < p.b := by exact_mod_cast hp.b_pos
  have hu : (0 : ℝ) < p.u := by exact_mod_cast hp.u_pos
  by_cases hpq : W.1.1.edge s = W.1.2.edge s
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, Nat.cast_one, Quad.shift, hpq, iff_false,
      not_true_eq_false, Quad.mate, Quad.weight, Quad.type, ne_eq, decide_false, Params.β, mul_ite,
      mul_one, mul_zero]
    split_ifs
    · field_simp
      ring
    · ring
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, Nat.cast_one, Quad.shift, hpq,
      CharP.cast_eq_zero, add_zero, Quad.mate, Quad.weight, Quad.type, ne_eq, not_false_eq_true,
      decide_true, Params.β]
    field_simp
    ring

/-- **The occupation comparison.** The sum over the slice of the product of the local
polynomials of four paths is at most the dimension of the slice times the product of their
geometric moments. -/
theorem sum_local_le (hp : p.Good) (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k)
    (W : Quad p.n) :
    ((∑ M : Slice p (p.a, p.b), ∏ t, W.local p M.1 t : ℕ) : ℝ) ≤
      p.D * ∏ t, W.weight p (W.type t) t := by
  have hSV : p.varV.Nonempty := Finset.card_pos.1 (card_varV hcard ▸ hp.v_pos)
  have hSU : p.varU.Nonempty := Finset.card_pos.1 (card_varU hcard ▸ hp.u_pos)
  have hsplit : ∑ M : Slice p (p.a, p.b), ∏ t, W.local p M.1 t =
      (∑ x ∈ p.varV.finsuppAntidiag p.a, ∏ s with p.isV s, W.local p x s) *
        ∑ y ∈ p.varU.finsuppAntidiag p.b, ∏ s with ¬ p.isV s, W.local p y s := by
    rw [← sum_slice_mul p.a p.b (fun x => ∏ s with p.isV s, W.local p x s)
      (fun y => ∏ s with ¬ p.isV s, W.local p y s)
      (fun x y h => Finset.prod_congr rfl fun s hs => by
        have hs' := (Finset.mem_filter.1 hs).2
        rw [Quad.local, Quad.local, h (W.1.1.edge s) hs',
          h (W.mate s) (by change p.isV (W.mate s).1 = true; rwa [W.mate_fst])])
      (fun x y h => Finset.prod_congr rfl fun s hs => by
        have hs' := (Finset.mem_filter.1 hs).2
        rw [Quad.local, Quad.local, h (W.1.1.edge s) hs',
          h (W.mate s) (by change ¬ p.isV (W.mate s).1 = true; rwa [W.mate_fst])])]
    exact Finset.sum_congr rfl fun M _ =>
      (Finset.prod_filter_mul_prod_filter_not _ (fun t => (p.isV t : Prop)) _).symm
  have hV : ((∑ x ∈ p.varV.finsuppAntidiag p.a, ∏ s with p.isV s, W.local p x s : ℕ) : ℝ) ≤
      p.varV.card.multichoose p.a * ∏ s with p.isV s,
        (((p.a : ℝ) / p.varV.card + ((if p.isV s then 0 else 1 : ℕ) : ℝ)) *
            ((p.a : ℝ) / p.varV.card + W.shift p s) +
          if W.1.1.edge s = W.mate s then ((p.a : ℝ) / p.varV.card) ^ 2 + (p.a : ℝ) / p.varV.card
          else 0) :=
    sum_prod_two_le (fun t => p.isV t) p.varV rfl hSV (fun t => W.1.1.edge t) W.mate
      (fun _ => rfl) W.mate_fst (fun t => if p.isV t then 0 else 1) (W.shift p) p.a hp.a_pos
  have hU : ((∑ y ∈ p.varU.finsuppAntidiag p.b, ∏ s with ¬ p.isV s, W.local p y s : ℕ) : ℝ) ≤
      p.varU.card.multichoose p.b * ∏ s with ¬ p.isV s,
        (((p.b : ℝ) / p.varU.card + ((if p.isV s then 0 else 1 : ℕ) : ℝ)) *
            ((p.b : ℝ) / p.varU.card + W.shift p s) +
          if W.1.1.edge s = W.mate s then ((p.b : ℝ) / p.varU.card) ^ 2 + (p.b : ℝ) / p.varU.card
          else 0) :=
    sum_prod_two_le (fun t => ¬ p.isV t) p.varU rfl hSU (fun t => W.1.1.edge t) W.mate
      (fun _ => rfl) W.mate_fst (fun t => if p.isV t then 0 else 1) (W.shift p) p.b hp.b_pos
  rw [card_varV hcard] at hV
  rw [card_varU hcard] at hU
  rw [Finset.prod_congr rfl fun s hs => weight_of_isV hp W (Finset.mem_filter.1 hs).2] at hV
  rw [Finset.prod_congr rfl fun s hs => weight_of_not_isV hp W (Finset.mem_filter.1 hs).2] at hU
  calc ((∑ M : Slice p (p.a, p.b), ∏ t, W.local p M.1 t : ℕ) : ℝ)
      = ((∑ x ∈ p.varV.finsuppAntidiag p.a, ∏ s with p.isV s, W.local p x s : ℕ) : ℝ) *
          ((∑ y ∈ p.varU.finsuppAntidiag p.b, ∏ s with ¬ p.isV s, W.local p y s : ℕ) : ℝ) := by
        rw [hsplit, Nat.cast_mul]
    _ ≤ (p.v.multichoose p.a * ∏ s with p.isV s, W.weight p (W.type s) s) *
          (p.u.multichoose p.b * ∏ s with ¬ p.isV s, W.weight p (W.type s) s) :=
        mul_le_mul hV hU (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
          (Finset.prod_nonneg fun s _ => W.weight_nonneg hp _ s))
    _ = p.D * ∏ t, W.weight p (W.type t) t := by
        rw [Params.D, Nat.cast_mul, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
          (fun t => (p.isV t : Prop)) fun t => W.weight p (W.type t) t]
        ring

/-- The product of the geometric moments of the layers, for four paths of type `τ`. -/
private theorem prod_weight_le (hp : p.Good)
    (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k) (W : Quad p.n)
    (τ : Fin p.n → Bool) :
    ∏ t, W.weight p (τ t) t ≤ p.μ ^ 2 * (1 + p.β) ^ p.m * (p.α⁻¹ ^ p.dV τ * p.β ^ p.dU τ) *
      ∏ t with p.isV t ∧ τ t = false,
        (1 + p.α⁻¹ * if W.1.1.edge t = W.2.1.edge t then 1 else 0) := by
  have hα := hp.α_pos
  have hβ := hp.β_pos
  have hm : (Finset.univ.filter fun t => ¬ p.isV t).card = p.m := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p.n)))
      (fun t => p.isV t)
    have := p.hkm
    rw [hcard, Finset.card_univ, Fintype.card_fin] at h
    omega
  have hω (t : Fin p.n) : W.weight p (τ t) t ≤
      (if p.isV t then ((p.a : ℝ) / p.v) ^ 2 else (1 + (p.b : ℝ) / p.u) ^ 2) *
        ((if ¬ p.isV t then 1 + p.β else 1) * (if p.isV t ∧ τ t then p.α⁻¹ else 1) *
          (if ¬ p.isV t ∧ τ t then p.β else 1) *
          if p.isV t ∧ τ t = false then
            1 + p.α⁻¹ * if W.1.1.edge t = W.2.1.edge t then 1 else 0 else 1) := by
    by_cases ht : p.isV t <;> by_cases hτ : τ t = true
    · simp [Quad.weight, ht, hτ]
    · simp [Quad.weight, ht, hτ]
    · simp only [Quad.weight, ht, hτ, Bool.false_eq_true, ite_false, ite_true, not_false_eq_true,
        false_and, and_self, mul_one]
      gcongr
      nlinarith
    · simp only [Quad.weight, ht, hτ, Bool.false_eq_true, ite_false, ite_true, not_false_eq_true,
        false_and, and_false, mul_one]
      gcongr
      split_ifs <;> linarith
  refine (Finset.prod_le_prod₀ (fun t _ => W.weight_nonneg hp _ t) fun t _ => hω t).trans
    (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const, Finset.prod_const,
    ← Finset.prod_filter, ← Finset.prod_filter, ← Finset.prod_filter, ← Finset.prod_filter,
    Finset.prod_const, Finset.prod_const, Finset.prod_const, hcard, hm, Params.μ, Params.dV,
    Params.dU]
  generalize (p.a : ℝ) / p.v = A
  generalize 1 + (p.b : ℝ) / p.u = B
  ring

/-- **The moment reduction.** The second trace is at most `D * n ^ (2 * (n - 1)) * μ ^ 2` times
`(1 + β) ^ m` times the sum of the weights of the type words. -/
theorem second_trace_le (hp : p.Good)
    (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k)
    (hadj : ∀ t t' : Fin p.n, (t : ℕ) + 1 = t' → p.isV t → p.isV t' → False) :
    (((pathMatrix p)ᵀ * pathMatrix p) * ((pathMatrix p)ᵀ * pathMatrix p)).trace ≤
      p.D * (p.n : ℝ) ^ (2 * (p.n - 1)) * p.μ ^ 2 * (1 + p.β) ^ p.m * ∑ τ, p.wordWeight τ := by
  have hα := hp.α_pos
  have hβ := hp.β_pos
  have hμ : 0 ≤ p.μ ^ 2 * (1 + p.β) ^ p.m := by positivity
  have h₁ (W : Quad p.n) : ∑ M : Slice p (p.a, p.b),
      (if W.HasType W.type then ((∏ t, W.local p M.1 t : ℕ) : ℝ) else 0) ≤
      ∑ τ : Fin p.n → Bool, if W.HasType τ then p.D * ∏ t, W.weight p (τ t) t else 0 := by
    have hnn (τ : Fin p.n → Bool) :
        0 ≤ if W.HasType τ then p.D * ∏ t, W.weight p (τ t) t else 0 := by
      split_ifs
      · exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun t _ => W.weight_nonneg hp _ t)
      · rfl
    by_cases h : W.HasType W.type
    · simp only [h, ite_true]
      rw [← Nat.cast_sum]
      refine (sum_local_le hp hcard W).trans (le_trans (le_of_eq ?_)
        (Finset.single_le_sum (fun τ _ => hnn τ) (Finset.mem_univ W.type)))
      rw [ite_eq_left h]
    · simp only [h, ite_false, Finset.sum_const_zero]
      exact Finset.sum_nonneg fun τ _ => hnn τ
  refine second_trace_le_sum_local.trans ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_le_sum fun W _ => h₁ W).trans ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  calc ∑ W : Quad p.n, (if W.HasType τ then p.D * ∏ t, W.weight p (τ t) t else 0)
      ≤ ∑ W : Quad p.n, p.D * (p.μ ^ 2 * (1 + p.β) ^ p.m * (p.α⁻¹ ^ p.dV τ * p.β ^ p.dU τ)) *
          if W.HasType τ then ∏ t with p.isV t ∧ τ t = false,
            (1 + p.α⁻¹ * if W.1.1.edge t = W.2.1.edge t then 1 else 0) else 0 := by
        refine Finset.sum_le_sum fun W _ => ?_
        split_ifs
        · rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (prod_weight_le hp hcard W τ) (Nat.cast_nonneg _)
        · rw [mul_zero]
    _ ≤ p.D * (p.μ ^ 2 * (1 + p.β) ^ p.m * (p.α⁻¹ ^ p.dV τ * p.β ^ p.dU τ)) *
          ((p.n : ℝ) ^ (2 * (p.n - 1)) * ((p.n : ℝ)⁻¹) ^ p.switches τ *
            ∏ t with p.isV t ∧ τ t = false, (1 + p.α⁻¹ * ((p.n : ℝ)⁻¹) ^ p.nbrN τ t)) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_quad_le p hadj τ (inv_nonneg.2 hα.le))
          (by positivity)
    _ = _ := by
        rw [Params.wordWeight]
        ring

end Cslib.Circuits.DepthFive
