/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.PathMatrix

/-!
# Sums over the exponent vectors of a bidegree

An exponent vector of bidegree `(a, b)` is a pair of a weak composition of `a` into the
differentiated variables and a weak composition of `b` into the multiplied variables. A sum
over the slice of a product of a function of the first and a function of the second is
therefore a product of two sums over weak compositions (`sum_slice_mul`). This is the
independence of the two exponent vectors of a uniformly chosen basis vector in
[OpenAI, §4][OpenAI2026DepthFive].

A product over the layers `t` of a function of the variable `c t` chosen in layer `t` is a
product over all variables (`prod_ite_section`), which is the form of the comparison lemmas for
weak compositions.

## Main definitions

* `Params.varV`, `Params.varU`: the sets of differentiated and multiplied variables.

## Main results

* `sum_slice_mul`: a sum over a slice of a product is a product of sums.
* `prod_ite_section`: a product over layers as a product over variables.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §4 (unrefereed preprint)
-/

@[expose] public section

open MvPolynomial Finsupp

namespace Cslib.Circuits.DepthFive

variable (p : Params)

/-- The differentiated variables. -/
abbrev Params.varV : Finset (Fin p.n × Fin p.n × Fin p.n) := Finset.univ.filter p.layerVar

/-- The multiplied variables. -/
abbrev Params.varU : Finset (Fin p.n × Fin p.n × Fin p.n) := Finset.univ.filter (¬ p.layerVar ·)

variable {p}

private theorem card_filter_fst (q : Fin p.n → Prop) [DecidablePred q] :
    (Finset.univ.filter fun x : Fin p.n × Fin p.n × Fin p.n => q x.1).card =
      (Finset.univ.filter q).card * p.n ^ 2 := by
  rw [← Finset.univ_product_univ, Finset.filter_product_left, Finset.card_product,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]

theorem card_varV (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k) :
    p.varV.card = p.v := by
  rw [Params.v, ← hcard]
  exact card_filter_fst fun t => p.isV t

theorem card_varU (hcard : (Finset.univ.filter fun t => p.isV t).card = p.k) :
    p.varU.card = p.u := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p.n)))
    (fun t => p.isV t)
  have hm : (Finset.univ.filter fun t => ¬ p.isV t).card = p.m := by
    have := p.hkm
    rw [hcard, Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [Params.u, ← hm]
  exact card_filter_fst fun t => ¬ p.isV t

/-- A sum over the slice of bidegree `(a, b)` of a product of a function of the differentiated
exponents and a function of the multiplied exponents is the product of the two sums over weak
compositions. -/
theorem sum_slice_mul {R : Type*} [CommSemiring R] (a b : ℕ)
    (FV FU : (Fin p.n × Fin p.n × Fin p.n →₀ ℕ) → R)
    (hV : ∀ x y, (∀ c, p.layerVar c → x c = y c) → FV x = FV y)
    (hU : ∀ x y, (∀ c, ¬ p.layerVar c → x c = y c) → FU x = FU y) :
    ∑ M : Slice p (a, b), FV M.1 * FU M.1 =
      (∑ x ∈ p.varV.finsuppAntidiag a, FV x) * ∑ y ∈ p.varU.finsuppAntidiag b, FU y := by
  rw [← (bidegreeEquiv p.layerVar a b).symm.sum_comp, Fintype.sum_prod_type,
    ← Finset.sum_coe_sort (p.varV.finsuppAntidiag a),
    ← Finset.sum_coe_sort (p.varU.finsuppAntidiag b), Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hx := (Finset.mem_finsuppAntidiag.1 x.2).2
  have hy := (Finset.mem_finsuppAntidiag.1 y.2).2
  have hV' : FV (x.1 + y.1) = FV x.1 := hV _ _ fun c hc => by
    have : y.1 c = 0 := by
      by_contra h
      exact (Finset.mem_filter.1 (hy (Finsupp.mem_support_iff.2 h))).2 hc
    rw [Finsupp.add_apply, this, add_zero]
  have hU' : FU (x.1 + y.1) = FU y.1 := hU _ _ fun c hc => by
    have : x.1 c = 0 := by
      by_contra h
      exact hc (Finset.mem_filter.1 (hx (Finsupp.mem_support_iff.2 h))).2
    rw [Finsupp.add_apply, this, zero_add]
  exact congrArg₂ (· * ·) hV' hU'

/-- A product over the layers `t` in a set of a function of a variable `c t` of layer `t` is a
product over all variables of these layers. -/
@[to_additive /-- A sum over the layers `t` in a set of a function of a variable `c t` of layer
`t` is a sum over all variables of these layers. -/]
theorem prod_ite_section {R : Type*} [CommMonoid R] (q : Fin p.n → Prop) [DecidablePred q]
    (c : Fin p.n → Fin p.n × Fin p.n × Fin p.n) (hc : ∀ t, (c t).1 = t)
    (f : Fin p.n → Fin p.n × Fin p.n × Fin p.n → R) :
    ∏ x with q x.1, (if x = c x.1 then f x.1 x else 1) = ∏ t with q t, f t (c t) := by
  rw [← Finset.prod_filter, Finset.filter_filter]
  refine (Finset.prod_bij (fun t _ => c t) (fun t ht => ?_) (fun t _ t' _ h => ?_)
    (fun x hx => ?_) fun t _ => by rw [hc]).symm
  · rw [Finset.mem_filter, hc]
    exact ⟨Finset.mem_univ _, (Finset.mem_filter.1 ht).2, rfl⟩
  · rw [← hc t, ← hc t', h]
  · obtain ⟨-, hq, hx⟩ := Finset.mem_filter.1 hx
    exact ⟨x.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩, hx.symm⟩

end Cslib.Circuits.DepthFive
