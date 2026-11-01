/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Degree
public import Complexity.Foundations.BooleanAnalysis.Hypercube
public import Cslib.Computability.QueryComplexity.Measures

/-!
# Huang's sensitivity theorem

Every Boolean function satisfies `deg(f) ≤ s(f)²` [Huang2019]. Gotsman and Linial reduced this to
the induced subgraph theorem [GotsmanLinial1992]: if `f`, read as signs, has a nonzero Fourier
coefficient on `S`, then `g = f ⊕ parity_S` is unbalanced, so one of its fibers `V` contains more
than half of the cube. By Huang's induced subgraph theorem
(`BitString.exists_mem_sqrt_card_le_card_update_mem`) some `x ∈ V` has at least `√|S|` neighbors
in `V` in the directions of `S`. Flipping a bit of `S` flips `parity_S`, so along these directions
`g` is constant and `f` changes: `f` has at least `√|S|` sensitive coordinates at `x`
(`BitString.sqrt_card_le_sensitivity_of_fourierCoeff_ne_zero`). A coefficient on a set of `deg(f)`
coordinates gives `√deg(f) ≤ s(f)` (`QueryComplexity.sqrt_degree_le_sensitivity`).

## Main results

* `Cslib.BitString.exists_two_pow_lt_two_mul_card_forall_isSensitiveCoord`: a nonzero Fourier
  coefficient on `S` gives a set of more than half of the points whose edges in the directions of
  `S` are all sensitive.
* `Cslib.BitString.sqrt_card_le_sensitivity_of_fourierCoeff_ne_zero`: a nonzero Fourier
  coefficient on `S` forces sensitivity at least `√|S|`.
* `Cslib.QueryComplexity.degree_le_sensitivity_sq`: **Huang's sensitivity theorem**,
  `deg(f) ≤ s(f)²`.
* `Cslib.QueryComplexity.sqrt_degree_le_sensitivity`: `√deg(f) ≤ s(f)`.

## References

* [H. Huang, *Induced subgraphs of hypercubes and a proof of the Sensitivity
  Conjecture*][Huang2019]
* [C. Gotsman, N. Linial, *The equivalence of two problems on the cube*][GotsmanLinial1992]
-/

@[expose] public section

namespace Cslib

open Finset Function

variable {n : ℕ}

namespace BitString

/-- **A nonzero Fourier coefficient gives a large fiber of sensitive edges**: if `f`, read as signs,
has a nonzero Fourier coefficient on `S`, then some set `V` of more than half of the points of the
cube has every edge inside `V` in a direction of `S` sensitive for `f`. The set is a fiber of the
twist `f ⊕ parity_S` of `f` by the parity on `S`, which the coefficient makes unbalanced
[GotsmanLinial1992]. -/
theorem exists_two_pow_lt_two_mul_card_forall_isSensitiveCoord {f : BooleanFunction n}
    {S : Finset (Fin n)} (h : fourierCoeff (fun x => signVal (f x)) S ≠ 0) :
    ∃ V : Finset (BitString n), 2 ^ n < 2 * #V ∧
      ∀ x ∈ V, ∀ i ∈ S, update x i (!x i) ∈ V → IsSensitiveCoord f x i := by
  -- `f` twisted by the parity on `S`
  set g : BitString n → Bool := fun x => f x ^^ parityOn S x with hg
  have hf (y : BitString n) : f y = (g y ^^ parityOn S y) := by
    simp only [hg, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  -- the coefficient is the bias of `g`, so `g` is unbalanced
  have hsum : ∑ x, signVal (g x) = (#{x | ¬g x = true} : ℝ) - #{x | g x = true} := by
    simp only [signVal, sum_ite, sum_const, nsmul_eq_mul, mul_neg, mul_one]
    ring
  have hne : #{x | g x = true} ≠ #{x | ¬g x = true} := fun heq => h (by
    simp only [fourierCoeff, chi_eq_signVal_parityOn, ← signVal_xor]
    rw [expect_eq_sum_div_card, hsum, heq, sub_self, zero_div])
  have hcard := card_filter_add_card_filter_not (s := univ) fun x : BitString n =>
    g x = true
  rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  -- one of the fibers of `g` has more than half of the points
  obtain ⟨c, hc⟩ : ∃ c : Bool, 2 ^ n < 2 * #{x | g x = c} := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine ⟨false, ?_⟩
      simp only [Bool.not_eq_true] at hcard hlt
      omega
    · exact ⟨true, by omega⟩
  -- along the directions of `S` inside the fiber, `g` is constant and `f` flips
  refine ⟨_, hc, fun x hx i hiS hiV => ?_⟩
  have hgx : g x = c := (mem_filter.1 hx).2
  have hgi : g (update x i (!x i)) = c := (mem_filter.1 hiV).2
  rw [IsSensitiveCoord, hf, hf x, hgi, hgx, parityOn_update_not hiS]
  cases c <;> cases parityOn S x <;> decide

/-- **A nonzero Fourier coefficient forces sensitivity**: if `f`, read as signs, has a nonzero
Fourier coefficient on `S`, then `f` has at least `√|S|` sensitive coordinates at some input. -/
theorem sqrt_card_le_sensitivity_of_fourierCoeff_ne_zero {f : BooleanFunction n}
    {S : Finset (Fin n)} (h : fourierCoeff (fun x => signVal (f x)) S ≠ 0) :
    √(#S : ℝ) ≤ sensitivity f := by
  obtain ⟨V, hV, hsens⟩ := exists_two_pow_lt_two_mul_card_forall_isSensitiveCoord h
  obtain ⟨x, hx, hS⟩ := exists_mem_sqrt_card_le_card_update_mem
    (by rwa [Fintype.card_fin]) S
  refine hS.trans (Nat.cast_le.2
    (card_le_sensitivity_of_forall_isSensitiveCoord (x := x) fun i hi => ?_))
  obtain ⟨hiS, hiV⟩ := mem_filter.1 hi
  exact hsens x hx i hiS hiV

end BitString

namespace QueryComplexity

open BitString

/-- **Huang's sensitivity theorem**: the degree of a Boolean function is at most the square of its
sensitivity, `deg(f) ≤ s(f)²` [Huang2019]. -/
theorem degree_le_sensitivity_sq (f : BooleanFunction n) : degree f ≤ sensitivity f ^ 2 := by
  rcases Nat.eq_zero_or_pos (degree f) with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  rw [degree_eq_totalDegree_signVal] at hpos ⊢
  obtain ⟨S, hS, hne⟩ := exists_card_eq_totalDegree_fourierCoeff_ne_zero hpos.ne'
  have h := sqrt_card_le_sensitivity_of_fourierCoeff_ne_zero hne
  rw [hS, Real.sqrt_le_left (Nat.cast_nonneg _)] at h
  exact_mod_cast h

/-- **Huang's sensitivity theorem**: `√deg(f) ≤ s(f)`. -/
theorem sqrt_degree_le_sensitivity (f : BooleanFunction n) :
    √(degree f : ℝ) ≤ sensitivity f :=
  (Real.sqrt_le_left (Nat.cast_nonneg _)).2 (by exact_mod_cast degree_le_sensitivity_sq f)

end QueryComplexity

end Cslib
