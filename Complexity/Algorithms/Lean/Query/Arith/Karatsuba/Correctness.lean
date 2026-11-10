/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Query.Arith.Karatsuba.Defs
public import Complexity.Foundations.Data.Polynomial.CoeffList
import Mathlib.Tactic.LinearCombination

/-!
# Correctness of Karatsuba multiplication

Under the honest oracle of a commutative ring, `Cslib.Query.karatsuba p q` returns the coefficient
list of the product of the polynomials with coefficient lists `p` and `q`
(`Cslib.Query.ofCoeffList_eval_karatsuba`). Each step is checked against `Polynomial.ofCoeffList`:
the three recursive products `Z₀ = P₀ Q₀`, `Z₁ = (P₀ + P₁) (Q₀ + Q₁)` and `Z₂ = P₁ Q₁` of the
halves `P = P₀ + X ^ m P₁`, `Q = Q₀ + X ^ m Q₁` recombine as
`P Q = Z₀ + X ^ m (Z₁ - Z₀ - Z₂) + X ^ (2 m) Z₂`.

## Main results

* `Cslib.Query.Karatsuba.ofCoeffList_eval_mulFit`: `mulFit n` multiplies the zero-padded first `n`
  coefficients.
* `Cslib.Query.ofCoeffList_eval_karatsuba`: `karatsuba` multiplies polynomials.
* `Cslib.Query.ofCoeffList_eval_karatsuba_coeffsBelow`: on the first `n` coefficients of two
  polynomials of degree less than `n`, `karatsuba` computes their product.

## References

* [Karatsuba and Ofman, *Multiplication of Many-Digital Numbers by Automatic
  Computers*][KaratsubaOfman1962].
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Problem 30-1.
-/

public section

namespace Cslib.Query

open Polynomial ArithQuery

variable {α : Type} [CommRing α]

namespace Karatsuba

/-- Honest `addList` adds the polynomials. -/
theorem ofCoeffList_eval_addList (p q : List α) :
    ofCoeffList ((addList p q).eval honest) = ofCoeffList p + ofCoeffList q := by
  induction p generalizing q with
  | nil => simp [addList]
  | cons a p ih =>
    cases q with
    | nil => simp [addList]
    | cons b q =>
      simp only [addList, doAdd, FreeM.eval_bind, FreeM.eval_lift, FreeM.eval_pure, honest,
        ofCoeffList_cons, ih, C_add]
      ring

/-- Honest `subList` subtracts the polynomials. -/
theorem ofCoeffList_eval_subList (p q : List α) :
    ofCoeffList ((subList p q).eval honest) = ofCoeffList p - ofCoeffList q := by
  induction q generalizing p with
  | nil => simp [subList]
  | cons b q ih =>
    simp only [subList, doSub, FreeM.eval_bind, FreeM.eval_lift, FreeM.eval_pure, honest,
      ofCoeffList_cons, ih, C_sub]
    rw [ofCoeffList_eq_C_headD_add_X_mul_tail p]
    ring

/-- Honest `addAt m base w` adds `X ^ m` times `w` when `m ≤ base.length`. -/
theorem ofCoeffList_eval_addAt {m : ℕ} {base : List α} (w : List α) (h : m ≤ base.length) :
    ofCoeffList ((addAt m base w).eval honest) = ofCoeffList base + X ^ m * ofCoeffList w := by
  conv_rhs => rw [← List.take_append_drop m base]
  simp only [addAt, FreeM.eval_bind, FreeM.eval_pure, ofCoeffList_append, ofCoeffList_eval_addList,
    List.length_take, Nat.min_eq_left h]
  ring

/-- Honest `mulFit n` multiplies the zero-padded first `n` coefficients of its operands. -/
theorem ofCoeffList_eval_mulFit (n : ℕ) (p q : List α) :
    ofCoeffList ((mulFit n p q).eval honest) =
      ofCoeffList (p.takeD n 0) * ofCoeffList (q.takeD n 0) := by
  induction n using Nat.strong_induction_on generalizing p q with
  | _ n ih =>
    match n with
    | 0 => simp [mulFit]
    | 1 => simp [mulFit, doMul, honest, ofCoeffList_cons, List.headD_eq_head?_getD]
    | n + 2 =>
      have ih' : ∀ j < n + 2, ∀ p q : List α, p.length ≤ j → q.length ≤ j →
          ofCoeffList ((mulFit j p q).eval honest) = ofCoeffList p * ofCoeffList q := by
        intro j hj p q hp hq
        rw [ih j hj, ofCoeffList_takeD_of_length_le hp, ofCoeffList_takeD_of_length_le hq]
      rw [mulFit]
      simp only [FreeM.eval_bind]
      obtain ⟨m, hm⟩ : ∃ m, (n + 2) / 2 = m := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k, n + 2 - m = k := ⟨_, rfl⟩
      have hN : n + 2 = m + k := by omega
      rw [hm, hk, hN, ofCoeffList_takeD_add p, ofCoeffList_takeD_add q]
      set p₀ := p.takeD m 0
      set p₁ := (p.drop m).takeD k 0
      set q₀ := q.takeD m 0
      set q₁ := (q.drop m).takeD k 0
      have hp₀ : p₀.length = m := List.takeD_length _ _ _
      have hp₁ : p₁.length = k := List.takeD_length _ _ _
      have hq₀ : q₀.length = m := List.takeD_length _ _ _
      have hq₁ : q₁.length = k := List.takeD_length _ _ _
      set s := (addList p₀ p₁).eval honest with hs
      set t := (addList q₀ q₁).eval honest with ht
      have hsl : s.length ≤ k := by rw [hs, length_eval_addList, hp₀, hp₁]; omega
      have htl : t.length ≤ k := by rw [ht, length_eval_addList, hq₀, hq₁]; omega
      have hlen₀ := length_eval_mulFit honest m p₀ q₀
      rw [ofCoeffList_eval_addAt _ (by simp only [List.length_append, hlen₀]; omega),
        ofCoeffList_eval_subList, ofCoeffList_eval_subList, ofCoeffList_append, ofCoeffList_cons,
        hlen₀, ih' m (by omega) p₀ q₀ hp₀.le hq₀.le, ih' k (by omega) s t hsl htl,
        ih' k (by omega) p₁ q₁ hp₁.le hq₁.le, hs, ht, ofCoeffList_eval_addList,
        ofCoeffList_eval_addList, C_0, zero_add]
      have hX : (X : α[X]) ^ (2 * m - 1) * X = X ^ m * X ^ m := by
        rw [← pow_succ, ← pow_add]
        congr 1
        omega
      linear_combination (ofCoeffList p₁ * ofCoeffList q₁) * hX

end Karatsuba

/-- **Correctness of Karatsuba multiplication.** Under the honest oracle, `karatsuba p q` is a
coefficient list of the product of the polynomials with coefficient lists `p` and `q`. -/
theorem ofCoeffList_eval_karatsuba (p q : List α) :
    ofCoeffList ((karatsuba p q).eval honest) = ofCoeffList p * ofCoeffList q := by
  rw [karatsuba, Karatsuba.ofCoeffList_eval_mulFit,
    ofCoeffList_takeD_of_length_le (le_max_left _ _),
    ofCoeffList_takeD_of_length_le (le_max_right _ _)]

/-- On the first `n` coefficients of two polynomials of degree less than `n`, honest `karatsuba`
returns a coefficient list of their product. -/
theorem ofCoeffList_eval_karatsuba_coeffsBelow {P Q : α[X]} {n : ℕ} (hP : P.natDegree < n)
    (hQ : Q.natDegree < n) :
    ofCoeffList ((karatsuba (P.coeffsBelow n) (Q.coeffsBelow n)).eval honest) = P * Q := by
  rw [ofCoeffList_eval_karatsuba, ofCoeffList_coeffsBelow hP, ofCoeffList_coeffsBelow hQ]

end Cslib.Query
