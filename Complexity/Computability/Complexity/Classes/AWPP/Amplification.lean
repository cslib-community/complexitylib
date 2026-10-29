/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.AWPP
public import Complexity.Computability.Complexity.Classes.SharpP.Aggregation
import Complexity.Computability.Complexity.Classes.BPP.Amplification
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.BitString.WordCount
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Uniform error reduction for AWPP

Majority amplification is a uniform polynomial in a GapP numerator and its complementary
numerator. Uniform word sums and unary powers establish its GapP membership. A finite counting
identity then permits the same majority tail estimate as in BPP; it does not assume that a GapP
numerator can itself be computed or sampled in polynomial time.

## Main definitions

* `AWPPAmplification.majorityPolynomial`: the homogeneous majority polynomial.

## Main results

* `AWPPAmplification.majorityPolynomial_mem`: the uniform majority numerator belongs to GapP.
* `AWPPAmplification.amplify`: explicit denominator and error bounds for a length polynomial.
* `exists_AWPP_gap_errorExponent`: exponentially small error for any polynomially bounded
  input-dependent exponent.

## References

* [S. Fenner, *PP-Lowness and a Simple Definition of AWPP*][Fenner2003].
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 7.4.1.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Finset

namespace AWPPAmplification

/-- The numerator of strict majority among `2R` independent trials with weights `g` and `D-g`. -/
def majorityPolynomial (g D : ℤ) (R : ℕ) : ℤ :=
  ∑ w : Fin (2 * R) → Bool,
    if R < (List.ofFn w).countP id then
      g ^ (List.ofFn w).countP id * (D - g) ^ (2 * R - (List.ofFn w).countP id) else 0

private theorem card_outcome_fiber {β : Type} [Fintype β] (V : β → Bool) {T : ℕ}
    (w : Fin T → Bool) :
    #{x : Fin T → β | (fun i => V (x i)) = w} =
      #{b | V b = true} ^ (List.ofFn w).countP id *
        #{b | V b = false} ^ (T - (List.ofFn w).countP id) := by
  classical
  have heq : (univ.filter fun x : Fin T → β => (fun i => V (x i)) = w) =
      Fintype.piFinset (fun i => univ.filter fun b => V b = w i) := by
    ext x
    simp [funext_iff]
  rw [heq, Fintype.card_piFinset]
  have hrow (i : Fin T) : #{b | V b = w i} =
      if w i then #{b | V b = true} else #{b | V b = false} := by cases w i <;> rfl
  simp_rw [hrow]
  rw [Finset.prod_ite]
  have hc : (List.ofFn w).countP id = #{i | w i = true} := by
    simp only [List.countP_ofFn, card_filter, id_eq]
  simp only [Finset.prod_const, hc]
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin T)))
    (fun i => w i = true)
  simp only [card_univ, Fintype.card_fin] at hsum
  congr 1
  congr 1
  lia

private theorem card_majority_eq {β : Type} [Fintype β] (V : β → Bool) (R : ℕ) :
    (#{x : Fin (2 * R) → β | R < (List.ofFn fun i => V (x i)).countP id} : ℤ) =
      majorityPolynomial #{b | V b = true}
        (#{b | V b = true} + #{b | V b = false}) R := by
  classical
  let S := univ.filter fun x : Fin (2 * R) → β =>
    R < (List.ofFn fun i => V (x i)).countP id
  have hfiber (w : Fin (2 * R) → Bool) :
      #{x ∈ S | (fun i => V (x i)) = w} =
        if R < (List.ofFn w).countP id then
          #{x : Fin (2 * R) → β | (fun i => V (x i)) = w} else 0 := by
    by_cases hw : R < (List.ofFn w).countP id
    · rw [ite_eq_left hw]
      congr 1
      ext x
      simp only [S, mem_filter, mem_univ, true_and]
      exact ⟨And.right, fun h => ⟨h ▸ hw, h⟩⟩
    · rw [ite_eq_right hw, card_eq_zero]
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      simp only [S, mem_filter, mem_univ, true_and] at hx
      exact hw (hx.2 ▸ hx.1)
  have h := card_eq_sum_card_fiberwise (s := S) (t := univ)
    (f := fun x i => V (x i)) (fun _ _ => mem_univ _)
  change (S.card : ℤ) = _
  rw [h, Nat.cast_sum]
  unfold majorityPolynomial
  apply Finset.sum_congr rfl
  intro w _
  rw [hfiber, card_outcome_fiber]
  split_ifs <;> simp [Nat.cast_mul, Nat.cast_pow]

/-- The majority polynomial is uniformly GapP for polynomial-time unary repetition counts. -/
theorem majorityPolynomial_mem {α : Type} {enc : α ↪ List Bool} {g D : α → ℤ}
    {r : α → ℕ} (hg : g ∈ GapP enc) (hD : D ∈ GapP enc)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun a => majorityPolynomial (g a) (D a) (r a)) ∈ GapP enc := by
  let ones : α × List Bool → ℕ := fun x => x.2.countP id
  have hones : ComputableInPolyTime ones (encPair enc encBits) encUnary := by
    dsimp [ones]
    fun_prop
  have hR : ComputableInPolyTime (fun x : α × List Bool => r x.1)
      (encPair enc encBits) encUnary := hr.comp (.fst enc encBits)
  have hz : ComputableInPolyTime (fun x : α × List Bool => 2 * r x.1 - ones x)
      (encPair enc encBits) encUnary := by fun_prop
  have hg' := GapP.pow_mem_polyTime (GapP.comp_mem hg (.fst enc encBits)) hones
  have hd' := GapP.pow_mem_polyTime (GapP.comp_mem (GapP.sub_mem' hD hg) (.fst enc encBits)) hz
  have htest : ComputableInPolyTime
      (fun x : α × List Bool => if r x.1 < ones x then (1 : ℕ) else 0)
      (encPair enc encBits) encNat :=
    (ComputableInPolyTime.ite_decide (ComputableInPolyTime.unary_lt' hR
      hones) (.const 1) (.const 0))
  have hweight := GapP.mul_mem (GapP.mul_mem hg' hd')
    (SharpP.natCast_mem_GapP (mem_SharpP_of_polyTime htest))
  have hsum := GapP.sum_bits_mem hweight
    (ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hr))
  convert hsum using 1
  ext a
  unfold majorityPolynomial
  apply Finset.sum_congr rfl
  intro w _
  simp only [Pi.mul_apply, Function.comp_apply, Pi.sub_apply, ones]
  split_ifs <;> simp

/-- The majority polynomial has the same bounds as a majority count, even when its numerator
is a GapP value rather than an efficiently sampleable acceptance count. -/
theorem majorityPolynomial_bounds {g : ℤ} {m e : ℕ}
    (h0 : 0 ≤ g) (h1 : g ≤ (2 : ℤ) ^ m) :
    let H := majorityPolynomial g ((2 : ℤ) ^ m) (6 * e)
    let D := (2 : ℤ) ^ (2 * (6 * e) * m)
    (0 ≤ H ∧ H ≤ D) ∧
      (2 * (2 : ℤ) ^ m ≤ 3 * g → (2 : ℤ) ^ e * (D - H) ≤ D) ∧
      (3 * g ≤ (2 : ℤ) ^ m → (2 : ℤ) ^ e * H ≤ D) := by
  classical
  let V : BitString m → Bool := fun x => decide (BitString.binaryValue (List.ofFn x) < g.toNat)
  have hg : g.toNat ≤ 2 ^ m := by
    rw [Int.toNat_le]
    exact_mod_cast h1
  have hv : #{x | V x = true} = g.toNat := by
    simpa only [V, decide_eq_true_eq] using BitString.card_filter_binaryValue_lt hg
  have htot : #{x | V x = true} + #{x | V x = false} = 2 ^ m := by
    simpa only [Bool.not_eq_true, card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool] using card_filter_add_card_filter_not (s := (univ : Finset (BitString m)))
        (fun x => V x = true)
  let M := #{x : BitString (2 * (6 * e) * m) |
    6 * e < #{i | V (BitString.block x i) = true}}
  have hM : (M : ℤ) = majorityPolynomial g ((2 : ℤ) ^ m) (6 * e) := by
    have heq : M = #{x : Fin (2 * (6 * e)) → BitString m |
        6 * e < (List.ofFn fun i => V (x i)).countP id} := by
      apply card_equiv BitString.blocksEquiv
      intro x
      simp only [mem_filter, mem_univ, true_and, List.countP_ofFn, card_filter,
        id_eq, BitString.blocksEquiv_apply]
    rw [heq, card_majority_eq]
    have ht : (#{x | V x = true} : ℤ) + #{x | V x = false} = (2 : ℤ) ^ m := by
      exact_mod_cast htot
    rw [ht, hv, Int.toNat_of_nonneg h0]
  have hMle : M ≤ 2 ^ (2 * (6 * e) * m) := by
    exact (card_filter_le _ _).trans (by simp)
  have hcompl : M + #{x : BitString (2 * (6 * e) * m) |
      #{i | V (BitString.block x i) = true} ≤ 6 * e} = 2 ^ (2 * (6 * e) * m) := by
    simpa only [not_lt, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using
      card_filter_add_card_filter_not (s := (univ : Finset (BitString (2 * (6 * e) * m))))
        (fun x => 6 * e < #{i | V (BitString.block x i) = true})
  dsimp only
  rw [← hM]
  refine ⟨⟨by positivity, by exact_mod_cast hMle⟩, ?_, ?_⟩
  · intro hy
    have hv' : 2 * 2 ^ m ≤ 3 * #{x | V x = true} := by
      rw [hv]
      exact_mod_cast (show 2 * (2 : ℤ) ^ m ≤ 3 * (g.toNat : ℤ) by
        simpa only [Int.toNat_of_nonneg h0] using hy)
    have htail := BitString.two_pow_mul_card_filter_card_filter_block_le (e := e) rfl
      (fun x => V x = true) hv'
    have hc : (#{x : BitString (2 * (6 * e) * m) |
        #{i | V (BitString.block x i) = true} ≤ 6 * e} : ℤ) =
        (2 : ℤ) ^ (2 * (6 * e) * m) - M := by
      have hc' : (M : ℤ) + (#{x : BitString (2 * (6 * e) * m) |
          #{i | V (BitString.block x i) = true} ≤ 6 * e} : ℤ) =
          (2 : ℤ) ^ (2 * (6 * e) * m) := by exact_mod_cast hcompl
      lia
    have htail' : (2 : ℤ) ^ e *
        (#{x : BitString (2 * (6 * e) * m) |
          #{i | V (BitString.block x i) = true} ≤ 6 * e} : ℤ) ≤
        (2 : ℤ) ^ (2 * (6 * e) * m) := by exact_mod_cast htail
    rwa [hc] at htail'
  · intro hn
    have hv' : 2 * 2 ^ m ≤ 3 * #{x | V x = false} := by
      have hn' : 3 * g.toNat ≤ 2 ^ m := by
        exact_mod_cast (show 3 * (g.toNat : ℤ) ≤ (2 : ℤ) ^ m by
          simpa only [Int.toNat_of_nonneg h0] using hn)
      lia
    have htail := BitString.two_pow_mul_card_filter_card_filter_block_le (e := e) rfl
      (fun x => V x = false) hv'
    have hsub : M ≤ #{x : BitString (2 * (6 * e) * m) |
        #{i | V (BitString.block x i) = false} ≤ 6 * e} := by
      apply card_le_card
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      have hs := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * (6 * e)))))
        (fun i => V (BitString.block x i) = true)
      simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at hs
      lia
    exact_mod_cast (Nat.mul_le_mul_left (2 ^ e) hsub).trans htail

/-- A dyadic AWPP witness with exponent `p(n)` amplifies to error `2^(-q(n))` by `12q(n)`
majority trials, with exact denominator exponent `12q(n)p(n)`. The amplified numerator is
uniformly GapP; no efficient sampler for the original numerator is assumed. -/
theorem amplify {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {g : α → ℤ} (hg : g ∈ GapP enc) (p q : Polynomial ℕ)
    (hA : ∀ a, (0 ≤ g a ∧ g a ≤ (2 : ℤ) ^ p.eval (enc a).length) ∧
      (a ∈ A → 2 * (2 : ℤ) ^ p.eval (enc a).length ≤ 3 * g a) ∧
      (a ∉ A → 3 * g a ≤ (2 : ℤ) ^ p.eval (enc a).length)) :
    let G := fun a => majorityPolynomial (g a) ((2 : ℤ) ^ p.eval (enc a).length)
      (6 * q.eval (enc a).length)
    G ∈ GapP enc ∧ ∀ a,
      let D := (2 : ℤ) ^ (12 * q * p).eval (enc a).length
      (0 ≤ G a ∧ G a ≤ D) ∧
        (a ∈ A → (2 : ℤ) ^ q.eval (enc a).length * (D - G a) ≤ D) ∧
        (a ∉ A → (2 : ℤ) ^ q.eval (enc a).length * G a ≤ D) := by
  refine ⟨majorityPolynomial_mem hg (GapP.two_pow_mem p) (by fun_prop), fun a => ?_⟩
  obtain ⟨hb, hy, hn⟩ := hA a
  have h := majorityPolynomial_bounds (e := q.eval (enc a).length) hb.1 hb.2
  have he : (12 * q * p).eval (enc a).length =
      2 * (6 * q.eval (enc a).length) * p.eval (enc a).length := by
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
    ring
  dsimp only
  rw [he]
  exact ⟨h.1, fun ha => h.2.1 (hy ha), fun ha => h.2.2 (hn ha)⟩

end AWPPAmplification

/-- **Uniform AWPP amplification.** For every requested exponent bounded by a polynomial in
encoded input length, one GapP witness has error at most `2^(-r(a))` and a length-polynomial
dyadic denominator. The requested function need not itself be computable: the construction
uses a fixed dominating polynomial, not an oracle for that function. -/
theorem exists_AWPP_gap_errorExponent {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ AWPP enc) (r : α → ℕ)
    (hr : PolyBounded (fun a => (enc a).length) r) :
    ∃ G ∈ GapP enc, ∃ P : Polynomial ℕ, ∀ a,
      let D := (2 : ℤ) ^ P.eval (enc a).length
      (0 ≤ G a ∧ G a ≤ D) ∧
        (a ∈ A → (2 : ℤ) ^ r a * (D - G a) ≤ D) ∧
        (a ∉ A → (2 : ℤ) ^ r a * G a ≤ D) := by
  obtain ⟨g, hg, p, hA⟩ := hA
  obtain ⟨c, d, hb⟩ := hr.exists_le
  let q : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d
  obtain ⟨hG, hbound⟩ := AWPPAmplification.amplify hg p q hA
  refine ⟨_, hG, 12 * q * p, fun a => ?_⟩
  obtain ⟨h01, hy, hn⟩ := hbound a
  have hle : r a ≤ q.eval (enc a).length := by simpa [q] using hb a
  have hpow : (2 : ℤ) ^ r a ≤ (2 : ℤ) ^ q.eval (enc a).length :=
    pow_le_pow_right₀ (by norm_num) hle
  exact ⟨h01, fun ha => (mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr h01.2)).trans (hy ha),
    fun ha => (mul_le_mul_of_nonneg_right hpow h01.1).trans (hn ha)⟩

end Cslib.Complexity
