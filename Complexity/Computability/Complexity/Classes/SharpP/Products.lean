/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Aggregation
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.List.OfFn
import Cslib.Foundations.Data.Polynomial.Monotone
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Uniform indexed products of counting functions

A jointly uniform family on an encoded instance and a unary index admits products over a
polynomial-time unary number of factors. Index-dependent certificates are padded to a common
polynomially bounded row width, preserving their counts exactly. For GapP, expansion over
Boolean choices reduces the product of differences to uniform #P products and a signed word sum.

## Main definitions

* `SharpP.indexedProductVerifier`: check a separate indexed verifier on each certificate row.

## Main results

* `SharpP.acceptCount_indexedProductVerifier`: exact cardinality factorization.
* `SharpP.prod_range_mem`: uniform indexed products preserve #P.
* `GapP.prod_range_mem`: uniform indexed products preserve GapP.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994].
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Finset

variable {α : Type} {enc : α ↪ List Bool}

namespace SharpP

/-- The verifier checks row `i` using the indexed instance `(a, i)`, for every `i < r(a)`. -/
def indexedProductVerifier (r k : α → ℕ) (V : (α × ℕ) × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  (List.range (r x.1)).all fun i => V ((x.1, i), BitString.listRow (k x.1) i x.2)

/-- Uniform row counts, widths and indexed tests give a polynomial-time product verifier. -/
@[fun_prop]
theorem polyTime_indexedProductVerifier {r k : α → ℕ} {V : (α × ℕ) × List Bool → Bool}
    (hr : ComputableInPolyTime r enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary)
    (hV : ComputableInPolyTime V (encPair (encPair enc encUnary) encBits) encBool) :
    ComputableInPolyTime (indexedProductVerifier r k V) (encPair enc encBits) encBool := by
  unfold indexedProductVerifier
  fun_prop

/-- Indexed row tuples have the product of their individual acceptance counts. -/
theorem acceptCount_indexedProductVerifier (r k : α → ℕ)
    (V : (α × ℕ) × List Bool → Bool) (a : α) :
    acceptCount (indexedProductVerifier r k V) a (r a * k a) =
      ∏ i ∈ range (r a), acceptCount V (a, i) (k a) := by
  rw [← Fin.prod_univ_eq_prod_range]
  simp only [acceptCount]
  rw [← Fintype.card_piFinset]
  apply card_equiv BitString.blocksEquiv
  intro x
  simp only [mem_filter, mem_univ, true_and, indexedProductVerifier, List.all_eq_true,
    List.mem_range, Fintype.mem_piFinset]
  constructor
  · intro h i
    simpa only [BitString.listRow_eq_ofFn (k a) i, BitString.ofList_ofFn,
      BitString.blocksEquiv_apply] using h i i.2
  · intro h i hi
    simpa only [BitString.listRow_eq_ofFn (k a) ⟨i, hi⟩, BitString.ofList_ofFn,
      BitString.blocksEquiv_apply] using h ⟨i, hi⟩

/-- A jointly uniform #P family on an instance and unary index may be multiplied over a
polynomial-time unary range. If the original certificate polynomial is `p`, a common row width
is `p(2|a|+1+r(a))`, and the unpadded total length is `r(a)` times that width. -/
theorem prod_range_mem {f : α × ℕ → ℕ} {r : α → ℕ}
    (hf : f ∈ SharpP (encPair enc encUnary))
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun a => ∏ i ∈ range (r a), f (a, i)) ∈ SharpP enc := by
  obtain ⟨p, V, hV, hf⟩ := mem_SharpP.mp hf
  let width : α × ℕ → ℕ := fun x => p.eval ((encPair enc encUnary) x).length
  let k : α → ℕ := fun a => p.eval (2 * (enc a).length + 1 + r a)
  let W := andVerifier width V allFalseVerifier
  have hk : ComputableInPolyTime k enc encUnary := by dsimp [k]; fun_prop
  have hW : ComputableInPolyTime W
      (encPair (encPair enc encUnary) encBits) encBool := by dsimp [W, width]; fun_prop
  convert mem_SharpP_of_polyTime_length
    (polyTime_indexedProductVerifier hr hk hW)
    ((ComputableInPolyTime.unary_mul.comp (hr.prod hk))) using 1
  ext a
  change _ = acceptCount (indexedProductVerifier r k W) a (r a * k a)
  rw [acceptCount_indexedProductVerifier]
  apply prod_congr rfl
  intro i hi
  have hle : width (a, i) ≤ k a := by
    simp only [width, k, length_encPair, encUnary_apply, List.length_replicate]
    exact p.eval_mono (by lia [mem_range.mp hi])
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hle
  rw [hn, acceptCount_andVerifier_allFalseVerifier, hf]

end SharpP

/-- Expanding a product of `(f i - c * g i)` over Boolean choices pulls out `(-c)` to the number of
true bits. -/
theorem prod_sub_mul_eq_sum {n : ℕ} (f g : Fin n → ℤ) (c : ℤ) :
    (∏ i, (f i - c * g i)) = ∑ w : Fin n → Bool,
      (-c) ^ (List.ofFn w).countP id * ∏ i, if w i then g i else f i := by
  have h (w : Fin n → Bool) :
      (∏ i, if w i then -(c * g i) else f i) =
        (-c) ^ (List.ofFn w).countP id * ∏ i, if w i then g i else f i := by
    calc
      _ = ∏ i, (if w i then -c else 1) * (if w i then g i else f i) := by
        apply prod_congr rfl
        intro i _
        cases w i <;> simp
      _ = _ := by
        rw [prod_mul_distrib, prod_ite]
        simp only [prod_const, one_pow, mul_one, List.countP_ofFn, card_filter, id_eq]
  simp_rw [← h]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) => if b then -(c * g i) else f i)]
  simp [sub_eq_add_neg, add_comm]

/-- Expanding a product of differences over Boolean choices: each term selects `g i` where `w i` is
true and `f i` where `w i` is false, weighted by `(-1)` to the number of true bits. -/
theorem prod_sub_eq_sum {n : ℕ} (f g : Fin n → ℤ) :
    (∏ i, (f i - g i)) = ∑ w : Fin n → Bool,
      (-1 : ℤ) ^ (List.ofFn w).countP id * ∏ i, if w i then g i else f i := by
  simpa using prod_sub_mul_eq_sum f g 1

/-- A jointly uniform GapP family on an instance and unary index may be multiplied over a
polynomial-time unary range. Boolean expansion uses certified #P products and a polynomial-time
parity sign, so no general GapP product closure is assumed. -/
theorem GapP.prod_range_mem {g : α × ℕ → ℤ} {r : α → ℕ}
    (hg : g ∈ GapP (encPair enc encUnary))
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun a => ∏ i ∈ range (r a), g (a, i)) ∈ GapP enc := by
  obtain ⟨f₁, h₁, f₂, h₂, hg⟩ := hg
  let select : (α × List Bool) × ℕ → ℕ := fun x =>
    if x.1.2.getD x.2 false then f₂ (x.1.1, x.2) else f₁ (x.1.1, x.2)
  have hreindex : ComputableInPolyTime
      (fun x : (α × List Bool) × ℕ => (x.1.1, x.2))
      (encPair (encPair enc encBits) encUnary) (encPair enc encUnary) := by fun_prop
  have hselect : select ∈ SharpP (encPair (encPair enc encBits) encUnary) :=
    SharpP.ite_mem (by fun_prop) (SharpP.comp_mem h₂ hreindex) (SharpP.comp_mem h₁ hreindex)
  have hprod := SharpP.prod_range_mem hselect (hr.comp (.fst enc encBits))
  have hsign : ComputableInPolyTime
      (fun x : α × List Bool => (-1 : ℤ) ^ x.2.countP id)
      (encPair enc encBits) encIntBin := by fun_prop
  have hsum := GapP.sum_bits_mem
    (GapP.mul_mem (mem_GapP_of_polyTime hsign) (SharpP.natCast_mem_GapP hprod)) hr
  convert hsum using 1
  ext a
  rw [← Fin.prod_univ_eq_prod_range]
  simp only [hg]
  rw [prod_sub_eq_sum]
  apply sum_congr rfl
  intro w _
  simp only [Pi.mul_apply, Function.comp_apply, Nat.cast_prod]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range]
  apply prod_congr rfl
  intro i _
  simp [select, List.getD, i.2]

end Cslib.Complexity
