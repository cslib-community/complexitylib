/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Closure
public import Complexity.Foundations.Data.BitString.List
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.BitString.WordCount
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# Uniform aggregation of counting functions

Unary polynomial-time bounds permit a single verifier to aggregate an input-dependent number
of factors or summands. Padding certificates with false bits preserves counts exactly. Signed
products maintain two Boolean states, whose difference multiplies the signed contribution of
each block. This gives variable powers of GapP functions, not just fixed subring powers.

## Main results

* `SharpP.sum_bits_mem`, `GapP.sum_bits_mem`: sum over all words of a computed unary length.
* `GapP.pow_mem_polyTime`: an input-dependent unary exponent preserves GapP.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994].
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- Summing a uniform #P family over all words of a polynomial-time unary length preserves #P. -/
theorem SharpP.sum_bits_mem {f : α × List Bool → ℕ} {r : α → ℕ}
    (hf : f ∈ SharpP (encPair enc encBits))
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun a => ∑ w : Fin (r a) → Bool, f (a, List.ofFn w)) ∈ SharpP enc := by
  obtain ⟨p, V, hV, hf⟩ := mem_SharpP.mp hf
  let q : α → ℕ := fun a => p.eval (2 * (enc a).length + 1 + r a)
  let W : α × List Bool → Bool := fun x => V ((x.1, x.2.take (r x.1)), x.2.drop (r x.1))
  have hq : ComputableInPolyTime q enc encUnary := by dsimp [q]; fun_prop
  have hW : ComputableInPolyTime W (encPair enc encBits) encBool := by dsimp [W]; fun_prop
  convert mem_SharpP_of_polyTime_length hW
    ((ComputableInPolyTime.unary_add.comp (hr.prod hq)))
    using 1
  ext a
  change _ = acceptCount W a (r a + q a)
  rw [acceptCount_add]
  apply Finset.sum_congr rfl
  intro w _
  rw [hf]
  simp only [length_encPair, encBits_apply, List.length_ofFn]
  simp only [acceptCount, W, List.take_left' List.length_ofFn,
    List.drop_left' List.length_ofFn, q]

/-- GapP is closed under summing over all words of a polynomial-time unary length. -/
theorem GapP.sum_bits_mem {g : α × List Bool → ℤ} {r : α → ℕ}
    (hg : g ∈ GapP (encPair enc encBits))
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun a => ∑ w : Fin (r a) → Bool, g (a, List.ofFn w)) ∈ GapP enc := by
  obtain ⟨f₁, h₁, f₂, h₂, hg⟩ := hg
  refine ⟨_, SharpP.sum_bits_mem h₁ hr, _, SharpP.sum_bits_mem h₂ hr, fun a => ?_⟩
  simp only [hg, Finset.sum_sub_distrib, Nat.cast_sum]

namespace SignedProduct

/-- Positive and negative acceptance flags for a partial product. -/
abbrev State := Bool × Bool

/-- Difference of the two acceptance flags. -/
private def sign (s : State) : ℤ := (if s.1 then 1 else 0) - (if s.2 then 1 else 0)

/-- Multiplication of signed Boolean flags; overlap cancels in their difference. -/
def mul (s t : State) : State :=
  ((s.1 && t.1) || (s.2 && t.2), (s.1 && t.2) || (s.2 && t.1))

private theorem sign_mul (s t : State) : sign (mul s t) = sign s * sign t := by
  rcases s with ⟨a, b⟩
  rcases t with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem sign_fold {β : Type} (v : β → State) (xs : List β) (s : State) :
    sign (xs.foldl (fun s x => mul s (v x)) s) = sign s * (xs.map (sign ∘ v)).prod := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, sign_mul, List.map_cons, List.prod_cons,
      Function.comp_apply, mul_assoc]

/-- Count products of signed row contributions by two ordinary verifiers. -/
def verifier (r k : α → ℕ) (V W : α × List Bool → Bool) (b : Bool)
    (x : α × List Bool) : Bool :=
  let s := (BitString.listRows (r x.1) (k x.1) x.2).foldl
    (fun s row => mul s (V (x.1, row), W (x.1, row))) (true, false)
  if b then s.2 else s.1

/-- The two product verifiers run in polynomial time for unary row count and width. -/
private theorem polyTime_verifier {r k : α → ℕ} {V W : α × List Bool → Bool}
    (hr : ComputableInPolyTime r enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hW : ComputableInPolyTime W (encPair enc encBits) encBool) (b : Bool) :
    ComputableInPolyTime (verifier r k V W b) (encPair enc encBits) encBool := by
  let encS := encPair encBool encBool
  have hstep : ComputableInPolyTime
      (fun x : (α × State) × List Bool => mul x.1.2 (V (x.1.1, x.2), W (x.1.1, x.2)))
      (encPair (encPair enc encS) encBits) encS := by dsimp [mul, encS]; fun_prop
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encA := encBits) (encB := encS) (par := fun x : α × List Bool => x.1)
    (list := fun x => BitString.listRows (r x.1) (k x.1) x.2)
    (init := fun _ => (true, false))
    (step := fun a s row => mul s (V (a, row), W (a, row)))
    (ComputableInPolyTime.fst enc encBits) (by fun_prop)
    (ComputableInPolyTime.const (true, false)) hstep
    (growth := fun _ => 0) (PolyBounded.const 0) (by
      intro x s row _
      simp [encS, encBool_apply])
  cases b
  · exact (ComputableInPolyTime.fst encBool encBool).comp hfold
  · exact (ComputableInPolyTime.snd encBool encBool).comp hfold

/-- The difference of the row-product counts is the power of the original difference. -/
theorem count_sub (r k : α → ℕ) (V W : α × List Bool → Bool) (a : α) :
    (acceptCount (verifier r k V W false) a (r a * k a) : ℤ) -
      acceptCount (verifier r k V W true) a (r a * k a) =
        ((acceptCount V a (k a) : ℤ) - acceptCount W a (k a)) ^ r a := by
  have hs (x : Fin (r a * k a) → Bool) :
      sign ((BitString.listRows (r a) (k a) (List.ofFn x)).foldl
        (fun s row => mul s (V (a, row), W (a, row))) (true, false)) =
      ∏ i : Fin (r a), sign (V (a, List.ofFn (BitString.blocksEquiv x i)),
        W (a, List.ofFn (BitString.blocksEquiv x i))) := by
    rw [sign_fold, BitString.listRows_eq_ofFn, BitString.ofList_ofFn]
    simp only [sign, Bool.false_eq_true, ite_true, ite_false, sub_zero, one_mul,
      List.map_ofFn, List.prod_ofFn, Function.comp_def, BitString.blocksEquiv_apply]
    rfl
  simp only [acceptCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, ← Finset.sum_sub_distrib]
  change (∑ x, sign ((BitString.listRows (r a) (k a) (List.ofFn x)).foldl
    (fun s row => mul s (V (a, row), W (a, row))) (true, false))) = _
  simp_rw [hs]
  rw [(BitString.blocksEquiv (m := r a) (k := k a)).sum_comp
    (fun x => ∏ i : Fin (r a), sign (V (a, List.ofFn (x i)), W (a, List.ofFn (x i))))]
  rw [← Fintype.prod_sum (fun (_ : Fin (r a)) (x : Fin (k a) → Bool) =>
    sign (V (a, List.ofFn x), W (a, List.ofFn x)))]
  simp [sign, Finset.sum_sub_distrib]

end SignedProduct

/-- A GapP function raised to an input-dependent polynomial-time unary exponent is in GapP. -/
theorem GapP.pow_mem_polyTime {g : α → ℤ} {r : α → ℕ} (hg : g ∈ GapP enc)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun a => g a ^ r a) ∈ GapP enc := by
  obtain ⟨f₁, ⟨p₁, V₁, hV₁, hf₁⟩, f₂, ⟨p₂, V₂, hV₂, hf₂⟩, hg⟩ := hg
  let k : α → ℕ := fun a => (p₁ + p₂).eval (enc a).length
  let V := andVerifier (fun a => p₁.eval (enc a).length) V₁ allFalseVerifier
  let W := andVerifier (fun a => p₂.eval (enc a).length) V₂ allFalseVerifier
  have hk : ComputableInPolyTime k enc encUnary := by dsimp [k]; fun_prop
  have hV : ComputableInPolyTime V (encPair enc encBits) encBool := by dsimp [V]; fun_prop
  have hW : ComputableInPolyTime W (encPair enc encBits) encBool := by dsimp [W]; fun_prop
  have hlength := ComputableInPolyTime.unary_mul.comp (hr.prod hk)
  refine ⟨_, mem_SharpP_of_polyTime_length
    ((SignedProduct.polyTime_verifier hr hk hV hW false)) hlength,
    _, mem_SharpP_of_polyTime_length ((SignedProduct.polyTime_verifier hr hk hV hW true))
      hlength,
    fun a => ?_⟩
  change g a ^ r a =
    (acceptCount (SignedProduct.verifier r k V W false) a (r a * k a) : ℤ) -
      acceptCount (SignedProduct.verifier r k V W true) a (r a * k a)
  rw [SignedProduct.count_sub]
  congr 1
  rw [hg, hf₁, hf₂]
  dsimp [V, W, k]
  rw [Polynomial.eval_add, acceptCount_andVerifier_allFalseVerifier,
    Nat.add_comm (p₁.eval _), acceptCount_andVerifier_allFalseVerifier]

end Cslib.Complexity
