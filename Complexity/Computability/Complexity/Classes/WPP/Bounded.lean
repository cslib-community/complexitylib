/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.WPP.Robustness
public import Complexity.Computability.Complexity.Classes.SharpP.Products
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Uniform bounded Boolean closure of wide-gap classes

A single jointly uniform language on instances and unary indices may be conjoined or disjoined
over a polynomial-time unary bound. For LWPP the bound may vary between inputs of the same
length: polynomial-family robustness normalizes all possible prefix-product targets.

## Main results

* `forall_lt_mem_WPP`, `exists_lt_mem_WPP`: uniform bounded Boolean closure of WPP.
* `forall_lt_mem_LWPP`, `exists_lt_mem_LWPP`: the corresponding LWPP closure, including
  input-dependent bounds.

## References

These are deductions from the counting product algebra of
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994] and polynomial-family robustness of
[Hemaspaandra, Hemaspaandra, Spakowski and Watanabe][HemaspaandraEtAl2018], Theorem 3.1.
The results concern the encoded verifier classes; they do not assert adaptive oracle closure.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Finset

variable {α : Type} {enc : α ↪ List Bool} {A : Set (α × ℕ)} {r : α → ℕ}

private theorem prod_eq_zero_of_not_forall {g f : α × ℕ → ℤ}
    (hg : ∀ x, g x = 0 ∨ g x = f x) (hA : ∀ x, x ∈ A ↔ g x = f x)
    {a : α} (ha : ¬ ∀ i < r a, (a, i) ∈ A) :
    (∏ i ∈ range (r a), g (a, i)) = 0 := by
  push Not at ha
  obtain ⟨i, hi, hno⟩ := ha
  apply prod_eq_zero (mem_range.mpr hi)
  exact (hg (a, i)).resolve_right (fun h => hno ((hA (a, i)).mpr h))

/-- A jointly WPP family is closed under conjunction over a polynomial-time unary bound. -/
theorem forall_lt_mem_WPP (hA : A ∈ WPP (encPair enc encUnary))
    (hr : ComputableInPolyTime r enc encUnary) :
    {a | ∀ i < r a, (a, i) ∈ A} ∈ WPP enc := by
  rw [mem_WPP] at hA ⊢
  obtain ⟨g, hg, f, hf, hn, hR, hA⟩ := hA
  let G a := ∏ i ∈ range (r a), g (a, i)
  let F a := ∏ i ∈ range (r a), f (a, i)
  have hF (a) : F a ≠ 0 := prod_ne_zero_iff.mpr fun i _ => hn (a, i)
  have hy (a) (ha : ∀ i < r a, (a, i) ∈ A) : G a = F a :=
    prod_congr rfl fun i hi => (hA (a, i)).mp (ha i (mem_range.mp hi))
  have hno (a) (ha : ¬ ∀ i < r a, (a, i) ∈ A) : G a = 0 :=
    prod_eq_zero_of_not_forall hR hA ha
  refine ⟨G, GapP.prod_range_mem hg hr, F,
    ComputableInPolyTime.intBin_prod_range hf hr, hF, ?_, ?_⟩
  · intro a
    by_cases ha : ∀ i < r a, (a, i) ∈ A
    · exact Or.inr (hy a ha)
    · exact Or.inl (hno a ha)
  · intro a
    change (∀ i < r a, (a, i) ∈ A) ↔ G a = F a
    constructor
    · exact hy a
    · intro h
      by_contra ha
      exact hF a (h.symm.trans (hno a ha))

/-- A jointly WPP family is closed under disjunction over a polynomial-time unary bound. -/
theorem exists_lt_mem_WPP (hA : A ∈ WPP (encPair enc encUnary))
    (hr : ComputableInPolyTime r enc encUnary) :
    {a | ∃ i < r a, (a, i) ∈ A} ∈ WPP enc := by
  convert compl_mem_WPP (forall_lt_mem_WPP (compl_mem_WPP hA) hr) using 1
  ext a
  simp

/-- A jointly LWPP family is closed under conjunction over a polynomial-time unary bound.
The count `r a` may vary at fixed input length. If `p` bounds it, polynomial-family robustness
normalizes the nonzero targets `∏ i < k, f (2 * n + 1 + i)` for every `k ≤ p n`. -/
theorem forall_lt_mem_LWPP (hA : A ∈ LWPP (encPair enc encUnary))
    (hr : ComputableInPolyTime r enc encUnary) :
    {a | ∀ i < r a, (a, i) ∈ A} ∈ LWPP enc := by
  obtain ⟨g, hg, f, hf, hn, hR, hA⟩ := mem_LWPP.mp hA
  obtain ⟨p, hb⟩ := hr.polyBounded.exists_polynomial
  let T (x : ℕ × ℕ) := ∏ i ∈ range x.2, f (2 * x.1 + 1 + i)
  have hT : ComputableInPolyTime T (encPair encUnary encUnary) encIntBin := by
    refine ComputableInPolyTime.intBin_prod_range
      (f := fun x : (ℕ × ℕ) × ℕ => f (2 * x.1.1 + 1 + x.2)) ?_ ?_ <;> fun_prop
  have hp : ComputableInPolyTime (fun n => p.eval n + 1) encUnary encUnary := by fun_prop
  apply mem_LWPP_of_indexed_targets (GapP.prod_range_mem hg hr) hT hp
  · intro n k _
    exact prod_ne_zero_iff.mpr fun i _ => hn _
  · intro a ha
    refine ⟨r a, ?_, ?_⟩
    · exact Nat.lt_succ_of_le (hb a)
    · apply prod_congr rfl
      intro i hi
      have h := (hA (a, i)).mp (ha i (mem_range.mp hi))
      simpa only [length_encPair, encUnary_apply, List.length_replicate] using h
  · intro a ha
    exact prod_eq_zero_of_not_forall hR hA ha

/-- A jointly LWPP family is closed under disjunction over an input-dependent polynomial-time
unary bound. The empty range gives the empty language. -/
theorem exists_lt_mem_LWPP (hA : A ∈ LWPP (encPair enc encUnary))
    (hr : ComputableInPolyTime r enc encUnary) :
    {a | ∃ i < r a, (a, i) ∈ A} ∈ LWPP enc := by
  convert compl_mem_LWPP (forall_lt_mem_LWPP (compl_mem_LWPP hA) hr) using 1
  ext a
  simp

end Cslib.Complexity
