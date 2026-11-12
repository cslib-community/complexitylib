/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.BitString.WordCount

/-!
# Combining verifiers

The counting classes `#P`, `PP`, `RP` and `BPP` are all defined through polynomial-time functions
`V : α × List Bool → Bool` that read an instance and a string of bits, and through the number
`Cslib.Complexity.acceptCount V a n` of strings of length `n` that `V` accepts together with `a`.
This file provides verifiers built from other verifiers, each with its polynomial-time rule
(registered with `fun_prop`) and the number of strings it accepts.

* `Cslib.Complexity.andVerifier k V₁ V₂` runs `V₁` on the first `k a` bits and `V₂` on the rest,
  and accepts when both accept. The number of strings it accepts is the product of the numbers
  that `V₁` and `V₂` accept (`Cslib.Complexity.acceptCount_andVerifier`). With `V₂` accepting
  everything, it multiplies the count by a power of two.
* `Cslib.Complexity.padVerifier k V` runs `V` on the first `k a` bits and requires the rest to be
  `false` (`Cslib.Complexity.allFalseVerifier`), so it accepts as many strings of any length
  `n ≥ k a` as `V` accepts of length `k a` (`Cslib.Complexity.acceptCount_padVerifier_of_le`).
* `Cslib.Complexity.orVerifier k V₁ V₂` accepts when either accepts; the rejected strings multiply
  (`Cslib.Complexity.acceptCount_orVerifier`).
* `Cslib.Complexity.selectVerifier V₀ V₁` lets the first bit choose between `V₀` and `V₁` on the
  remaining bits; the counts add (`Cslib.Complexity.acceptCount_selectVerifier`).
* `Cslib.Complexity.sumVerifier k₁ k₂ V₁ V₂` selects between `V₁` and `V₂` padded to a common
  length, so it adds counts taken at different lengths `k₁ a` and `k₂ a`
  (`Cslib.Complexity.acceptCount_sumVerifier`). This is how `#P` is closed under addition.

Running two verifiers on disjoint parts of the random string is the usual way to combine
independent random choices [Arora and Barak, Chapters 7 and 17][AroraBarak09].

## Main definitions

* `Cslib.Complexity.allFalseVerifier`, `Cslib.Complexity.andVerifier`,
  `Cslib.Complexity.padVerifier`, `Cslib.Complexity.orVerifier`,
  `Cslib.Complexity.selectVerifier`, `Cslib.Complexity.sumVerifier`.

## Main results

* `Cslib.Complexity.acceptCount_andVerifier`, `Cslib.Complexity.acceptCount_padVerifier_of_le`,
  `Cslib.Complexity.acceptCount_orVerifier`, `Cslib.Complexity.acceptCount_selectVerifier`,
  `Cslib.Complexity.acceptCount_sumVerifier`: counts of the combined verifiers.
* `Cslib.Complexity.computableInPolyTime_andVerifier`,
  `Cslib.Complexity.computableInPolyTime_padVerifier`,
  `Cslib.Complexity.computableInPolyTime_orVerifier`,
  `Cslib.Complexity.computableInPolyTime_selectVerifier`,
  `Cslib.Complexity.computableInPolyTime_sumVerifier`: the combined verifiers are
  polynomial-time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-! ### The string of `false`s -/

/-- The verifier accepting, with every instance, exactly the strings of `false`s. -/
def allFalseVerifier (x : α × List Bool) : Bool := !x.2.any fun b => b

/-- `allFalseVerifier` accepts one string of each length. -/
@[simp]
theorem acceptCount_allFalseVerifier (a : α) (n : ℕ) : acceptCount allFalseVerifier a n = 1 :=
  BitString.card_filter_not_any n

/-- `allFalseVerifier` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_allFalseVerifier {enc : α ↪ List Bool} :
    ComputableInPolyTime allFalseVerifier (encPair enc encBits) encBool := by
  unfold allFalseVerifier
  fun_prop

/-! ### Conjunction on disjoint parts of the string -/

/-- Run `V₁` on the first `k a` bits and `V₂` on the remaining bits, and accept when both
accept. -/
def andVerifier (k : α → ℕ) (V₁ V₂ : α × List Bool → Bool) (x : α × List Bool) : Bool :=
  V₁ (x.1, x.2.take (k x.1)) && V₂ (x.1, x.2.drop (k x.1))

/-- **Independent runs multiply**: on strings of length `k a + n`, `andVerifier k V₁ V₂` accepts
the product of the numbers of strings that `V₁` and `V₂` accept. -/
theorem acceptCount_andVerifier (k : α → ℕ) (V₁ V₂ : α × List Bool → Bool) (a : α) (n : ℕ) :
    acceptCount (andVerifier k V₁ V₂) a (k a + n) =
      acceptCount V₁ a (k a) * acceptCount V₂ a n := by
  have h := BitString.card_filter_ofFn_add (k a) n
    fun u w => V₁ (a, u) = true ∧ V₂ (a, w) = true
  simp only [acceptCount, andVerifier, Bool.and_eq_true]
  rw [h, Finset.card_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : V₁ (a, List.ofFn u) = true <;> simp [hu]

/-- Ignoring the bits after the first `k a` multiplies the number of accepted strings by a power
of two. -/
theorem acceptCount_andVerifier_true (k : α → ℕ) (V : α × List Bool → Bool) (a : α) (n : ℕ) :
    acceptCount (andVerifier k V fun _ => true) a (k a + n) = acceptCount V a (k a) * 2 ^ n := by
  rw [acceptCount_andVerifier, acceptCount_true]

/-- Independent conjunction of plain polynomial-time verifiers is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_andVerifier {enc : α ↪ List Bool} {k : α → ℕ}
    {V₁ V₂ : α × List Bool → Bool} (hk : ComputableInPolyTime k enc encUnary)
    (hV₁ : ComputableInPolyTime V₁ (encPair enc encBits) encBool)
    (hV₂ : ComputableInPolyTime V₂ (encPair enc encBits) encBool) :
    ComputableInPolyTime (andVerifier k V₁ V₂) (encPair enc encBits) encBool := by
  unfold andVerifier
  fun_prop

/-! ### Padding -/

/-- Run `V` on the first `k a` bits and require the remaining bits to be `false`. -/
def padVerifier (k : α → ℕ) (V : α × List Bool → Bool) : α × List Bool → Bool :=
  andVerifier k V allFalseVerifier

/-- **Padding**: on strings of any length `n ≥ k a`, `padVerifier k V` accepts as many strings as
`V` accepts of length `k a`. -/
theorem acceptCount_padVerifier_of_le (k : α → ℕ) (V : α × List Bool → Bool) {a : α} {n : ℕ}
    (h : k a ≤ n) : acceptCount (padVerifier k V) a n = acceptCount V a (k a) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [padVerifier, acceptCount_andVerifier, acceptCount_allFalseVerifier, mul_one]

/-- Padding a plain polynomial-time verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_padVerifier {enc : α ↪ List Bool} {k : α → ℕ}
    {V : α × List Bool → Bool} (hk : ComputableInPolyTime k enc encUnary)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ComputableInPolyTime (padVerifier k V) (encPair enc encBits) encBool := by
  unfold padVerifier
  fun_prop

/-! ### Disjunction on disjoint parts of the string -/

/-- Run `V₁` on the first `k a` bits and `V₂` on the remaining bits, and accept when either
accepts. -/
def orVerifier (k : α → ℕ) (V₁ V₂ : α × List Bool → Bool) (x : α × List Bool) : Bool :=
  V₁ (x.1, x.2.take (k x.1)) || V₂ (x.1, x.2.drop (k x.1))

/-- **Independent rejections multiply**: on strings of length `k a + n`, `orVerifier k V₁ V₂`
rejects the product of the numbers of strings that `V₁` and `V₂` reject. -/
theorem acceptCount_orVerifier (k : α → ℕ) (V₁ V₂ : α × List Bool → Bool) (a : α) (n : ℕ) :
    acceptCount (orVerifier k V₁ V₂) a (k a + n) +
        acceptCount (fun x => !V₁ x) a (k a) * acceptCount (fun x => !V₂ x) a n =
      2 ^ (k a + n) := by
  have h : acceptCount (andVerifier k (fun x => !V₁ x) fun x => !V₂ x) a (k a + n) =
      acceptCount (fun x => !orVerifier k V₁ V₂ x) a (k a + n) :=
    acceptCount_congr (fun _ => by simp only [andVerifier, orVerifier, Bool.not_or]) _
  rw [← acceptCount_andVerifier, h, acceptCount_add_acceptCount_not]

/-- Independent disjunction of plain polynomial-time verifiers is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_orVerifier {enc : α ↪ List Bool} {k : α → ℕ}
    {V₁ V₂ : α × List Bool → Bool} (hk : ComputableInPolyTime k enc encUnary)
    (hV₁ : ComputableInPolyTime V₁ (encPair enc encBits) encBool)
    (hV₂ : ComputableInPolyTime V₂ (encPair enc encBits) encBool) :
    ComputableInPolyTime (orVerifier k V₁ V₂) (encPair enc encBits) encBool := by
  unfold orVerifier
  fun_prop

/-! ### Choosing by the first bit -/

/-- Run `V₀` on the remaining bits when the first bit is `false`, and `V₁` when it is `true`. -/
def selectVerifier (V₀ V₁ : α × List Bool → Bool) (x : α × List Bool) : Bool :=
  if x.2.headD false then V₁ (x.1, x.2.tail) else V₀ (x.1, x.2.tail)

/-- **Choices add**: on strings of length `n + 1`, `selectVerifier V₀ V₁` accepts the sum of the
numbers of strings of length `n` that `V₀` and `V₁` accept. -/
theorem acceptCount_selectVerifier (V₀ V₁ : α × List Bool → Bool) (a : α) (n : ℕ) :
    acceptCount (selectVerifier V₀ V₁) a (n + 1) = acceptCount V₀ a n + acceptCount V₁ a n := by
  rw [acceptCount, BitString.card_filter_ofFn_succ _ fun l => selectVerifier V₀ V₁ (a, l) = true,
    Nat.add_comm]
  simp only [selectVerifier, List.headD_cons, List.tail_cons, ite_true, Bool.false_eq_true,
    ite_false]
  rfl

/-- Selection by the first bit preserves plain polynomial-time verification. -/
@[fun_prop]
theorem computableInPolyTime_selectVerifier {enc : α ↪ List Bool}
    {V₀ V₁ : α × List Bool → Bool}
    (hV₀ : ComputableInPolyTime V₀ (encPair enc encBits) encBool)
    (hV₁ : ComputableInPolyTime V₁ (encPair enc encBits) encBool) :
    ComputableInPolyTime (selectVerifier V₀ V₁) (encPair enc encBits) encBool := by
  unfold selectVerifier
  fun_prop

/-! ### Sums of two counts -/

/-- Let the first bit choose between `V₁` on `k₁ a` bits and `V₂` on `k₂ a` bits, padding the
chosen verifier's strings to `k₁ a + k₂ a` bits with `false`s. -/
def sumVerifier (k₁ k₂ : α → ℕ) (V₁ V₂ : α × List Bool → Bool) : α × List Bool → Bool :=
  selectVerifier (padVerifier k₁ V₁) (padVerifier k₂ V₂)

/-- **Counts add**: on strings of length `k₁ a + k₂ a + 1`, `sumVerifier k₁ k₂ V₁ V₂` accepts the
sum of the numbers of strings that `V₁` accepts of length `k₁ a` and `V₂` of length `k₂ a`. -/
theorem acceptCount_sumVerifier (k₁ k₂ : α → ℕ) (V₁ V₂ : α × List Bool → Bool) (a : α) :
    acceptCount (sumVerifier k₁ k₂ V₁ V₂) a (k₁ a + k₂ a + 1) =
      acceptCount V₁ a (k₁ a) + acceptCount V₂ a (k₂ a) := by
  rw [sumVerifier, acceptCount_selectVerifier,
    acceptCount_padVerifier_of_le k₁ V₁ (Nat.le_add_right _ _),
    acceptCount_padVerifier_of_le k₂ V₂ (Nat.le_add_left _ _)]

/-- The sum of two plain polynomial-time verifiers is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_sumVerifier {enc : α ↪ List Bool} {k₁ k₂ : α → ℕ}
    {V₁ V₂ : α × List Bool → Bool} (hk₁ : ComputableInPolyTime k₁ enc encUnary)
    (hk₂ : ComputableInPolyTime k₂ enc encUnary)
    (hV₁ : ComputableInPolyTime V₁ (encPair enc encBits) encBool)
    (hV₂ : ComputableInPolyTime V₂ (encPair enc encBits) encBool) :
    ComputableInPolyTime (sumVerifier k₁ k₂ V₁ V₂) (encPair enc encBits) encBool := by
  unfold sumVerifier
  fun_prop

end Cslib.Complexity
