/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.BitString.WordCount

/-!
# Combining verifiers

The counting classes `#P`, `PP`, `RP` and `BPP` are all defined through polynomial-time functions
`V : α × List Bool → Bool` that read an instance and a string of bits, and through the number
`Cslib.Complexity.acceptCount V a n` of strings of length `n` that `V` accepts together with `a`.
This file provides verifiers built from other verifiers, each with its polynomial-time rule
(registered with `fun_prop`) and the number of strings it accepts.

* `Cslib.Complexity.andVerifier k V₁ V₂` runs `V₁` on the first `k a` bits and `V₂` on the rest,
  and accepts when both accept. The number of strings it accepts is the product of the numbers
  that `V₁` and `V₂` accept (`Cslib.Complexity.acceptCount_andVerifier`). With `V₂` the verifier
  accepting only the string of `false`s (`Cslib.Complexity.allFalseVerifier`), it pads the strings
  of `V₁` without changing their number; with `V₂` accepting everything, it multiplies the count by
  a power of two.
* `Cslib.Complexity.orVerifier k V₁ V₂` accepts when either accepts; the rejected strings multiply
  (`Cslib.Complexity.acceptCount_orVerifier`).
* `Cslib.Complexity.selectVerifier V₀ V₁` lets the first bit choose between `V₀` and `V₁` on the
  remaining bits; the counts add (`Cslib.Complexity.acceptCount_selectVerifier`).

Running two verifiers on disjoint parts of the random string is the usual way to combine
independent random choices [Arora and Barak, Chapters 7 and 17][AroraBarak09].

## Main definitions

* `Cslib.Complexity.allFalseVerifier`, `Cslib.Complexity.andVerifier`,
  `Cslib.Complexity.orVerifier`, `Cslib.Complexity.selectVerifier`.

## Main results

* `Cslib.Complexity.acceptCount_andVerifier`, `Cslib.Complexity.acceptCount_orVerifier`,
  `Cslib.Complexity.acceptCount_selectVerifier`: counts of the combined verifiers.
* `Cslib.Complexity.computableInPolyTime_andVerifier`,
  `Cslib.Complexity.computableInPolyTime_orVerifier`,
  `Cslib.Complexity.computableInPolyTime_selectVerifier`: the combined verifiers are
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

/-- **Padding**: forcing the bits after the first `k a` to be `false` does not change the number
of accepted strings. -/
theorem acceptCount_andVerifier_allFalseVerifier (k : α → ℕ) (V : α × List Bool → Bool) (a : α)
    (n : ℕ) :
    acceptCount (andVerifier k V allFalseVerifier) a (k a + n) = acceptCount V a (k a) := by
  rw [acceptCount_andVerifier, acceptCount_allFalseVerifier, mul_one]

/-- Ignoring the bits after the first `k a` multiplies the number of accepted strings by a power
of two. -/
theorem acceptCount_andVerifier_true (k : α → ℕ) (V : α × List Bool → Bool) (a : α) (n : ℕ) :
    acceptCount (andVerifier k V fun _ => true) a (k a + n) = acceptCount V a (k a) * 2 ^ n := by
  rw [acceptCount_andVerifier, acceptCount_true]

/-- `andVerifier k V₁ V₂` is polynomial-time when `k` (in unary), `V₁` and `V₂` are. -/
@[fun_prop]
theorem computableTidilyInPolyTime_andVerifier {enc : α ↪ List Bool} {k : α → ℕ}
    {V₁ V₂ : α × List Bool → Bool} (hk : ComputableTidilyInPolyTime k enc encUnary)
    (hV₁ : ComputableTidilyInPolyTime V₁ (encPair enc encBits) encBool)
    (hV₂ : ComputableTidilyInPolyTime V₂ (encPair enc encBits) encBool) :
    ComputableTidilyInPolyTime (andVerifier k V₁ V₂) (encPair enc encBits) encBool := by
  unfold andVerifier
  fun_prop

/-- Independent conjunction of plain polynomial-time verifiers is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_andVerifier {enc : α ↪ List Bool} {k : α → ℕ}
    {V₁ V₂ : α × List Bool → Bool} (hk : ComputableInPolyTime k enc encUnary)
    (hV₁ : ComputableInPolyTime V₁ (encPair enc encBits) encBool)
    (hV₂ : ComputableInPolyTime V₂ (encPair enc encBits) encBool) :
    ComputableInPolyTime (andVerifier k V₁ V₂) (encPair enc encBits) encBool :=
  .of_tidy (computableTidilyInPolyTime_andVerifier hk.tidy hV₁.tidy hV₂.tidy)

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

/-- `orVerifier k V₁ V₂` is polynomial-time when `k` (in unary), `V₁` and `V₂` are. -/
@[fun_prop]
theorem computableTidilyInPolyTime_orVerifier {enc : α ↪ List Bool} {k : α → ℕ}
    {V₁ V₂ : α × List Bool → Bool} (hk : ComputableTidilyInPolyTime k enc encUnary)
    (hV₁ : ComputableTidilyInPolyTime V₁ (encPair enc encBits) encBool)
    (hV₂ : ComputableTidilyInPolyTime V₂ (encPair enc encBits) encBool) :
    ComputableTidilyInPolyTime (orVerifier k V₁ V₂) (encPair enc encBits) encBool := by
  unfold orVerifier
  fun_prop

/-- Independent disjunction of plain polynomial-time verifiers is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_orVerifier {enc : α ↪ List Bool} {k : α → ℕ}
    {V₁ V₂ : α × List Bool → Bool} (hk : ComputableInPolyTime k enc encUnary)
    (hV₁ : ComputableInPolyTime V₁ (encPair enc encBits) encBool)
    (hV₂ : ComputableInPolyTime V₂ (encPair enc encBits) encBool) :
    ComputableInPolyTime (orVerifier k V₁ V₂) (encPair enc encBits) encBool :=
  .of_tidy (computableTidilyInPolyTime_orVerifier hk.tidy hV₁.tidy hV₂.tidy)

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

/-- `selectVerifier V₀ V₁` is polynomial-time when `V₀` and `V₁` are. -/
@[fun_prop]
theorem computableTidilyInPolyTime_selectVerifier {enc : α ↪ List Bool}
    {V₀ V₁ : α × List Bool → Bool}
    (hV₀ : ComputableTidilyInPolyTime V₀ (encPair enc encBits) encBool)
    (hV₁ : ComputableTidilyInPolyTime V₁ (encPair enc encBits) encBool) :
    ComputableTidilyInPolyTime (selectVerifier V₀ V₁) (encPair enc encBits) encBool := by
  unfold selectVerifier
  fun_prop

/-- Selection by the first bit preserves plain polynomial-time verification. -/
@[fun_prop]
theorem computableInPolyTime_selectVerifier {enc : α ↪ List Bool}
    {V₀ V₁ : α × List Bool → Bool}
    (hV₀ : ComputableInPolyTime V₀ (encPair enc encBits) encBool)
    (hV₁ : ComputableInPolyTime V₁ (encPair enc encBits) encBool) :
    ComputableInPolyTime (selectVerifier V₀ V₁) (encPair enc encBits) encBool :=
  .of_tidy (computableTidilyInPolyTime_selectVerifier hV₀.tidy hV₁.tidy)

end Cslib.Complexity
