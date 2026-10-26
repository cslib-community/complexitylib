/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Complexity.Classes.Toda.Counting

/-! Direct clients of the ordinary plain rules. Disabling transitions here ensures a missing
plain operation cannot be hidden by the legacy tidy-to-plain transition. -/

open Turing.MultiTapeTM

namespace ComplexityTests.PlainAutomationSupport

example : ComputableInPolyTime (fun values : List Bool => values.headD false)
    encBits encBool := by
  exact ComputableInPolyTime.headD false

-- Membership and captured filtering work as written, rather than through a rewritten scan.
example : ComputableInPolyTime
    (fun p : List ℕ × List ℕ => p.1.filter fun x => decide (x ∉ p.2))
    (encPair (encList encNat) (encList encNat)) (encList encNat) := by
  simp only [decide_not]
  fun_prop (config := { maxTransitionDepth := 0 })

example : ComputableInPolyTime
    (fun G : List ℕ × List (ℕ × ℕ) => G.1.flatMap fun u =>
      (G.1.filter fun v => decide (u ≠ v ∧ (u, v) ∉ G.2 ∧ (v, u) ∉ G.2)).map fun v => (u, v))
    (encPair (encList encNat) (encList (encPair encNat encNat)))
    (encList (encPair encNat encNat)) := by
  simp only [Bool.decide_and, decide_not]
  fun_prop (config := { maxTransitionDepth := 0 })

-- The exponent is unary; the binary output may have length linear in that unary input.
example {α : Type} {enc : α ↪ List Bool} {k : α → ℕ}
    (hk : ComputableInPolyTime k enc encNat) (q : Polynomial ℕ) :
    ComputableInPolyTime (fun a => 3 * (k a * 2 ^ q.eval (enc a).length)) enc encNat := by
  fun_prop (config := { maxTransitionDepth := 0 })

-- Raw bits and framed Boolean lists retain distinct input certificates.
example {α : Type} {enc : α ↪ List Bool} (values : α → List Bool) (test : α → Bool → Bool)
    (hvalues : ComputableInPolyTime values enc encBits)
    (htest : ComputableInPolyTime (fun p : α × Bool => test p.1 p.2)
      (encPair enc encBool) encBool) :
    ComputableInPolyTime (fun a => (values a).any (test a)) enc encBool := by
  fail_if_success (clear hvalues; fun_prop (config := { maxTransitionDepth := 0 }))
  fail_if_success (clear htest; fun_prop (config := { maxTransitionDepth := 0 }))
  fun_prop (config := { maxTransitionDepth := 0 })

example {α : Type} {enc : α ↪ List Bool} (values : α → List Bool) (test : α → Bool → Bool)
    (hvalues : ComputableInPolyTime values enc (encList encBool))
    (htest : ComputableInPolyTime (fun p : α × Bool => test p.1 p.2)
      (encPair enc encBool) encBool) :
    ComputableInPolyTime (fun a => (values a).any (test a)) enc encBool := by
  exact ComputableInPolyTime.anyWithInput hvalues htest

-- The domain endpoint keeps its complete deterministic callback and unary parameter contracts.
example {α : Type} {enc : α ↪ List Bool} {V : (α × List Bool) × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair (encPair enc encBits) encBits) encBool)
    (R Z : Polynomial ℕ) :
    ComputableInPolyTime (fun x : α × List Bool =>
      Cslib.Complexity.Toda.sharpTest (fun r z => V ((x.1, r), z)) (R.eval (enc x.1).length)
        (Z.eval (enc x.1).length) x.2) (encPair enc encBits) encBool := by
  apply Cslib.Complexity.Toda.computableInPolyTime_sharpTest hV
  · exact ComputableInPolyTime.fst enc encBits
  · exact (ComputableInPolyTime.unary_eval R).comp
      ((ComputableInPolyTime.encoding_length enc).comp (ComputableInPolyTime.fst enc encBits))
  · exact (ComputableInPolyTime.unary_eval Z).comp
      ((ComputableInPolyTime.encoding_length enc).comp (ComputableInPolyTime.fst enc encBits))
  · exact ComputableInPolyTime.snd enc encBits


-- These are the actual framing and padding shapes from SavedPrediction and OneWayNormalization.
example {α : Type} (encoding : α ↪ List Bool) : ComputableInPolyTime
    (fun pair : α × List Bool => pair.2 ++ encPair encoding encBits (pair.1, pair.2.reverse))
    (encPair encoding encBits) encBits := by
  fun_prop (config := { maxTransitionDepth := 0 })

example : ComputableInPolyTime
    (fun word : List Bool => Cslib.BitString.padWord (word.length - 3) word) encBits encBits := by
  fun_prop (config := { maxTransitionDepth := 0 })

example {α : Type} {input : α ↪ List Bool} (bound : α → ℕ) (word : α → List Bool)
    (hbound : ComputableInPolyTime bound input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => Cslib.BitString.padWord (bound a) (word a)) input encBits := by
  fail_if_success (clear hbound; fun_prop (config := { maxTransitionDepth := 0 }))
  fail_if_success (clear hword; fun_prop (config := { maxTransitionDepth := 0 }))
  fun_prop (config := { maxTransitionDepth := 0 })


-- These are the actual Seed polynomial and Stretch slicing obligations from the library gate.
example (c d : ℕ) : ComputableInPolyTime (fun n : ℕ => c * (n + 1) ^ d)
    encUnary encUnary := by
  fun_prop (config := { maxTransitionDepth := 0 })

example (target : ℕ → ℕ) (htarget : ComputableInPolyTime target encUnary encUnary) :
    ComputableInPolyTime (fun p : ℕ × List Bool => p.2.take (target p.1))
      (encPair encUnary encBits) encBits := by
  fail_if_success (clear htarget; fun_prop (config := { maxTransitionDepth := 0 }))
  fun_prop (config := { maxTransitionDepth := 0 })

-- A fixed power certificate must not become a uniform unary runtime-exponent certificate.
example : True := by
  fail_if_success
    have : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 ^ p.2)
        (encPair encUnary encUnary) encUnary := by
      fun_prop (config := { maxTransitionDepth := 0 })
  trivial


private def repeatWord (p : ℕ × List Bool) : List Bool :=
  (fun state => p.2 ++ state)^[p.1] []

example : repeatWord (0, [true]) = [] := rfl
example : repeatWord (2, [true, false]) = [true, false, true, false] := rfl

-- A runtime word is captured by every step; the loop count remains unary.
example : ComputableInPolyTime repeatWord (encPair encUnary encBits) encBits := by
  unfold repeatWord
  apply ComputableInPolyTime.iterateWithInput_of_bounded_growth
    (growth := fun p => p.2.length)
  case hcount => exact ComputableInPolyTime.fst encUnary encBits
  case hinit => exact ComputableInPolyTime.const []
  case hstep => fun_prop (config := { maxTransitionDepth := 0 })
  case hbound =>
    constructor
    · exact (ComputableInPolyTime.snd encUnary encBits).polyBounded_length
    · intro p state
      simp only [encBits_apply, List.length_append]
      omega

private def repeatPerElement {α : Type} (p : List α × List Bool) : List Bool :=
  p.1.foldl (fun state _ => p.2 ++ state) []

example : repeatPerElement (([] : List ℕ), [true]) = [] := rfl
example : repeatPerElement ([3, 4], [true]) = [true, true] := rfl

-- Framed elements and raw accumulator bits have distinct encodings and full joint callbacks.
example {α : Type} (item : α ↪ List Bool) :
    ComputableInPolyTime (repeatPerElement (α := α))
      (encPair (encList item) encBits) encBits := by
  unfold repeatPerElement
  apply ComputableInPolyTime.foldlWithInput_of_bounded_growth
    (encA := item) (growth := fun p => p.2.length)
  case hinit => exact ComputableInPolyTime.const []
  case hcompute =>
    refine ⟨ComputableInPolyTime.fst (encList item) encBits, ?_, inferInstance, inferInstance⟩
    fun_prop (config := { maxTransitionDepth := 0 })
  case hbound =>
    constructor
    · exact (ComputableInPolyTime.snd (encList item) encBits).polyBounded_length
    · intro p state value _
      simp only [encBits_apply, List.length_append]
      omega

end ComplexityTests.PlainAutomationSupport
