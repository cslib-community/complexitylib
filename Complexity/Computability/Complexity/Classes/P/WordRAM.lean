/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.WordRAM.Turing

/-!
# Polynomial-time word-RAM deciders place their problems in `P`

A problem decided by a fixed word-RAM program in polynomially many instructions is in `P`, through
the simulation of the word RAM by multi-tape Turing machines
(`Cslib.WordRAM.Program.ComputesInTime.turingComputableInPolyTime_of_width`). The instance is the
bit string `encIn a`; its word list must be computable from it in polynomial time, and the size
measure must be polynomially bounded in its length. The conventions are those of the simulation:
unit-cost instructions on `w`-bit words, the input placed as in `State.init`, and a word size
computed by the simulating machine.

## Main results

* `Cslib.WordRAM.Program.DecidesInTime.mem_P_of_width`: a decider at a polynomial-time width
  schedule.
* `Cslib.WordRAM.Program.DecidesInTime.mem_P`: a decider within `T (size a)` instructions at every
  word size above `logWidth k (size a)`.
* `Cslib.WordRAM.UniformPolynomialTime.mem_P`: uniform polynomial word-RAM time is in `P`.
-/

@[expose] public section

namespace Cslib.WordRAM

open Turing.MultiTapeTM

variable {B : Basis} {r : ℕ} {α : Type} {encIn : α ↪ List Bool}

/-- **A word-RAM decider at a polynomial-time width schedule places its problem in `P`.** The
width `width a` must be computable in unary in polynomial time and admitted, the input must fit
it, its word list must be computable in polynomial time, and the time bound at that width must be
polynomial in `|encIn a|`. -/
theorem Program.DecidesInTime.mem_P_of_width
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat))
    {p : Program B r} {encode : ℕ → α → List ℕ} {A : Set α} {time : α → ℕ → ℕ}
    {allowed : α → ℕ → Prop} (h : p.DecidesInTime encode A time allowed) {width : α → ℕ}
    (hwidth : Turing.MultiTapeTM.ComputableInPolyTime width encIn encUnary)
    (hallowed : ∀ a, allowed a (width a))
    (hfits : ∀ a, InputFits (width a) (encode (width a) a))
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime (fun a => encode (width a) a) encIn
      (encList encNat))
    (htime : PolyBounded (fun a => (encIn a).length) (fun a => time a (width a))) :
    A ∈ Cslib.Complexity.P encIn := by
  classical
  have hf := h.computesInTime.turingComputableInPolyTime_of_width hop hwidth hallowed hfits
    hencode htime
  refine ⟨fun a => decide ((if a ∈ A then 1 else 0) = 1), hf.decide_eq' (.const 1), fun a => ?_⟩
  by_cases ha : a ∈ A <;> simp [ha]

/-- **A polynomial-time word-RAM decider places its problem in `P`.** The program decides `A`
within `T (size a)` instructions at every fitting word size above `logWidth k (size a)`, the word
list `encode a` is computable in polynomial time from `encIn a`, and `size a` is polynomially
bounded in `|encIn a|`. -/
theorem Program.DecidesInTime.mem_P
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat))
    {p : Program B r} {encode : α → List ℕ} {A : Set α} {size : α → ℕ} {T : ℕ → ℕ} {k : ℕ}
    (hT : PolynomiallyBounded T) (hsize : PolyBounded (fun a => (encIn a).length) size)
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime encode encIn (encList encNat))
    (h : p.DecidesInTime (fun _ => encode) A (fun a _ => T (size a))
      (fun a w => logWidth k (size a) ≤ w)) :
    A ∈ Cslib.Complexity.P encIn := by
  classical
  have hf := h.computesInTime.turingComputableInPolyTime hop hT hsize hencode
  refine ⟨fun a => decide ((if a ∈ A then 1 else 0) = 1), hf.decide_eq' (.const 1), fun a => ?_⟩
  by_cases ha : a ∈ A <;> simp [ha]

/-- **Uniform polynomial word-RAM time is in `P`**, for a width-independent word encoding
computable in polynomial time and a size measure polynomially bounded in the encoded input
length. -/
theorem UniformPolynomialTime.mem_P
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat))
    {encode : α → List ℕ} {A : Set α} {size : α → ℕ}
    (h : UniformPolynomialTime B A (fun _ => encode) size)
    (hsize : PolyBounded (fun a => (encIn a).length) size)
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime encode encIn (encList encNat)) :
    A ∈ Cslib.Complexity.P encIn := by
  obtain ⟨T, hT, k, -, r, p, hp⟩ := h
  exact Program.DecidesInTime.mem_P hop hT hsize hencode hp

end Cslib.WordRAM
