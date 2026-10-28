/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Classes.Promise.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fintype.Pi

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# The classes BPP and promise-BPP

`BPP` is defined through deterministic polynomial-time machines that read a random string
[Arora and Barak, Section 7.1][AroraBarak09]: `A ∈ BPP enc` when there are a polynomial `p`
and a function `V : α × List Bool → Bool`, computable in polynomial time on inputs
`encPair enc encBits (a, r) = frame (enc a) ++ r`, such that for every instance `a`, at least two
thirds of the random strings `r` of length `p (enc a).length` give the right answer:
`V (a, r) = true` exactly when `a ∈ A`.

The bounded-error condition is stated once, for promise problems
(`Cslib.Complexity.PromiseProblem.SolvesWithBoundedError`): the right answer is required only on
the yes-instances and the no-instances [Goldreich, Definition 1.2][Goldreich2006]. A decision
problem `A` is the promise problem `PromiseProblem.ofSet A`, so `DecidesWithBoundedError enc p V A`
is `(ofSet A).SolvesWithBoundedError enc p V`, and `A ∈ BPP enc` is, by definition,
`ofSet A ∈ PromiseBPP enc` (`Cslib.Complexity.ofSet_mem_PromiseBPP`). Results proved for
`PromiseBPP` specialize to `BPP` in this way.

The probability is written as a count over the random strings, which are functions
`Fin (p (enc a).length) → Bool`. The characterisation by probabilistic machines
(`Cslib.Complexity.mem_BPP_iff_exists_mem_BPTIME`) is proved in
`Complexity.Computability.Complexity.Classes.Time`.

## Main definitions

* `Cslib.Complexity.BoundedErrorAt`: the per-instance bounded-error condition for a specified
  Boolean answer.
* `Cslib.Complexity.PromiseProblem.SolvesWithBoundedError`: the bounded-error condition on a
  promise problem.
* `Cslib.Complexity.DecidesWithBoundedError`: its specialization to a decision problem.
* `Cslib.Complexity.PromiseBPP`, `Cslib.Complexity.BPP`.

## Main results

* `Cslib.Complexity.BoundedErrorAt.congr`, `Cslib.Complexity.BoundedErrorAt.not`: extensionality
  and negation for per-instance bounded error.
* `Cslib.Complexity.PromiseProblem.SolvesWithBoundedError.compl`,
  `Cslib.Complexity.DecidesWithBoundedError.compl`: negating the verifier solves the complement
  with bounded error.
* `Cslib.Complexity.compl_mem_PromiseBPP`, `Cslib.Complexity.compl_mem_BPP`,
  `Cslib.Complexity.BPP_eq_preimage_compl_BPP`: closure under complement.
* `Cslib.Complexity.mem_PromiseBPP_iff`: unfolding `PromiseBPP` to a polynomial-time verifier.
* `Cslib.Complexity.ofSet_mem_PromiseBPP`: `PromiseBPP` agrees with `BPP` on decision problems.
* `Cslib.Complexity.P_subset_BPP`: a decider is a bounded-error verifier ignoring its random string.

## References

* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [O. Goldreich, *On promise problems: a survey*][Goldreich2006]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- `V` gives the answer `b` with bounded error on the instance `a`, using random strings whose
length is `p` evaluated at the length of the encoded instance: at least two thirds of the random
strings `r` of length `p (enc a).length` give `V (a, r) = b`. -/
abbrev BoundedErrorAt (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (a : α) (b : Bool) : Prop :=
  2 * 2 ^ p.eval (enc a).length ≤
    3 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      V (a, List.ofFn r) = b).card

/-- Bounded error at an instance depends only on the verifier's values on strings of length
`p(|a|)`. -/
theorem BoundedErrorAt.congr {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V W : α × List Bool → Bool} {a : α} {b : Bool} (h : BoundedErrorAt enc p V a b)
    (hVW : ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn r) = W (a, List.ofFn r)) :
    BoundedErrorAt enc p W a b := by
  have hcard : (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      V (a, List.ofFn r) = b).card =
    (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      W (a, List.ofFn r) = b).card :=
    congrArg Finset.card (Finset.filter_congr fun r _ => by rw [hVW r])
  rwa [BoundedErrorAt, ← hcard]

/-- Negating the verifier negates the bounded-error answer at `a`. -/
theorem BoundedErrorAt.not {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {a : α} {b : Bool} (h : BoundedErrorAt enc p V a b) :
    BoundedErrorAt enc p (fun x => !V x) a (!b) := by
  have hcard : (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      (!V (a, List.ofFn r)) = !b).card =
    (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      V (a, List.ofFn r) = b).card :=
    congrArg Finset.card
      (Finset.filter_congr fun _ _ => by rw [Bool.not_eq_eq_eq_not, Bool.not_not])
  rwa [BoundedErrorAt, hcard]

namespace PromiseProblem

/-- `V` solves the promise problem `Q` with bounded error, using random strings whose length is `p`
evaluated at the length of the encoded instance: for every yes-instance at least two thirds of the
random strings are accepted, and for every no-instance at least two thirds are rejected
[Goldreich, Definition 1.2][Goldreich2006]. Nothing is required on
instances outside the promise. -/
def SolvesWithBoundedError (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (Q : PromiseProblem α) : Prop :=
  ∀ a, (a ∈ Q.yes → BoundedErrorAt enc p V a true) ∧
    (a ∈ Q.no → BoundedErrorAt enc p V a false)

/-- Negating the verifier solves the complement promise problem with bounded error. -/
theorem SolvesWithBoundedError.compl {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {Q : PromiseProblem α} (h : Q.SolvesWithBoundedError enc p V) :
    Qᶜ.SolvesWithBoundedError enc p (fun x => !V x) := fun a =>
  ⟨fun ha => ((h a).2 ha).not, fun ha => ((h a).1 ha).not⟩

end PromiseProblem

open PromiseProblem

/-- `V` decides `A` with bounded error, using random strings whose length is `p` evaluated at the
length of the encoded instance: it solves the promise problem `ofSet A` with bounded error. For
every instance `a`, at least two thirds of the random strings `r` give the right answer,
`V (a, r) = true` for members of `A` and `V (a, r) = false` for the others. -/
def DecidesWithBoundedError (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (A : Set α) : Prop :=
  (ofSet A).SolvesWithBoundedError enc p V

/-- Negating the verifier decides the complement with bounded error. -/
theorem DecidesWithBoundedError.compl {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} (h : DecidesWithBoundedError enc p V A) :
    DecidesWithBoundedError enc p (fun x => !V x) Aᶜ := by
  rw [DecidesWithBoundedError, ofSet_compl]
  exact SolvesWithBoundedError.compl h

/-- The promise problems solved with bounded error by polynomial-time algorithms reading
polynomially long random strings, with respect to the encoding `enc` of instances
[Goldreich, Definition 1.2][Goldreich2006]. -/
def PromiseBPP (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ Q.SolvesWithBoundedError enc p V}

/-- The problems decided with bounded error by polynomial-time machines reading polynomially long
random strings, with respect to the encoding `enc` of instances [Gill][Gill1977],
[Arora and Barak, Section 7.1][AroraBarak09]. -/
def BPP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ DecidesWithBoundedError enc p V A}

variable {enc : α ↪ List Bool} {Q : PromiseProblem α} {A : Set α}

/-- Membership in `PromiseBPP` unfolded to a polynomial coin bound and a polynomial-time
bounded-error solver. -/
theorem mem_PromiseBPP_iff : Q ∈ PromiseBPP enc ↔
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧ Q.SolvesWithBoundedError enc p V :=
  Iff.rfl

theorem mem_BPP : A ∈ BPP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        DecidesWithBoundedError enc p V A :=
  Iff.rfl

/-- A decision problem, as a promise problem, is in `PromiseBPP` exactly when it is in `BPP`; this
holds by definition. -/
@[simp]
theorem ofSet_mem_PromiseBPP : ofSet A ∈ PromiseBPP enc ↔ A ∈ BPP enc :=
  Iff.rfl

/-- `PromiseBPP` is closed under complement. -/
theorem compl_mem_PromiseBPP (hQ : Q ∈ PromiseBPP enc) : Qᶜ ∈ PromiseBPP enc :=
  let ⟨p, V, hV, h⟩ := hQ
  ⟨p, fun x => !V x, by fun_prop, h.compl⟩

/-- `BPP` is closed under complement. -/
theorem compl_mem_BPP (hA : A ∈ BPP enc) : Aᶜ ∈ BPP enc := by
  rw [← ofSet_mem_PromiseBPP, ofSet_compl]
  exact compl_mem_PromiseBPP hA

/-- `BPP` equals its preimage under complement. -/
theorem BPP_eq_preimage_compl_BPP (enc : α ↪ List Bool) : BPP enc = compl ⁻¹' BPP enc := by
  ext A
  refine ⟨compl_mem_BPP, fun hA => ?_⟩
  simpa using compl_mem_BPP hA

/-- **`P ⊆ BPP`**: a decider is a bounded-error verifier ignoring its random string, of length
`0`. -/
theorem P_subset_BPP : P enc ⊆ BPP enc := by
  rintro A ⟨f, hf, hA⟩
  refine ⟨0, fun x => f x.1, hf.comp (.fst enc encBits),
    fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · simp [BoundedErrorAt, (hA a).mp ha]
  · have : f a = false := by simpa [hA a] using ha
    simp [BoundedErrorAt, this]

end Cslib.Complexity
