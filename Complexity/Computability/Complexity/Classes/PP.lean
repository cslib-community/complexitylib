/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.SharpP

/-!
# The class PP

`PP` is defined like `BPP` (`Cslib.Complexity.BPP`), through deterministic polynomial-time machines
that read a random string, but with unbounded error [Gill][Gill1977]: `A ∈ PP enc` when there are
a polynomial `p` and a function `V : α × List Bool → Bool`, computable in polynomial time on inputs
`encPair enc encBits (a, r) = frame (enc a) ++ r`, such that `a ∈ A` exactly when more than half of
the random strings `r` of length `p (enc a).length` give `V (a, r) = true`. The probability is
written as a count (`Cslib.Complexity.acceptCount`), as in `BPP` and `#P`, so `PP` consists of the
problems decided by comparing a function in `#P` with half the number of certificates.

A bounded-error decider accepts the members of its problem with probability at least `2 / 3` and
the others with probability at most `1 / 3`, so it decides by majority: `BPP ⊆ PP` with the same
verifier (`BPP_subset_PP`).

Gill requires a strict majority on members, as here; the variant with a non-strict majority
defines the same class (`Cslib.Complexity.mem_PP_iff_decidesByNonstrictMajority`). The
characterisation by probabilistic machines is not proved here.

## Main definitions

* `Cslib.Complexity.DecidesByMajority`: the majority condition.
* `Cslib.Complexity.PP`.

## Main results

* `Cslib.Complexity.DecidesWithBoundedError.decidesByMajority`: bounded error gives a majority.
* `Cslib.Complexity.BPP_subset_PP`.

## References

* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- `V` decides `A` by majority, using random strings whose length is `p` evaluated at the length
of the encoded instance: `a ∈ A` exactly when more than half of the random strings `r` give
`V (a, r) = true`. -/
def DecidesByMajority (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (A : Set α) : Prop :=
  ∀ a, a ∈ A ↔ 2 ^ p.eval (enc a).length < 2 * acceptCount V a (p.eval (enc a).length)

/-- The problems decided by majority by polynomial-time machines reading polynomially long random
strings, with respect to the encoding `enc` of instances [Gill][Gill1977]. -/
def PP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ DecidesByMajority enc p V A}

variable {enc : α ↪ List Bool}

theorem mem_PP {A : Set α} : A ∈ PP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ DecidesByMajority enc p V A :=
  Iff.rfl

/-- Bounded error gives a majority: a decider that is right on at least two thirds of the random
strings accepts the members of its problem, and only them, on more than half. -/
theorem DecidesWithBoundedError.decidesByMajority {p : Polynomial ℕ} {V : α × List Bool → Bool}
    {A : Set α} (h : DecidesWithBoundedError enc p V A) : DecidesByMajority enc p V A := by
  intro a
  have hsum := acceptCount_add_card_filter_eq_false (V := V) (a := a) (n := p.eval (enc a).length)
  have hpos := Nat.one_le_two_pow (n := p.eval (enc a).length)
  constructor
  · intro ha
    have := (h a).1 ha
    rw [← acceptCount] at this
    omega
  · intro hlt
    by_contra ha
    have := (h a).2 ha
    omega

/-- **`BPP ⊆ PP`.** -/
theorem BPP_subset_PP : BPP enc ⊆ PP enc :=
  fun _ ⟨p, V, hV, h⟩ => ⟨p, V, hV, h.decidesByMajority⟩

end Cslib.Complexity
