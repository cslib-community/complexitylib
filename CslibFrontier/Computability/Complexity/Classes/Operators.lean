/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Classes.SharpP

/-!
# The `BP` and parity operators

A class operator turns a class `C` of problems about pairs `(a, w)` of an instance and a string
into a class of problems about instances, by quantifying over the strings `w` whose length is a
polynomial `p` of the length of the encoded instance [Schöning][Schoening1989],
[Toda][Toda1991]:

* `⊕·C` (`Cslib.Complexity.ParityOp`): `a ∈ L` exactly when an odd number of the strings `w` of
  length `p (enc a).length` have `(a, w) ∈ L'`, for some `L' ∈ C` and polynomial `p`.
* `BP·C` (`Cslib.Complexity.BPOp`): for some `L' ∈ C` and polynomial `p`, the pairs `(a, r)` in
  `L'`, with `r` ranging over the strings of length `p (enc a).length`, decide `L` with bounded
  error (`Cslib.Complexity.DecidesWithBoundedError`): at least two thirds of the random strings
  `r` give the right answer.

The problems of `C` are about pairs encoded by `encPair enc encBits`, so the polynomials of `C`
are polynomials of the length of the encoded pair, while `p` is a polynomial of the length of the
encoded instance. Every string counted by an operator has length `p (enc a).length`; problems of
`C` may say anything about other pairs.

`BPP` is `BP·P` (`Cslib.Complexity.BPOp_P`), and `⊕P` is defined as `⊕·P`
(`Cslib.Complexity.ParityP`). Toda's theorem places the polynomial hierarchy in `BP·⊕P`.

## Main definitions

* `Cslib.Complexity.ParityOp`: the parity operator `⊕·`.
* `Cslib.Complexity.BPOp`: the bounded-error operator `BP·`.

## Main results

* `Cslib.Complexity.ParityOp_mono`, `Cslib.Complexity.BPOp_mono`: the operators are monotone.
* `Cslib.Complexity.compl_mem_BPOp`: `BP·C` is closed under complement when `C` is.
* `Cslib.Complexity.BPOp_P`: `BP·P = BPP`.

## References

* [U. Schöning, *Probabilistic complexity classes and lowness*][Schoening1989]
* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

open Classical in
/-- **The parity operator `⊕·C`**: the problems `L` such that, for some `L' ∈ C` and polynomial
`p`, `a ∈ L` exactly when an odd number of the strings `w` of length `p (enc a).length` have
`(a, w) ∈ L'`. The problems of `C` are about pairs of an instance and a string
[Toda][Toda1991]. -/
def ParityOp (enc : α ↪ List Bool) (C : Set (Set (α × List Bool))) : Set (Set α) :=
  {L | ∃ (p : Polynomial ℕ), ∃ L' ∈ C,
    ∀ a, a ∈ L ↔ Odd (acceptCount (fun x => decide (x ∈ L')) a (p.eval (enc a).length))}

open Classical in
/-- **The bounded-error operator `BP·C`**: the problems `L` such that, for some `L' ∈ C` and
polynomial `p`, membership in `L'` decides `L` with bounded error using random strings of length
`p (enc a).length`: for every instance `a`, at least two thirds of the random strings `r` have
`(a, r) ∈ L'` exactly when `a ∈ L`. The problems of `C` are about pairs of an instance and a
string [Schöning][Schoening1989], [Toda][Toda1991]. -/
def BPOp (enc : α ↪ List Bool) (C : Set (Set (α × List Bool))) : Set (Set α) :=
  {L | ∃ (p : Polynomial ℕ), ∃ L' ∈ C, DecidesWithBoundedError enc p (fun x => decide (x ∈ L')) L}

variable {enc : α ↪ List Bool} {C D : Set (Set (α × List Bool))} {L : Set α}

open Classical in
theorem mem_ParityOp : L ∈ ParityOp enc C ↔ ∃ (p : Polynomial ℕ), ∃ L' ∈ C,
    ∀ a, a ∈ L ↔ Odd (acceptCount (fun x => decide (x ∈ L')) a (p.eval (enc a).length)) :=
  Iff.rfl

open Classical in
theorem mem_BPOp : L ∈ BPOp enc C ↔ ∃ (p : Polynomial ℕ), ∃ L' ∈ C,
    DecidesWithBoundedError enc p (fun x => decide (x ∈ L')) L :=
  Iff.rfl

/-- The parity operator is monotone. -/
theorem ParityOp_mono (h : C ⊆ D) : ParityOp enc C ⊆ ParityOp enc D :=
  fun _ ⟨p, L', hL', hL⟩ => ⟨p, L', h hL', hL⟩

/-- The bounded-error operator is monotone. -/
theorem BPOp_mono (h : C ⊆ D) : BPOp enc C ⊆ BPOp enc D :=
  fun _ ⟨p, L', hL', hL⟩ => ⟨p, L', h hL', hL⟩

/-- **`BP·C` is closed under complement when `C` is**: the complement of the deciding problem
decides the complement with bounded error. -/
theorem compl_mem_BPOp (hC : ∀ L' ∈ C, L'ᶜ ∈ C) (hL : L ∈ BPOp enc C) : Lᶜ ∈ BPOp enc C := by
  classical
  obtain ⟨p, L', hL', h⟩ := hL
  refine ⟨p, L'ᶜ, hC L' hL', ?_⟩
  convert h.compl using 1
  funext x
  simp

/-- **`BP·P = BPP`**: deciding with bounded error by a polynomial-time verifier is deciding with
bounded error by membership in a problem in `P`. -/
theorem BPOp_P : BPOp enc (P (encPair enc encBits)) = BPP enc := by
  classical
  ext L
  constructor
  · rintro ⟨p, L', ⟨f, hf, hL'⟩, h⟩
    refine ⟨p, f, hf, ?_⟩
    convert h using 1
    funext x
    simp [hL' x]
  · rintro ⟨p, V, hV, h⟩
    refine ⟨p, {x | V x = true}, ⟨V, hV, fun _ => Iff.rfl⟩, ?_⟩
    convert h using 1
    funext x
    simp

end Cslib.Complexity
