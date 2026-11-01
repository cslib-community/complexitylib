/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.BranchingProgram.MonoidProgram
public import Cslib.Computability.Languages.Slice
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Data.Set.Image

/-!
# Languages of polynomial-length programs over a monoid

A program over a monoid `M` *decides* a Boolean-valued function `f` of its input with an accepting
set `S` of elements of `M` when `f` is true exactly on the inputs where the value of the program
lies in `S` (`MonoidProgram.Decides`) [BarringtonTherien1988]. `PolyLength α M` is the class of
languages over the alphabet `α` decided, at every word length `n`, by programs over `M` of
polynomially bounded length reading the words of length `n` as inputs `Fin n → α`. Over the
alphabet `Bool`, the programs over `Equiv.Perm (Fin w)` are the permutation branching programs of
width `w`, and those over `Function.End (Fin w)` the branching programs of width `w`
[Barrington1989]. Like the circuit classes, `PolyLength α M` is nonuniform.

A program that `σ`-computes `f`, with `σ ≠ 1`, decides `f` with the accepting set `{σ}`
(`MonoidProgram.Computes.decides`), and an injective homomorphism of monoids embeds the classes
(`PolyLength.subset_of_injective`).

## Main definitions

* `Cslib.BranchingPrograms.MonoidProgram.Decides`: deciding a function with an accepting set.
* `Cslib.BranchingPrograms.PolyLength`: the languages of polynomial-length programs over a monoid.

## Main results

* `Cslib.BranchingPrograms.MonoidProgram.Computes.decides`: `σ`-computing is deciding.
* `Cslib.BranchingPrograms.PolyLength.subset_of_injective`: an injective homomorphism of monoids
  embeds the classes.

## Implementation notes

The languages of [BarringtonTherien1988] are over a finite alphabet, and their monoids finite.
Neither assumption is needed to state the class, so `PolyLength α M` takes any alphabet `α` and
monoid `M`; the theorems that need finiteness assume it.

## References

* [D. A. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
* [D. A. Mix Barrington, D. Thérien, *Finite monoids and the fine structure of
  NC¹*][BarringtonTherien1988]
-/

@[expose] public section

namespace Cslib.BranchingPrograms

variable {ι α M N : Type*} [Monoid M] [Monoid N]

/-- A program decides a Boolean-valued function `f` of its input with the accepting set `S` when
`f` is true exactly on the inputs where the value of the program lies in `S`. -/
def MonoidProgram.Decides (P : MonoidProgram ι α M) (S : Set M) (f : (ι → α) → Bool) : Prop :=
  ∀ x, f x = true ↔ P.eval x ∈ S

section Decides

variable {P : MonoidProgram ι α M} {S : Set M} {f : (ι → α) → Bool}

/-- A program that `σ`-computes `f`, with `σ ≠ 1`, decides `f` with the accepting set `{σ}`. -/
theorem MonoidProgram.Computes.decides {σ : M} (h : P.Computes σ f) (hσ : σ ≠ 1) :
    P.Decides {σ} f := fun x => by
  rw [h x, Set.mem_singleton_iff]
  cases f x
  · simpa using hσ.symm
  · simp

/-- Pushing a program along an injective homomorphism keeps what it decides, with the image of the
accepting set. -/
theorem MonoidProgram.Decides.map (h : P.Decides S f) {φ : M →* N} (hφ : Function.Injective φ) :
    (P.map φ).Decides (φ '' S) f := fun x => by
  rw [h x, eval_map, hφ.mem_set_image]

/-- On inputs with no positions, the empty program decides every function, accepting everything
when the function is true and nothing when it is false. -/
theorem MonoidProgram.decides_one [IsEmpty ι] (f : (ι → α) → Bool) :
    (1 : MonoidProgram ι α M).Decides {_m | f isEmptyElim = true} f := fun x => by
  rw [Subsingleton.elim x isEmptyElim]
  rfl

end Decides

/-- The languages over `α` decided, at every word length `n`, by a program over `M` of length at
most `s n`, with an accepting set, for a polynomially bounded `s`.

The class is meant for finite monoids, as in [BarringtonTherien1988]. Over an infinite monoid it
can contain every language: in the free monoid on `ℕ × α`, the program of length `n` that selects
the generator `(i, x i)` at each position `i` sends different inputs to different elements. -/
def PolyLength (α M : Type*) [Monoid M] : Set (Language α) :=
  {L | ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n,
    ∃ (P : MonoidProgram (Fin n) α M) (S : Set M), P.Decides S (L.slice n) ∧ P.toList.length ≤ s n}

/-- **An injective homomorphism of monoids embeds the classes**: push the programs along it. -/
theorem PolyLength.subset_of_injective {φ : M →* N} (hφ : Function.Injective φ) :
    PolyLength α M ⊆ PolyLength α N := by
  rintro L ⟨s, hs, hP⟩
  refine ⟨s, hs, fun n => ?_⟩
  obtain ⟨P, S, hPS, hlen⟩ := hP n
  exact ⟨P.map φ, φ '' S, hPS.map hφ, (MonoidProgram.length_map φ P).trans_le hlen⟩

end Cslib.BranchingPrograms
