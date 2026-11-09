/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.ModelTheory.Basic
public import Mathlib.ModelTheory.Semantics
import Mathlib.Basic.Finite.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

/-!
# Atomic facts and finite models for relational first-order languages

For a relational first-order language `L`, a structure on `Fin n` is determined by the truth
values of its atomic facts `R(a₁, …, aₗ)` (`Atom L n`).

This module defines the type of atomic facts `Atom L n`, the structure `Model x` induced by a
truth assignment `x : Atom L n → Bool`, the extraction `atomsOf e` of atomic facts from an
`L`-structure along an equivalence `e : M ≃ Fin n`, and the evaluation isomorphism
`realize_iff_atomsOf`.

## Main definitions

* `Cslib.Logic.FO.Atom`: the atomic facts of a structure for `L` on `Fin n`.
* `Cslib.Logic.FO.Model`: the universe `Fin n` with the structure whose true atomic facts are
  given by a truth assignment.
* `Cslib.Logic.FO.atomsOf`: the truth table of atomic facts on `Fin n` under an equivalence
  from `M`.
* `Cslib.Logic.FO.equivModel`: the first-order isomorphism between `M` and `Model (atomsOf e)`.

## Main results

* `Cslib.Logic.FO.realize_iff_atomsOf`: a sentence holds in `M` if and only if it holds in
  `Model (atomsOf e)`.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

@[expose] public section

namespace Cslib.Logic.FO

open FirstOrder FirstOrder.Language

variable {L : Language} [L.IsRelational] {n : ℕ}

/-- The atomic facts of a structure for `L` on `Fin n`: a relation symbol and a tuple of
elements. -/
def Atom (L : Language) (n : ℕ) : Type _ :=
  Σ R : Σ l, L.Relations l, Fin R.1 → Fin n

/-- The universe `Fin n` with the structure whose true atomic facts are those given by `x`. -/
@[nolint unusedArguments]
def Model (_x : Atom L n → Bool) : Type :=
  Fin n

/-- The first-order `L.Structure` on `Model x` whose relations are given by the truth table `x`. -/
instance (x : Atom L n → Bool) : L.Structure (Model x) where
  funMap f := isEmptyElim f
  RelMap {l} R t := x ⟨⟨l, R⟩, t⟩ = true

/-- There are finitely many atomic facts on `Fin n` when `L` has finitely many relation symbols. -/
instance [Fintype (Σ l, L.Relations l)] : Fintype (Atom L n) :=
  inferInstanceAs (Fintype (Σ R : Σ l, L.Relations l, Fin R.1 → Fin n))

/-- Finitely many atomic facts when the relations are finite. -/
instance [Finite (Σ l, L.Relations l)] : Finite (Atom L n) :=
  inferInstanceAs (Finite (Σ R : Σ l, L.Relations l, Fin R.1 → Fin n))

variable {M : Type*} [L.Structure M]

open Classical in
/-- The atomic facts of a structure on `M`, read through an enumeration `e` of `M` by `Fin n`. -/
noncomputable def atomsOf (e : M ≃ Fin n) : Atom L n → Bool :=
  fun a => decide (Structure.RelMap a.1.2 (e.symm ∘ a.2))

/-- An enumeration of `M` is an isomorphism onto the structure with the atomic facts of `M`. -/
def equivModel (e : M ≃ Fin n) : M ≃[L] Model (atomsOf (L := L) e) where
  toEquiv := e
  map_fun' f := isEmptyElim f
  map_rel' R t := by
    change atomsOf e ⟨⟨_, R⟩, e ∘ t⟩ = true ↔ Structure.RelMap R t
    simp [atomsOf, Function.comp_def]

/-- A structure satisfies a sentence exactly when the structure with its atomic facts does. -/
theorem realize_iff_atomsOf (e : M ≃ Fin n) (φ : L.Sentence) :
    M ⊨ φ ↔ Model (atomsOf (L := L) e) ⊨ φ :=
  StrongHomClass.realize_sentence (equivModel e) φ

end Cslib.Logic.FO
