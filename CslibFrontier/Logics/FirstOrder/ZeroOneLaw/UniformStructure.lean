/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Atom
public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Transfer
import CslibFrontier.Foundations.ModelTheory.Basic
import CslibFrontier.Probability.PMF.Uniform

/-!
# The uniform random structure for a finite relational vocabulary

For a relational language `L` with finitely many relation symbols, a structure for `L` on `Fin n`
is the same as the truth table of its atomic facts `R(a₁, …, aₗ)`
(`Cslib.Logic.FO.atomStructureEquiv`). `Cslib.Logic.FO.uniformStructure n` draws every atomic fact
independently with probability `1/2`. Equivalently, it is the uniform distribution on the
`L`-structures on `Fin n` (`Cslib.Logic.FO.structProb_uniformStructure_eq_card`): the measure `μₙ`
of the 0-1 law [GlebskiiKoganLiogonkiiTalanov1969] [Fagin1976] [Libkin2004, Chapter 12].

For `L = Language.graph` the uniform random structure is a random *directed* graph with loops: each
of the `n²` ordered pairs is an edge with probability `1/2`. It is not `G(n, 1/2)`, the uniform
random simple graph of `CslibFrontier.Logics.FirstOrder.ZeroOneLaw`; under it the simple-graph
axioms
hold with probability tending to `0`, as the library's tests check.

Atomic facts are `Cslib.Logic.FO.Atom`, and the structure given by a truth table is that of
`Cslib.Logic.FO.Model`.

Random structures in which each relation symbol has its own constant probability are
`Cslib.Logic.FO.bernoulliStructure`, which also records that a nullary relation symbol breaks the
0-1 law (`Cslib.Logic.FO.not_zero_one_law_of_nullary`).

## Main definitions

* `Cslib.Logic.FO.atomStructure`: the structure on `Fin n` given by a truth table of atomic facts.
* `Cslib.Logic.FO.atomStructureEquiv`: truth tables and structures correspond.
* `Cslib.Logic.FO.uniformStructure`: the uniform random structure on `Fin n`.

## Main results

* `Cslib.Logic.FO.structProb_uniformStructure`: probabilities are fractions of truth tables.
* `Cslib.Logic.FO.structProb_uniformStructure_eq_card`: probabilities are fractions of structures.

## References

* [Y. V. Glebskiĭ, D. I. Kogan, M. I. Liogon'kiĭ and V. A. Talanov, *Range and degree of
  realizability of formulas in the restricted predicate calculus*]
  [GlebskiiKoganLiogonkiiTalanov1969]
* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 12.
-/

public section

open FirstOrder Language Structure Cslib.Probability

namespace Cslib.Logic.FO

universe u v

variable {L : Language.{u, v}} [L.IsRelational]

/-- The structure on `Fin n` whose true atomic facts are those given by `y`: the structure of
`Cslib.Logic.FO.Model y`. -/
abbrev atomStructure {n : ℕ} (y : Atom L n → Bool) : L.Structure (Fin n) :=
  inferInstanceAs (L.Structure (Model y))

theorem relMap_atomStructure {n l : ℕ} (y : Atom L n → Bool) (R : L.Relations l)
    (t : Fin l → Fin n) : @RelMap L (Fin n) (atomStructure y) l R t ↔ y ⟨⟨l, R⟩, t⟩ = true :=
  Iff.rfl

open Classical in
/-- For a relational language, a structure on `Fin n` is the same as the truth table of its
atomic facts. The inverse reads off the atomic facts with `Cslib.Logic.FO.atomsOf`. -/
noncomputable def atomStructureEquiv (n : ℕ) : (Atom L n → Bool) ≃ L.Structure (Fin n) where
  toFun := atomStructure
  invFun S := letI := S; atomsOf (L := L) (Equiv.refl (Fin n))
  left_inv y := by
    funext a
    exact Bool.decide_eq_true
  right_inv S := Structure.ext_of_isRelational fun R x => decide_eq_true_iff

@[simp]
theorem atomStructureEquiv_apply {n : ℕ} (y : Atom L n → Bool) :
    atomStructureEquiv n y = atomStructure y := by
  rw [atomStructureEquiv]
  rfl

variable [Finite (Σ l, L.Relations l)]

open Classical in
/-- The **uniform random structure** on `Fin n`: every atomic fact `R(a₁, …, aₗ)` holds
independently with probability `1/2`. -/
noncomputable def uniformStructure (n : ℕ) : PMF (L.Structure (Fin n)) :=
  have := Fintype.ofFinite (Σ l, L.Relations l)
  (PMF.uniformOfFintype (Atom L n → Bool)).map atomStructure

/-- `uniformStructure n` is the image of the uniform truth table under `atomStructure`, for any
`Fintype` instance on the truth tables. -/
theorem uniformStructure_eq_map (n : ℕ) [Fintype (Atom L n → Bool)] :
    uniformStructure n = (PMF.uniformOfFintype (Atom L n → Bool)).map atomStructure := by
  rw [uniformStructure]
  congr
  exact Subsingleton.elim _ _

/-- The probability of a property under the uniform random structure is the fraction of the
truth tables of the atomic facts that give a structure with the property. -/
theorem structProb_uniformStructure (n : ℕ) (P : L.Structure (Fin n) → Prop) :
    structProb (uniformStructure n) P =
      Nat.card {y : Atom L n → Bool // P (atomStructure y)} / Nat.card (Atom L n → Bool) := by
  classical
  let := Fintype.ofFinite (Σ l, L.Relations l)
  rw [structProb_def, uniformStructure, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFintype_toReal, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- **The uniform random structure is uniform.** The probability of a property is the fraction of
the structures on `Fin n` that have it: the measure `μₙ` of the 0-1 law [Fagin1976]. -/
theorem structProb_uniformStructure_eq_card (n : ℕ) (P : L.Structure (Fin n) → Prop) :
    structProb (uniformStructure n) P =
      Nat.card {S : L.Structure (Fin n) // P S} / Nat.card (L.Structure (Fin n)) := by
  rw [structProb_uniformStructure, Nat.card_congr (atomStructureEquiv (L := L) n),
    ← Nat.card_congr ((atomStructureEquiv (L := L) n).subtypeEquiv fun y => Iff.rfl)]
  rfl

end Cslib.Logic.FO
