/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Atom
public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Transfer
import CslibFrontier.Foundations.Data.Fintype.RestrictInjective
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

A nullary relation symbol is a single atomic fact, true with probability exactly `1/2` for every
`n`, so a vocabulary with one has no 0-1 law (`Cslib.Logic.FO.not_zero_one_law_of_nullary`).

## Main definitions

* `Cslib.Logic.FO.atomStructure`: the structure on `Fin n` given by a truth table of atomic facts.
* `Cslib.Logic.FO.atomStructureEquiv`: truth tables and structures correspond.
* `Cslib.Logic.FO.uniformStructure`: the uniform random structure on `Fin n`.

## Main results

* `Cslib.Logic.FO.structProb_uniformStructure`: probabilities are fractions of truth tables.
* `Cslib.Logic.FO.structProb_uniformStructure_eq_card`: probabilities are fractions of structures.
* `Cslib.Logic.FO.structProb_uniformStructure_relMap`: each atomic fact has probability `1/2`.
* `Cslib.Logic.FO.not_zero_one_law_of_nullary`: a nullary relation symbol breaks the 0-1 law.

## References

* [Y. V. Glebskiĭ, D. I. Kogan, M. I. Liogon'kiĭ and V. A. Talanov, *Range and degree of
  realizability of formulas in the restricted predicate calculus*]
  [GlebskiiKoganLiogonkiiTalanov1969]
* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 12.
-/

public section

open FirstOrder Language Structure Cslib.Probability Filter

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

/-- Each atomic fact holds in the uniform random structure with probability `1/2`. -/
theorem structProb_uniformStructure_relMap {n l : ℕ} (R : L.Relations l) (t : Fin l → Fin n) :
    structProb (uniformStructure n) (fun S => @RelMap L (Fin n) S l R t) = 1 / 2 := by
  rw [structProb_uniformStructure]
  refine (Nat.card_subtype_comp_injective_div (β := Bool)
    (fun _ : Unit => (⟨⟨l, R⟩, t⟩ : Atom L n)) (fun _ _ _ => rfl) (fun h => h () = true)).trans ?_
  have h1 : Nat.card {h : Unit → Bool // h () = true} = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => Subtype.ext (funext fun u => by
      cases u; rw [a.2, b.2])⟩, ⟨⟨fun _ => true, rfl⟩⟩⟩
  have h2 : Nat.card (Unit → Bool) = 2 := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
      Nat.card_eq_fintype_card (α := Unit), Fintype.card_unit, pow_one]
  rw [h1, h2]
  norm_num

/-- A nullary relation symbol holds in the uniform random structure with probability exactly `1/2`,
for every `n`. -/
theorem sentenceProb_uniformStructure_nullary (R : L.Relations 0) (n : ℕ) :
    sentenceProb (uniformStructure n) (Relations.formula R Fin.elim0) = 1 / 2 := by
  rw [sentenceProb_def, ← structProb_uniformStructure_relMap R (Fin.elim0 : Fin 0 → Fin n)]
  congr 1
  funext S
  let := S
  refine propext ?_
  rw [Sentence.Realize, Formula.realize_rel]
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- **Nullary relation symbols break the 0-1 law.** If `L` has a nullary relation symbol `R`,
then the sentence `R` holds in the uniform random structure on `Fin n` with probability exactly
`1/2`, so its probability tends neither to `0` nor to `1`. -/
theorem not_zero_one_law_of_nullary (R : L.Relations 0) :
    ¬∀ φ : L.Sentence,
      Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 0) ∨
        Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 1) := by
  intro h
  have hconst : (fun n => sentenceProb (uniformStructure (L := L) n)
      (Relations.formula R Fin.elim0)) = fun _ => 1 / 2 :=
    funext (sentenceProb_uniformStructure_nullary R)
  rcases h (Relations.formula R Fin.elim0) with h | h <;> rw [hconst] at h <;>
    have := tendsto_nhds_unique tendsto_const_nhds h <;> norm_num at this

end Cslib.Logic.FO
