/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Problems.SizedGraph
public import Complexity.Logics.SecondOrder.Reduction

/-!
# Independent set, clique and vertex cover are existential second-order definable

A `sizedGraph` structure has an independent set of the target size exactly when some set `S` of
vertices and some binary relation `F` satisfy: `F` is a bijection from `S` onto the size relation,
and no two distinct vertices of `S` are adjacent. This is an existential second-order sentence
(`Cslib.Logic.FO.sizedGraph.independentSetSentence`), so the class `sizedGraph.IndependentSet` is
existential second-order definable [Fagin1974], [Immerman, Chapter 7][Immerman1999]; so are clique
and vertex cover, which are quantifier-free reducible to it.

## Main definitions

* `Cslib.Logic.FO.sizedGraph.independentSetArity`,
  `Cslib.Logic.FO.sizedGraph.independentSetLanguage`: the relation variable arities and expanded
  language of the independent-set sentence.
* `Cslib.Logic.FO.sizedGraph.adjSym`, `Cslib.Logic.FO.sizedGraph.sizeSym`,
  `Cslib.Logic.FO.sizedGraph.setSym`, `Cslib.Logic.FO.sizedGraph.bijSym`: the relation symbols of
  `independentSetLanguage`.
* `Cslib.Logic.FO.sizedGraph.independentSetMatrix`,
  `Cslib.Logic.FO.sizedGraph.independentSetSentence`: the first-order matrix and defining
  existential second-order sentence of independent set.

## Main results

* `Cslib.Logic.FO.sizedGraph.realize_independentSetSentence`: its semantics.
* `Cslib.Logic.FO.sizedGraph.definable_IndependentSet`,
  `Cslib.Logic.FO.sizedGraph.definable_Clique`, `Cslib.Logic.FO.sizedGraph.definable_VertexCover`:
  the three classes are existential second-order definable.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe w

namespace Cslib.Logic.FO.sizedGraph

open FirstOrder Language Structure CategoryTheory ESO

/-- The arities of the relation variables: a unary `S` and a binary `F`. -/
abbrev independentSetArity : Fin 2 → ℕ :=
  ![1, 2]

/-- The language of the independent-set sentence. -/
abbrev independentSetLanguage : Language :=
  sizedGraph.sum (varLanguage independentSetArity)

/-- The edge relation, among the symbols of the independent-set sentence. -/
abbrev adjSym : independentSetLanguage.Relations 2 :=
  Sum.inl sizedGraph.adj

/-- The size relation, among the symbols of the independent-set sentence. -/
abbrev sizeSym : independentSetLanguage.Relations 1 :=
  Sum.inl sizedGraph.size

/-- The relation variable `S`, the independent set. -/
abbrev setSym : independentSetLanguage.Relations 1 :=
  Sum.inr ⟨0, rfl⟩

/-- The relation variable `F`, a bijection from `S` onto the size relation. -/
abbrev bijSym : independentSetLanguage.Relations 2 :=
  Sum.inr ⟨1, rfl⟩

/-- The first-order part of the independent-set sentence: `F` is a bijection from `S` onto the
size relation, and `S` is independent. -/
def independentSetMatrix : independentSetLanguage.Sentence :=
  (∀' ∀' (bijSym.boundedFormula₂ &0 &1 ⟹
      (setSym.boundedFormula₁ &0 ⊓ sizeSym.boundedFormula₁ &1))) ⊓
    (∀' ∀' ∀' ((bijSym.boundedFormula₂ &0 &1 ⊓ bijSym.boundedFormula₂ &0 &2) ⟹
      Term.bdEqual &1 &2)) ⊓
    (∀' ∀' ∀' ((bijSym.boundedFormula₂ &0 &2 ⊓ bijSym.boundedFormula₂ &1 &2) ⟹
      Term.bdEqual &0 &1)) ⊓
    (∀' (setSym.boundedFormula₁ &0 ⟹ ∃' bijSym.boundedFormula₂ &0 &1)) ⊓
    (∀' (sizeSym.boundedFormula₁ &0 ⟹ ∃' bijSym.boundedFormula₂ &1 &0)) ⊓
    (∀' ∀' ((setSym.boundedFormula₁ &0 ⊓ setSym.boundedFormula₁ &1 ⊓ ∼(Term.bdEqual &0 &1)) ⟹
      ∼(adjSym.boundedFormula₂ &0 &1)))

/-- The **independent-set sentence** `∃ S F, F is a bijection from S onto size ∧ S is
independent`. -/
def independentSetSentence : ESO.Sentence sizedGraph :=
  ⟨Fin 2, independentSetArity, independentSetMatrix⟩

variable {M : Type*} [sizedGraph.Structure M]

private theorem realize_independentSetMatrix (R : ∀ i, Set (Fin (independentSetArity i) → M)) :
    (letI := varLanguage.structure R; M ⊨ independentSetMatrix) ↔
      (∀ x y, ![x, y] ∈ R 1 → ![x] ∈ R 0 ∧ RelMap sizedGraph.size ![y]) ∧
      (∀ x y z, ![x, y] ∈ R 1 → ![x, z] ∈ R 1 → y = z) ∧
      (∀ x y z, ![x, z] ∈ R 1 → ![y, z] ∈ R 1 → x = y) ∧
      (∀ x, ![x] ∈ R 0 → ∃ y, ![x, y] ∈ R 1) ∧
      (∀ y, RelMap sizedGraph.size ![y] → ∃ x, ![x, y] ∈ R 1) ∧
      (∀ x y, ![x] ∈ R 0 → ![y] ∈ R 0 → x ≠ y → ¬RelMap sizedGraph.adj ![x, y]) := by
  let _ := varLanguage.structure R
  have hset (x : Fin 1 → M) : RelMap setSym x ↔ x ∈ R 0 := Iff.rfl
  have hbij (x : Fin 2 → M) : RelMap bijSym x ↔ x ∈ R 1 := Iff.rfl
  have hsize (x : Fin 1 → M) : RelMap sizeSym x ↔ RelMap sizedGraph.size x := Iff.rfl
  have hadj (x : Fin 2 → M) : RelMap adjSym x ↔ RelMap sizedGraph.adj x := Iff.rfl
  simp only [independentSetMatrix, Language.Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_inf,
    BoundedFormula.realize_all, BoundedFormula.realize_imp, BoundedFormula.realize_ex,
    BoundedFormula.realize_not, BoundedFormula.realize_rel₁, BoundedFormula.realize_rel₂,
    BoundedFormula.realize_bdEqual, hset, hbij, hsize, hadj]
  simp [Fin.snoc, and_assoc, and_imp]

/-- The independent-set sentence holds exactly in the structures with an independent set of the
target size. -/
theorem realize_independentSetSentence [Finite M] :
    independentSetSentence.Realize M ↔ ∃ s : Set M,
      s.ncard = {x : M | RelMap sizedGraph.size ![x]}.ncard ∧
        s.Pairwise fun x y => ¬RelMap sizedGraph.adj ![x, y] := by
  change (∃ R : ∀ i, Set (Fin (independentSetArity i) → M),
    letI := varLanguage.structure R; M ⊨ independentSetMatrix) ↔ _
  simp only [realize_independentSetMatrix]
  constructor
  · rintro ⟨R, h₁, h₂, h₃, h₄, h₅, h₆⟩
    refine ⟨{x | ![x] ∈ R 0}, ?_, fun x hx y hy hxy => h₆ x y hx hy hxy⟩
    choose f hf using h₄
    refine Set.ncard_congr (fun x hx => f x hx) (fun x hx => (h₁ _ _ (hf x hx)).2)
      (fun x y hx hy hxy => h₃ x y _ (hf x hx) (hxy ▸ hf y hy)) fun y hy => ?_
    obtain ⟨x, hx⟩ := h₅ y hy
    exact ⟨x, (h₁ _ _ hx).1, h₂ _ _ _ (hf x _) hx⟩
  · rintro ⟨s, hs, hind⟩
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at hs
    obtain ⟨g⟩ := Finite.card_eq.1 hs
    let R : ∀ i, Set (Fin (independentSetArity i) → M) := fun i =>
      Fin.cases (motive := fun i => Set (Fin (independentSetArity i) → M)) {v | v (0 : Fin 1) ∈ s}
        (fun j => Fin.cases (motive := fun j => Set (Fin (independentSetArity j.succ) → M))
          {v | ∃ h : v (0 : Fin 2) ∈ s, (g ⟨v (0 : Fin 2), h⟩).1 = v (1 : Fin 2)}
          (fun k => k.elim0) j) i
    refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro x y ⟨hx, hxy⟩
      change x ∈ s at hx
      change (g ⟨x, hx⟩).1 = y at hxy
      subst hxy
      exact ⟨hx, (g ⟨x, hx⟩).2⟩
    · rintro x y z ⟨hx, hxy⟩ ⟨hx', hxz⟩
      change x ∈ s at hx hx'
      change (g ⟨x, hx⟩).1 = y at hxy
      change (g ⟨x, hx'⟩).1 = z at hxz
      exact hxy.symm.trans hxz
    · rintro x y z ⟨hx, hxz⟩ ⟨hy, hyz⟩
      change x ∈ s at hx
      change y ∈ s at hy
      change (g ⟨x, hx⟩).1 = z at hxz
      change (g ⟨y, hy⟩).1 = z at hyz
      exact congrArg Subtype.val (g.injective (Subtype.ext (hxz.trans hyz.symm)))
    · intro x hx
      exact ⟨(g ⟨x, hx⟩).1, hx, rfl⟩
    · intro y hy
      obtain ⟨⟨x, hx⟩, hxy⟩ := g.surjective ⟨y, hy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
    · intro x y hx hy hxy
      exact hind hx hy hxy

/-- **Independent set is existential second-order definable.** -/
theorem definable_IndependentSet : ESO.Definable IndependentSet.{w} :=
  ⟨independentSetSentence, fun _ _ => realize_independentSetSentence.symm⟩

/-- **Clique is existential second-order definable**, as it reduces to independent set. -/
theorem definable_Clique : ESO.Definable Clique.{w} :=
  definable_IndependentSet.of_reduces qfReduces_Clique_IndependentSet.reduces

/-- **Vertex cover is existential second-order definable**, as it reduces to independent set. -/
theorem definable_VertexCover : ESO.Definable VertexCover.{w} :=
  definable_IndependentSet.of_reduces qfReduces_VertexCover_IndependentSet.reduces

end Cslib.Logic.FO.sizedGraph
