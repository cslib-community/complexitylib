/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.QuantifierFree
public import CslibFrontier.Logics.FirstOrder.Reduction

/-!
# Quantifier-free first-order reductions

A class `K` of `L`-structures is **quantifier-free reducible** to a class `K'` of `L'`-structures
(`FO.QFReduces K K'`) when it is first-order reducible to it (`FO.Reduces`) through a
quantifier-free interpretation (`Interpretation.IsQF`): the domain and the relations of the
interpreted structure are Boolean combinations of atomic formulas of `L`. Like first-order
reducibility, quantifier-free reducibility is reflexive on classes closed under isomorphism of a
relational language, because the identity interpretation is quantifier-free, and transitive when
the last class is closed under isomorphism, because quantifier-free interpretations compose.

The vocabularies are parameters: no order or BIT predicate is assumed, and the dimension is any
finite type. Quantifier-free reductions are therefore not quantifier-free projections, which
moreover allow only a single input literal for each output bit and fix the numeric vocabulary
[Immerman and Landau, Definitions 3.3--3.6][ImmermanLandau1995]; see
`CslibFrontier.Logics.FirstOrder.Projection`.

A reduction through a given interpretation is proved by two kinds of arguments: syntactic side
conditions, such as quantifier-freeness, and the semantic statement that `M ∈ K` exactly when the
interpreted structure belongs to `K'`. For a one-dimensional interpretation whose domain formula
always holds, `QFReduces.of_unitStructure` states the semantic part on the input universe itself,
as `Reduces.of_unitStructure` does for first-order reductions; for an interpretation of any
dimension whose domain formula always holds, `QFReduces.of_tupleStructure` states it on tuples of
the input universe. The tactic `fo_reduction` applies
these lemmas and proves the side conditions.

## Main definitions

* `Cslib.Logic.FO.QFReduces`: quantifier-free reducibility between classes of finite structures.

## Main results

* `Cslib.Logic.FO.QFReduces.reduces`: quantifier-free reductions are first-order reductions.
* `Cslib.Logic.FO.QFReduces.refl`, `Cslib.Logic.FO.QFReduces.trans`: quantifier-free
  reducibility is a preorder on classes closed under isomorphism.
* `Cslib.Logic.FO.QFReduces.of_unitStructure`: quantifier-free reductions through
  one-dimensional interpretations, stated on the input universe.
* `Cslib.Logic.FO.QFReduces.of_tupleStructure`: quantifier-free reductions through
  interpretations whose domain formula always holds, stated on tuples of the input universe.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995]
-/

@[expose] public section

universe u v u' v' u'' v'' w

open FirstOrder Language Structure CategoryTheory

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}
  [L'.IsRelational] {K : Set (Bundled.{w} L.Structure)} {K' : Set (Bundled.{w} L'.Structure)}

/-- A class `K` of `L`-structures is **quantifier-free reducible** to a class `K'` of
`L'`-structures when some quantifier-free first-order interpretation of `L'` in `L` maps the finite
members of `K` into `K'` and the other finite `L`-structures outside `K'`. -/
def QFReduces (K : Set (Bundled.{w} L.Structure)) (K' : Set (Bundled.{w} L'.Structure)) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (I : Interpretation L L' ι), I.IsQF ∧
    ∀ (M : Bundled.{w} L.Structure) [Finite M],
      M ∈ K ↔ Bundled.of (c := L'.Structure) (I.Model M) ∈ K'

namespace QFReduces

/-- A quantifier-free reduction through a given interpretation. -/
theorem of_interpretation {ι : Type} [Finite ι] (I : Interpretation L L' ι)
    (h : ∀ (M : Bundled.{w} L.Structure) [Finite M],
      M ∈ K ↔ Bundled.of (c := L'.Structure) (I.Model M) ∈ K')
    (hI : I.IsQF) : QFReduces K K' :=
  ⟨ι, inferInstance, I, hI, h⟩

/-- A quantifier-free reduction is a first-order reduction. -/
theorem reduces (h : QFReduces K K') : Reduces K K' :=
  let ⟨ι, hι, I, _, hI⟩ := h
  ⟨ι, hι, I, hI⟩

/-- **Quantifier-free reducibility is reflexive** on classes closed under isomorphism, through the
identity interpretation. -/
theorem refl [L.IsRelational] (hK : IsoClosed K) : QFReduces K K :=
  ⟨Unit, inferInstance, Interpretation.id L, Interpretation.isQF_id L,
    fun _ _ => hK Interpretation.idEquiv.symm⟩

/-- **Quantifier-free reducibility is transitive** when the last class is closed under
isomorphism, through the composite interpretation. -/
theorem trans [L''.IsRelational] {K'' : Set (Bundled.{w} L''.Structure)} (h : QFReduces K K')
    (h' : QFReduces K' K'') (hK'' : IsoClosed K'') : QFReduces K K'' := by
  obtain ⟨ι, _, I, hIqf, hI⟩ := h
  obtain ⟨κ, _, J, hJqf, hJ⟩ := h'
  refine ⟨κ × ι, inferInstance, J.comp I, hJqf.comp hIqf, fun M _ => ?_⟩
  rw [hI M, hJ (Bundled.of (I.Model M))]
  exact hK'' (Interpretation.compEquiv J I)

/-- A class quantifier-free reducible to a class closed under isomorphism is closed under
isomorphism. -/
theorem isoClosed (h : QFReduces K K') (hK' : IsoClosed K') : IsoClosed K :=
  h.reduces.isoClosed hK'

/-- A quantifier-free reduction from `K` to `K'` is also a reduction from `Kᶜ` to `K'ᶜ`. -/
theorem compl (h : QFReduces K K') : QFReduces Kᶜ K'ᶜ :=
  let ⟨ι, hι, I, hIqf, hI⟩ := h
  ⟨ι, hι, I, hIqf, fun M _ => not_congr (hI M)⟩

/-- A quantifier-free reduction through a one-dimensional interpretation whose domain formula
holds of every element of every finite structure, to a class closed under isomorphism, stated on
the input universe. -/
theorem of_unitStructure (I : Interpretation L L' Unit)
    (h : ∀ (M : Bundled.{w} L.Structure) [Finite M],
      M ∈ K ↔ (⟨M, I.unitStructure M⟩ : Bundled.{w} L'.Structure) ∈ K')
    (hI : I.IsQF) (hK' : IsoClosed K') (hdom : ∀ (M : Type w) [L.Structure M] [Finite M] (x : M),
      I.domain.Realize fun _ => x) :
    QFReduces K K' :=
  .of_interpretation I (fun M _ => (h M).trans (I.mem_iff_unitStructure hK' M (hdom M)).symm) hI

/-- A quantifier-free reduction through an interpretation whose domain formula holds of every
tuple of every finite structure, to a class closed under isomorphism, stated on the tuples of the
input universe. -/
theorem of_tupleStructure {ι : Type} [Finite ι] (I : Interpretation L L' ι)
    (h : ∀ (M : Bundled.{w} L.Structure) [Finite M],
      M ∈ K ↔ (⟨ι → M, I.tupleStructure M⟩ : Bundled.{w} L'.Structure) ∈ K')
    (hI : I.IsQF) (hK' : IsoClosed K') (hdom : ∀ (M : Type w) [L.Structure M] [Finite M]
      (x : ι → M), I.domain.Realize x) :
    QFReduces K K' :=
  .of_interpretation I (fun M _ => (h M).trans (I.mem_iff_tupleStructure hK' M (hdom M)).symm) hI

end QFReduces

end Cslib.Logic.FO
