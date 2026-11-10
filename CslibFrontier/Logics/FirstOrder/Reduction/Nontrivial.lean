/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Interpretation.Tagged

/-!
# Order-free interpretations on structures with at least two elements

The reductions in this module use order-free first-order interpretations. Input structures have
no built-in order or numeric predicates; these are variants of the standard ordered setting.

Order-free reductions (`Cslib.Logic.FO.Reduces`) are asked to be correct on every finite
structure, including the empty one and those with one element. On these, an interpretation of the
unordered structures of this library has little room: an interpretation of positive dimension
maps the empty structure to the empty structure, and a structure with one element to a structure
with at most one element. Whether a reduction to a class exists then depends on how the class
treats its smallest members. Every structure with at most one element is an independent set
instance with a solution, for example, while the empty clause on one element is an unsatisfiable
CNF structure, so SAT is not order-free reducible to independent set in this sense.

Immerman's Boolean-constant convention requires at least two elements, with distinct `0` and `1`
[Immerman, Proviso 1.15][Immerman1999]. Here the same size restriction is used without built-in
order: `ReducesNontrivial K K'` requires an order-free interpretation to be correct on each finite
structure with at least two elements. It is distinct from the unrestricted `Reduces`, which also
handles empty and singleton structures. Such reductions compose when the first interpretation
preserves nontriviality, or when the second reduction is unrestricted. A compiled tagged
interpretation preserves nontriviality when its tagged output is nonempty.

## Main definitions

* `Cslib.Logic.FO.ReducesNontrivial`: order-free reducibility on structures with two distinct
  elements.

## Main results

* `Cslib.Logic.FO.Reduces.reducesNontrivial`: order-free reductions are reductions on nontrivial
  structures.
* `Cslib.Logic.FO.ReducesNontrivial.refl`, `Cslib.Logic.FO.ReducesNontrivial.trans_reduces`,
  `Cslib.Logic.FO.ReducesNontrivial.trans_of_nontrivial`: reflexivity and composition.
* `Cslib.Logic.FO.ReducesNontrivial.of_tagged`: reductions on nontrivial structures by tagged
  interpretations; no nonemptiness assumption is needed for correctness.
* `Cslib.Logic.FO.TaggedInterpretation.nontrivial_and_mem_iff_toInterpretation`: correctness
  together with nontriviality preservation when the tagged outputs are nonempty.
* `Cslib.Logic.FO.Reduces.of_reducesNontrivial`: between classes containing every structure with
  at most one element, reductions on nontrivial structures are order-free reductions.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v u' v' u'' v'' w

open FirstOrder Language Structure CategoryTheory

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}
  [L'.IsRelational] [L''.IsRelational]

/-- A class `K` of `L`-structures is **reducible by an order-free interpretation on nontrivial
structures** to a class `K'` of `L'`-structures when some first-order interpretation of `L'` in
`L` maps every finite `L`-structure with two distinct elements inside `K'` exactly when it is in
`K`. -/
def ReducesNontrivial (K : Set (Bundled.{w} L.Structure)) (K' : Set (Bundled.{w} L'.Structure)) :
    Prop :=
  ∃ (ι : Type) (_ : Finite ι) (I : Interpretation L L' ι),
    ∀ (M : Bundled.{w} L.Structure) [Finite M], Nontrivial M →
      (M ∈ K ↔ Bundled.of (c := L'.Structure) (I.Model M) ∈ K')

variable {K : Set (Bundled.{w} L.Structure)} {K' : Set (Bundled.{w} L'.Structure)}
  {K'' : Set (Bundled.{w} L''.Structure)}

/-- An order-free reduction is a reduction on nontrivial structures. -/
theorem Reduces.reducesNontrivial (h : Reduces K K') : ReducesNontrivial K K' :=
  let ⟨ι, hι, I, hI⟩ := h
  ⟨ι, hι, I, fun M _ _ => hI M⟩

namespace ReducesNontrivial

/-- Reducibility on nontrivial structures is reflexive on classes closed under isomorphism. -/
theorem refl [L.IsRelational] (hK : IsoClosed K) : ReducesNontrivial K K :=
  (Reduces.refl hK).reducesNontrivial

/-- A reduction on nontrivial structures from `K` to `K'` is also one from `Kᶜ` to `K'ᶜ`. -/
theorem compl (h : ReducesNontrivial K K') : ReducesNontrivial Kᶜ K'ᶜ :=
  let ⟨ι, hι, I, hI⟩ := h
  ⟨ι, hι, I, fun M _ hM => not_congr (hI M hM)⟩

/-- A reduction on nontrivial structures followed by an order-free reduction. -/
theorem trans_reduces (h : ReducesNontrivial K K') (h' : Reduces K' K'') (hK'' : IsoClosed K'') :
    ReducesNontrivial K K'' := by
  obtain ⟨ι, _, I, hI⟩ := h
  obtain ⟨κ, _, J, hJ⟩ := h'
  refine ⟨κ × ι, inferInstance, J.comp I, fun M _ hM => ?_⟩
  rw [hI M hM, hJ (Bundled.of (I.Model M))]
  exact hK'' (Interpretation.compEquiv J I)

/-- A reduction on nontrivial structures through an interpretation that keeps them nontrivial,
followed by a reduction on nontrivial structures. -/
theorem trans_of_nontrivial {ι : Type} [Finite ι] (I : Interpretation L L' ι)
    (hI : ∀ (M : Bundled.{w} L.Structure) [Finite M], Nontrivial M →
      Nontrivial (I.Model M) ∧ (M ∈ K ↔ Bundled.of (c := L'.Structure) (I.Model M) ∈ K'))
    (h' : ReducesNontrivial K' K'') (hK'' : IsoClosed K'') : ReducesNontrivial K K'' := by
  obtain ⟨κ, _, J, hJ⟩ := h'
  refine ⟨κ × ι, inferInstance, J.comp I, fun M _ hM => ?_⟩
  obtain ⟨hnt, hiff⟩ := hI M hM
  rw [hiff, hJ (Bundled.of (I.Model M)) hnt]
  exact hK'' (Interpretation.compEquiv J I)

end ReducesNontrivial

/-- A reduction on nontrivial structures between classes containing every finite structure with
at most one element is an order-free reduction: an interpretation maps a structure with at most one
element to a structure with at most one element. -/
theorem Reduces.of_reducesNontrivial (h : ReducesNontrivial K K')
    (hK : ∀ (M : Bundled.{w} L.Structure) [Finite M], Subsingleton M → M ∈ K)
    (hK' : ∀ (N : Bundled.{w} L'.Structure) [Finite N], Subsingleton N → N ∈ K') :
    Reduces K K' := by
  obtain ⟨ι, _, I, hI⟩ := h
  refine .of_interpretation I fun M _ => ?_
  rcases subsingleton_or_nontrivial M with hM | hM
  · have : Subsingleton (I.Model M) :=
      ⟨fun x y => Interpretation.Model.ext (Subsingleton.elim _ _)⟩
    exact iff_of_true (hK M hM) (hK' _ this)
  · exact hI M hM

/-- A compiled tagged interpretation preserves class membership and nontriviality when its
tagged outputs are nonempty and the target class is closed under isomorphism and copies. -/
theorem TaggedInterpretation.nontrivial_and_mem_iff_toInterpretation
    {K : Set (Bundled.{w} L.Structure)}
    {K' : Set (Bundled.{w} L'.Structure)} (hK' : IsoClosed K') (hcopy : CopyInvariant K')
    {T : Type} [Finite T] {ι : T → Type} [∀ t, Finite (ι t)]
    (I : TaggedInterpretation L L' T ι)
    (hne : ∀ (M : Type w) [L.Structure M] [Finite M], Nontrivial M → Nonempty (I.Model M))
    (hlarge : ∀ (M : Bundled.{w} L.Structure) [Finite M], Nontrivial M →
      (M ∈ K ↔ (Bundled.of (I.Model M) : Bundled.{w} L'.Structure) ∈ K'))
    (M : Bundled.{w} L.Structure) [Finite M] (hM : Nontrivial M) :
    Nontrivial ((I.toInterpretation (Interpretation.empty L L')).Model M) ∧
      (M ∈ K ↔ Bundled.of (c := L'.Structure)
        ((I.toInterpretation (Interpretation.empty L L')).Model M) ∈ K') := by
  have := hne M hM
  refine ⟨I.nontrivial_toInterpretation_model _, ?_⟩
  have : Finite (Bundled.of (c := L'.Structure)
      (Copies (TaggedInterpretation.Pairs M) (I.Model M))) :=
    inferInstanceAs (Finite (Copies _ _))
  rw [hlarge M hM, ← hcopy (TaggedInterpretation.Pairs M)]
  exact hK' (TaggedInterpretation.copiesEquiv _)

/-- **Tagged interpretations give reductions on nontrivial structures** to classes closed under
isomorphism and copies. -/
theorem ReducesNontrivial.of_tagged {K : Set (Bundled.{w} L.Structure)}
    {K' : Set (Bundled.{w} L'.Structure)} (hK' : IsoClosed K') (hcopy : CopyInvariant K')
    {T : Type} [Finite T] {ι : T → Type} [∀ t, Finite (ι t)]
    (I : TaggedInterpretation L L' T ι)
    (hlarge : ∀ (M : Bundled.{w} L.Structure) [Finite M], Nontrivial M →
      (M ∈ K ↔ (Bundled.of (I.Model M) : Bundled.{w} L'.Structure) ∈ K')) :
    ReducesNontrivial K K' :=
  ⟨_, inferInstance, I.toInterpretation (Interpretation.empty L L'), fun M _ hM => by
    have : Finite (Bundled.of (c := L'.Structure)
        (Copies (TaggedInterpretation.Pairs M) (I.Model M))) :=
      inferInstanceAs (Finite (Copies _ _))
    rw [hlarge M hM, ← hcopy (TaggedInterpretation.Pairs M)]
    exact hK' (TaggedInterpretation.copiesEquiv _)⟩

end Cslib.Logic.FO
