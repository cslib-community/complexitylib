/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Interpretation.Tuple
public import CslibFrontier.Logics.FirstOrder.Interpretation.Unit
public import Mathlib.ModelTheory.Bundled

/-!
# First-order definability and first-order reductions

Descriptive complexity studies classes of finite structures. As in Mathlib's model theory, a class
of `L`-structures is a set of bundled structures, `Set (Bundled L.Structure)`; the notions below
only look at its finite members. In particular, a class is closed under isomorphism
(`Cslib.Logic.IsoClosed`) when it contains, with a finite structure, every structure isomorphic to
it.

A class `K` is first-order definable (`FO.Definable K`) when some first-order sentence holds in
exactly the finite structures of `K`. Such a class is closed under isomorphism, and the definable
classes are closed under complement, intersection and union.

A class `K` of `L`-structures is first-order reducible to a class `K'` of `L'`-structures
(`FO.Reduces K K'`) when some first-order interpretation `I` of `L'` in `L` satisfies
`M ∈ K ↔ I.Model M ∈ K'` for every finite `M`. This reducibility is order-free: the structures
have no built-in order or numeric predicates, the formulas of `I` use only the symbols of `L` and
equality, and the empty and the one-element structures are among the `M`. It is the order-free
counterpart of first-order reducibility of ordered queries, `Cslib.Logic.FO.Ordered.Reduces`
[Immerman, Definition 2.11][Immerman1999].
Reducibility is reflexive and transitive on classes closed under isomorphism
[Immerman, Exercise 2.15][Immerman1999], and first-order definability is closed under it: if `K'`
is defined by `φ`, then `K` is defined by the pullback of `φ`
[Immerman, Definition 3.9 and Framework 3.12][Immerman1999].

Senellart and Gnatenko formalize first-order reductions over Mathlib's model theory too, as the
backbone of a library of completeness results [Senellart and Gnatenko][SenellartGnatenko2026].
Their decision problems are predicates on structures bundled with a proof of invariance under
isomorphism, and their reductions are data, required to be correct on the finite nonempty
structures. Here a class is a set of bundled structures, as in Mathlib, invariance under
isomorphism is the separate hypothesis `IsoClosed`, reducibility is a proposition, and the empty
structure is not set apart.

## Main definitions

* `Cslib.Logic.IsoClosed`: closure of a class of structures under isomorphism of finite structures.
* `Cslib.Logic.FO.Definable`: first-order definability of a class of finite structures.
* `Cslib.Logic.FO.Reduces`: order-free first-order reducibility between classes of finite
  structures.

## Main results

* `Cslib.Logic.FO.Definable.isoClosed`: definable classes are closed under isomorphism.
* `Cslib.Logic.FO.Definable.compl`, `Cslib.Logic.FO.Definable.inter`,
  `Cslib.Logic.FO.Definable.union`: Boolean operations.
* `Cslib.Logic.FO.Reduces.refl`, `Cslib.Logic.FO.Reduces.trans`: reducibility is a preorder on
  classes closed under isomorphism.
* `Cslib.Logic.FO.Reduces.isoClosed`: a class reducible to a class closed under isomorphism is
  closed under isomorphism.
* `Cslib.Logic.IsoClosed.of_forall_imp`: closure under isomorphism from one direction.
* `Cslib.Logic.FO.Reduces.of_unitStructure`: a reduction through a one-dimensional interpretation
  whose domain formula always holds, stated on the input universe.
* `Cslib.Logic.FO.Reduces.of_tupleStructure`: a reduction through an interpretation whose domain
  formula always holds, stated on the tuples of the input universe.
* `Cslib.Logic.FO.Definable.of_reduces`: definability is closed under first-order reductions.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [P. Senellart and A. Gnatenko, *Descriptive Complexity in Lean: Completeness by First-Order
  Reductions*][SenellartGnatenko2026]
-/

@[expose] public section

universe u v u' v' u'' v'' w

open FirstOrder Language Structure CategoryTheory

namespace Cslib.Logic

variable {L : Language.{u, v}}

/-- A class of structures is **closed under isomorphism** when it contains, with a finite
structure, every structure isomorphic to it. Only finite structures are asked about, as in the
notions of definability and reducibility of finite structures. -/
def IsoClosed (K : Set (Bundled.{w} L.Structure)) : Prop :=
  ∀ ⦃M N : Bundled.{w} L.Structure⦄ [Finite M], (M ≃[L] N) → (M ∈ K ↔ N ∈ K)

/-- A class containing the image of each of its finite members under each isomorphism is closed
under isomorphism. -/
theorem IsoClosed.of_forall_imp {K : Set (Bundled.{w} L.Structure)}
    (h : ∀ ⦃M N : Bundled.{w} L.Structure⦄ [Finite M], (M ≃[L] N) → M ∈ K → N ∈ K) :
    IsoClosed K := fun _ N _ e =>
  have : Finite N := Finite.of_equiv _ e.toEquiv
  ⟨h e, h e.symm⟩

end Cslib.Logic

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}

/-! ### First-order definability -/

/-- A class of structures is **first-order definable** when some first-order sentence holds in
exactly its finite members, among all finite structures. -/
def Definable (K : Set (Bundled.{w} L.Structure)) : Prop :=
  ∃ φ : L.Sentence, ∀ (M : Bundled.{w} L.Structure) [Finite M], M ∈ K ↔ M ⊨ φ

namespace Definable

/-- The class of empty structures is first-order definable, by `∀ x, ⊥`. -/
theorem isEmpty :
    Definable {M : Bundled.{w} L.Structure | IsEmpty M} :=
  ⟨∀' ⊥, fun _ _ => ⟨fun h x => h.false x, fun h => ⟨fun x => h x⟩⟩⟩


variable {K K₁ K₂ : Set (Bundled.{w} L.Structure)}

/-- A first-order definable class is closed under isomorphism. -/
theorem isoClosed (hK : Definable K) : IsoClosed K := by
  intro M N _ e
  obtain ⟨φ, hφ⟩ := hK
  have : Finite N := Finite.of_equiv _ e.toEquiv
  rw [hφ M, hφ N]
  exact StrongHomClass.realize_sentence e φ

/-- The complement of a first-order definable class is first-order definable. -/
theorem compl (hK : Definable K) : Definable Kᶜ := by
  obtain ⟨φ, hφ⟩ := hK
  exact ⟨φ.not, fun M _ => by rw [Set.mem_compl_iff, hφ M, Sentence.realize_not]⟩

/-- The intersection of two first-order definable classes is first-order definable. -/
theorem inter (h₁ : Definable K₁) (h₂ : Definable K₂) : Definable (K₁ ∩ K₂) := by
  obtain ⟨φ₁, hφ₁⟩ := h₁
  obtain ⟨φ₂, hφ₂⟩ := h₂
  exact ⟨φ₁ ⊓ φ₂, fun M _ => by rw [Set.mem_inter_iff, hφ₁ M, hφ₂ M, Sentence.realize_inf]⟩

/-- The union of two first-order definable classes is first-order definable. -/
theorem union (h₁ : Definable K₁) (h₂ : Definable K₂) : Definable (K₁ ∪ K₂) := by
  obtain ⟨φ₁, hφ₁⟩ := h₁
  obtain ⟨φ₂, hφ₂⟩ := h₂
  exact ⟨φ₁ ⊔ φ₂, fun M _ => by rw [Set.mem_union, hφ₁ M, hφ₂ M, Sentence.realize_sup]⟩

end Definable

/-! ### First-order reductions -/

/-- The universe of a bundled structure `Bundled.of M` is `M`. The simp set `fo_realize` uses this
to see the interpreted structure in the semantic statement of a reduction. -/
@[fo_realize]
theorem coe_bundledOf (M : Type w) [L.Structure M] :
    (Bundled.of (c := L.Structure) M : Type w) = M :=
  rfl

variable [L'.IsRelational]

/-- The structure interpreted in a finite structure is finite, also when bundled. -/
instance {ι : Type*} [Finite ι] (I : Interpretation L L' ι) (M : Type w) [L.Structure M]
    [Finite M] :
    Finite (Bundled.of (c := L'.Structure) (I.Model M)) :=
  inferInstanceAs (Finite (I.Model M))

/-- A class `K` of `L`-structures is **first-order reducible** to a class `K'` of `L'`-structures
when some first-order interpretation of `L'` in `L` maps the finite members of `K` into `K'` and
the other finite `L`-structures outside `K'`. The structures have no built-in order or numeric
predicates, and every finite `L`-structure is covered, the empty one included: this is the
order-free counterpart of first-order reducibility of ordered queries,
`Cslib.Logic.FO.Ordered.Reduces` [Immerman, Definition 2.11][Immerman1999]. -/
def Reduces (K : Set (Bundled.{w} L.Structure)) (K' : Set (Bundled.{w} L'.Structure)) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (I : Interpretation L L' ι),
    ∀ (M : Bundled.{w} L.Structure) [Finite M],
      M ∈ K ↔ Bundled.of (c := L'.Structure) (I.Model M) ∈ K'

namespace Reduces

/-- **First-order reducibility is reflexive** on classes closed under isomorphism, through the
identity interpretation. -/
theorem refl [L.IsRelational] {K : Set (Bundled.{w} L.Structure)} (hK : IsoClosed K) :
    Reduces K K :=
  ⟨Unit, inferInstance, Interpretation.id L, fun _ _ => hK Interpretation.idEquiv.symm⟩

/-- **First-order reducibility is transitive** when the last class is closed under isomorphism,
through the composite interpretation [Immerman, Exercise 2.15][Immerman1999]. -/
theorem trans [L''.IsRelational] {K : Set (Bundled.{w} L.Structure)}
    {K' : Set (Bundled.{w} L'.Structure)} {K'' : Set (Bundled.{w} L''.Structure)}
    (h : Reduces K K') (h' : Reduces K' K'') (hK'' : IsoClosed K'') : Reduces K K'' := by
  obtain ⟨ι, _, I, hI⟩ := h
  obtain ⟨κ, _, J, hJ⟩ := h'
  refine ⟨κ × ι, inferInstance, J.comp I, fun M _ => ?_⟩
  rw [hI M, hJ (Bundled.of (I.Model M))]
  exact hK'' (Interpretation.compEquiv J I)

/-- A class reducible to a class closed under isomorphism is closed under isomorphism:
isomorphic structures interpret isomorphic structures. -/
theorem isoClosed {K : Set (Bundled.{w} L.Structure)} {K' : Set (Bundled.{w} L'.Structure)}
    (h : Reduces K K') (hK' : IsoClosed K') : IsoClosed K := by
  intro M N _ e
  obtain ⟨ι, _, I, hI⟩ := h
  have : Finite N := Finite.of_equiv _ e.toEquiv
  rw [hI M, hI N]
  exact hK' (I.mapEquiv e)

/-- A first-order reduction through a given interpretation. -/
theorem of_interpretation {K : Set (Bundled.{w} L.Structure)} {K' : Set (Bundled.{w} L'.Structure)}
    {ι : Type} [Finite ι] (I : Interpretation L L' ι)
    (h : ∀ (M : Bundled.{w} L.Structure) [Finite M],
      M ∈ K ↔ Bundled.of (c := L'.Structure) (I.Model M) ∈ K') :
    Reduces K K' :=
  ⟨ι, inferInstance, I, h⟩

/-- A first-order reduction from `K` to `K'` is also a reduction from `Kᶜ` to `K'ᶜ`. -/
theorem compl {K : Set (Bundled.{w} L.Structure)} {K' : Set (Bundled.{w} L'.Structure)}
    (h : Reduces K K') : Reduces Kᶜ K'ᶜ :=
  let ⟨ι, hι, I, hI⟩ := h
  ⟨ι, hι, I, fun M _ => not_congr (hI M)⟩

end Reduces

/-! ### One-dimensional reductions -/

/-- For a one-dimensional interpretation whose domain formula always holds, the interpreted
structure belongs to a class closed under isomorphism exactly when the structure defined on the
input universe does. -/
theorem Interpretation.mem_iff_unitStructure {K' : Set (Bundled.{w} L'.Structure)}
    (hK' : IsoClosed K') (I : Interpretation L L' Unit) (M : Type w) [L.Structure M] [Finite M]
    (hdom : ∀ x : M, I.domain.Realize fun _ => x) :
    Bundled.of (c := L'.Structure) (I.Model M) ∈ K' ↔
      (⟨M, I.unitStructure M⟩ : Bundled.{w} L'.Structure) ∈ K' :=
  hK' (I.unitModelEquiv M hdom)

/-- A first-order reduction through a one-dimensional interpretation whose domain formula holds of
every element of every finite structure, to a class closed under isomorphism, stated on the input
universe: `M ∈ K` exactly when `M`, with the relations defined by the interpretation, belongs to
`K'`. -/
theorem Reduces.of_unitStructure {K : Set (Bundled.{w} L.Structure)}
    {K' : Set (Bundled.{w} L'.Structure)} (I : Interpretation L L' Unit)
    (h : ∀ (M : Bundled.{w} L.Structure) [Finite M],
      M ∈ K ↔ (⟨M, I.unitStructure M⟩ : Bundled.{w} L'.Structure) ∈ K')
    (hK' : IsoClosed K') (hdom : ∀ (M : Type w) [L.Structure M] [Finite M] (x : M),
      I.domain.Realize fun _ => x) :
    Reduces K K' :=
  .of_interpretation I fun M _ => (h M).trans (I.mem_iff_unitStructure hK' M (hdom M)).symm

/-! ### Reductions on tuples -/

/-- For an interpretation whose domain formula holds of every tuple, the interpreted structure
belongs to a class closed under isomorphism exactly when the structure defined on the tuples of the
input universe does. -/
theorem Interpretation.mem_iff_tupleStructure {K' : Set (Bundled.{w} L'.Structure)}
    (hK' : IsoClosed K') {ι : Type} [Finite ι] (I : Interpretation L L' ι) (M : Type w)
    [L.Structure M] [Finite M] (hdom : ∀ x : ι → M, I.domain.Realize x) :
    Bundled.of (c := L'.Structure) (I.Model M) ∈ K' ↔
      (⟨ι → M, I.tupleStructure M⟩ : Bundled.{w} L'.Structure) ∈ K' :=
  hK' (I.tupleModelEquiv M hdom)

/-- A first-order reduction through an interpretation whose domain formula holds of every tuple
of every finite structure, to a class closed under isomorphism, stated on the tuples of the input
universe: `M ∈ K` exactly when the tuples `ι → M`, with the relations defined by the
interpretation, belong to `K'`. -/
theorem Reduces.of_tupleStructure {K : Set (Bundled.{w} L.Structure)}
    {K' : Set (Bundled.{w} L'.Structure)} {ι : Type} [Finite ι] (I : Interpretation L L' ι)
    (h : ∀ (M : Bundled.{w} L.Structure) [Finite M],
      M ∈ K ↔ (⟨ι → M, I.tupleStructure M⟩ : Bundled.{w} L'.Structure) ∈ K')
    (hK' : IsoClosed K') (hdom : ∀ (M : Type w) [L.Structure M] [Finite M] (x : ι → M),
      I.domain.Realize x) :
    Reduces K K' :=
  .of_interpretation I fun M _ => (h M).trans (I.mem_iff_tupleStructure hK' M (hdom M)).symm

/-- **First-order definability is closed under first-order reductions**: if `K` reduces to a
class `K'` defined by `φ`, then `K` is defined by the pullback of `φ`
[Immerman, Framework 3.12][Immerman1999]. -/
theorem Definable.of_reduces {K : Set (Bundled.{w} L.Structure)}
    {K' : Set (Bundled.{w} L'.Structure)} (hK' : Definable K') (h : Reduces K K') :
    Definable K := by
  obtain ⟨ι, _, I, hI⟩ := h
  obtain ⟨φ, hφ⟩ := hK'
  exact ⟨I.onSentence φ, fun M _ => by
    rw [hI M, hφ (Bundled.of (I.Model M)), Interpretation.realize_onSentence]
    rfl⟩

end Cslib.Logic.FO
