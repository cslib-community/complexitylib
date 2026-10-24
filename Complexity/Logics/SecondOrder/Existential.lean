/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Reduction
public import Mathlib.Basic.Finite.Sum

/-!
# Existential second-order logic

An existential second-order sentence `∃ R₁ … Rₖ, φ` over a language `L` quantifies finitely many
relation variables `R₁, …, Rₖ` of given arities over a first-order sentence `φ` of `L` extended by
them. It holds in an `L`-structure `M` when some relations `R₁, …, Rₖ` on `M` make `φ` true, that
is, when some expansion of `M` by these relations is a model of `φ` [Fagin, Section 2][Fagin1974],
[Immerman, Section 7.1][Immerman1999]. The relation variables form the relational language
`ESO.varLanguage arity`, and the sentence `φ` is a sentence of Mathlib's first-order logic over
`L.sum (ESO.varLanguage arity)`.

A class of structures is existential second-order definable (`ESO.Definable`) when some
existential second-order sentence holds in exactly its finite members; Fagin calls these classes
generalized spectra, and his theorem identifies them with the classes decidable in nondeterministic
polynomial time. The existential second-order definable classes contain the first-order definable
ones, are closed under intersection and union, and are closed under isomorphism.

## Main definitions

* `Cslib.Logic.ESO.varLanguage`, `Cslib.Logic.ESO.varLanguage.structure`: the relational language
  of relation variables of given arities and its interpretation on a domain.
* `Cslib.Logic.ESO.varLanguage.sumInl`, `Cslib.Logic.ESO.varLanguage.sumInr`: the embeddings of two
  blocks of relation variables into their sum.
* `Cslib.Logic.ESO.Sentence`, `Cslib.Logic.ESO.Sentence.expansionEquiv`: existential second-order
  sentences, with `Sentence.Realize` and the isomorphism of expanded structures.
* `Cslib.Logic.ESO.Sentence.ofSentence`: a first-order sentence as an existential second-order one.
* `Cslib.Logic.ESO.Definable`: existential second-order definability of a class of finite
  structures.

## Main results

* `Cslib.Logic.ESO.Sentence.realize_ofSentence`, `Cslib.Logic.ESO.Sentence.realize_inf`,
  `Cslib.Logic.ESO.Sentence.realize_sup`: semantics of the embedding of first-order logic and of
  conjunction and disjunction.
* `Cslib.Logic.ESO.Sentence.realize_iff_of_equiv`: invariance under isomorphism.
* `Cslib.Logic.ESO.Definable.of_fo`, `Cslib.Logic.ESO.Definable.inter`,
  `Cslib.Logic.ESO.Definable.union`, `Cslib.Logic.ESO.Definable.isoClosed`.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v w w'

namespace Cslib.Logic.ESO

open FirstOrder Language Structure CategoryTheory

/-! ### Relation variables -/

/-- The relational language with a relation symbol of arity `arity i` for each `i : ι`: the
relation variables of an existential second-order sentence. -/
def varLanguage {ι : Type} (arity : ι → ℕ) : Language.{0, 0} where
  Functions _ := Empty
  Relations n := {i : ι // arity i = n}

/-- `varLanguage arity` is a relational language. -/
instance {ι : Type} (arity : ι → ℕ) : (varLanguage arity).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

/-- The structure interpreting each relation variable `i` as the relation `R i`. -/
@[instance_reducible]
def varLanguage.structure {ι : Type} {arity : ι → ℕ} {M : Type w}
    (R : ∀ i, Set (Fin (arity i) → M)) : (varLanguage arity).Structure M where
  RelMap r x := x ∘ Fin.cast r.2 ∈ R r.1

namespace varLanguage

variable {ι ι' : Type} {arity : ι → ℕ} {arity' : ι' → ℕ} {M : Type w}

/-- In `varLanguage.structure R`, the relation symbol `r` holds of `x` iff `x ∘ Fin.cast r.2`
belongs to `R r.1`. -/
theorem relMap_structure (R : ∀ i, Set (Fin (arity i) → M)) {n : ℕ}
    (r : (varLanguage arity).Relations n) (x : Fin n → M) :
    (varLanguage.structure R).RelMap r x ↔ x ∘ Fin.cast r.2 ∈ R r.1 :=
  Iff.rfl

/-- The relation variables of `arity` among those of `Sum.elim arity arity'`. -/
def sumInl : varLanguage arity →ᴸ varLanguage (Sum.elim arity arity') where
  onRelation _ r := ⟨.inl r.1, r.2⟩

/-- The relation variables of `arity'` among those of `Sum.elim arity arity'`. -/
def sumInr : varLanguage arity' →ᴸ varLanguage (Sum.elim arity arity') where
  onRelation _ r := ⟨.inr r.1, r.2⟩

/-- `varLanguage.structure R` is an expansion along `sumInl` of the structure for the left
relation variables. -/
theorem sumInl_isExpansionOn (R : ∀ i, Set (Fin (Sum.elim arity arity' i) → M)) :
    @LHom.IsExpansionOn _ _ (sumInl (arity' := arity')) M
      (varLanguage.structure fun i => R (.inl i)) (varLanguage.structure R) :=
  @LHom.IsExpansionOn.mk _ _ _ M (varLanguage.structure _) (varLanguage.structure _)
    (fun f => isEmptyElim f) fun _ _ => rfl

/-- `varLanguage.structure R` is an expansion along `sumInr` of the structure for the right
relation variables. -/
theorem sumInr_isExpansionOn (R : ∀ i, Set (Fin (Sum.elim arity arity' i) → M)) :
    @LHom.IsExpansionOn _ _ (sumInr (arity := arity)) M
      (varLanguage.structure fun i => R (.inr i)) (varLanguage.structure R) :=
  @LHom.IsExpansionOn.mk _ _ _ M (varLanguage.structure _) (varLanguage.structure _)
    (fun f => isEmptyElim f) fun _ _ => rfl

end varLanguage

/-! ### Sentences -/

/-- An **existential second-order sentence** `∃ R₁ … Rₖ, φ` over `L`: finitely many relation
variables with their arities, and a first-order sentence `φ` of `L` extended by them. -/
structure Sentence (L : Language.{u, v}) where
  /-- The relation variables. -/
  Var : Type
  [finite : Finite Var]
  /-- The arity of each relation variable. -/
  arity : Var → ℕ
  /-- The first-order part, a sentence of `L` extended by the relation variables. -/
  matrix : (L.sum (varLanguage arity)).Sentence

attribute [instance] Sentence.finite

namespace Sentence

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]

/-- An existential second-order sentence holds in `M` when some relations on `M`, interpreting
its relation variables, make its first-order part true. -/
def Realize (Φ : Sentence L) (M : Type w) [L.Structure M] : Prop :=
  ∃ R : ∀ i, Set (Fin (Φ.arity i) → M), letI := varLanguage.structure R; M ⊨ Φ.matrix

/-- A first-order sentence, as an existential second-order sentence without relation variables. -/
def ofSentence (φ : L.Sentence) : Sentence L where
  Var := Empty
  arity := Empty.elim
  matrix := LHom.sumInl.onSentence φ

/-- The embedding of first-order logic preserves truth. -/
@[simp]
theorem realize_ofSentence (φ : L.Sentence) : (ofSentence φ).Realize M ↔ M ⊨ φ := by
  refine ⟨fun ⟨R, h⟩ => ?_, fun h => ⟨fun i => i.elim, ?_⟩⟩
  · let _ := varLanguage.structure R
    exact (LHom.realize_onSentence M LHom.sumInl φ).1 h
  · let _ := varLanguage.structure (M := M) (arity := (ofSentence φ).arity) fun i => i.elim
    exact (LHom.realize_onSentence M LHom.sumInl φ).2 h

/-- The conjunction of two existential second-order sentences, which quantifies the relation
variables of both. -/
instance : Min (Sentence L) where
  min Φ Ψ :=
    { Var := Φ.Var ⊕ Ψ.Var
      arity := Sum.elim Φ.arity Ψ.arity
      matrix := (LHom.sumMap (LHom.id L) varLanguage.sumInl).onSentence Φ.matrix ⊓
        (LHom.sumMap (LHom.id L) varLanguage.sumInr).onSentence Ψ.matrix }

/-- The disjunction of two existential second-order sentences, which quantifies the relation
variables of both. -/
instance : Max (Sentence L) where
  max Φ Ψ :=
    { Var := Φ.Var ⊕ Ψ.Var
      arity := Sum.elim Φ.arity Ψ.arity
      matrix := (LHom.sumMap (LHom.id L) varLanguage.sumInl).onSentence Φ.matrix ⊔
        (LHom.sumMap (LHom.id L) varLanguage.sumInr).onSentence Ψ.matrix }

section Connectives

variable {Φ Ψ : Sentence L}

/-- Relations for the variables of `Φ ⊓ Ψ` restrict to relations for the variables of `Φ`. -/
theorem realize_onSentence_sumInl (R : ∀ i, Set (Fin (Sum.elim Φ.arity Ψ.arity i) → M)) :
    (letI := varLanguage.structure R;
      M ⊨ (LHom.sumMap (LHom.id L) (varLanguage.sumInl (arity' := Ψ.arity))).onSentence
        Φ.matrix) ↔
      letI := varLanguage.structure (arity := Φ.arity) fun i => R (.inl i)
      M ⊨ Φ.matrix :=
  @LHom.realize_onSentence _ _ M (@sumStructure _ _ M _ (varLanguage.structure _))
    (@sumStructure _ _ M _ (varLanguage.structure R)) _
    (@LHom.sumMap_isExpansionOn _ _ (LHom.id L) _ _ varLanguage.sumInl M _ _
      (varLanguage.structure _) (varLanguage.structure R) (LHom.id_isExpansionOn M)
      (varLanguage.sumInl_isExpansionOn R)) Φ.matrix

/-- Relations for the variables of `Φ ⊓ Ψ` restrict to relations for the variables of `Ψ`. -/
theorem realize_onSentence_sumInr (R : ∀ i, Set (Fin (Sum.elim Φ.arity Ψ.arity i) → M)) :
    (letI := varLanguage.structure R;
      M ⊨ (LHom.sumMap (LHom.id L) (varLanguage.sumInr (arity := Φ.arity))).onSentence
        Ψ.matrix) ↔
      letI := varLanguage.structure (arity := Ψ.arity) fun i => R (.inr i)
      M ⊨ Ψ.matrix :=
  @LHom.realize_onSentence _ _ M (@sumStructure _ _ M _ (varLanguage.structure _))
    (@sumStructure _ _ M _ (varLanguage.structure R)) _
    (@LHom.sumMap_isExpansionOn _ _ (LHom.id L) _ _ varLanguage.sumInr M _ _
      (varLanguage.structure _) (varLanguage.structure R) (LHom.id_isExpansionOn M)
      (varLanguage.sumInr_isExpansionOn R)) Ψ.matrix

/-- **Conjunction**: `Φ ⊓ Ψ` holds exactly when both `Φ` and `Ψ` hold. -/
@[simp]
theorem realize_inf : (Φ ⊓ Ψ).Realize M ↔ Φ.Realize M ∧ Ψ.Realize M := by
  constructor
  · rintro ⟨R, h⟩
    let _ := varLanguage.structure R
    replace h := (FirstOrder.Language.Sentence.realize_inf M).1 h
    exact ⟨⟨_, (realize_onSentence_sumInl R).1 h.1⟩, ⟨_, (realize_onSentence_sumInr R).1 h.2⟩⟩
  · rintro ⟨⟨R₁, h₁⟩, ⟨R₂, h₂⟩⟩
    let R : ∀ i, Set (Fin (Sum.elim Φ.arity Ψ.arity i) → M) := Sum.rec R₁ R₂
    let _ := varLanguage.structure R
    exact ⟨R, (FirstOrder.Language.Sentence.realize_inf M).2
      ⟨(realize_onSentence_sumInl R).2 h₁, (realize_onSentence_sumInr R).2 h₂⟩⟩

/-- **Disjunction**: `Φ ⊔ Ψ` holds exactly when `Φ` or `Ψ` holds. -/
@[simp]
theorem realize_sup : (Φ ⊔ Ψ).Realize M ↔ Φ.Realize M ∨ Ψ.Realize M := by
  constructor
  · rintro ⟨R, h⟩
    let _ := varLanguage.structure R
    rcases (FirstOrder.Language.Sentence.realize_sup M).1 h with h | h
    · exact .inl ⟨_, (realize_onSentence_sumInl R).1 h⟩
    · exact .inr ⟨_, (realize_onSentence_sumInr R).1 h⟩
  · rintro (⟨R₁, h₁⟩ | ⟨R₂, h₂⟩)
    · let R : ∀ i, Set (Fin (Sum.elim Φ.arity Ψ.arity i) → M) := Sum.rec R₁ fun _ => ∅
      let _ := varLanguage.structure R
      exact ⟨R, (FirstOrder.Language.Sentence.realize_sup M).2
        (.inl ((realize_onSentence_sumInl R).2 h₁))⟩
    · let R : ∀ i, Set (Fin (Sum.elim Φ.arity Ψ.arity i) → M) := Sum.rec (fun _ => ∅) R₂
      let _ := varLanguage.structure R
      exact ⟨R, (FirstOrder.Language.Sentence.realize_sup M).2
        (.inr ((realize_onSentence_sumInr R).2 h₂))⟩

end Connectives

/-- An isomorphism `M ≃[L] N`, together with relations on `M` and their images on `N`, is an
isomorphism of the expansions. -/
def expansionEquiv (Φ : Sentence L) (e : M ≃[L] N) (R : ∀ i, Set (Fin (Φ.arity i) → M)) :
    letI := varLanguage.structure R
    letI := varLanguage.structure fun i => {x | e.symm ∘ x ∈ R i}
    M ≃[L.sum (varLanguage Φ.arity)] N :=
  letI := varLanguage.structure R
  letI := varLanguage.structure fun i => {x | e.symm ∘ x ∈ R i}
  { e.toEquiv with
    map_fun' := fun f x => match f with
      | .inl f => e.map_fun f x
      | .inr f => isEmptyElim f
    map_rel' := fun r x => match r with
      | .inl r => e.map_rel r x
      | .inr r => by
        change e.symm ∘ (e ∘ x) ∘ Fin.cast r.2 ∈ R r.1 ↔ x ∘ Fin.cast r.2 ∈ R r.1
        simp [Function.comp_def] }

/-- An isomorphism `M ≃[L] N` transports satisfaction of an existential second-order sentence `Φ`
from `M` to `N`. -/
theorem realize_of_equiv (Φ : Sentence L) (e : M ≃[L] N) (h : Φ.Realize M) : Φ.Realize N := by
  obtain ⟨R, hR⟩ := h
  let _ := varLanguage.structure R
  let _ := varLanguage.structure fun i => {x | e.symm ∘ x ∈ R i}
  exact ⟨_, (StrongHomClass.realize_sentence (Φ.expansionEquiv e R) Φ.matrix).1 hR⟩

/-- **Existential second-order sentences are invariant under isomorphism.** -/
theorem realize_iff_of_equiv (Φ : Sentence L) (e : M ≃[L] N) : Φ.Realize M ↔ Φ.Realize N :=
  ⟨Φ.realize_of_equiv e, Φ.realize_of_equiv e.symm⟩

end Sentence

/-! ### Definable classes -/

variable {L : Language.{u, v}}

/-- A class of structures is **existential second-order definable** when some existential
second-order sentence holds in exactly its finite members, among all finite structures: it is a
generalized spectrum [Fagin, Section 2][Fagin1974]. -/
def Definable (K : Set (Bundled.{w} L.Structure)) : Prop :=
  ∃ Φ : Sentence L, ∀ (M : Bundled.{w} L.Structure) [Finite M], M ∈ K ↔ Φ.Realize M

namespace Definable

variable {K K₁ K₂ : Set (Bundled.{w} L.Structure)}

/-- **First-order definable classes are existential second-order definable.** -/
theorem of_fo (hK : FO.Definable K) : Definable K := by
  obtain ⟨φ, hφ⟩ := hK
  exact ⟨.ofSentence φ, fun M _ => by rw [hφ M, Sentence.realize_ofSentence]⟩

/-- The intersection of two existential second-order definable classes is existential
second-order definable. -/
theorem inter (h₁ : Definable K₁) (h₂ : Definable K₂) : Definable (K₁ ∩ K₂) := by
  obtain ⟨Φ₁, hΦ₁⟩ := h₁
  obtain ⟨Φ₂, hΦ₂⟩ := h₂
  exact ⟨Φ₁ ⊓ Φ₂, fun M _ => by rw [Set.mem_inter_iff, hΦ₁ M, hΦ₂ M, Sentence.realize_inf]⟩

/-- The union of two existential second-order definable classes is existential second-order
definable. -/
theorem union (h₁ : Definable K₁) (h₂ : Definable K₂) : Definable (K₁ ∪ K₂) := by
  obtain ⟨Φ₁, hΦ₁⟩ := h₁
  obtain ⟨Φ₂, hΦ₂⟩ := h₂
  exact ⟨Φ₁ ⊔ Φ₂, fun M _ => by rw [Set.mem_union, hΦ₁ M, hΦ₂ M, Sentence.realize_sup]⟩

/-- An existential second-order definable class is closed under isomorphism. -/
theorem isoClosed (hK : Definable K) : IsoClosed K := by
  intro M N _ e
  obtain ⟨Φ, hΦ⟩ := hK
  have : Finite N := Finite.of_equiv _ e.toEquiv
  rw [hΦ M, hΦ N]
  exact Φ.realize_iff_of_equiv e

end Definable

end Cslib.Logic.ESO
