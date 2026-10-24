/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.DomainInterpretation.Composition
public import Complexity.Computability.Complexity.Reduction.ManyOne

/-!
# First-order reductions between ordered queries

An ordered query `K` first-order reduces to `K'`, written `K ≤_fo K'`, when some first-order query
on ordered structures maps the members of `K` to members of `K'` and the other structures outside
`K'` [Immerman1999, Definition 2.11]. A first-order query on ordered structures includes
first-order definitions of the numeric relations and constants of its image [Immerman1999,
Remark 1.32]; with a domain formula other than `true` these are a genuine obligation, since target
`BIT` need not be definable [Immerman1999, the paragraph after Exercise 1.33]. Here the admissible
maps are therefore the images `I.map hI` of admissible ordered interpretations `I` that have a
numeric certificate, and `Ordered.Reduces` is the many-one reducibility by these maps.

Reflexivity uses the identity interpretation of dimension one. Transitivity composes
interpretations, substituting the inner numeric definitions into the outer formulas
[Immerman1999, Proposition 1.28 and Exercise 2.15(1)]. Definability pulls back along reductions.

## Main definitions

* `Cslib.Logic.FO.Ordered.IsFirstOrderMap`: the images of certified admissible interpretations.
* `Cslib.Logic.FO.Ordered.Reduces`: first-order reducibility of ordered queries.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.id`: the identity interpretation.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.Certificate.id`: its numeric certificate.

## Main results

* `Cslib.Logic.FO.Ordered.Reduces.refl`, `Cslib.Logic.FO.Ordered.Reduces.trans`: `≤_fo` is a
  preorder.
* `Cslib.Logic.FO.Ordered.Reduces.compl`: reductions between complements.
* `Cslib.Logic.FO.Ordered.IsFirstOrderMap.isDomainMap`: first-order maps are domain maps.
* `Cslib.Logic.FO.Ordered.Definable.of_reduces`: first-order definability pulls back.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Proviso 1.15, Definition 1.26,
  Proposition 1.28, Remark 1.32, Exercise 1.33 and the paragraph after it, Definition 2.11 and
  Exercise 2.15(1).
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure Cslib.Complexity

/-! ### The identity interpretation -/

namespace DomainInterpretation

variable (L : Language)

/-- The identity interpretation of dimension one: every element is in the domain and every input
relation defines itself. -/
def id : DomainInterpretation L L 1 where
  domain := ⊤
  rel R := (LHom.sumInl : L →ᴸ language L).onFormula (R.formula fun i => .var (i, 0))

variable {L} {M : Structure L}

private theorem exists_unrank_id :
    ∃ h : (id L).card M = M.size, ∀ i, (id L).unrank M i = fun _ => Fin.cast h i :=
  unrank_eq_of_strictMono (fun i _ => i) (fun _ => Formula.realize_top.mpr trivial)
    (fun x _ => ⟨x 0, funext fun i => congrArg x (Subsingleton.elim 0 i)⟩)
    (fun _ _ h => by simpa [lexRank_apply] using h)

/-- The identity interpretation on `M` has `M.size` domain elements. -/
theorem card_id (M : Structure L) : (id L).card M = M.size :=
  exists_unrank_id.1

/-- The `i`-th domain tuple of `id L` is the constant tuple at `i`. -/
theorem unrank_id (i : Fin ((id L).card M)) : (id L).unrank M i = fun _ => Fin.cast (card_id M) i :=
  exists_unrank_id.2 i

/-- The identity interpretation is admissible on every ordered structure. -/
theorem admissible_id : (id L).Admissible :=
  fun M => (card_id M).symm ▸ M.size_ge_two

variable (L) in
/-- The identity interpretation defines the canonical numerics directly. -/
def Certificate.id : (DomainInterpretation.id L).Certificate where
  le := Ordered.le L (.var (0, 0)) (.var (1, 0))
  bit := Ordered.bit L (.var (0, 0)) (.var (1, 0))
  const c := Term.equal (.var 0)
    (match c with | .zero => Ordered.zero L | .one => Ordered.one L | .max => Ordered.max L)
  realize_le M v := by
    simp only [Ordered.realize_le, Term.realize_var, unrank_id]
    exact Fin.cast_le_cast _
  realize_bit M v := by
    simp only [Ordered.realize_bit, Term.realize_var, unrank_id, Fin.val_cast]
  realize_const M c i := by
    simp only [Formula.realize_equal, Term.realize_var, unrank_id, Fin.ext_iff, Fin.val_cast]
    cases c
    · exact Iff.rfl
    · exact Iff.rfl
    · change i.val = M.size - 1 ↔ i.val = (DomainInterpretation.id L).card M - 1
      have := card_id M
      constructor <;> intro h <;> lia

variable [L.IsRelational]

/-- The identity interpretation maps every ordered structure to itself. -/
theorem map_id (M : Structure L) : (id L).map admissible_id M = M :=
  Structure.ext (card_id M) fun R x => by
    change ((LHom.sumInl : L →ᴸ language L).onFormula _).Realize _ ↔ _
    rw [realize_inputFormula, Formula.realize_rel]
    exact iff_of_eq (congrArg (RelMap R) (funext fun i => congrFun (unrank_id (x i)) 0))

end DomainInterpretation

/-! ### First-order reductions -/

variable {L L' L'' : Language}

/-- The maps between ordered structures given by first-order queries: images under admissible
ordered interpretations with numeric certificates. -/
def IsFirstOrderMap [L'.IsRelational] (f : Structure L → Structure L') : Prop :=
  ∃ (k : ℕ) (I : DomainInterpretation L L' k) (hI : I.Admissible),
    Nonempty I.Certificate ∧ f = I.map hI

/-- First-order maps are domain maps, forgetting the certificate. -/
theorem IsFirstOrderMap.isDomainMap [L'.IsRelational] {f : Structure L → Structure L'}
    (hf : IsFirstOrderMap f) : IsDomainMap f :=
  let ⟨k, I, hI, _, hf⟩ := hf
  ⟨k, I, hI, hf⟩

/-- The image of a certified admissible interpretation is a first-order map. -/
theorem DomainInterpretation.isFirstOrderMap [L'.IsRelational] {k : ℕ}
    {I : DomainInterpretation L L' k} (hI : I.Admissible) (C : I.Certificate) :
    IsFirstOrderMap (I.map hI) :=
  ⟨k, I, hI, ⟨C⟩, rfl⟩

/-- The identity is a first-order map. -/
theorem IsFirstOrderMap.id [L.IsRelational] : IsFirstOrderMap (_root_.id : Structure L → _) :=
  ⟨1, .id L, DomainInterpretation.admissible_id, ⟨DomainInterpretation.Certificate.id L⟩,
    funext fun M => (DomainInterpretation.map_id M).symm⟩

/-- First-order maps compose. -/
theorem IsFirstOrderMap.comp [L'.IsRelational] [L''.IsRelational] {f : Structure L → Structure L'}
    {g : Structure L' → Structure L''} (hf : IsFirstOrderMap f) (hg : IsFirstOrderMap g) :
    IsFirstOrderMap (g ∘ f) := by
  obtain ⟨k, I, hI, ⟨C⟩, rfl⟩ := hf
  obtain ⟨l, J, hJ, ⟨C'⟩, rfl⟩ := hg
  exact ⟨l * k, J.comp C, J.admissible_comp C hI hJ, ⟨C'.comp C hI⟩,
    funext fun M => (J.map_comp C hI hJ M).symm⟩

/-- **First-order reducibility** of ordered queries, `K ≤_fo K'`: many-one reducibility by
first-order maps [Immerman1999, Definition 2.11 and Remark 1.32]. This is the ordered counterpart
of the order-free `Cslib.Logic.FO.Reduces`.

The target language is relational: the image carries only the canonical numeric constants, and
Immerman's formulas for target constant symbols are not handled. The image is always ordered
lexicographically, Remark 1.32's default ("unless we state otherwise"), so this is the
lexicographic case of `≤_fo`; reductions whose image order is another definable order are not
covered. -/
def Reduces [L'.IsRelational] (K : Query L) (K' : Query L') : Prop :=
  ManyOneReducibleBy IsFirstOrderMap K K'

namespace Reduces

/-- **First-order reducibility is reflexive.** -/
@[refl] theorem refl [L.IsRelational] (K : Query L) : Reduces K K :=
  ManyOneReducibleBy.refl IsFirstOrderMap.id K

/-- **First-order reducibility is transitive** [Immerman1999, Exercise 2.15(1)]. -/
theorem trans [L'.IsRelational] [L''.IsRelational] {K : Query L} {K' : Query L'}
    {K'' : Query L''} (h : Reduces K K') (h' : Reduces K' K'') : Reduces K K'' :=
  ManyOneReducibleBy.trans (fun _ _ hf hg => hf.comp hg) h h'

/-- A reduction of `K` to `K'` reduces the complement of `K` to that of `K'`. -/
theorem compl [L'.IsRelational] {K : Query L} {K' : Query L'} (h : Reduces K K') :
    Reduces Kᶜ K'ᶜ :=
  ManyOneReducibleBy.compl h

/-- A certified admissible interpretation that maps exactly the members of `K` into `K'` reduces
`K` to `K'`. -/
theorem of_interpretation [L'.IsRelational] {K : Query L} {K' : Query L'} {k : ℕ}
    {I : DomainInterpretation L L' k} (hI : I.Admissible) (C : I.Certificate)
    (h : ∀ M, M ∈ K ↔ I.map hI M ∈ K') : Reduces K K' :=
  ⟨I.map hI, I.isFirstOrderMap hI C, h⟩

end Reduces

/-- **First-order definability pulls back along first-order reductions**, by the certified pullback
of the defining sentence. -/
theorem Definable.of_reduces [L'.IsRelational] {K : Query L} {K' : Query L'}
    (h : Reduces K K') (hK' : Definable K') : Definable K := by
  obtain ⟨f, ⟨k, I, hI, ⟨C⟩, rfl⟩, hf⟩ := h
  obtain ⟨φ, hφ⟩ := hK'
  exact ⟨C.onSentence φ, fun M => (hf M).trans ((hφ _).trans (C.realize_onSentence hI φ).symm)⟩

end Cslib.Logic.FO.Ordered
