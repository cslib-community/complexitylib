/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.DomainInterpretation
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Reduction
import Mathlib.ModelTheory.Graph

/-!
# Tests for ordered first-order reductions with a domain formula

The client is a two-dimensional interpretation of directed graphs whose domain is the set of
pairs `(0, y)`. Its rank is `y`, so the target order, `BIT` and constants are defined from the
source numerics on the second coordinate: a genuine numeric certificate for a restricted domain.
It reverses every edge, and so reduces "an edge from `max` to `0`" to "an edge from `0` to `max`".
Its ranks equal a coordinate, so the domain does not depend on the input relations;
`CslibFrontierTests/OrderedReduction.lean` covers an input-dependent domain for the logspace
computation of the encoded map, which needs no certificate.

An interpretation whose domain has a single tuple is not admissible, and its encoded image does not
decode.
-/

namespace CslibFrontierTests.OrderedFOReduction

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered

/-- The ordered sentence asking for an edge from `s` to `t`. -/
noncomputable def edge (s t : (language Language.graph).Term Empty) :
    (language Language.graph).Sentence :=
  Relations.formula₂ (Sum.inl adj : (language Language.graph).Relations 2) s t

/-- Directed graphs with an edge from `0` to `max`. -/
noncomputable def edgeZeroMax : Query Language.graph :=
  {N | (edge (zero _) (max _)).Realize N}

/-- Directed graphs with an edge from `max` to `0`. -/
noncomputable def edgeMaxZero : Query Language.graph :=
  {N | (edge (max _) (zero _)).Realize N}

theorem realize_edge (N : Structure Language.graph) (s t : (language Language.graph).Term Empty) :
    (edge s t).Realize N ↔ RelMap adj ![s.realize (default : Empty → N), t.realize default] := by
  rw [edge, Sentence.Realize]
  exact Formula.realize_rel₂.trans Iff.rfl

/-! ### A restricted domain with a genuine certificate -/

/-- The pairs whose first coordinate is `0`, with every edge reversed on second coordinates. -/
noncomputable def reverse : DomainInterpretation Language.graph Language.graph 2 where
  domain := Term.equal (.var 0) (zero _)
  rel
    | graphRel.adj => (LHom.sumInl : Language.graph →ᴸ language Language.graph).onFormula
        (Relations.formula₂ adj (.var (1, 1)) (.var (0, 1)))

variable {M : Structure Language.graph}

/-- The zero element of a canonical ordered structure. -/
def zeroElt (M : Structure Language.graph) : Fin M.size := ⟨0, by have := M.size_ge_two; lia⟩

private theorem exists_unrank_reverse :
    ∃ h : reverse.card M = M.size, ∀ i, reverse.unrank M i = ![zeroElt M, Fin.cast h i] := by
  refine DomainInterpretation.unrank_eq_of_strictMono (fun y => ![zeroElt M, y]) ?_ ?_ ?_
  · intro y
    change (Term.equal (.var 0) (zero _) : (language Language.graph).Formula (Fin 2)).Realize _
    simp only [Formula.realize_equal, Term.realize_var]
    exact Fin.ext rfl
  · intro x hx
    change (Term.equal (.var 0) (zero _) : (language Language.graph).Formula (Fin 2)).Realize x
      at hx
    simp only [Formula.realize_equal, Term.realize_var] at hx
    refine ⟨x 1, funext fun i => ?_⟩
    fin_cases i
    · exact (Fin.ext (congrArg Fin.val hx)).symm
    · rfl
  · intro y y' h
    simpa [lexRank_apply, Fin.sum_univ_two, zeroElt] using h

theorem card_reverse (M : Structure Language.graph) : reverse.card M = M.size :=
  exists_unrank_reverse.1

theorem unrank_reverse (i : Fin (reverse.card M)) :
    reverse.unrank M i = ![zeroElt M, Fin.cast (card_reverse M) i] :=
  exists_unrank_reverse.2 i

theorem unrank_reverse_one (i : Fin (reverse.card M)) :
    reverse.unrank M i 1 = Fin.cast (card_reverse M) i := by
  rw [unrank_reverse]
  rfl

theorem admissible_reverse : reverse.Admissible :=
  fun M => (card_reverse M).symm ▸ M.size_ge_two

/-- The certificate reads the order, `BIT` and constants off the second coordinate. -/
noncomputable def reverseCertificate : reverse.Certificate where
  le := le _ (.var (0, 1)) (.var (1, 1))
  bit := bit _ (.var (0, 1)) (.var (1, 1))
  const c := Term.equal (.var 1)
    (match c with | .zero => zero _ | .one => one _ | .max => max _)
  realize_le M v := by
    simp only [Ordered.realize_le, Term.realize_var, unrank_reverse_one]
    exact Fin.cast_le_cast _
  realize_bit M v := by
    simp only [Ordered.realize_bit, Term.realize_var, unrank_reverse_one, Fin.val_cast]
  realize_const M c i := by
    simp only [Formula.realize_equal, Term.realize_var, unrank_reverse_one, Fin.ext_iff,
      Fin.val_cast]
    cases c
    · exact Iff.rfl
    · exact Iff.rfl
    · change i.val = M.size - 1 ↔ i.val = reverse.card M - 1
      have := card_reverse M
      constructor <;> intro h <;> lia

theorem relMap_map_reverse (x : Fin 2 → reverse.map admissible_reverse M) :
    RelMap adj x ↔
      RelMap adj ![Fin.cast (card_reverse M) (x 1), Fin.cast (card_reverse M) (x 0)] := by
  change ((LHom.sumInl : Language.graph →ᴸ language Language.graph).onFormula
    (Relations.formula₂ adj (Term.var ((1 : Fin 2), (1 : Fin 2))) (Term.var (0, 1)))).Realize
    (fun p : Fin 2 × Fin 2 => reverse.unrank M (x p.1) p.2) ↔ _
  rw [realize_inputFormula, Formula.realize_rel₂]
  simp only [Term.realize_var]
  exact iff_of_eq (congrArg (RelMap adj) (funext fun i => by
    fin_cases i <;> exact unrank_reverse_one _))

/-- **Reversing edges reduces an edge from `max` to `0` to an edge from `0` to `max`**, by an
interpretation with a restricted domain. -/
theorem reduces_edgeMaxZero_edgeZeroMax : Reduces edgeMaxZero edgeZeroMax := by
  refine Reduces.of_interpretation admissible_reverse reverseCertificate fun M => ?_
  change (edge (max _) (zero _)).Realize M ↔
    (edge (zero _) (max _)).Realize (reverse.map admissible_reverse M)
  rw [realize_edge, realize_edge, relMap_map_reverse]
  have := card_reverse M
  refine iff_of_eq (congrArg (RelMap adj) (funext fun i => ?_))
  fin_cases i
  · exact Fin.ext (by change M.size - 1 = reverse.card M - 1; rw [this])
  · exact Fin.ext rfl

/-- The pullback of the target sentence defines the source query. -/
example : Ordered.Definable edgeMaxZero :=
  Definable.of_reduces reduces_edgeMaxZero_edgeZeroMax ⟨edge (zero _) (max _), fun _ => Iff.rfl⟩

/-- First-order reductions compose: reversing twice. -/
example : Reduces edgeMaxZero edgeMaxZero :=
  reduces_edgeMaxZero_edgeZeroMax.trans
    (Reduces.of_interpretation admissible_reverse reverseCertificate fun M => by
      change (edge (zero _) (max _)).Realize M ↔
        (edge (max _) (zero _)).Realize (reverse.map admissible_reverse M)
      rw [realize_edge, realize_edge, relMap_map_reverse]
      have := card_reverse M
      refine iff_of_eq (congrArg (RelMap adj) (funext fun i => ?_))
      fin_cases i
      · exact Fin.ext rfl
      · exact Fin.ext (by change M.size - 1 = reverse.card M - 1; rw [this]))

example : Reduces edgeZeroMax edgeZeroMax := Reduces.refl _

/-- `Reduces.refl` is a `@[refl]` lemma. -/
example : Reduces edgeZeroMax edgeZeroMax := by rfl

example : Reduces edgeMaxZeroᶜ edgeZeroMaxᶜ := reduces_edgeMaxZero_edgeZeroMax.compl

/-- A concrete vocabulary for graphs. -/
def graphVocabulary : Vocabulary Language.graph where
  count := 1
  symbol := {
    toFun := fun _ => ⟨2, .adj⟩
    invFun := fun _ => 0
    left_inv := fun i => Subsingleton.elim _ i
    right_inv := fun r => by
      rcases r with ⟨n, R⟩
      cases R
      rfl }

/-- The encoded map commutes with partial decoding, as `ManyOneReducibleBy.lift` requires. -/
example (a : EncodedStructure) :
    decode? graphVocabulary (reverse.encodedMap graphVocabulary graphVocabulary a) =
      (decode? graphVocabulary a).map (reverse.map admissible_reverse) :=
  reverse.decode?_encodedMap graphVocabulary graphVocabulary admissible_reverse a

/-! ### A non-admissible domain -/

/-- One-dimensional interpretation whose domain is the single tuple `max`. -/
noncomputable def onlyMax : DomainInterpretation Language.graph Language.graph 1 where
  domain := Term.equal (.var 0) (max _)
  rel _ := ⊥

theorem card_onlyMax (M : Structure Language.graph) : onlyMax.card M = 1 := by
  refine (DomainInterpretation.unrank_eq_of_strictMono (I := onlyMax) (M := M)
    (fun _ _ => (max Language.graph).realize (default : Empty → Fin M.size)) ?_ ?_ ?_).1
  · exact fun _ => rfl
  · intro x hx
    refine ⟨0, funext fun i => ?_⟩
    rw [Subsingleton.elim i 0]
    exact hx.symm
  · intro i j h
    exact absurd h (by simp [Subsingleton.elim i j])

/-- A domain with one tuple is rejected. -/
theorem not_admissible_onlyMax : ¬ onlyMax.Admissible := fun h => by
  have := h ⟨2, le_refl _, ⟨fun _ => isEmptyElim ‹_›, fun _ _ => False⟩⟩
  rw [card_onlyMax] at this
  lia

/-- Its encoded images have one element, and do not decode as ordered structures. -/
example (a : EncodedStructure) :
    decode? graphVocabulary (onlyMax.encodedMap graphVocabulary graphVocabulary a) = none := by
  by_cases h : graphVocabulary.WellFormed a ∧ 2 ≤ a.1
  · refine decode?_of_not_admissible _ fun h' => ?_
    have := h'.2
    rw [onlyMax.card_encodedMap _ _ h.1 h.2, card_onlyMax] at this
    lia
  · refine decode?_of_not_admissible _ fun h' => h ?_
    exact (onlyMax.wellFormed_encodedMap_iff _ _).mp h'.1

/-! ### Full-tuple interpretations -/

/-- Pairs of vertices, with an edge between pairs whose first coordinates are adjacent. -/
noncomputable def pairs : FullTupleInterpretation Language.graph Language.graph 2 where
  rel
    | graphRel.adj => (LHom.sumInl : Language.graph →ᴸ language Language.graph).onFormula
        (Relations.formula₂ adj (.var (0, 0)) (.var (1, 0)))

example : IsFirstOrderMap (pairs.toDomainInterpretation.map
    (FullTupleInterpretation.admissible_toDomainInterpretation (by decide))) :=
  pairs.isFirstOrderMap_map_toDomainInterpretation (by decide)

example : pairs.toDomainInterpretation.encodedMap graphVocabulary graphVocabulary =
    pairs.encodedMap graphVocabulary graphVocabulary :=
  pairs.encodedMap_toDomainInterpretation graphVocabulary graphVocabulary

/-- A positive-dimensional full-tuple interpretation reduces the pullback of any query. -/
example (K' : Query Language.graph) :
    Reduces {M | pairs.toDomainInterpretation.map
      (FullTupleInterpretation.admissible_toDomainInterpretation (by decide)) M ∈ K'} K' :=
  pairs.reduces (by decide) fun _ => Iff.rfl

/-! ### First-order reductions are logspace reductions -/

/-- The restricted-domain reduction gives a logspace reduction of the encoded queries. -/
example : Cslib.Complexity.LogSpaceReducible encStructure encStructure
    (edgeMaxZero.encodedLanguage graphVocabulary) (edgeZeroMax.encodedLanguage graphVocabulary) :=
  reduces_edgeMaxZero_edgeZeroMax.logSpaceReducible graphVocabulary graphVocabulary

end CslibFrontierTests.OrderedFOReduction
