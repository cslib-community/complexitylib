/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.DomainInterpretation
public import Complexity.Logics.FirstOrder.Ordered.FullTuple

/-!
# Numeric certificates for ordered interpretations

A first-order query on ordered structures must include first-order definitions of the numeric
relations and constants of its image [Immerman1999, Remark 1.32]. Without the assumption that the
domain formula is `true`, these need not exist: target `BIT` need not be first-order definable
[Immerman1999, the paragraph after Exercise 1.33]. A *numeric certificate* for an ordered
interpretation supplies these definitions over the source language, on domain tuples, together
with a proof that on every source they define the canonical order, `BIT` and constants `0`, `1`,
`max` of the rank numbering. The constants are thus the least, second and greatest domain tuples
in lexicographic order, as in [Immerman1999, Definition 1.26 and Exercise 1.33(1)].

A certificate turns the interpretation into an order-free interpretation of the ordered target
language with formula-defined constants, whose interpreted structure is isomorphic, by ranking, to
the image. Hence every ordered target formula pulls back to a source formula with the same truth
value [Immerman1999, Proposition 3.5].

## Main definitions

* `Cslib.Logic.FO.Ordered.DomainInterpretation.Certificate`: numeric definitions and their
  correctness on every source.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.Certificate.toInterpretation`,
  `Cslib.Logic.FO.Ordered.DomainInterpretation.Certificate.constants`,
  `Cslib.Logic.FO.Ordered.DomainInterpretation.Certificate.modelStructure`: the relational
  interpretation of the ordered target language, its constant definitions, and the interpreted
  ordered structure.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.Certificate.onFormula`,
  `Cslib.Logic.FO.Ordered.DomainInterpretation.Certificate.onSentence`: pullback of ordered
  target formulas.

## Main results

* `Cslib.Logic.FO.Ordered.DomainInterpretation.Certificate.modelEquiv`: ranking is an isomorphism
  of ordered structures onto the image.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.Certificate.realize_onFormula`,
  `Cslib.Logic.FO.Ordered.DomainInterpretation.Certificate.realize_onSentence`: truth preservation.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Definition 1.26, Remark 1.32,
  Exercise 1.33 and the paragraph after it, and Proposition 3.5.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

namespace DomainInterpretation

variable {L L' : Language} {k : ℕ}

/-- A **numeric certificate** for an ordered interpretation: source formulas defining, on domain
tuples, the canonical order, `BIT` and numeric constants of the rank numbering, with a proof that
they do so on every source. -/
structure Certificate (I : DomainInterpretation L L' k) where
  /-- The definition of the target order on two blocks of `k` variables. -/
  le : (language L).Formula (Fin 2 × Fin k)
  /-- The definition of target `BIT` on two blocks of `k` variables. -/
  bit : (language L).Formula (Fin 2 × Fin k)
  /-- The definition of each target constant; domain membership is imposed separately. -/
  const : NumericFunction 0 → (language L).Formula (Fin k)
  /-- The order formula compares ranks. -/
  realize_le : ∀ (M : Structure L) (v : Fin 2 → Fin (I.card M)),
    le.Realize (fun p => I.unrank M (v p.1) p.2) ↔ v 0 ≤ v 1
  /-- The `BIT` formula is `BIT` of ranks. -/
  realize_bit : ∀ (M : Structure L) (v : Fin 2 → Fin (I.card M)),
    bit.Realize (fun p => I.unrank M (v p.1) p.2) ↔ (v 0).val.testBit (v 1).val = true
  /-- The constant formulas select the domain tuples of ranks `0`, `1` and `card - 1`. -/
  realize_const : ∀ (M : Structure L) (c : NumericFunction 0) (i : Fin (I.card M)),
    (const c).Realize (I.unrank M i) ↔ i.val = c.index (I.card M)

namespace Certificate

variable {I : DomainInterpretation L L' k} (C : I.Certificate)

/-- The relational interpretation of the ordered target language: the domain and relations of
`I`, with the certificate's order and `BIT`. -/
def toInterpretation :
    Interpretation (language L) (relationalLanguage L') (Fin k) where
  domain := I.domain
  rel
    | .inl R => I.rel R
    | .inr .le => C.le
    | .inr .bit => C.bit

/-- The certificate's definitions of the target constants. -/
def constants : C.toInterpretation.WithConstants (NumericFunction 0) where
  constant := C.const

variable {M : Structure L}

/-- Each certificate constant selects the domain tuple of its rank. -/
theorem constants_valid (hI : I.Admissible) : C.constants.Valid (Fin M.size) := by
  intro c
  refine ⟨⟨I.unrank M ⟨c.index (I.card M), c.index_lt (hI M)⟩, realize_domain_unrank _⟩,
    (C.realize_const M c _).mpr rfl, ?_⟩
  intro x hx
  apply Interpretation.Model.ext
  change x.val = I.unrank M _
  rw [← unrank_rank x.property] at hx ⊢
  exact congrArg _ (Fin.ext ((C.realize_const M c _).mp hx))

/-- The rank of the tuple selected by `C.constants` for `c` is `c.index (I.card M)`. -/
theorem val_rank_value (hI : I.Admissible) (c : NumericFunction 0) :
    (I.rank M (C.constants.value (C.constants_valid hI) c).val
      (C.constants.value (C.constants_valid hI) c).property).val = c.index (I.card M) := by
  have h := C.constants.value_spec (C.constants_valid hI (M := M)) c
  rw [← unrank_rank (C.constants.value (C.constants_valid hI) c).property] at h
  exact (C.realize_const M c _).mp h

variable [L'.IsRelational]

/-- The interpreted ordered structure, with the certificate's constants. -/
@[instance_reducible]
noncomputable def modelStructure (hI : I.Admissible) :
    (language L').Structure (C.toInterpretation.Model (Fin M.size)) :=
  letI := C.constants.modelStructure (C.constants_valid hI (M := M))
  (constantsLanguageMap L').reduct _

/-- **Ranking is an isomorphism** from the interpreted ordered structure onto the image, including
the canonical order, `BIT` and constants. -/
noncomputable def modelEquiv (hI : I.Admissible) :
    letI := C.modelStructure hI (M := M)
    C.toInterpretation.Model (Fin M.size) ≃[language L'] I.map hI M := by
  letI := C.modelStructure hI (M := M)
  refine
    { toFun := fun x => I.rank M x.val x.property
      invFun := fun i => ⟨I.unrank M i, realize_domain_unrank i⟩
      left_inv := fun x => Interpretation.Model.ext (unrank_rank x.property)
      right_inv := rank_unrank
      map_fun' := ?_
      map_rel' := ?_ }
  · intro r f x
    cases f with
    | inl f => exact isEmptyElim f
    | inr f =>
      cases f <;> apply Fin.ext
      · exact C.val_rank_value hI .zero
      · exact C.val_rank_value hI .one
      · exact C.val_rank_value hI .max
  · intro r R x
    have hv : (fun p : Fin r × Fin k => I.unrank M (I.rank M (x p.1).val (x p.1).property) p.2) =
        fun p => (x p.1).val p.2 := by
      funext p
      exact congrFun (unrank_rank (x p.1).property) p.2
    cases R with
    | inl R =>
      change (I.rel R).Realize (fun p => I.unrank M (I.rank M (x p.1).val (x p.1).property) p.2) ↔
        (I.rel R).Realize (fun p => (x p.1).val p.2)
      rw [hv]
    | inr R =>
      cases R
      · change I.rank M (x 0).val (x 0).property ≤ I.rank M (x 1).val (x 1).property ↔
          C.le.Realize (fun p => (x p.1).val p.2)
        rw [← hv]
        exact (C.realize_le M fun a => I.rank M (x a).val (x a).property).symm
      · change (I.rank M (x 0).val (x 0).property).val.testBit
            (I.rank M (x 1).val (x 1).property).val = true ↔
          C.bit.Realize (fun p => (x p.1).val p.2)
        rw [← hv]
        exact (C.realize_bit M fun a => I.rank M (x a).val (x a).property).symm

/-- `C.modelEquiv hI` maps a domain tuple to its rank in `I.map hI M`. -/
theorem modelEquiv_apply (hI : I.Admissible)
    (x : C.toInterpretation.Model (Fin M.size)) :
    C.modelEquiv hI x = I.rank M x.val x.property :=
  rfl

variable {α : Type*}

/-- Pull back an ordered target formula along a certified interpretation. -/
noncomputable def onFormula (φ : (language L').Formula α) : (language L).Formula (α × Fin k) :=
  C.constants.onFormula ((constantsLanguageMap L').onFormula φ)

/-- **Pullback preserves truth**: the pullback holds of the domain tuples of some ranks exactly
when the formula holds of these ranks in the image. -/
theorem realize_onFormula (hI : I.Admissible) (φ : (language L').Formula α)
    (v : α → I.map hI M) :
    (C.onFormula φ).Realize (fun p => I.unrank M (v p.1) p.2) ↔ φ.Realize v := by
  let := C.constants.modelStructure (C.constants_valid hI (M := M))
  let := C.modelStructure hI (M := M)
  let v' : α → C.toInterpretation.Model (Fin M.size) :=
    fun a => ⟨I.unrank M (v a), realize_domain_unrank (v a)⟩
  change (C.constants.onFormula ((constantsLanguageMap L').onFormula φ)).Realize
      (fun p => (v' p.1).val p.2) ↔ _
  rw [C.constants.realize_onFormula (C.constants_valid hI), LHom.realize_onFormula]
  refine (StrongHomClass.realize_formula (C.modelEquiv hI) φ).symm.trans ?_
  apply iff_of_eq
  congr 1
  funext a
  exact rank_unrank (v a)

/-- Pull back an ordered target sentence along a certified interpretation. -/
noncomputable def onSentence (φ : (language L').Sentence) : (language L).Sentence :=
  (C.onFormula φ).relabel Prod.fst

/-- **Pullback preserves sentence truth** in the image. -/
theorem realize_onSentence (hI : I.Admissible) (φ : (language L').Sentence) :
    (C.onSentence φ).Realize M ↔ φ.Realize (I.map hI M) := by
  rw [onSentence, Sentence.Realize, Formula.realize_relabel, Sentence.Realize]
  convert C.realize_onFormula hI φ (fun a => a.elim) using 1
  · exact iff_of_eq (congrArg (C.onFormula φ).Realize (Subsingleton.elim _ _))
  · exact iff_of_eq (congrArg (Formula.Realize (M := I.map hI M) φ) (Subsingleton.elim _ _))

end Certificate

end DomainInterpretation

end Cslib.Logic.FO.Ordered
