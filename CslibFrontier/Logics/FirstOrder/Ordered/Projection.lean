/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.QFNumeric
public import CslibFrontier.Logics.FirstOrder.ProjectionFormula
public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.DomainInterpretation

/-!
# First-order and quantifier-free projections of ordered structures

Immerman and Landau's first-order projections are first-order interpretations in which each
output relation is a disjunction of mutually exclusive numeric cases, each guarding a single input
literal; the guards mention no input relation. Each output bit is therefore an input bit, its
negation, or a constant, selected by numeric information alone, as in Valiant's projections. A
quantifier-free projection is a first-order projection that is also a quantifier-free
interpretation, whose numeric tests do not use `BIT`.

Here a projection is a property of a `FullTupleInterpretation`, whose universe is the set of all
`k`-tuples, as in Immerman and Landau's Definition 3.3. Each output relation must be
`ProjectionFormula.toOrdered` of a projection formula: a decision tree of numeric guards with
input literals at the leaves, whose leaf cases are mutually exclusive
(`ProjectionFormula.realize_iff_exists_case`). For first-order projections the guards are formulas
of the canonical numeric vocabulary `numericLanguage` (`≤`, `BIT`, `0`, `1`, `max`); for
quantifier-free projections they are quantifier-free formulas of `qfNumericLanguage` (`≤`,
successor, `0`, `max`), translated by `toNumeric`. Projection maps are the images of
positive-dimensional projections; they are first-order maps. Dimension zero is excluded, since
its image has one element (`not_admissible_toDomainInterpretation_zero`).

No reducibility relation, transitivity or hardness result is stated here.

## Main definitions

* `Cslib.Logic.FO.ProjectionFormula.toOrdered`: a projection formula with canonical numeric guards
  as a formula of the ordered vocabulary.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.IsProjection`,
  `Cslib.Logic.FO.Ordered.FullTupleInterpretation.IsQFProjection`: first-order and
  quantifier-free projections.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.ofProjection`,
  `Cslib.Logic.FO.Ordered.FullTupleInterpretation.ofQFProjection`: the interpretations given by
  projection formulas.
* `Cslib.Logic.FO.Ordered.IsProjectionMap`, `Cslib.Logic.FO.Ordered.IsQFProjectionMap`: images
  of positive-dimensional projections.

## Main results

* `Cslib.Logic.FO.ProjectionFormula.realize_toOrdered`: the formula is realized as the literal
  selected by the numeric structure.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.IsProjection.exists_literal`: each output bit
  is one input literal, chosen before the input relations.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.IsQFProjection.isProjection`,
  `Cslib.Logic.FO.Ordered.IsQFProjectionMap.isProjectionMap`,
  `Cslib.Logic.FO.Ordered.IsProjectionMap.isFirstOrderMap`: quantifier-free projections are
  first-order projections, which are first-order maps.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.not_admissible_toDomainInterpretation_zero`:
  dimension zero has no admissible image.

## References

* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995],
  Definitions 3.3 and 3.6 and footnote 1.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Definition 1.26 and Remark 1.32.
-/

public section

namespace Cslib.Logic.FO

open FirstOrder Language Structure Ordered

namespace ProjectionFormula

variable {L : Language} {α : Type*}

/-- A projection formula with canonical numeric guards, as a formula of the ordered vocabulary:
guards are numeric formulas and literals are input formulas. -/
def toOrdered (p : ProjectionFormula numericLanguage L α) : (language L).Formula α :=
  (LHom.sumElim LHom.sumInr LHom.sumInl : numericLanguage.sum L →ᴸ language L).onFormula
    p.toFormula

/-- On `Fin n` with `2 ≤ n`, `p.toOrdered` holds exactly when the literal selected by the
canonical numeric structure holds. -/
theorem realize_toOrdered {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]
    (p : ProjectionFormula numericLanguage L α) (x : α → Fin n) :
    p.toOrdered.Realize x ↔ (p.select x).Realize x := by
  rw [toOrdered, LHom.realize_onFormula, realize_toFormula]

end ProjectionFormula

namespace Ordered

namespace FullTupleInterpretation

variable {L L' : Language} {k : ℕ}

/-- **First-order projections** [Immerman and Landau, Definition 3.6][ImmermanLandau1995]: each
output relation is defined by a projection formula whose guards are canonical numeric formulas,
`BIT` included. -/
@[expose] def IsProjection (I : FullTupleInterpretation L L' k) : Prop :=
  ∀ {r : ℕ} (R : L'.Relations r),
    ∃ p : ProjectionFormula numericLanguage L (Fin r × Fin k), I.rel R = p.toOrdered

/-- **Quantifier-free projections** [Immerman and Landau, Definition 3.6][ImmermanLandau1995]:
each output relation is defined by a projection formula whose guards are quantifier-free formulas
of `≤`, successor, `0` and `max`, without `BIT`. -/
@[expose] def IsQFProjection (I : FullTupleInterpretation L L' k) : Prop :=
  ∀ {r : ℕ} (R : L'.Relations r),
    ∃ q : ProjectionFormula qfNumericLanguage L (Fin r × Fin k),
      q.IsQF ∧ I.rel R = (q.subst toNumeric .leaf).toOrdered

/-- The full-tuple interpretation defined by projection formulas with canonical numeric guards. -/
def ofProjection
    (p : ∀ {r : ℕ}, L'.Relations r → ProjectionFormula numericLanguage L (Fin r × Fin k)) :
    FullTupleInterpretation L L' k where
  rel R := (p R).toOrdered

/-- The full-tuple interpretation defined by projection formulas with guards in
`qfNumericLanguage`. -/
noncomputable def ofQFProjection
    (q : ∀ {r : ℕ}, L'.Relations r → ProjectionFormula qfNumericLanguage L (Fin r × Fin k)) :
    FullTupleInterpretation L L' k where
  rel R := ((q R).subst toNumeric .leaf).toOrdered

/-- The relation formulas of `ofProjection p`. -/
@[simp]
theorem rel_ofProjection
    (p : ∀ {r : ℕ}, L'.Relations r → ProjectionFormula numericLanguage L (Fin r × Fin k))
    {r : ℕ} (R : L'.Relations r) : (ofProjection p).rel R = (p R).toOrdered := by
  unfold ofProjection; rfl

/-- The relation formulas of `ofQFProjection q`. -/
@[simp]
theorem rel_ofQFProjection
    (q : ∀ {r : ℕ}, L'.Relations r → ProjectionFormula qfNumericLanguage L (Fin r × Fin k))
    {r : ℕ} (R : L'.Relations r) :
    (ofQFProjection q).rel R = ((q R).subst toNumeric .leaf).toOrdered := by
  unfold ofQFProjection; rfl

/-- Projection formulas define a first-order projection. -/
theorem isProjection_ofProjection
    (p : ∀ {r : ℕ}, L'.Relations r → ProjectionFormula numericLanguage L (Fin r × Fin k)) :
    (ofProjection p).IsProjection :=
  fun R => ⟨p R, rel_ofProjection p R⟩

/-- Quantifier-free projection formulas define a quantifier-free projection. -/
theorem isQFProjection_ofQFProjection
    (q : ∀ {r : ℕ}, L'.Relations r → ProjectionFormula qfNumericLanguage L (Fin r × Fin k))
    (hq : ∀ {r : ℕ} (R : L'.Relations r), (q R).IsQF) : (ofQFProjection q).IsQFProjection :=
  fun R => ⟨q R, hq R, rel_ofQFProjection q R⟩

/-- **Quantifier-free projections are first-order projections.** -/
theorem IsQFProjection.isProjection {I : FullTupleInterpretation L L' k} (h : I.IsQFProjection) :
    I.IsProjection := fun R =>
  let ⟨q, _, hq⟩ := h R
  ⟨q.subst toNumeric .leaf, hq⟩

/-- On `Fin n` with `2 ≤ n`, the relation formulas of `ofQFProjection q` hold exactly when the
literal selected by the canonical `qfNumericLanguage` structure holds. -/
theorem realize_rel_ofQFProjection {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]
    (q : ∀ {r : ℕ}, L'.Relations r → ProjectionFormula qfNumericLanguage L (Fin r × Fin k))
    {r : ℕ} (R : L'.Relations r) (x : Fin r × Fin k → Fin n) :
    ((ofQFProjection q).rel R).Realize x ↔ ((q R).select x).Realize x := by
  rw [rel_ofQFProjection, ProjectionFormula.toOrdered, LHom.realize_onFormula,
    ProjectionFormula.realize_subst toNumeric .leaf x x (fun g => realize_toNumeric_formula g x)
      (fun l => ProjectionFormula.realize_toFormula_leaf l x),
    ProjectionFormula.realize_toFormula]

/-- **Each output bit is one input literal** [Immerman and Landau, Definition 3.6]
[ImmermanLandau1995]. For every output relation and every address, one literal of the input
vocabulary, chosen before the input relations, has the truth value of the output bit under every
interpretation of the input relations. -/
theorem IsProjection.exists_literal {I : FullTupleInterpretation L L' k} (h : I.IsProjection)
    {n : ℕ} [Fact (2 ≤ n)] {r : ℕ} (R : L'.Relations r) (x : Fin r × Fin k → Fin n) :
    ∃ l : InputLiteral L (Fin r × Fin k),
      ∀ _ : L.Structure (Fin n), (I.rel R).Realize x ↔ l.Realize x := by
  obtain ⟨p, hp⟩ := h R
  exact ⟨p.select x, fun _ => hp ▸ p.realize_toOrdered x⟩

/-- **Dimension zero is not admissible**: its image of a two-element structure has one element. -/
theorem not_admissible_toDomainInterpretation_zero (I : FullTupleInterpretation L L' 0) :
    ¬I.toDomainInterpretation.Admissible := by
  intro h
  let M : Ordered.Structure L :=
    ⟨2, le_rfl, { funMap := fun _ _ => 0, RelMap := fun _ _ => False }⟩
  have := h M
  rw [card_toDomainInterpretation, pow_zero] at this
  lia

end FullTupleInterpretation

variable {L L' : Language} [L'.IsRelational]

/-- **First-order projection maps**: images of first-order projections of positive dimension. -/
@[expose] def IsProjectionMap (f : Ordered.Structure L → Ordered.Structure L') : Prop :=
  ∃ (k : ℕ) (I : FullTupleInterpretation L L' k) (hk : 0 < k),
    I.IsProjection ∧ f = I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk)

/-- **Quantifier-free projection maps**: images of quantifier-free projections of positive
dimension. -/
@[expose] def IsQFProjectionMap (f : Ordered.Structure L → Ordered.Structure L') : Prop :=
  ∃ (k : ℕ) (I : FullTupleInterpretation L L' k) (hk : 0 < k),
    I.IsQFProjection ∧ f = I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk)

/-- The image of a positive-dimensional first-order projection is a projection map. -/
theorem FullTupleInterpretation.IsProjection.isProjectionMap {k : ℕ}
    {I : FullTupleInterpretation L L' k} (h : I.IsProjection) (hk : 0 < k) :
    IsProjectionMap (I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk)) :=
  ⟨k, I, hk, h, rfl⟩

/-- The image of a positive-dimensional quantifier-free projection is a quantifier-free projection
map. -/
theorem FullTupleInterpretation.IsQFProjection.isQFProjectionMap {k : ℕ}
    {I : FullTupleInterpretation L L' k} (h : I.IsQFProjection) (hk : 0 < k) :
    IsQFProjectionMap (I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk)) :=
  ⟨k, I, hk, h, rfl⟩

/-- Quantifier-free projection maps are first-order projection maps. -/
theorem IsQFProjectionMap.isProjectionMap {f : Ordered.Structure L → Ordered.Structure L'}
    (hf : IsQFProjectionMap f) : IsProjectionMap f :=
  let ⟨k, I, hk, hI, hf⟩ := hf
  ⟨k, I, hk, hI.isProjection, hf⟩

/-- **First-order projection maps are first-order maps**, through the native numeric certificate
of full-tuple interpretations. -/
theorem IsProjectionMap.isFirstOrderMap {f : Ordered.Structure L → Ordered.Structure L'}
    (hf : IsProjectionMap f) : IsFirstOrderMap f := by
  obtain ⟨k, I, hk, -, rfl⟩ := hf
  exact I.isFirstOrderMap_map_toDomainInterpretation hk

/-- First-order projection maps are domain maps. -/
theorem IsProjectionMap.isDomainMap {f : Ordered.Structure L → Ordered.Structure L'}
    (hf : IsProjectionMap f) : IsDomainMap f :=
  hf.isFirstOrderMap.isDomainMap

end Ordered

end Cslib.Logic.FO
