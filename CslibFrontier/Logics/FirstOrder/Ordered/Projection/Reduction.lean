/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Projection.Composition

/-!
# First-order and quantifier-free projection reductions on ordered structures

An ordered query `K` reduces to `K'` by a first-order projection (`ProjectionReduces K K'`,
classically `K ≤_fop K'`) or by a quantifier-free projection (`QFProjectionReduces K K'`,
classically `K ≤_qfp K'`) when an admissible positive-dimensional projection map sends the members
of `K` to members of `K'` and the non-members outside `K'`
[Immerman and Landau, Definition 3.6][ImmermanLandau1995]. Both relations instantiate
`Cslib.Complexity.ManyOneReducibleBy`.

First-order projection reducibility is reflexive and transitive
[Immerman and Landau, Proposition 3.7][ImmermanLandau1995]. Quantifier-free projection reducibility
is reflexive and refines `ProjectionReduces`, which in turn refines `Ordered.Reduces`; transitivity
of quantifier-free projections (`QFProjectionReduces.trans`) is treated separately with the
`BIT`-free tuple numeric translations.

For the logspace encoding lift (`ProjectionReduces.logSpaceReducible` and
`QFProjectionReduces.logSpaceReducible` at `encStructure`), see
`CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Projection`.

## Main definitions

* `Cslib.Logic.FO.Ordered.ProjectionReduces`: many-one reducibility of ordered queries by
  first-order projection maps (`≤_fop`).
* `Cslib.Logic.FO.Ordered.QFProjectionReduces`: many-one reducibility of ordered queries by
  quantifier-free projection maps (`≤_qfp`).

## Main results

* `Cslib.Logic.FO.Ordered.ProjectionReduces.refl`,
  `Cslib.Logic.FO.Ordered.ProjectionReduces.trans`: `≤_fop` is a preorder on relational ordered
  queries.
* `Cslib.Logic.FO.Ordered.ProjectionReduces.compl`,
  `Cslib.Logic.FO.Ordered.QFProjectionReduces.compl`: complement closure.
* `Cslib.Logic.FO.Ordered.QFProjectionReduces.refl`: `≤_qfp` is reflexive.
* `Cslib.Logic.FO.Ordered.QFProjectionReduces.projectionReduces`,
  `Cslib.Logic.FO.Ordered.ProjectionReduces.reduces`,
  `Cslib.Logic.FO.Ordered.QFProjectionReduces.reduces`: `≤_qfp` refines `≤_fop`, which refines
  `≤_fo`.

## References

* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995],
  Definitions 3.3 and 3.6 and Proposition 3.7.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Definition 2.11, Remark 1.32 and
  Exercise 2.15(1).
-/

public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Cslib.Complexity

variable {L L' L'' : Language}

/-- **First-order projection reducibility** of ordered queries (`K ≤_fop K'`): many-one
reducibility by positive-dimensional first-order projection maps
[Immerman and Landau, Definition 3.6][ImmermanLandau1995]. -/
@[expose] def ProjectionReduces [L'.IsRelational] (K : Query L) (K' : Query L') : Prop :=
  ManyOneReducibleBy IsProjectionMap K K'

/-- **Quantifier-free projection reducibility** of ordered queries (`K ≤_qfp K'`): many-one
reducibility by positive-dimensional quantifier-free projection maps over `≤`, successor, `0` and
`max`, without `BIT` [Immerman and Landau, Definition 3.6][ImmermanLandau1995]. -/
@[expose] def QFProjectionReduces [L'.IsRelational] (K : Query L) (K' : Query L') : Prop :=
  ManyOneReducibleBy IsQFProjectionMap K K'

namespace ProjectionReduces

/-- **First-order projection reducibility is reflexive.** -/
@[refl] theorem refl [L.IsRelational] (K : Query L) : ProjectionReduces K K :=
  ManyOneReducibleBy.refl IsProjectionMap.id K

/-- **First-order projection reducibility is transitive**
[Immerman and Landau, Proposition 3.7][ImmermanLandau1995]. -/
theorem trans [L'.IsRelational] [L''.IsRelational] {K : Query L} {K' : Query L'}
    {K'' : Query L''} (h : ProjectionReduces K K') (h' : ProjectionReduces K' K'') :
    ProjectionReduces K K'' :=
  ManyOneReducibleBy.trans (fun _ _ hf hg => hf.comp hg) h h'

/-- A first-order projection reduction of `K` to `K'` reduces `Kᶜ` to `K'ᶜ`. -/
theorem compl [L'.IsRelational] {K : Query L} {K' : Query L'} (h : ProjectionReduces K K') :
    ProjectionReduces Kᶜ K'ᶜ :=
  ManyOneReducibleBy.compl h

/-- **First-order projection reductions are first-order reductions** (`≤_fop` refines `≤_fo`). -/
theorem reduces [L'.IsRelational] {K : Query L} {K' : Query L'} (h : ProjectionReduces K K') :
    Reduces K K' :=
  ManyOneReducibleBy.mono (fun _ hf => hf.isFirstOrderMap) h

/-- A positive-dimensional first-order projection that maps exactly the members of `K` into `K'`
reduces `K` to `K'`. -/
theorem of_projection [L'.IsRelational] {K : Query L} {K' : Query L'} {k : ℕ}
    {I : FullTupleInterpretation L L' k} (hI : I.IsProjection) (hk : 0 < k)
    (h : ∀ M, M ∈ K ↔
      I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M ∈ K') :
    ProjectionReduces K K' :=
  ⟨I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk), hI.isProjectionMap hk, h⟩

end ProjectionReduces

namespace QFProjectionReduces

/-- **Quantifier-free projection reducibility is reflexive.** -/
@[refl] theorem refl [L.IsRelational] (K : Query L) : QFProjectionReduces K K :=
  ManyOneReducibleBy.refl IsQFProjectionMap.id K

/-- A quantifier-free projection reduction of `K` to `K'` reduces `Kᶜ` to `K'ᶜ`. -/
theorem compl [L'.IsRelational] {K : Query L} {K' : Query L'} (h : QFProjectionReduces K K') :
    QFProjectionReduces Kᶜ K'ᶜ :=
  ManyOneReducibleBy.compl h

/-- **Quantifier-free projection reductions are first-order projection reductions** (`≤_qfp`
refines `≤_fop`). -/
theorem projectionReduces [L'.IsRelational] {K : Query L} {K' : Query L'}
    (h : QFProjectionReduces K K') : ProjectionReduces K K' :=
  ManyOneReducibleBy.mono (fun _ hf => hf.isProjectionMap) h

/-- **Quantifier-free projection reductions are first-order reductions** (`≤_qfp` refines `≤_fo`).
-/
theorem reduces [L'.IsRelational] {K : Query L} {K' : Query L'} (h : QFProjectionReduces K K') :
    Reduces K K' :=
  h.projectionReduces.reduces

/-- A positive-dimensional quantifier-free projection that maps exactly the members of `K` into
`K'` reduces `K` to `K'`. -/
theorem of_qfProjection [L'.IsRelational] {K : Query L} {K' : Query L'} {k : ℕ}
    {I : FullTupleInterpretation L L' k} (hI : I.IsQFProjection) (hk : 0 < k)
    (h : ∀ M, M ∈ K ↔
      I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk) M ∈ K') :
    QFProjectionReduces K K' :=
  ⟨I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hk),
    hI.isQFProjectionMap hk, h⟩

end QFProjectionReduces

end Cslib.Logic.FO.Ordered
