/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Fagin.Ordered
public import CslibFrontier.Computability.Complexity.Problems.Clique
public import CslibFrontier.Computability.Complexity.Problems.Coloring
public import CslibFrontier.Computability.Complexity.Problems.IndependentSet
public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Complexity.Problems.VertexCover
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Logics.FirstOrder.Ordered.Problems.CNF
public import CslibFrontier.Logics.FirstOrder.Ordered.Problems.Coloring
public import CslibFrontier.Logics.FirstOrder.Ordered.Problems.SizedGraph
public import CslibFrontier.Logics.FirstOrder.Ordered.Projection.Reduction
public import CslibFrontier.Logics.FirstOrder.Ordered.Reduction
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Reduction
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Fagin.Ordered.Problems
import CslibFrontier.Computability.Complexity.Fagin.Ordered.Verifier
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Logics.FirstOrder.Ordered.Problems.IndependentSetReduction
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Logics.SecondOrder.Ordered.Grounding

/-!
# Unconditional ordered `NP`-completeness under quantifier-free projections and polytime bridges

Combining the ordered Fagin tableau sentence over a polynomial power structure
(`Vocabulary.exists_powerSentence_of_mem_NP`,
`Vocabulary.realize_onESOSentence_powerInterpretation`)
with the `BIT`-free quantifier-free projection grounding of relational existential second-order
sentences (`qfProjectionReduces_SAT_of_orderSentence`), every ordered query whose source-only
encoded language belongs to native `NP` at `encStructure` reduces to `Ordered.SAT` by a
`BIT`-free quantifier-free projection (`QFProjectionReduces K Ordered.SAT`,
[Immerman, Chapter 7][Immerman1999]).

Conversely, because every ordered first-order reduction (`Ordered.Reduces`) compiles to a
deterministic logarithmic-space — hence polynomial-time — many-one reduction on `encStructure`
(`Reduces.logSpaceReducible`), native `NP` membership at `encStructure` is closed downward under
`Ordered.Reduces`, `ProjectionReduces`, and `QFProjectionReduces`. Composing with the explicit
`BIT`-free quantifier-free projections from `Ordered.SAT` into `Ordered.ThreeSAT`,
`Ordered.SimpleThreeColorable`, `Ordered.ThreeColorable`, `Ordered.IndependentSet`,
`Ordered.Clique`, and `Ordered.VertexCover` characterizes `K.encodedLanguage v ∈ NP encStructure`
(and `ESODefinable K`) uniformly by reducibility under `QFProjectionReduces`, `ProjectionReduces`,
or `Ordered.Reduces` to each of the seven canonical ordered queries.

At the machine level, `cnfToOrdered` translates any propositional formula `φ : PL.CNF ℕ` (`encCNF`)
in polynomial time into a canonically ordered `FO.cnf` structure (`encStructure`) of size
`max 2 (|φ.distinctVars| + |φ|)`, placing self-tautologies outside the clause block and the clauses
of `φ` inside `[|φ.distinctVars|, |φ.distinctVars| + |φ|)`. Together with Cook–Levin's
`SAT_npHard` and the logspace reductions among the seven ordered queries, this establishes
`NPHard encStructure` and `NPComplete encStructure` for all seven ordered problems, as well as
explicit bidirectional `PolyTimeReducible` bridges to `Complexity.SAT`, `Complexity.ThreeSAT`,
`Complexity.ThreeColoring`, `Complexity.IndependentSet`, `Complexity.Clique`, and
`Complexity.VertexCover`.

## Main definitions

* `Cslib.Logic.FO.Ordered.cnfToOrderedSize`, `Cslib.Logic.FO.Ordered.cnfToOrderedEntry`,
  `Cslib.Logic.FO.Ordered.cnfToOrderedTable`, `Cslib.Logic.FO.Ordered.cnfToOrdered`: polynomial-time
  encoding of `PL.CNF ℕ` into canonically ordered `FO.cnf` structures.

## Main results

* `Cslib.Logic.FO.Ordered.Reduces.encodedLanguage_mem_NP`,
  `Cslib.Logic.FO.Ordered.ProjectionReduces.encodedLanguage_mem_NP`,
  `Cslib.Logic.FO.Ordered.QFProjectionReduces.encodedLanguage_mem_NP`,
  `Cslib.Logic.FO.Ordered.Reduces.esoDefinable`: closure of ordered `NP` and `ESODefinable` under
  ordered first-order reductions.
* `Cslib.Logic.FO.Ordered.qfProjectionReduces_SAT_of_encodedLanguage_mem_NP`: unconditional
  `≤_qfp`-hardness of `Ordered.SAT` for ordered `NP` [Immerman, Chapter 7][Immerman1999].
* `Cslib.Logic.FO.Ordered.esoDefinable_iff_qfProjectionReduces_SAT`,
  `Cslib.Logic.FO.Ordered.esoDefinable_iff_projectionReduces_SAT`,
  `Cslib.Logic.FO.Ordered.esoDefinable_iff_reduces_SAT`: logical equivalence between `ESODefinable`
  and reducibility to `Ordered.SAT`.
* `qfProjectionReduces_*_iff_encodedLanguage_mem_NP`,
  `projectionReduces_*_iff_encodedLanguage_mem_NP`, and `reduces_*_iff_encodedLanguage_mem_NP` for
  `SAT`, `ThreeSAT`, `SimpleThreeColorable`, `ThreeColorable`, `IndependentSet`, `Clique`, and
  `VertexCover`.
* `Cslib.Logic.FO.Ordered.cnfToOrdered_mem_iff`,
  `Cslib.Logic.FO.Ordered.computableInPolyTime_cnfToOrdered`,
  `Cslib.Logic.FO.Ordered.cnf_polyTimeReducible_orderedSAT`: correctness and polynomial-time
  computability of `cnfToOrdered`.
* `*_npHard`, `*_npComplete`, and bidirectional `PolyTimeReducible` bridges for all seven canonical
  ordered queries.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Chapter 7
* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure
open Cslib.Complexity Turing.MultiTapeTM

/-! ### Closure of ordered `NP` under first-order reductions -/

/-- **Ordered queries in native `NP` are closed under ordered first-order reductions**: every
`Ordered.Reduces K K'` compiles to a deterministic logspace — hence polynomial-time — many-one
reduction on `encStructure`. -/
theorem Reduces.encodedLanguage_mem_NP {L L' : Language} [L.IsRelational] [L'.IsRelational]
    (v : Vocabulary L) (v' : Vocabulary L') {K : Query L} {K' : Query L'}
    (h : Reduces K K') (hNP : K'.encodedLanguage v' ∈ NP encStructure) :
    K.encodedLanguage v ∈ NP encStructure :=
  (h.logSpaceReducible v v').polyTimeReducible.mem_NP hNP

/-- Ordered queries in native `NP` are closed under `BIT`-allowed first-order projections. -/
theorem ProjectionReduces.encodedLanguage_mem_NP {L L' : Language}
    [L.IsRelational] [L'.IsRelational] (v : Vocabulary L) (v' : Vocabulary L')
    {K : Query L} {K' : Query L'} (h : ProjectionReduces K K')
    (hNP : K'.encodedLanguage v' ∈ NP encStructure) :
    K.encodedLanguage v ∈ NP encStructure :=
  (ProjectionReduces.reduces h).encodedLanguage_mem_NP v v' hNP

/-- Ordered queries in native `NP` are closed under `BIT`-free quantifier-free projections. -/
theorem QFProjectionReduces.encodedLanguage_mem_NP {L L' : Language}
    [L.IsRelational] [L'.IsRelational] (v : Vocabulary L) (v' : Vocabulary L')
    {K : Query L} {K' : Query L'} (h : QFProjectionReduces K K')
    (hNP : K'.encodedLanguage v' ∈ NP encStructure) :
    K.encodedLanguage v ∈ NP encStructure :=
  (QFProjectionReduces.reduces h).encodedLanguage_mem_NP v v' hNP

/-- Existential second-order definability over finite relational vocabularies pulls back along
ordered first-order reductions. -/
theorem Reduces.esoDefinable {L L' : Language} [L.IsRelational] [L'.IsRelational]
    (v : Vocabulary L) (v' : Vocabulary L') {K : Query L} {K' : Query L'}
    (h : Reduces K K') (hK' : ESODefinable K') : ESODefinable K :=
  ESODefinable.of_encodedLanguage_mem_NP v
    (h.encodedLanguage_mem_NP v v' (hK'.encodedLanguage_mem_NP v'))

/-! ### Unconditional `≤_qfp`, `≤_fop`, and `≤_fo` completeness for ordered `NP` -/

/-- **Unconditional `≤_qfp`-hardness of `Ordered.SAT` for ordered `NP`**
([Immerman, Chapter 7][Immerman1999]): every ordered query over a finite relational vocabulary `v`
whose source-only encoded language belongs to native `NP` reduces to `Ordered.SAT` by a `BIT`-free
quantifier-free projection. -/
theorem qfProjectionReduces_SAT_of_encodedLanguage_mem_NP {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} (hNP : K.encodedLanguage v ∈ NP encStructure) :
    QFProjectionReduces K SAT := by
  obtain ⟨k, hk, har, Ψ, hΨ⟩ := v.exists_powerSentence_of_mem_NP hNP
  refine qfProjectionReduces_SAT_of_orderSentence ((v.powerInterpretation k har).onESOSentence Ψ)
    fun M => ?_
  rw [v.realize_onESOSentence_powerInterpretation k hk har M (Equiv.refl M) Ψ]
  exact (mem_encodedLanguage_encode v K M).symm.trans
    (hΨ (encode v M) (v.wellFormed_encode M (Equiv.refl M)) M.size_ge_two)

private theorem qfProjectionReduces_iff_of_sat {L L' : Language}
    [L.IsRelational] [L'.IsRelational] (v : Vocabulary L) (v' : Vocabulary L')
    {K : Query L} {Q : Query L'} (hSAT : QFProjectionReduces SAT Q)
    (hQ : Q.encodedLanguage v' ∈ NP encStructure) :
    QFProjectionReduces K Q ↔ K.encodedLanguage v ∈ NP encStructure :=
  ⟨fun h => h.encodedLanguage_mem_NP v v' hQ,
    fun h => (qfProjectionReduces_SAT_of_encodedLanguage_mem_NP v h).trans hSAT⟩

private theorem projectionReduces_iff_of_sat {L L' : Language}
    [L.IsRelational] [L'.IsRelational] (v : Vocabulary L) (v' : Vocabulary L')
    {K : Query L} {Q : Query L'} (hSAT : QFProjectionReduces SAT Q)
    (hQ : Q.encodedLanguage v' ∈ NP encStructure) :
    ProjectionReduces K Q ↔ K.encodedLanguage v ∈ NP encStructure :=
  ⟨fun h => h.encodedLanguage_mem_NP v v' hQ,
    fun h => QFProjectionReduces.projectionReduces
      ((qfProjectionReduces_SAT_of_encodedLanguage_mem_NP v h).trans hSAT)⟩

private theorem reduces_iff_of_sat {L L' : Language}
    [L.IsRelational] [L'.IsRelational] (v : Vocabulary L) (v' : Vocabulary L')
    {K : Query L} {Q : Query L'} (hSAT : QFProjectionReduces SAT Q)
    (hQ : Q.encodedLanguage v' ∈ NP encStructure) :
    Reduces K Q ↔ K.encodedLanguage v ∈ NP encStructure :=
  ⟨fun h => h.encodedLanguage_mem_NP v v' hQ,
    fun h => QFProjectionReduces.reduces
      ((qfProjectionReduces_SAT_of_encodedLanguage_mem_NP v h).trans hSAT)⟩

/-- **Unconditional `≤_qfp`-completeness of `Ordered.SAT` for ordered `NP`**
([Immerman, Chapter 7][Immerman1999]). -/
theorem qfProjectionReduces_SAT_iff_encodedLanguage_mem_NP {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} :
    QFProjectionReduces K SAT ↔ K.encodedLanguage v ∈ NP encStructure :=
  qfProjectionReduces_iff_of_sat v FO.cnf.vocabulary (QFProjectionReduces.refl SAT)
    sat_encodedLanguage_mem_NP

/-- **Unconditional `≤_fop`-completeness of `Ordered.SAT` for ordered `NP`.** -/
theorem projectionReduces_SAT_iff_encodedLanguage_mem_NP {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} :
    ProjectionReduces K SAT ↔ K.encodedLanguage v ∈ NP encStructure :=
  projectionReduces_iff_of_sat v FO.cnf.vocabulary (QFProjectionReduces.refl SAT)
    sat_encodedLanguage_mem_NP

/-- **Unconditional ordered first-order (`≤_fo`) completeness of `Ordered.SAT` for ordered
`NP`.** -/
theorem reduces_SAT_iff_encodedLanguage_mem_NP {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} :
    Reduces K SAT ↔ K.encodedLanguage v ∈ NP encStructure :=
  reduces_iff_of_sat v FO.cnf.vocabulary (QFProjectionReduces.refl SAT)
    sat_encodedLanguage_mem_NP

/-- Over a finite relational vocabulary `v`, `ESODefinable K` is equivalent to quantifier-free
projection reducibility `QFProjectionReduces K Ordered.SAT`. -/
theorem esoDefinable_iff_qfProjectionReduces_SAT {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} :
    ESODefinable K ↔ QFProjectionReduces K SAT :=
  (esoDefinable_iff_encodedLanguage_mem_NP v K).trans
    (qfProjectionReduces_SAT_iff_encodedLanguage_mem_NP v).symm

/-- Over a finite relational vocabulary `v`, `ESODefinable K` is equivalent to first-order
projection reducibility `ProjectionReduces K Ordered.SAT`. -/
theorem esoDefinable_iff_projectionReduces_SAT {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} :
    ESODefinable K ↔ ProjectionReduces K SAT :=
  (esoDefinable_iff_encodedLanguage_mem_NP v K).trans
    (projectionReduces_SAT_iff_encodedLanguage_mem_NP v).symm

/-- Over a finite relational vocabulary `v`, `ESODefinable K` is equivalent to ordered first-order
reducibility `Ordered.Reduces K Ordered.SAT`. -/
theorem esoDefinable_iff_reduces_SAT {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} :
    ESODefinable K ↔ Reduces K SAT :=
  (esoDefinable_iff_encodedLanguage_mem_NP v K).trans
    (reduces_SAT_iff_encodedLanguage_mem_NP v).symm

/-- **Unconditional `≤_qfp`-completeness of `Ordered.ThreeSAT` for ordered `NP`.** -/
theorem qfProjectionReduces_ThreeSAT_iff_encodedLanguage_mem_NP {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} :
    QFProjectionReduces K ThreeSAT ↔ K.encodedLanguage v ∈ NP encStructure :=
  qfProjectionReduces_iff_of_sat v FO.cnf.vocabulary sat_qfProjectionReduces_ThreeSAT
    threeSAT_encodedLanguage_mem_NP

/-- **Unconditional `≤_fop`-completeness of `Ordered.ThreeSAT` for ordered `NP`.** -/
theorem projectionReduces_ThreeSAT_iff_encodedLanguage_mem_NP {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} :
    ProjectionReduces K ThreeSAT ↔ K.encodedLanguage v ∈ NP encStructure :=
  projectionReduces_iff_of_sat v FO.cnf.vocabulary sat_qfProjectionReduces_ThreeSAT
    threeSAT_encodedLanguage_mem_NP

/-- **Unconditional ordered first-order (`≤_fo`) completeness of `Ordered.ThreeSAT` for ordered
`NP`.** -/
theorem reduces_ThreeSAT_iff_encodedLanguage_mem_NP {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} :
    Reduces K ThreeSAT ↔ K.encodedLanguage v ∈ NP encStructure :=
  reduces_iff_of_sat v FO.cnf.vocabulary sat_qfProjectionReduces_ThreeSAT
    threeSAT_encodedLanguage_mem_NP

/-- **Unconditional `≤_qfp`-completeness of `Ordered.SimpleThreeColorable` for ordered `NP`.** -/
theorem qfProjectionReduces_SimpleThreeColorable_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    QFProjectionReduces K SimpleThreeColorable ↔ K.encodedLanguage v ∈ NP encStructure :=
  qfProjectionReduces_iff_of_sat v graphVocabulary sat_qfProjectionReduces_SimpleThreeColorable
    simpleThreeColorable_encodedLanguage_mem_NP

/-- **Unconditional `≤_fop`-completeness of `Ordered.SimpleThreeColorable` for ordered `NP`.** -/
theorem projectionReduces_SimpleThreeColorable_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    ProjectionReduces K SimpleThreeColorable ↔ K.encodedLanguage v ∈ NP encStructure :=
  projectionReduces_iff_of_sat v graphVocabulary sat_qfProjectionReduces_SimpleThreeColorable
    simpleThreeColorable_encodedLanguage_mem_NP

/-- **Unconditional ordered first-order (`≤_fo`) completeness of `Ordered.SimpleThreeColorable` for
ordered `NP`.** -/
theorem reduces_SimpleThreeColorable_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    Reduces K SimpleThreeColorable ↔ K.encodedLanguage v ∈ NP encStructure :=
  reduces_iff_of_sat v graphVocabulary sat_qfProjectionReduces_SimpleThreeColorable
    simpleThreeColorable_encodedLanguage_mem_NP

/-- **Unconditional `≤_qfp`-completeness of `Ordered.ThreeColorable` for ordered `NP`.** -/
theorem qfProjectionReduces_ThreeColorable_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    QFProjectionReduces K ThreeColorable ↔ K.encodedLanguage v ∈ NP encStructure :=
  qfProjectionReduces_iff_of_sat v graphVocabulary sat_qfProjectionReduces_ThreeColorable
    threeColorable_encodedLanguage_mem_NP

/-- **Unconditional `≤_fop`-completeness of `Ordered.ThreeColorable` for ordered `NP`.** -/
theorem projectionReduces_ThreeColorable_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    ProjectionReduces K ThreeColorable ↔ K.encodedLanguage v ∈ NP encStructure :=
  projectionReduces_iff_of_sat v graphVocabulary sat_qfProjectionReduces_ThreeColorable
    threeColorable_encodedLanguage_mem_NP

/-- **Unconditional ordered first-order (`≤_fo`) completeness of `Ordered.ThreeColorable` for
ordered `NP`.** -/
theorem reduces_ThreeColorable_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    Reduces K ThreeColorable ↔ K.encodedLanguage v ∈ NP encStructure :=
  reduces_iff_of_sat v graphVocabulary sat_qfProjectionReduces_ThreeColorable
    threeColorable_encodedLanguage_mem_NP

/-- **Unconditional `≤_qfp`-completeness of `Ordered.IndependentSet` for ordered `NP`.** -/
theorem qfProjectionReduces_IndependentSet_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    QFProjectionReduces K IndependentSet ↔ K.encodedLanguage v ∈ NP encStructure :=
  qfProjectionReduces_iff_of_sat v sizedGraphVocabulary sat_qfProjectionReduces_IndependentSet
    independentSet_encodedLanguage_mem_NP

/-- **Unconditional `≤_fop`-completeness of `Ordered.IndependentSet` for ordered `NP`.** -/
theorem projectionReduces_IndependentSet_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    ProjectionReduces K IndependentSet ↔ K.encodedLanguage v ∈ NP encStructure :=
  projectionReduces_iff_of_sat v sizedGraphVocabulary sat_qfProjectionReduces_IndependentSet
    independentSet_encodedLanguage_mem_NP

/-- **Unconditional ordered first-order (`≤_fo`) completeness of `Ordered.IndependentSet` for
ordered `NP`.** -/
theorem reduces_IndependentSet_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    Reduces K IndependentSet ↔ K.encodedLanguage v ∈ NP encStructure :=
  reduces_iff_of_sat v sizedGraphVocabulary sat_qfProjectionReduces_IndependentSet
    independentSet_encodedLanguage_mem_NP

/-- **Unconditional `≤_qfp`-completeness of `Ordered.Clique` for ordered `NP`.** -/
theorem qfProjectionReduces_Clique_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    QFProjectionReduces K Clique ↔ K.encodedLanguage v ∈ NP encStructure :=
  qfProjectionReduces_iff_of_sat v sizedGraphVocabulary sat_qfProjectionReduces_Clique
    clique_encodedLanguage_mem_NP

/-- **Unconditional `≤_fop`-completeness of `Ordered.Clique` for ordered `NP`.** -/
theorem projectionReduces_Clique_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    ProjectionReduces K Clique ↔ K.encodedLanguage v ∈ NP encStructure :=
  projectionReduces_iff_of_sat v sizedGraphVocabulary sat_qfProjectionReduces_Clique
    clique_encodedLanguage_mem_NP

/-- **Unconditional ordered first-order (`≤_fo`) completeness of `Ordered.Clique` for ordered
`NP`.** -/
theorem reduces_Clique_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    Reduces K Clique ↔ K.encodedLanguage v ∈ NP encStructure :=
  reduces_iff_of_sat v sizedGraphVocabulary sat_qfProjectionReduces_Clique
    clique_encodedLanguage_mem_NP

/-- **Unconditional `≤_qfp`-completeness of `Ordered.VertexCover` for ordered `NP`.** -/
theorem qfProjectionReduces_VertexCover_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    QFProjectionReduces K VertexCover ↔ K.encodedLanguage v ∈ NP encStructure :=
  qfProjectionReduces_iff_of_sat v sizedGraphVocabulary sat_qfProjectionReduces_VertexCover
    vertexCover_encodedLanguage_mem_NP

/-- **Unconditional `≤_fop`-completeness of `Ordered.VertexCover` for ordered `NP`.** -/
theorem projectionReduces_VertexCover_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    ProjectionReduces K VertexCover ↔ K.encodedLanguage v ∈ NP encStructure :=
  projectionReduces_iff_of_sat v sizedGraphVocabulary sat_qfProjectionReduces_VertexCover
    vertexCover_encodedLanguage_mem_NP

/-- **Unconditional ordered first-order (`≤_fo`) completeness of `Ordered.VertexCover` for ordered
`NP`.** -/
theorem reduces_VertexCover_iff_encodedLanguage_mem_NP
    {L : Language} [L.IsRelational] (v : Vocabulary L) {K : Query L} :
    Reduces K VertexCover ↔ K.encodedLanguage v ∈ NP encStructure :=
  reduces_iff_of_sat v sizedGraphVocabulary sat_qfProjectionReduces_VertexCover
    vertexCover_encodedLanguage_mem_NP

/-! ### Explicit polynomial-time reduction `Complexity.SAT → Ordered.SAT` -/

/-- Universe size `max 2 (|φ.distinctVars| + |φ|)` of the canonically ordered `FO.cnf` structure
encoding a propositional formula `φ : PL.CNF ℕ`. -/
@[expose] def cnfToOrderedSize (φ : PL.CNF ℕ) : ℕ :=
  Max.max (2 : ℕ) (φ.distinctVars.length + φ.length)

/-- Entry `(c, v)` of polarity `b` in `cnfToOrdered φ`: indices outside the clause block
`[|φ.distinctVars|, |φ.distinctVars| + |φ|)` carry the self-tautology `c ∨ ¬ c`, while clause
index `|φ.distinctVars| + j` encodes the literals of `φ[j]` over the compacted variables
`0 .. |φ.distinctVars| - 1`. -/
@[expose] def cnfToOrderedEntry (φ : PL.CNF ℕ) (b : Bool) (c v : ℕ) : Bool :=
  if c < φ.distinctVars.length ∨ φ.distinctVars.length + φ.length ≤ c then
    decide (c = v)
  else
    decide (v < φ.distinctVars.length ∧
      (φ.distinctVars.getD v 0, b) ∈ φ.getD (c - φ.distinctVars.length) [])

/-- Flattened truth table of length `(cnfToOrderedSize φ) ^ 2` for `FO.cnf.lit b` in `tupleIndex`
order (`c + v * n`). -/
@[expose] def cnfToOrderedTable (b : Bool) (φ : PL.CNF ℕ) : List Bool :=
  (List.range (cnfToOrderedSize φ)).flatMap fun v =>
    (List.range (cnfToOrderedSize φ)).map fun c =>
      cnfToOrderedEntry φ b c v

/-- Explicit polynomial-time translation of a propositional CNF formula `φ : PL.CNF ℕ` into a
canonically ordered `FO.cnf` structure encoding. -/
@[expose] def cnfToOrdered (φ : PL.CNF ℕ) : EncodedStructure :=
  (cnfToOrderedSize φ, [cnfToOrderedTable true φ, cnfToOrderedTable false φ])

section CnfToOrderedProofs

private theorem length_flatMap_range {α : Type*} (n : ℕ) {g : ℕ → List α}
    (hg : ∀ y, (g y).length = n) :
    ∀ k : ℕ, ((List.range k).flatMap g).length = k * n
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_range n hg k,
      List.flatMap_singleton, hg k, Nat.add_one_mul]

private theorem getD_flatMap_range {α : Type*} (n : ℕ) {g : ℕ → List α}
    (hg : ∀ y, (g y).length = n) (d : α) :
    ∀ {k c v : ℕ}, c < n → v < k →
      ((List.range k).flatMap g).getD (c + v * n) d = (g v).getD c d
  | 0, _, _, _, hv => absurd hv (Nat.not_lt_zero _)
  | k + 1, c, v, hc, hv => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hlen : ((List.range k).flatMap g).length = k * n := length_flatMap_range n hg k
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hlt | heq
    · have hidx : c + v * n < ((List.range k).flatMap g).length := by
        rw [hlen]
        calc c + v * n < n + v * n := Nat.add_lt_add_right hc _
          _ = (v + 1) * n := by ring
          _ ≤ k * n := Nat.mul_le_mul_right n hlt
      rw [List.getD_append _ _ _ _ hidx]
      exact getD_flatMap_range n hg d hc hlt
    · subst v
      have hidx : ((List.range k).flatMap g).length ≤ c + k * n := by
        rw [hlen]
        exact Nat.le_add_left _ _
      rw [List.getD_append_right _ _ _ _ hidx, hlen, Nat.add_sub_cancel]

private theorem length_cnfToOrderedTable (b : Bool) (φ : PL.CNF ℕ) :
    (cnfToOrderedTable b φ).length = cnfToOrderedSize φ ^ 2 := by
  rw [cnfToOrderedTable, length_flatMap_range (cnfToOrderedSize φ)
    (fun _ => by simp only [List.length_map, List.length_range]), sq]

private theorem tupleIndex_pair {n : ℕ} (c v : Fin n) :
    tupleIndex ![c, v] = c.val + v.val * n := by
  rw [tupleIndex_apply, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero, pow_zero, mul_one,
    Fin.val_one, pow_one]

/-- Every output `cnfToOrdered φ` is well-formed for `FO.cnf.vocabulary`. -/
theorem wellFormed_cnfToOrdered (φ : PL.CNF ℕ) :
    FO.cnf.vocabulary.WellFormed (cnfToOrdered φ) := by
  refine ⟨rfl, fun i => ?_⟩
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => exact length_cnfToOrderedTable true φ
  | 1, _ => exact length_cnfToOrderedTable false φ

/-- Every output `cnfToOrdered φ` has universe size at least `2`. -/
theorem two_le_cnfToOrderedSize (φ : PL.CNF ℕ) : 2 ≤ cnfToOrderedSize φ :=
  le_max_left 2 _

private theorem relMap_decode_cnfToOrdered (φ : PL.CNF ℕ) (b : Bool)
    (c v : Fin (cnfToOrderedSize φ)) :
    (FO.cnf.vocabulary.decode (cnfToOrdered φ)).RelMap (FO.cnf.lit b) ![c, v] ↔
      cnfToOrderedEntry φ b c.val v.val = true := by
  have htab : FO.cnf.vocabulary.table (cnfToOrdered φ) ⟨2, FO.cnf.lit b⟩ =
      cnfToOrderedTable b φ := by
    cases b <;> rfl
  rw [Vocabulary.relMap_decode, htab]
  change (cnfToOrderedTable b φ).getD (tupleIndex (n := cnfToOrderedSize φ) ![c, v]) false = true ↔
    cnfToOrderedEntry φ b c.val v.val = true
  rw [tupleIndex_pair, cnfToOrderedTable,
    getD_flatMap_range (cnfToOrderedSize φ)
      (fun _ => by simp only [List.length_map, List.length_range]) false c.isLt v.isLt,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; exact c.isLt),
    List.getElem_map, List.getElem_range]

end CnfToOrderedProofs

/-- **Semantic correctness of `cnfToOrdered`**: `cnfToOrdered φ` belongs to the ordered `SAT`
encoded language if and only if `φ` is satisfiable (`φ ∈ Complexity.SAT`). -/
theorem cnfToOrdered_mem_iff (φ : PL.CNF ℕ) :
    cnfToOrdered φ ∈ SAT.encodedLanguage FO.cnf.vocabulary ↔ φ ∈ Complexity.SAT := by
  let vs := φ.distinctVars
  let n := cnfToOrderedSize φ
  have hn : 2 ≤ n := two_le_cnfToOrderedSize φ
  have hwf : FO.cnf.vocabulary.WellFormed (cnfToOrdered φ) := wellFormed_cnfToOrdered φ
  simp only [Query.encodedLanguage, Set.mem_ofPred_eq, mem_SAT, FO.cnf.Satisfiable,
    Complexity.mem_SAT]
  constructor
  · rintro ⟨-, hn', A, hA⟩
    classical
    let A' : Fin n → Prop := A
    let σ : ℕ → Bool := fun x => decide (∃ h : vs.idxOf x < n, A' ⟨vs.idxOf x, h⟩)
    refine ⟨σ, (PL.CNF.eval_eq_true_iff σ φ).mpr fun cl hcl => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hcl
    have hcj : vs.length + j < n := by
      have h1 : vs.length + j < vs.length + φ.length := Nat.add_lt_add_left hj _
      exact lt_of_lt_of_le h1 (le_max_right (2 : ℕ) _)
    let c : Fin n := ⟨vs.length + j, hcj⟩
    have hnc : ¬ (c.val < vs.length ∨ vs.length + φ.length ≤ c.val) := by
      change ¬ (vs.length + j < vs.length ∨ vs.length + φ.length ≤ vs.length + j)
      omega
    have hlit (b : Bool) (v : Fin n) (hentry : cnfToOrderedEntry φ b c.val v.val = true) :
        ∃ hv : v.val < φ.distinctVars.length,
          (φ.distinctVars[v.val], b) ∈ φ[j] ∧
            φ.distinctVars.idxOf φ.distinctVars[v.val] = v.val := by
      simp only [cnfToOrderedEntry, vs, hnc, ↓reduceIte, decide_eq_true_eq] at hentry
      obtain ⟨hv, hmem⟩ := hentry
      have hget_cl : φ.getD (c.val - φ.distinctVars.length) [] = φ[j] := by
        change φ.getD (vs.length + j - vs.length) [] = φ[j]
        rw [Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hj]
      rw [hget_cl, List.getD_eq_getElem _ _ hv] at hmem
      exact ⟨hv, hmem, List.Nodup.idxOf_getElem (PL.CNF.nodup_distinctVars φ) v.val hv⟩
    obtain ⟨v, ⟨hpos, hAv⟩ | ⟨hneg, hnAv⟩⟩ := hA c
    · obtain ⟨hv, hmem, hidx⟩ := hlit true v ((relMap_decode_cnfToOrdered φ true c v).mp hpos)
      refine (PL.Clause.eval_eq_true_iff σ φ[j]).mpr ⟨(φ.distinctVars[v.val], true), hmem, ?_⟩
      simp only [σ, vs, A', hidx, decide_eq_true_eq]
      exact ⟨v.isLt, hAv⟩
    · obtain ⟨hv, hmem, hidx⟩ := hlit false v ((relMap_decode_cnfToOrdered φ false c v).mp hneg)
      refine (PL.Clause.eval_eq_true_iff σ φ[j]).mpr ⟨(φ.distinctVars[v.val], false), hmem, ?_⟩
      simp only [σ, vs, A', hidx, decide_eq_false_iff_not, not_exists]
      intro _ hA''
      exact hnAv hA''
  · rintro ⟨σ, hσ⟩
    refine ⟨hwf, hn, fun v => σ (vs.getD v.val 0) = true, fun c => ?_⟩
    by_cases hout : c.val < vs.length ∨ vs.length + φ.length ≤ c.val
    · by_cases hc : σ (vs.getD c.val 0) = true
      · refine ⟨c, .inl ⟨(relMap_decode_cnfToOrdered φ true c c).mpr ?_, hc⟩⟩
        simp only [cnfToOrderedEntry, vs, hout, ↓reduceIte, decide_true]
      · refine ⟨c, .inr ⟨(relMap_decode_cnfToOrdered φ false c c).mpr ?_, hc⟩⟩
        simp only [cnfToOrderedEntry, vs, hout, ↓reduceIte, decide_true]
    · have hge : vs.length ≤ c.val := by omega
      have hlt : c.val < vs.length + φ.length := by omega
      let j := c.val - vs.length
      have hj : j < φ.length := by omega
      have hcl_eval : φ[j].eval σ = true :=
        (PL.CNF.eval_eq_true_iff σ φ).mp hσ φ[j] (List.getElem_mem hj)
      obtain ⟨⟨x, b⟩, hl_mem, hl_sat⟩ := (PL.Clause.eval_eq_true_iff σ φ[j]).mp hcl_eval
      have hx_vars : x ∈ φ.vars :=
        List.mem_map.mpr ⟨(x, b), List.mem_flatten.mpr ⟨φ[j], List.getElem_mem hj, hl_mem⟩, rfl⟩
      have hx_vs : x ∈ vs := PL.CNF.mem_distinctVars.mpr hx_vars
      have hi_lt : vs.idxOf x < vs.length := List.idxOf_lt_length_of_mem hx_vs
      have hi_n : vs.idxOf x < n :=
        lt_of_lt_of_le (lt_of_lt_of_le hi_lt (Nat.le_add_right _ _)) (le_max_right (2 : ℕ) _)
      let v : Fin n := ⟨vs.idxOf x, hi_n⟩
      have hget_v : vs.getD v.val 0 = x := by simp [v, List.getD_eq_getElem?_getD, hx_vs]
      have hrel : (FO.cnf.vocabulary.decode (cnfToOrdered φ)).RelMap (FO.cnf.lit b) ![c, v] := by
        refine (relMap_decode_cnfToOrdered φ b c v).mpr ?_
        simp only [cnfToOrderedEntry, vs, hout, ↓reduceIte, decide_eq_true_eq]
        refine ⟨hi_lt, ?_⟩
        rw [hget_v, List.getD_eq_getElem _ _ hj]
        exact hl_mem
      cases b
      · refine ⟨v, .inr ⟨hrel, ?_⟩⟩
        change ¬ (σ (vs.getD v.val 0) = true)
        rw [hget_v, hl_sat]
        exact Bool.false_ne_true
      · refine ⟨v, .inl ⟨hrel, ?_⟩⟩
        change σ (vs.getD v.val 0) = true
        rw [hget_v, hl_sat]

@[fun_prop]
private theorem computableInPolyTime_cnfToOrderedSize :
    ComputableInPolyTime cnfToOrderedSize encCNF encUnary := by
  unfold cnfToOrderedSize
  fun_prop

private theorem computableInPolyTime_cnfToOrderedEntry (b : Bool) :
    ComputableInPolyTime
      (fun p : (PL.CNF ℕ × ℕ) × ℕ =>
        let (fv, c) := p
        let (φ, v) := fv
        cnfToOrderedEntry φ b c v)
      (encPair (encPair encCNF encUnary) encUnary) encBool := by
  let encP := encPair (encPair encCNF encUnary) encUnary
  have hfv : ComputableInPolyTime Prod.fst encP (encPair encCNF encUnary) :=
    ComputableInPolyTime.fst _ _
  have hφ : ComputableInPolyTime (fun p : (PL.CNF ℕ × ℕ) × ℕ => (Prod.fst p).fst) encP encCNF :=
    (ComputableInPolyTime.fst encCNF encUnary).comp hfv
  have hv : ComputableInPolyTime (fun p : (PL.CNF ℕ × ℕ) × ℕ => (Prod.fst p).snd) encP encUnary :=
    (ComputableInPolyTime.snd encCNF encUnary).comp hfv
  have hc : ComputableInPolyTime Prod.snd encP encUnary :=
    ComputableInPolyTime.snd _ _
  have hvs : ComputableInPolyTime
      (fun p : (PL.CNF ℕ × ℕ) × ℕ => (Prod.fst p).fst.distinctVars) encP (encList encNat) :=
    (PL.CNF.computableInPolyTime_distinctVars encNat).comp hφ
  have hnumVars : ComputableInPolyTime
      (fun p : (PL.CNF ℕ × ℕ) × ℕ => (Prod.fst p).fst.distinctVars.length) encP encUnary :=
    (ComputableInPolyTime.length_list encNat).comp hvs
  have hnumClauses : ComputableInPolyTime
      (fun p : (PL.CNF ℕ × ℕ) × ℕ => (Prod.fst p).fst.length) encP encUnary :=
    PL.CNF.computableInPolyTime_length hφ
  have hvar : ComputableInPolyTime
      (fun p : (PL.CNF ℕ × ℕ) × ℕ => (Prod.fst p).fst.distinctVars.getD (Prod.fst p).snd 0)
      encP encNat :=
    (ComputableInPolyTime.listGetD (encA := encNat) (encL := encList encNat) 0).comp
      (hvs.prod hv)
  have hlit : ComputableInPolyTime
      (fun p : (PL.CNF ℕ × ℕ) × ℕ => ((Prod.fst p).fst.distinctVars.getD (Prod.fst p).snd 0, b))
      encP (encPair encNat encBool) :=
    hvar.prod (ComputableInPolyTime.const b)
  have hidx : ComputableInPolyTime
      (fun p : (PL.CNF ℕ × ℕ) × ℕ => Prod.snd p - (Prod.fst p).fst.distinctVars.length)
      encP encUnary := by
    fun_prop
  have hcl : ComputableInPolyTime
      (fun p : (PL.CNF ℕ × ℕ) × ℕ =>
        (Prod.fst p).fst.getD (Prod.snd p - (Prod.fst p).fst.distinctVars.length) [])
      encP (PL.encClause encNat) :=
    (ComputableInPolyTime.listGetD (encA := PL.encClause encNat)
      (encL := PL.encCNFOver encNat) []).comp (hφ.prod hidx)
  have hmem : ComputableInPolyTime
      (fun p : (PL.CNF ℕ × ℕ) × ℕ =>
        decide (((Prod.fst p).fst.distinctVars.getD (Prod.fst p).snd 0, b) ∈
          (Prod.fst p).fst.getD (Prod.snd p - (Prod.fst p).fst.distinctVars.length) []))
      encP encBool :=
    ComputableInPolyTime.decide_mem hcl hlit
  have hcond : ComputableInPolyTime
      (fun p : (PL.CNF ℕ × ℕ) × ℕ =>
        decide (Prod.snd p < (Prod.fst p).fst.distinctVars.length ∨
          (Prod.fst p).fst.distinctVars.length + (Prod.fst p).fst.length ≤ Prod.snd p))
      encP encBool := by
    fun_prop
  have hdiag : ComputableInPolyTime
      (fun p : (PL.CNF ℕ × ℕ) × ℕ => decide (Prod.snd p = (Prod.fst p).snd))
      encP encBool := by
    fun_prop
  have hbody : ComputableInPolyTime
      (fun p : (PL.CNF ℕ × ℕ) × ℕ =>
        decide ((Prod.fst p).snd < (Prod.fst p).fst.distinctVars.length) &&
          decide (((Prod.fst p).fst.distinctVars.getD (Prod.fst p).snd 0, b) ∈
            (Prod.fst p).fst.getD (Prod.snd p - (Prod.fst p).fst.distinctVars.length) []))
      encP encBool := by
    fun_prop
  have heq : (fun p : (PL.CNF ℕ × ℕ) × ℕ =>
        let (fv, c) := p
        let (φ, v) := fv
        cnfToOrderedEntry φ b c v) =
      (fun p : (PL.CNF ℕ × ℕ) × ℕ =>
        if decide (Prod.snd p < (Prod.fst p).fst.distinctVars.length ∨
            (Prod.fst p).fst.distinctVars.length + (Prod.fst p).fst.length ≤ Prod.snd p) then
          decide (Prod.snd p = (Prod.fst p).snd)
        else
          decide ((Prod.fst p).snd < (Prod.fst p).fst.distinctVars.length) &&
            decide (((Prod.fst p).fst.distinctVars.getD (Prod.fst p).snd 0, b) ∈
              (Prod.fst p).fst.getD (Prod.snd p - (Prod.fst p).fst.distinctVars.length) [])) := by
    ext ⟨⟨φ, v⟩, c⟩
    simp only [cnfToOrderedEntry]
    by_cases h : c < φ.distinctVars.length ∨ φ.distinctVars.length + φ.length ≤ c
    · simp only [h, decide_true, ↓reduceIte]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.decide_and]
  rw [heq]
  exact ComputableInPolyTime.ite hcond hdiag hbody

private theorem computableInPolyTime_cnfToOrderedTable (b : Bool) :
    ComputableInPolyTime (cnfToOrderedTable b) encCNF encBits := by
  have hentry := computableInPolyTime_cnfToOrderedEntry b
  have hrow : ComputableInPolyTime
      (fun fv : PL.CNF ℕ × ℕ =>
        (List.range (cnfToOrderedSize fv.fst)).map fun c =>
          cnfToOrderedEntry fv.fst b c fv.snd)
      (encPair encCNF encUnary) (encList encBool) :=
    ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp
        (computableInPolyTime_cnfToOrderedSize.comp (ComputableInPolyTime.fst _ _)))
      hentry
  have hframed : ComputableInPolyTime (cnfToOrderedTable b) encCNF (encList encBool) :=
    ComputableInPolyTime.flatMapWithInput
      (ComputableInPolyTime.range.comp computableInPolyTime_cnfToOrderedSize)
      hrow
  exact (bits_encList_polyTime encBool).2.comp hframed

/-- **`cnfToOrdered` is computable in polynomial time** from `encCNF` to `encStructure`. -/
@[fun_prop]
theorem computableInPolyTime_cnfToOrdered :
    ComputableInPolyTime cnfToOrdered encCNF encStructure := by
  have ht := computableInPolyTime_cnfToOrderedTable true
  have hf := computableInPolyTime_cnfToOrderedTable false
  unfold cnfToOrdered
  fun_prop

/-- **`Complexity.SAT` reduces in polynomial time to `Ordered.SAT`** via `cnfToOrdered`. -/
theorem cnf_polyTimeReducible_orderedSAT :
    PolyTimeReducible encCNF encStructure Complexity.SAT (SAT.encodedLanguage FO.cnf.vocabulary) :=
  ⟨cnfToOrdered, computableInPolyTime_cnfToOrdered, fun φ => (cnfToOrdered_mem_iff φ).symm⟩

/-! ### Machine-level `NP`-completeness (`encStructure`) and bidirectional `PolyTimeReducible`
bridges -/

/-- **`Ordered.SAT` is `NP`-hard** at `encStructure`. -/
theorem sat_npHard : NPHard encStructure (SAT.encodedLanguage FO.cnf.vocabulary) :=
  CookLevin.SAT_npHard.trans cnf_polyTimeReducible_orderedSAT

/-- **`Ordered.SAT` is `NP`-complete** at `encStructure`. -/
theorem sat_npComplete : NPComplete encStructure (SAT.encodedLanguage FO.cnf.vocabulary) :=
  ⟨sat_encodedLanguage_mem_NP, sat_npHard⟩

/-- **`Ordered.ThreeSAT` is `NP`-hard** at `encStructure`. -/
theorem threeSAT_npHard : NPHard encStructure (ThreeSAT.encodedLanguage FO.cnf.vocabulary) :=
  sat_npHard.trans sat_logSpaceReducible_ThreeSAT.polyTimeReducible

/-- **`Ordered.ThreeSAT` is `NP`-complete** at `encStructure`. -/
theorem threeSAT_npComplete :
    NPComplete encStructure (ThreeSAT.encodedLanguage FO.cnf.vocabulary) :=
  ⟨threeSAT_encodedLanguage_mem_NP, threeSAT_npHard⟩

/-- **`Ordered.SimpleThreeColorable` is `NP`-hard** at `encStructure`. -/
theorem simpleThreeColorable_npHard :
    NPHard encStructure (SimpleThreeColorable.encodedLanguage graphVocabulary) :=
  sat_npHard.trans sat_logSpaceReducible_SimpleThreeColorable.polyTimeReducible

/-- **`Ordered.SimpleThreeColorable` is `NP`-complete** at `encStructure`. -/
theorem simpleThreeColorable_npComplete :
    NPComplete encStructure (SimpleThreeColorable.encodedLanguage graphVocabulary) :=
  ⟨simpleThreeColorable_encodedLanguage_mem_NP, simpleThreeColorable_npHard⟩

/-- **`Ordered.ThreeColorable` is `NP`-hard** at `encStructure`. -/
theorem threeColorable_npHard :
    NPHard encStructure (ThreeColorable.encodedLanguage graphVocabulary) :=
  sat_npHard.trans sat_logSpaceReducible_ThreeColorable.polyTimeReducible

/-- **`Ordered.ThreeColorable` is `NP`-complete** at `encStructure`. -/
theorem threeColorable_npComplete :
    NPComplete encStructure (ThreeColorable.encodedLanguage graphVocabulary) :=
  ⟨threeColorable_encodedLanguage_mem_NP, threeColorable_npHard⟩

/-- **`Ordered.IndependentSet` is `NP`-hard** at `encStructure`. -/
theorem independentSet_npHard :
    NPHard encStructure (IndependentSet.encodedLanguage sizedGraphVocabulary) :=
  sat_npHard.trans sat_logSpaceReducible_IndependentSet.polyTimeReducible

/-- **`Ordered.IndependentSet` is `NP`-complete** at `encStructure`. -/
theorem independentSet_npComplete :
    NPComplete encStructure (IndependentSet.encodedLanguage sizedGraphVocabulary) :=
  ⟨independentSet_encodedLanguage_mem_NP, independentSet_npHard⟩

/-- **`Ordered.Clique` is `NP`-hard** at `encStructure`. -/
theorem clique_npHard :
    NPHard encStructure (Clique.encodedLanguage sizedGraphVocabulary) :=
  sat_npHard.trans sat_logSpaceReducible_Clique.polyTimeReducible

/-- **`Ordered.Clique` is `NP`-complete** at `encStructure`. -/
theorem clique_npComplete :
    NPComplete encStructure (Clique.encodedLanguage sizedGraphVocabulary) :=
  ⟨clique_encodedLanguage_mem_NP, clique_npHard⟩

/-- **`Ordered.VertexCover` is `NP`-hard** at `encStructure`. -/
theorem vertexCover_npHard :
    NPHard encStructure (VertexCover.encodedLanguage sizedGraphVocabulary) :=
  sat_npHard.trans sat_logSpaceReducible_VertexCover.polyTimeReducible

/-- **`Ordered.VertexCover` is `NP`-complete** at `encStructure`. -/
theorem vertexCover_npComplete :
    NPComplete encStructure (VertexCover.encodedLanguage sizedGraphVocabulary) :=
  ⟨vertexCover_encodedLanguage_mem_NP, vertexCover_npHard⟩

/-! #### Bidirectional `PolyTimeReducible` bridges to separately encoded `Cslib.Complexity`
problems -/

/-- **`Ordered.SAT` reduces in polynomial time to `Complexity.SAT`.** -/
theorem orderedSAT_polyTimeReducible_cnf :
    PolyTimeReducible encStructure encCNF (SAT.encodedLanguage FO.cnf.vocabulary) Complexity.SAT :=
  CookLevin.SAT_npHard encStructure (SAT.encodedLanguage FO.cnf.vocabulary)
    sat_encodedLanguage_mem_NP

/-- **`Complexity.ThreeSAT` reduces in polynomial time to `Ordered.ThreeSAT`.** -/
theorem threeSAT_polyTimeReducible_orderedThreeSAT :
    PolyTimeReducible encCNF encStructure
      Complexity.ThreeSAT (ThreeSAT.encodedLanguage FO.cnf.vocabulary) :=
  threeSAT_npHard encCNF Complexity.ThreeSAT Complexity.ThreeSAT.mem_NP

/-- **`Ordered.ThreeSAT` reduces in polynomial time to `Complexity.ThreeSAT`.** -/
theorem orderedThreeSAT_polyTimeReducible_threeSAT :
    PolyTimeReducible encStructure encCNF
      (ThreeSAT.encodedLanguage FO.cnf.vocabulary) Complexity.ThreeSAT :=
  ThreeSAT_npHard encStructure (ThreeSAT.encodedLanguage FO.cnf.vocabulary)
    threeSAT_encodedLanguage_mem_NP

/-- **`Complexity.ThreeColoring` reduces in polynomial time to
`Ordered.SimpleThreeColorable`.** -/
theorem threeColoring_polyTimeReducible_orderedSimpleThreeColorable :
    PolyTimeReducible encGraph encStructure
      Complexity.ThreeColoring (SimpleThreeColorable.encodedLanguage graphVocabulary) :=
  simpleThreeColorable_npHard encGraph Complexity.ThreeColoring (Complexity.KColoring.mem_NP 3)

/-- **`Ordered.SimpleThreeColorable` reduces in polynomial time to
`Complexity.ThreeColoring`.** -/
theorem orderedSimpleThreeColorable_polyTimeReducible_threeColoring :
    PolyTimeReducible encStructure encGraph
      (SimpleThreeColorable.encodedLanguage graphVocabulary) Complexity.ThreeColoring :=
  ThreeColoring_npHard encStructure (SimpleThreeColorable.encodedLanguage graphVocabulary)
    simpleThreeColorable_encodedLanguage_mem_NP

/-- **`Complexity.ThreeColoring` reduces in polynomial time to `Ordered.ThreeColorable`.** -/
theorem threeColoring_polyTimeReducible_orderedThreeColorable :
    PolyTimeReducible encGraph encStructure
      Complexity.ThreeColoring (ThreeColorable.encodedLanguage graphVocabulary) :=
  threeColorable_npHard encGraph Complexity.ThreeColoring (Complexity.KColoring.mem_NP 3)

/-- **`Ordered.ThreeColorable` reduces in polynomial time to `Complexity.ThreeColoring`.** -/
theorem orderedThreeColorable_polyTimeReducible_threeColoring :
    PolyTimeReducible encStructure encGraph
      (ThreeColorable.encodedLanguage graphVocabulary) Complexity.ThreeColoring :=
  ThreeColoring_npHard encStructure (ThreeColorable.encodedLanguage graphVocabulary)
    threeColorable_encodedLanguage_mem_NP

/-- **`Complexity.IndependentSet` reduces in polynomial time to `Ordered.IndependentSet`.** -/
theorem independentSet_polyTimeReducible_orderedIndependentSet :
    PolyTimeReducible encIndependentSetInstance encStructure
      Complexity.IndependentSet (IndependentSet.encodedLanguage sizedGraphVocabulary) :=
  independentSet_npHard encIndependentSetInstance Complexity.IndependentSet
    Complexity.IndependentSet.mem_NP

/-- **`Ordered.IndependentSet` reduces in polynomial time to `Complexity.IndependentSet`.** -/
theorem orderedIndependentSet_polyTimeReducible_independentSet :
    PolyTimeReducible encStructure encIndependentSetInstance
      (IndependentSet.encodedLanguage sizedGraphVocabulary) Complexity.IndependentSet :=
  IndependentSet_npHard encStructure (IndependentSet.encodedLanguage sizedGraphVocabulary)
    independentSet_encodedLanguage_mem_NP

/-- **`Complexity.Clique` reduces in polynomial time to `Ordered.Clique`.** -/
theorem clique_polyTimeReducible_orderedClique :
    PolyTimeReducible encCliqueInstance encStructure
      Complexity.Clique (Clique.encodedLanguage sizedGraphVocabulary) :=
  clique_npHard encCliqueInstance Complexity.Clique Complexity.Clique.mem_NP

/-- **`Ordered.Clique` reduces in polynomial time to `Complexity.Clique`.** -/
theorem orderedClique_polyTimeReducible_clique :
    PolyTimeReducible encStructure encCliqueInstance
      (Clique.encodedLanguage sizedGraphVocabulary) Complexity.Clique :=
  Clique_npHard encStructure (Clique.encodedLanguage sizedGraphVocabulary)
    clique_encodedLanguage_mem_NP

/-- **`Complexity.VertexCover` reduces in polynomial time to `Ordered.VertexCover`.** -/
theorem vertexCover_polyTimeReducible_orderedVertexCover :
    PolyTimeReducible encVertexCoverInstance encStructure
      Complexity.VertexCover (VertexCover.encodedLanguage sizedGraphVocabulary) :=
  vertexCover_npHard encVertexCoverInstance Complexity.VertexCover
    Complexity.VertexCover.mem_NP

/-- **`Ordered.VertexCover` reduces in polynomial time to `Complexity.VertexCover`.** -/
theorem orderedVertexCover_polyTimeReducible_vertexCover :
    PolyTimeReducible encStructure encVertexCoverInstance
      (VertexCover.encodedLanguage sizedGraphVocabulary) Complexity.VertexCover :=
  VertexCover_npHard encStructure (VertexCover.encodedLanguage sizedGraphVocabulary)
    vertexCover_encodedLanguage_mem_NP

end Cslib.Logic.FO.Ordered
