/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Projection
public import CslibFrontier.Computability.Complexity.Fagin.Ordered
public import CslibFrontier.Logics.FirstOrder.Ordered.Problems.CNF
public import CslibFrontier.Logics.FirstOrder.Ordered.Problems.Coloring
public import CslibFrontier.Logics.FirstOrder.Ordered.Problems.SizedGraph
import CslibFrontier.Computability.Complexity.Fagin.Ordered.Verifier
import CslibFrontier.Logics.FirstOrder.Ordered.Problems.IndependentSetReduction
import CslibFrontier.Logics.SecondOrder.Coloring
import CslibFrontier.Logics.SecondOrder.IndependentSet

/-!
# ESO definability, native `NP` membership, and logspace reductions for ordered problems

For each of the seven canonical ordered target queries
* `Ordered.SAT` and `Ordered.ThreeSAT` over `FO.cnf`,
* `Ordered.ThreeColorable` and `Ordered.SimpleThreeColorable` over `FirstOrder.Language.graph`, and
* `Ordered.IndependentSet`, `Ordered.Clique`, and `Ordered.VertexCover` over `FO.sizedGraph`,

pushing the existing unordered existential second-order defining sentences forward along
`LHom.sumInl : L →ᴸ Ordered.language L` (`ESO.Sentence.mapLanguage`, `ESODefinable.of_definable`)
establishes `Ordered.ESODefinable`, and the ordered Fagin verifier
(`ESODefinable.encodedLanguage_mem_NP`) places every source-only encoded query language in native
`NP` at `encStructure`.

Applying `QFProjectionReduces.logSpaceReducible` to the certified `BIT`-free quantifier-free
projections in `CslibFrontier.Logics.FirstOrder.Ordered.Problems.*` yields deterministic
logarithmic-space many-one reductions (`LogSpaceReducible encStructure encStructure`) across all
corresponding encoded languages.

## Main definitions

* `Cslib.Logic.ESO.Sentence.mapLanguage`: push an existential second-order sentence forward along a
  first-order language homomorphism without changing its relation variables.

## Main results

* `Cslib.Logic.ESO.Sentence.realize_mapLanguage`: `mapLanguage` preserves satisfaction on expansions
  along `g : L →ᴸ L'`.
* `Cslib.Logic.FO.Ordered.ESODefinable.of_definable`: any unordered `ESO.Definable` class restricts
  to an `Ordered.ESODefinable` query on canonically ordered structures.
* `Cslib.Logic.FO.Ordered.esoDefinable_SAT`, `Cslib.Logic.FO.Ordered.esoDefinable_ThreeSAT`,
  `Cslib.Logic.FO.Ordered.esoDefinable_ThreeColorable`,
  `Cslib.Logic.FO.Ordered.esoDefinable_SimpleThreeColorable`,
  `Cslib.Logic.FO.Ordered.esoDefinable_IndependentSet`,
  `Cslib.Logic.FO.Ordered.esoDefinable_Clique`,
  `Cslib.Logic.FO.Ordered.esoDefinable_VertexCover`: existential second-order definability of all
  seven canonical ordered queries.
* `Cslib.Logic.FO.Ordered.sat_encodedLanguage_mem_NP`,
  `Cslib.Logic.FO.Ordered.threeSAT_encodedLanguage_mem_NP`,
  `Cslib.Logic.FO.Ordered.threeColorable_encodedLanguage_mem_NP`,
  `Cslib.Logic.FO.Ordered.simpleThreeColorable_encodedLanguage_mem_NP`,
  `Cslib.Logic.FO.Ordered.independentSet_encodedLanguage_mem_NP`,
  `Cslib.Logic.FO.Ordered.clique_encodedLanguage_mem_NP`,
  `Cslib.Logic.FO.Ordered.vertexCover_encodedLanguage_mem_NP`: native `NP` membership at
  `encStructure`.
* `Cslib.Logic.FO.Ordered.independentSet_logSpaceReducible_Clique`,
  `Cslib.Logic.FO.Ordered.clique_logSpaceReducible_IndependentSet`,
  `Cslib.Logic.FO.Ordered.independentSet_logSpaceReducible_VertexCover`,
  `Cslib.Logic.FO.Ordered.vertexCover_logSpaceReducible_IndependentSet`,
  `Cslib.Logic.FO.Ordered.clique_logSpaceReducible_VertexCover`,
  `Cslib.Logic.FO.Ordered.vertexCover_logSpaceReducible_Clique`,
  `Cslib.Logic.FO.Ordered.sat_logSpaceReducible_ThreeSAT`,
  `Cslib.Logic.FO.Ordered.sat_logSpaceReducible_IndependentSet`,
  `Cslib.Logic.FO.Ordered.sat_logSpaceReducible_Clique`,
  `Cslib.Logic.FO.Ordered.sat_logSpaceReducible_VertexCover`,
  `Cslib.Logic.FO.Ordered.sat_logSpaceReducible_SimpleThreeColorable`,
  `Cslib.Logic.FO.Ordered.sat_logSpaceReducible_ThreeColorable`: deterministic logarithmic-space
  many-one reductions at `encStructure`.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995]
-/

public section

universe u v u' v' w

namespace Cslib.Logic

open FirstOrder Language Structure CategoryTheory
open Cslib.Complexity Turing.MultiTapeTM

namespace ESO.Sentence

/-- Push an existential second-order sentence forward along a language homomorphism `g : L →ᴸ L'`,
leaving the quantified relation variables unchanged. -/
@[expose] def mapLanguage {L : Language.{u, v}} {L' : Language.{u', v'}}
    (g : L →ᴸ L') (Φ : Sentence L) : Sentence L' where
  Var := Φ.Var
  arity := Φ.arity
  matrix := (LHom.sumMap g (LHom.id (varLanguage Φ.arity))).onSentence Φ.matrix

/-- On an expansion along `g : L →ᴸ L'`, `Φ.mapLanguage g` has the same truth value as `Φ`. -/
theorem realize_mapLanguage {L : Language.{u, v}} {L' : Language.{u', v'}}
    {M : Type w} [L.Structure M] [L'.Structure M] (g : L →ᴸ L') [g.IsExpansionOn M]
    (Φ : Sentence L) :
    (Φ.mapLanguage g).Realize M ↔ Φ.Realize M := by
  refine exists_congr fun R => ?_
  exact @LHom.realize_onSentence _ _ M
    (@sumStructure _ _ M _ (varLanguage.structure R))
    (@sumStructure _ _ M _ (varLanguage.structure R))
    (LHom.sumMap g (LHom.id (varLanguage Φ.arity)))
    (@LHom.sumMap_isExpansionOn _ _ g _ _ (LHom.id (varLanguage Φ.arity)) M _ _
      (varLanguage.structure R) (varLanguage.structure R)
      inferInstance (@LHom.id_isExpansionOn _ M (varLanguage.structure R)))
    Φ.matrix

end ESO.Sentence

namespace FO.Ordered

/-- Every unordered existential second-order definable class `S` restricts to an `ESODefinable`
ordered query `{M | Bundled.of M ∈ S}` via `LHom.sumInl : L →ᴸ Ordered.language L`. -/
theorem ESODefinable.of_definable {L : Language.{u, v}}
    {S : Set (Bundled.{0} L.Structure)} (hS : ESO.Definable S) :
    ESODefinable {M : Ordered.Structure L | Bundled.of (c := L.Structure) M ∈ S} := by
  obtain ⟨Φ, hΦ⟩ := hS
  refine ⟨Φ.mapLanguage (LHom.sumInl : L →ᴸ language L), fun M => ?_⟩
  have hfin : Finite (Bundled.of (c := L.Structure) M) := inferInstanceAs (Finite (Fin M.size))
  have h1 : Bundled.of (c := L.Structure) M ∈ S ↔ Φ.Realize M :=
    @hΦ (Bundled.of (c := L.Structure) M) hfin
  exact h1.trans (Φ.realize_mapLanguage (M := M) (LHom.sumInl : L →ᴸ language L)).symm

/-! ### Existential second-order definability of canonical ordered queries -/

/-- **`Ordered.SAT` is existential second-order definable.** -/
theorem esoDefinable_SAT : ESODefinable SAT :=
  ESODefinable.of_definable FO.cnf.definable_SAT

/-- **`Ordered.ThreeSAT` is existential second-order definable.** -/
theorem esoDefinable_ThreeSAT : ESODefinable ThreeSAT :=
  ESODefinable.of_definable FO.cnf.definable_ThreeSAT

/-- **`Ordered.ThreeColorable` is existential second-order definable.** -/
theorem esoDefinable_ThreeColorable : ESODefinable ThreeColorable :=
  ESODefinable.of_definable FO.graph.definable_ThreeColorable

/-- **`Ordered.SimpleThreeColorable` is existential second-order definable.** -/
theorem esoDefinable_SimpleThreeColorable : ESODefinable SimpleThreeColorable :=
  ESODefinable.of_definable FO.graph.definable_SimpleThreeColorable

/-- **`Ordered.IndependentSet` is existential second-order definable.** -/
theorem esoDefinable_IndependentSet : ESODefinable IndependentSet :=
  ESODefinable.of_definable FO.sizedGraph.definable_IndependentSet

/-- **`Ordered.Clique` is existential second-order definable.** -/
theorem esoDefinable_Clique : ESODefinable Clique :=
  ESODefinable.of_definable FO.sizedGraph.definable_Clique

/-- **`Ordered.VertexCover` is existential second-order definable.** -/
theorem esoDefinable_VertexCover : ESODefinable VertexCover :=
  ESODefinable.of_definable FO.sizedGraph.definable_VertexCover

/-! ### Native `NP` membership at `encStructure` -/

/-- **`Ordered.SAT` belongs to native `NP`** at `encStructure`. -/
theorem sat_encodedLanguage_mem_NP :
    SAT.encodedLanguage FO.cnf.vocabulary ∈ NP encStructure :=
  esoDefinable_SAT.encodedLanguage_mem_NP FO.cnf.vocabulary

/-- **`Ordered.ThreeSAT` belongs to native `NP`** at `encStructure`. -/
theorem threeSAT_encodedLanguage_mem_NP :
    ThreeSAT.encodedLanguage FO.cnf.vocabulary ∈ NP encStructure :=
  esoDefinable_ThreeSAT.encodedLanguage_mem_NP FO.cnf.vocabulary

/-- **`Ordered.ThreeColorable` belongs to native `NP`** at `encStructure`. -/
theorem threeColorable_encodedLanguage_mem_NP :
    ThreeColorable.encodedLanguage graphVocabulary ∈ NP encStructure :=
  esoDefinable_ThreeColorable.encodedLanguage_mem_NP graphVocabulary

/-- **`Ordered.SimpleThreeColorable` belongs to native `NP`** at `encStructure`. -/
theorem simpleThreeColorable_encodedLanguage_mem_NP :
    SimpleThreeColorable.encodedLanguage graphVocabulary ∈ NP encStructure :=
  esoDefinable_SimpleThreeColorable.encodedLanguage_mem_NP graphVocabulary

/-- **`Ordered.IndependentSet` belongs to native `NP`** at `encStructure`. -/
theorem independentSet_encodedLanguage_mem_NP :
    IndependentSet.encodedLanguage sizedGraphVocabulary ∈ NP encStructure :=
  esoDefinable_IndependentSet.encodedLanguage_mem_NP sizedGraphVocabulary

/-- **`Ordered.Clique` belongs to native `NP`** at `encStructure`. -/
theorem clique_encodedLanguage_mem_NP :
    Clique.encodedLanguage sizedGraphVocabulary ∈ NP encStructure :=
  esoDefinable_Clique.encodedLanguage_mem_NP sizedGraphVocabulary

/-- **`Ordered.VertexCover` belongs to native `NP`** at `encStructure`. -/
theorem vertexCover_encodedLanguage_mem_NP :
    VertexCover.encodedLanguage sizedGraphVocabulary ∈ NP encStructure :=
  esoDefinable_VertexCover.encodedLanguage_mem_NP sizedGraphVocabulary

/-! ### Logspace many-one reductions at `encStructure` -/

/-- **`Ordered.IndependentSet` reduces to `Ordered.Clique` in deterministic logarithmic space.** -/
theorem independentSet_logSpaceReducible_Clique :
    LogSpaceReducible encStructure encStructure
      (IndependentSet.encodedLanguage sizedGraphVocabulary)
      (Clique.encodedLanguage sizedGraphVocabulary) :=
  independentSet_qfProjectionReduces_Clique.logSpaceReducible
    sizedGraphVocabulary sizedGraphVocabulary

/-- **`Ordered.Clique` reduces to `Ordered.IndependentSet` in deterministic logarithmic space.** -/
theorem clique_logSpaceReducible_IndependentSet :
    LogSpaceReducible encStructure encStructure
      (Clique.encodedLanguage sizedGraphVocabulary)
      (IndependentSet.encodedLanguage sizedGraphVocabulary) :=
  clique_qfProjectionReduces_IndependentSet.logSpaceReducible
    sizedGraphVocabulary sizedGraphVocabulary

/-- **`Ordered.IndependentSet` reduces to `Ordered.VertexCover` in deterministic logarithmic
space.** -/
theorem independentSet_logSpaceReducible_VertexCover :
    LogSpaceReducible encStructure encStructure
      (IndependentSet.encodedLanguage sizedGraphVocabulary)
      (VertexCover.encodedLanguage sizedGraphVocabulary) :=
  independentSet_qfProjectionReduces_VertexCover.logSpaceReducible
    sizedGraphVocabulary sizedGraphVocabulary

/-- **`Ordered.VertexCover` reduces to `Ordered.IndependentSet` in deterministic logarithmic
space.** -/
theorem vertexCover_logSpaceReducible_IndependentSet :
    LogSpaceReducible encStructure encStructure
      (VertexCover.encodedLanguage sizedGraphVocabulary)
      (IndependentSet.encodedLanguage sizedGraphVocabulary) :=
  vertexCover_qfProjectionReduces_IndependentSet.logSpaceReducible
    sizedGraphVocabulary sizedGraphVocabulary

/-- **`Ordered.Clique` reduces to `Ordered.VertexCover` in deterministic logarithmic space.** -/
theorem clique_logSpaceReducible_VertexCover :
    LogSpaceReducible encStructure encStructure
      (Clique.encodedLanguage sizedGraphVocabulary)
      (VertexCover.encodedLanguage sizedGraphVocabulary) :=
  clique_qfProjectionReduces_VertexCover.logSpaceReducible
    sizedGraphVocabulary sizedGraphVocabulary

/-- **`Ordered.VertexCover` reduces to `Ordered.Clique` in deterministic logarithmic space.** -/
theorem vertexCover_logSpaceReducible_Clique :
    LogSpaceReducible encStructure encStructure
      (VertexCover.encodedLanguage sizedGraphVocabulary)
      (Clique.encodedLanguage sizedGraphVocabulary) :=
  vertexCover_qfProjectionReduces_Clique.logSpaceReducible
    sizedGraphVocabulary sizedGraphVocabulary

/-- **`Ordered.SAT` reduces to `Ordered.ThreeSAT` in deterministic logarithmic space.** -/
theorem sat_logSpaceReducible_ThreeSAT :
    LogSpaceReducible encStructure encStructure
      (SAT.encodedLanguage FO.cnf.vocabulary)
      (ThreeSAT.encodedLanguage FO.cnf.vocabulary) :=
  sat_qfProjectionReduces_ThreeSAT.logSpaceReducible FO.cnf.vocabulary FO.cnf.vocabulary

/-- **`Ordered.SAT` reduces to `Ordered.IndependentSet` in deterministic logarithmic space.** -/
theorem sat_logSpaceReducible_IndependentSet :
    LogSpaceReducible encStructure encStructure
      (SAT.encodedLanguage FO.cnf.vocabulary)
      (IndependentSet.encodedLanguage sizedGraphVocabulary) :=
  sat_qfProjectionReduces_IndependentSet.logSpaceReducible FO.cnf.vocabulary sizedGraphVocabulary

/-- **`Ordered.SAT` reduces to `Ordered.Clique` in deterministic logarithmic space.** -/
theorem sat_logSpaceReducible_Clique :
    LogSpaceReducible encStructure encStructure
      (SAT.encodedLanguage FO.cnf.vocabulary)
      (Clique.encodedLanguage sizedGraphVocabulary) :=
  sat_qfProjectionReduces_Clique.logSpaceReducible FO.cnf.vocabulary sizedGraphVocabulary

/-- **`Ordered.SAT` reduces to `Ordered.VertexCover` in deterministic logarithmic space.** -/
theorem sat_logSpaceReducible_VertexCover :
    LogSpaceReducible encStructure encStructure
      (SAT.encodedLanguage FO.cnf.vocabulary)
      (VertexCover.encodedLanguage sizedGraphVocabulary) :=
  sat_qfProjectionReduces_VertexCover.logSpaceReducible FO.cnf.vocabulary sizedGraphVocabulary

/-- **`Ordered.SAT` reduces to `Ordered.SimpleThreeColorable` in deterministic logarithmic
space.** -/
theorem sat_logSpaceReducible_SimpleThreeColorable :
    LogSpaceReducible encStructure encStructure
      (SAT.encodedLanguage FO.cnf.vocabulary)
      (SimpleThreeColorable.encodedLanguage graphVocabulary) :=
  sat_qfProjectionReduces_SimpleThreeColorable.logSpaceReducible FO.cnf.vocabulary graphVocabulary

/-- **`Ordered.SAT` reduces to `Ordered.ThreeColorable` in deterministic logarithmic space.** -/
theorem sat_logSpaceReducible_ThreeColorable :
    LogSpaceReducible encStructure encStructure
      (SAT.encodedLanguage FO.cnf.vocabulary)
      (ThreeColorable.encodedLanguage graphVocabulary) :=
  sat_qfProjectionReduces_ThreeColorable.logSpaceReducible FO.cnf.vocabulary graphVocabulary

end FO.Ordered

end Cslib.Logic
