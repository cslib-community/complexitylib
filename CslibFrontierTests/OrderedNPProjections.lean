/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Fagin.Ordered.Problems
import CslibFrontier.Logics.FirstOrder.Ordered.Problems.IndependentSetReduction
import Mathlib.Tactic.FinCases

/-!
# Tests for canonical ordered `NP` queries, native `NP` membership, and `≤_qfp` projections

Concrete positive instances, negative controls, and boundary checks for:
* `CslibFrontier/Logics/FirstOrder/Ordered/Problems/CNF.lean`,
* `CslibFrontier/Logics/FirstOrder/Ordered/Problems/Coloring.lean`,
* `CslibFrontier/Logics/FirstOrder/Ordered/Problems/SizedGraph.lean`,
* `CslibFrontier/Logics/FirstOrder/Ordered/Problems/IndependentSetReduction.lean`, and
* `CslibFrontier/Computability/Complexity/Fagin/Ordered/Problems.lean`.

Covers:
* wide 4-literal satisfiable vs unsatisfiable `FO.cnf` structures on the smallest ordered universe
  `Fin 2`, verifying that `twoFourLitSat ∉ Ordered.ThreeSAT` becomes a valid 3-CNF in
  `Ordered.ThreeSAT` on `Fin 32` under `satToThreeSATInterpretation`, while `twoUnsatUnits` maps to
  an unsatisfiable 3-CNF on `Fin 32`, a non-member of `Ordered.IndependentSet` on `Fin 16`, and a
  simple uncolorable graph on `Fin 64`;
* directed, simple, self-loop, and `K₄` graph structures separating `Ordered.SimpleThreeColorable`,
  `Ordered.ThreeColorable`, and uncolorable graphs;
* `FO.sizedGraph` boundary cases (`size = ∅`, `size = Set.univ`, and self-loop diagonal suppression
  under `complementEdgesInterpretation`) across `Ordered.IndependentSet`, `Ordered.Clique`, and
  `Ordered.VertexCover`;
* `IsQFProjectionMap`, `ProjectionReduces`, `Ordered.Reduces`, `Ordered.ESODefinable`, native `NP`
  membership at `encStructure`, and `LogSpaceReducible encStructure encStructure` corollaries.
-/

@[expose] public section

namespace Cslib.Tests.OrderedNPProjections

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered
open Cslib.Complexity Turing.MultiTapeTM

/-! ### Helper constructors for concrete ordered structures -/

/-- Build an ordered `FO.cnf` structure on `Fin n` (`2 ≤ n`) from Boolean literal tables. -/
def mkOrderedCNF (n : ℕ) (hn : 2 ≤ n) (posRel negRel : Fin n → Fin n → Bool) :
    Ordered.Structure FO.cnf where
  size := n
  size_ge_two := hn
  input :=
    { funMap := fun f => isEmptyElim f
      RelMap
        | .pos, x => posRel (x 0) (x 1) = true
        | .neg, x => negRel (x 0) (x 1) = true }

/-- Build an ordered `Language.graph` structure on `Fin n` (`2 ≤ n`). -/
def mkOrderedGraph (n : ℕ) (hn : 2 ≤ n) (edge : Fin n → Fin n → Bool) :
    Ordered.Structure Language.graph where
  size := n
  size_ge_two := hn
  input :=
    { funMap := fun f => isEmptyElim f
      RelMap
        | .adj, x => edge (x 0) (x 1) = true }

/-- Build an ordered `FO.sizedGraph` structure on `Fin n` (`2 ≤ n`). -/
def mkOrderedSizedGraph (n : ℕ) (hn : 2 ≤ n) (edge : Fin n → Fin n → Bool)
    (sz : Fin n → Bool) : Ordered.Structure FO.sizedGraph where
  size := n
  size_ge_two := hn
  input :=
    { funMap := fun f => isEmptyElim f
      RelMap
        | .adj, x => edge (x 0) (x 1) = true
        | .size, x => sz (x 0) = true }

/-! ### Concrete `FO.cnf` instances on `Fin 2` (`SAT`, `ThreeSAT`, and all three `SAT` gadgets) -/

/-- On `Fin 2`, clause `0` has all 4 literals `(x₀ ∨ x₁ ∨ ¬ x₀ ∨ ¬ x₁)` and clause `1` has unit
literal `x₁`: satisfiable (`A x ↔ x = 1`) but NOT 3-CNF! -/
def twoFourLitSat : Ordered.Structure FO.cnf :=
  mkOrderedCNF 2 (by decide) (fun c x => c == 0 || x == 1) (fun c _ => c == 0)

/-- On `Fin 2`, clause `0` has unit literal `x₀` and clause `1` has unit literal `¬ x₀`: 3-CNF but
unsatisfiable. -/
def twoUnsatUnits : Ordered.Structure FO.cnf :=
  mkOrderedCNF 2 (by decide) (fun c x => c == 0 && x == 0) (fun c x => c == 1 && x == 0)

theorem twoFourLitSat_mem_SAT : twoFourLitSat ∈ Ordered.SAT := by
  refine ⟨fun x : Fin 2 => x = 1, fun (c : Fin 2) => ?_⟩
  exact ⟨(1 : Fin 2), .inl ⟨by fin_cases c <;> (change _ = true; decide), rfl⟩⟩

theorem twoFourLitSat_not_mem_ThreeSAT : twoFourLitSat ∉ Ordered.ThreeSAT := by
  rintro ⟨h3, -⟩
  have hc0 : (FO.cnf.literals (0 : Fin twoFourLitSat.size)).encard ≤ 3 := h3 0
  have huniv : FO.cnf.literals (0 : Fin twoFourLitSat.size) = Set.univ := by
    ext ⟨b, x⟩
    simp only [Set.mem_univ, iff_true, FO.cnf.mem_literals]
    change Fin 2 at x
    cases b <;> fin_cases x <;> (change _ = true; decide)
  rw [huniv] at hc0
  have hcard : (Set.univ : Set (Bool × Fin twoFourLitSat.size)).encard = 4 := by
    change (Set.univ : Set (Bool × Fin 2)).encard = 4
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
    decide
  rw [hcard] at hc0
  exact absurd hc0 (by decide)

theorem twoUnsatUnits_not_mem_SAT : twoUnsatUnits ∉ Ordered.SAT := by
  rintro ⟨A, hA⟩
  obtain ⟨x0, ⟨h0, hx0⟩ | ⟨h0, -⟩⟩ := hA (0 : Fin 2)
  · have rx0 : x0 = (0 : Fin 2) := by
      change Fin 2 at x0
      fin_cases x0
      · rfl
      · exact absurd h0 (by change ¬ _ = true; decide)
    subst rx0
    obtain ⟨x1, ⟨h1, -⟩ | ⟨h1, hnx1⟩⟩ := hA (1 : Fin 2)
    · change Fin 2 at x1
      fin_cases x1 <;> exact absurd h1 (by change ¬ _ = true; decide)
    · have rx1 : x1 = (0 : Fin 2) := by
        change Fin 2 at x1
        fin_cases x1
        · rfl
        · exact absurd h1 (by change ¬ _ = true; decide)
      subst rx1
      exact hnx1 hx0
  · change Fin 2 at x0
    fin_cases x0 <;> exact absurd h0 (by change ¬ _ = true; decide)

/-- **`satToThreeSATInterpretation` splits a 4-literal clause on `Fin 2` into a 3-CNF on `Fin 32`**,
accepting `twoFourLitSat` and rejecting `twoUnsatUnits` while maintaining `IsThreeCNF` on both. -/
example :
    let hI := satToThreeSATInterpretation.admissible_toDomainInterpretation (by decide)
    let Mpos := satToThreeSATInterpretation.toDomainInterpretation.map hI twoFourLitSat
    let Mneg := satToThreeSATInterpretation.toDomainInterpretation.map hI twoUnsatUnits
    Mpos.size = 32 ∧ Mneg.size = 32 ∧
      FO.cnf.IsThreeCNF Mpos ∧ FO.cnf.IsThreeCNF Mneg ∧
      Mpos ∈ Ordered.ThreeSAT ∧ Mneg ∉ Ordered.ThreeSAT := by
  refine ⟨satToThreeSATInterpretation.card_toDomainInterpretation _,
    satToThreeSATInterpretation.card_toDomainInterpretation _,
    isThreeCNF_satToThreeSAT twoFourLitSat,
    isThreeCNF_satToThreeSAT twoUnsatUnits, ?_, ?_⟩
  · rw [mem_ThreeSAT_satToThreeSATInterpretation]
    exact twoFourLitSat_mem_SAT
  · rw [mem_ThreeSAT_satToThreeSATInterpretation]
    exact twoUnsatUnits_not_mem_SAT

/-- **`satToIndependentSetInterpretation` (`Fin 2 → Fin 16`)** separates `twoFourLitSat` from
`twoUnsatUnits`. -/
example :
    let hI := satToIndependentSetInterpretation.admissible_toDomainInterpretation (by decide)
    let Gpos := satToIndependentSetInterpretation.toDomainInterpretation.map hI twoFourLitSat
    let Gneg := satToIndependentSetInterpretation.toDomainInterpretation.map hI twoUnsatUnits
    Gpos.size = 16 ∧ Gpos ∈ Ordered.IndependentSet ∧ Gneg ∉ Ordered.IndependentSet := by
  refine ⟨satToIndependentSetInterpretation.card_toDomainInterpretation _, ?_, ?_⟩
  · rw [mem_IndependentSet_satToIndependentSetInterpretation]
    exact twoFourLitSat_mem_SAT
  · rw [mem_IndependentSet_satToIndependentSetInterpretation]
    exact twoUnsatUnits_not_mem_SAT

/-- **`satToColoringInterpretation` (`Fin 2 → Fin 64`)** produces simple graphs on all inputs and
separates `twoFourLitSat` from `twoUnsatUnits` for both `SimpleThreeColorable` and
`ThreeColorable`. -/
example :
    let hI := satToColoringInterpretation.admissible_toDomainInterpretation (by decide)
    let Cpos := satToColoringInterpretation.toDomainInterpretation.map hI twoFourLitSat
    let Cneg := satToColoringInterpretation.toDomainInterpretation.map hI twoUnsatUnits
    Cpos.size = 64 ∧ (Cneg ⊨ Theory.simpleGraph) ∧
      Cpos ∈ Ordered.SimpleThreeColorable ∧ Cneg ∉ Ordered.SimpleThreeColorable ∧
      Cpos ∈ Ordered.ThreeColorable ∧ Cneg ∉ Ordered.ThreeColorable := by
  refine ⟨satToColoringInterpretation.card_toDomainInterpretation _,
    simpleGraph_satToColoring twoUnsatUnits, ?_, ?_, ?_, ?_⟩
  · rw [mem_SimpleThreeColorable_satToColoringInterpretation]
    exact twoFourLitSat_mem_SAT
  · rw [mem_SimpleThreeColorable_satToColoringInterpretation]
    exact twoUnsatUnits_not_mem_SAT
  · rw [mem_ThreeColorable_satToColoringInterpretation]
    exact twoFourLitSat_mem_SAT
  · rw [mem_ThreeColorable_satToColoringInterpretation]
    exact twoUnsatUnits_not_mem_SAT

/-! ### Graph 3-colorability controls (directed arc, self-loop, triangle, and `K₄`) -/

/-- `Fin 3` with the single directed arc `0 → 1`: 3-colorable, but asymmetric so not simple. -/
def threeDirectedArc : Ordered.Structure Language.graph :=
  mkOrderedGraph 3 (by decide) fun x y => x == 0 && y == 1

/-- `Fin 2` with a self-loop `0 → 0`: uncolorable under any number of colors. -/
def twoSelfLoop : Ordered.Structure Language.graph :=
  mkOrderedGraph 2 (by decide) fun x y => x == 0 && y == 0

/-- Undirected `K₃` on `Fin 3`. -/
def threeTriangle : Ordered.Structure Language.graph :=
  mkOrderedGraph 3 (by decide) fun x y => x != y

/-- Undirected `K₄` on `Fin 4`. -/
def fourClique : Ordered.Structure Language.graph :=
  mkOrderedGraph 4 (by decide) fun x y => x != y

/-- `threeDirectedArc` separates `Ordered.ThreeColorable` from `Ordered.SimpleThreeColorable`. -/
example :
    threeDirectedArc ∈ Ordered.ThreeColorable ∧
      threeDirectedArc ∉ Ordered.SimpleThreeColorable := by
  refine ⟨⟨id, fun x y hxy heq => ?_⟩, fun ⟨hsimple, _⟩ => ?_⟩
  · subst heq
    have hfalse : ((x == 0 && x == 1) : Bool) = true := hxy
    change Fin 3 at x
    revert hfalse
    fin_cases x <;> decide
  · rw [Theory.simpleGraph_model_iff] at hsimple
    obtain ⟨_, ⟨hsymm⟩⟩ := hsimple
    have h10 : RelMap (M := threeDirectedArc) Language.adj ![(1 : Fin 3), (0 : Fin 3)] :=
      hsymm (0 : Fin 3) (1 : Fin 3) (by change _ = true; decide)
    change ((1 : Fin 3) == 0 && (0 : Fin 3) == 1) = true at h10
    exact absurd h10 (by decide)

/-- Self-loops and `K₄` are outside `Ordered.ThreeColorable`, while `K₃` belongs to
`Ordered.SimpleThreeColorable`. -/
example :
    twoSelfLoop ∉ Ordered.ThreeColorable ∧
      threeTriangle ∈ Ordered.SimpleThreeColorable ∧
      fourClique ∉ Ordered.ThreeColorable := by
  refine ⟨fun ⟨f, hf⟩ => hf (0 : Fin 2) (0 : Fin 2) (by change _ = true; decide) rfl,
    ?_, fun ⟨f, hf⟩ => ?_⟩
  · refine ⟨?_, ⟨id, fun x y hxy heq => ?_⟩⟩
    · rw [Theory.simpleGraph_model_iff]
      refine ⟨⟨fun (x : Fin 3) => ?_⟩, ⟨fun (x y : Fin 3) hxy => ?_⟩⟩
      · change ¬ ((x : Fin 3) != x) = true
        fin_cases x <;> decide
      · change ((x : Fin 3) != y) = true at hxy
        change ((y : Fin 3) != x) = true
        revert hxy
        fin_cases x <;> fin_cases y <;> decide
    · subst heq
      change Fin 3 at x
      have hfalse : ((x : Fin 3) != x) = true := hxy
      revert hfalse
      fin_cases x <;> decide
  · have hinj : Function.Injective f := by
      intro (x : Fin 4) (y : Fin 4) hxy
      by_contra hne
      have hadj : RelMap (M := fourClique) Language.adj ![x, y] := by
        change ((x : Fin 4) != y) = true
        exact bne_iff_ne.mpr hne
      exact hf x y hadj hxy
    have hle : Fintype.card (Fin 4) ≤ Fintype.card (Fin 3) := Fintype.card_le_of_injective f hinj
    exact absurd hle (by decide)

/-! ### `FO.sizedGraph` boundary cases (`size = ∅`, `size = univ`, and diagonal loop suppression) -/

/-- `K₂` on `Fin 2` with `size = ∅` (target cardinality `0`). -/
def k2EmptySize : Ordered.Structure FO.sizedGraph :=
  mkOrderedSizedGraph 2 (by decide) (fun x y => x != y) (fun _ => false)

/-- `K₂` on `Fin 2` with `size = univ` (target cardinality `2`). -/
def k2FullSize : Ordered.Structure FO.sizedGraph :=
  mkOrderedSizedGraph 2 (by decide) (fun x y => x != y) (fun _ => true)

/-- Self-loop `0 → 0` only on `Fin 2` with `size = univ`: edgeless off the diagonal, so it has an
independent set of size `2`, while its `complementEdgesInterpretation` image is loop-free `K₂` and
therefore has NO independent set of size `2`! -/
def loopOnlyFullSize : Ordered.Structure FO.sizedGraph :=
  mkOrderedSizedGraph 2 (by decide) (fun x y => x == 0 && y == 0) (fun _ => true)

/-- Helper: a subset of `Fin 2` of cardinality `2` contains both `0` and `1`. -/
private theorem mem_zero_and_one_of_ncard_two {s : Set (Fin 2)} (hs : s.ncard = 2) :
    (0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∈ s := by
  by_contra hnot
  by_cases h0 : (0 : Fin 2) ∈ s
  · have h1 : (1 : Fin 2) ∉ s := fun h1 => hnot ⟨h0, h1⟩
    have hsub : s ⊆ {(0 : Fin 2)} := by
      intro x hx
      fin_cases x
      · exact Set.mem_singleton _
      · exact absurd hx h1
    have hle := Set.ncard_le_ncard hsub
    simp only [Set.ncard_singleton] at hle
    omega
  · have hsub : s ⊆ {(1 : Fin 2)} := by
      intro x hx
      fin_cases x
      · exact absurd hx h0
      · exact Set.mem_singleton _
    have hle := Set.ncard_le_ncard hsub
    simp only [Set.ncard_singleton] at hle
    omega

/-- Boundary checks at `size = ∅` and `size = univ` on `K₂`. -/
example :
    k2EmptySize ∈ Ordered.IndependentSet ∧
      k2EmptySize ∈ Ordered.Clique ∧
      k2EmptySize ∉ Ordered.VertexCover ∧
      k2FullSize ∉ Ordered.IndependentSet ∧
      k2FullSize ∈ Ordered.Clique ∧
      k2FullSize ∈ Ordered.VertexCover := by
  have hempty : {x : k2EmptySize | RelMap FO.sizedGraph.size ![x]} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact Bool.false_ne_true
  have hfull : {x : k2FullSize | RelMap FO.sizedGraph.size ![x]} = Set.univ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨∅, by rw [hempty], Set.pairwise_empty _⟩
  · exact ⟨∅, by rw [hempty], Set.pairwise_empty _⟩
  · rintro ⟨s, hs, hcov⟩
    rw [hempty, Set.ncard_empty, Set.ncard_eq_zero] at hs
    subst hs
    rcases hcov (0 : Fin 2) (1 : Fin 2) (by decide : (0 : Fin 2) ≠ (1 : Fin 2))
      (by change _ = true; decide) with h | h <;> exact h
  · rintro ⟨s, hs, hind⟩
    have hcard : s.ncard = 2 := by
      rw [hs, hfull, Set.ncard_univ, Nat.card_eq_fintype_card]
      decide
    obtain ⟨h0, h1⟩ := mem_zero_and_one_of_ncard_two hcard
    exact hind h0 h1 (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) (by change _ = true; decide)
  · refine ⟨Set.univ, by rw [hfull], fun (x : Fin 2) _ (y : Fin 2) _ hne => ?_⟩
    change ((x : Fin 2) != y) = true
    exact bne_iff_ne.mpr hne
  · exact ⟨Set.univ, by rw [hfull], fun x _ _ _ => .inl (Set.mem_univ x)⟩

/-- Diagonal loop suppression in `complementEdgesInterpretation` (`Fin 2 → Fin 2`). -/
example :
    let hI := complementEdgesInterpretation.admissible_toDomainInterpretation one_pos
    loopOnlyFullSize ∈ Ordered.IndependentSet ∧
      complementEdgesInterpretation.toDomainInterpretation.map hI loopOnlyFullSize ∈
        Ordered.Clique ∧
      complementEdgesInterpretation.toDomainInterpretation.map hI loopOnlyFullSize ∉
        Ordered.IndependentSet := by
  have hfull : {x : loopOnlyFullSize | RelMap FO.sizedGraph.size ![x]} = Set.univ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    rfl
  have hind : loopOnlyFullSize ∈ Ordered.IndependentSet := by
    refine ⟨Set.univ, by rw [hfull], fun (x : Fin 2) _ (y : Fin 2) _ hne hloop => ?_⟩
    have hx0 : x = (0 : Fin 2) ∧ y = (0 : Fin 2) := by
      change ((x : Fin 2) == 0 && (y : Fin 2) == 0) = true at hloop
      revert hloop
      fin_cases x <;> fin_cases y <;> decide
    rcases hx0 with ⟨rfl, rfl⟩
    exact hne rfl
  refine ⟨hind, ?_, ?_⟩
  · exact (mem_Clique_complementEdgesInterpretation loopOnlyFullSize).mpr hind
  · rw [mem_IndependentSet_complementEdgesInterpretation]
    rintro ⟨s, hs, hclq⟩
    have hcard : s.ncard = 2 := by
      rw [hs, hfull, Set.ncard_univ, Nat.card_eq_fintype_card]
      decide
    obtain ⟨h0, h1⟩ := mem_zero_and_one_of_ncard_two hcard
    have h01 : RelMap (M := loopOnlyFullSize) FO.sizedGraph.adj ![(0 : Fin 2), (1 : Fin 2)] :=
      hclq h0 h1 (by decide : (0 : Fin 2) ≠ (1 : Fin 2))
    change ((0 : Fin 2) == 0 && (1 : Fin 2) == 0) = true at h01
    exact absurd h01 (by decide)

/-! ### Reduction hierarchy, `ESODefinable`, native `NP`, and `LogSpaceReducible` checks -/

/-- Every certified `≤_qfp` reduction refines to `ProjectionReduces` (`≤_fop`), `Ordered.Reduces`,
and `LogSpaceReducible encStructure encStructure`, while canonical encodings of `twoFourLitSat` and
`twoUnsatUnits` separate `SAT.encodedLanguage FO.cnf.vocabulary`. -/
example :
    ProjectionReduces Ordered.SAT Ordered.ThreeSAT ∧
      Ordered.Reduces Ordered.SAT Ordered.SimpleThreeColorable ∧
      QFProjectionReduces Ordered.SAT Ordered.VertexCover ∧
      ESODefinable Ordered.SAT ∧
      ESODefinable Ordered.SimpleThreeColorable ∧
      ESODefinable Ordered.VertexCover ∧
      SAT.encodedLanguage FO.cnf.vocabulary ∈ NP encStructure ∧
      SimpleThreeColorable.encodedLanguage graphVocabulary ∈ NP encStructure ∧
      VertexCover.encodedLanguage sizedGraphVocabulary ∈ NP encStructure ∧
      LogSpaceReducible encStructure encStructure
        (SAT.encodedLanguage FO.cnf.vocabulary)
        (SimpleThreeColorable.encodedLanguage graphVocabulary) ∧
      encode FO.cnf.vocabulary twoFourLitSat ∈ SAT.encodedLanguage FO.cnf.vocabulary ∧
      encode FO.cnf.vocabulary twoUnsatUnits ∉ SAT.encodedLanguage FO.cnf.vocabulary :=
  ⟨sat_qfProjectionReduces_ThreeSAT.projectionReduces,
    sat_qfProjectionReduces_SimpleThreeColorable.reduces,
    sat_qfProjectionReduces_Clique.trans clique_qfProjectionReduces_VertexCover,
    esoDefinable_SAT,
    esoDefinable_SimpleThreeColorable,
    esoDefinable_VertexCover,
    sat_encodedLanguage_mem_NP,
    simpleThreeColorable_encodedLanguage_mem_NP,
    vertexCover_encodedLanguage_mem_NP,
    sat_logSpaceReducible_SimpleThreeColorable,
    (mem_encodedLanguage_encode FO.cnf.vocabulary Ordered.SAT twoFourLitSat).mpr
      twoFourLitSat_mem_SAT,
    fun h => twoUnsatUnits_not_mem_SAT
      ((mem_encodedLanguage_encode FO.cnf.vocabulary Ordered.SAT twoUnsatUnits).mp h)⟩

end Cslib.Tests.OrderedNPProjections
