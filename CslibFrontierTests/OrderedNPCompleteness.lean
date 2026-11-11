/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Fagin.Ordered.Completeness
public import CslibFrontier.Logics.SecondOrder.Ordered.Grounding
import CslibFrontier.Logics.FirstOrder.Basic
import Mathlib.Tactic.FinCases

/-!
# Tests for ordered `NP`-completeness under quantifier-free projections and polytime bridges

Concrete positive instances, negative controls, and boundary checks for:
* `CslibFrontier/Logics/SecondOrder/Ordered/Grounding.lean`, and
* `CslibFrontier/Computability/Complexity/Fagin/Ordered/Completeness.lean`.

Covers:
* an order-dependent existential second-order sentence `forwardEdgeWitnessSentence` over
  `Language.graph.sum ESO.orderLanguage` separating two unordered-isomorphic 3-vertex directed
  graphs (`forwardArc3` with `0 → 2` vs `backwardArc3` with `2 → 0`) through its `BIT`-free
  quantifier-free projection grounding `groundQFInterpretation`;
* concrete evaluation (`rfl`) and semantic checks for `cnfToOrdered` on the empty formula `[]`,
  the empty-clause formula `[[]]`, a satisfiable formula with non-contiguous variable numbers
  `[[(10, true), (25, false)], [(25, true)]]`, and an unsatisfiable unit contradiction
  `[[(7, true)], [(7, false)]]`;
* unconditional `≤_qfp`, `≤_fop`, and `Ordered.Reduces` completeness characterizations instantiated
  on the order-dependent query `ForwardEdgeQuery`, deriving `QFProjectionReduces` reductions to all
  seven canonical ordered `NP` queries (`SAT`, `ThreeSAT`, `SimpleThreeColorable`,
  `ThreeColorable`, `IndependentSet`, `Clique`, and `VertexCover`);
* machine-level `NPComplete encStructure` and bidirectional `PolyTimeReducible` bridges to
  `Complexity.SAT`, `Complexity.ThreeSAT`, `Complexity.ThreeColoring`, `Complexity.IndependentSet`,
  `Complexity.Clique`, and `Complexity.VertexCover`.
-/

public section

namespace Cslib.Tests.OrderedNPCompleteness

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered
open Cslib.Complexity Turing.MultiTapeTM

/-! ### 1. Grounding an order-dependent ESO sentence via a `BIT`-free quantifier-free projection -/

/-- Build an ordered `Language.graph` structure on `Fin n` (`2 ≤ n`). -/
def mkOrderedGraph (n : ℕ) (hn : 2 ≤ n) (edge : Fin n → Fin n → Bool) :
    Ordered.Structure Language.graph where
  size := n
  size_ge_two := hn
  input :=
    { funMap := fun f => isEmptyElim f
      RelMap
        | .adj, x => edge (x 0) (x 1) = true }

/-- Directed 3-vertex graph with single forward arc `0 → 2` (`0 < 2`). -/
def forwardArc3 : Ordered.Structure Language.graph :=
  mkOrderedGraph 3 (by decide) (fun u v => u == 0 && v == 2)

/-- Directed 3-vertex graph with single backward arc `2 → 0` (`2 > 0`), isomorphic to `forwardArc3`
as an unordered digraph via swapping `0` and `2`, but distinct as an ordered structure. -/
def backwardArc3 : Ordered.Structure Language.graph :=
  mkOrderedGraph 3 (by decide) (fun u v => u == 2 && v == 0)

abbrev witnessArity : Unit → ℕ := fun _ => 1

def ltRel : (Language.graph.sum ESO.orderLanguage).Relations 2 :=
  Sum.inr ESO.ltSym

def adjRel : (Language.graph.sum ESO.orderLanguage).Relations 2 :=
  Sum.inl Language.adj

def witRel :
    ((Language.graph.sum ESO.orderLanguage).sum (ESO.varLanguage witnessArity)).Relations 1 :=
  Sum.inr ⟨(), rfl⟩

def forwardEdgeBody :
    ((Language.graph.sum ESO.orderLanguage).sum (ESO.varLanguage witnessArity)).Formula (Fin 2) :=
  (FO.rel₂ (LHom.sumInl.onRelation ltRel) 0 1) ⊓
    (FO.rel₂ (LHom.sumInl.onRelation adjRel) 0 1) ⊓
    (FO.rel₁ witRel 0) ⊓
    ∼(FO.rel₁ witRel 1)

/-- Order-dependent ESO sentence `∃ S, ∃ x y, x < y ∧ adj(x, y) ∧ S(x) ∧ ∼S(y)` over
`Language.graph.sum ESO.orderLanguage`. -/
noncomputable abbrev forwardEdgeWitnessSentence :
    ESO.Sentence (Language.graph.sum ESO.orderLanguage) where
  Var := Unit
  arity := witnessArity
  matrix := FO.closeEx (Fin 2) forwardEdgeBody

theorem realize_forwardEdgeWitnessSentence_iff (G : Ordered.Structure Language.graph) :
    (letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
      (ESO.orderRelOfEquiv (Equiv.refl G));
      forwardEdgeWitnessSentence.Realize G) ↔
      ∃ x y : Fin G.size, x < y ∧ G.input.RelMap Language.adj ![x, y] := by
  let _ := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
    (ESO.orderRelOfEquiv (Equiv.refl G))
  constructor
  · rintro ⟨R, hmat⟩
    let R' : ∀ i, Set (Fin (witnessArity i) → G) := R
    let _ := ESO.varLanguage.structure R'
    obtain ⟨u, hu⟩ := (FO.realize_closeEx (Fin 2) forwardEdgeBody).mp hmat
    rw [forwardEdgeBody] at hu
    simp only [Formula.realize_inf, Formula.realize_not, FO.realize_rel₂, FO.realize_rel₁] at hu
    obtain ⟨⟨⟨hlt, hadj⟩, _⟩, _⟩ := hu
    have hlt' : u 0 < u 1 := hlt
    have hadj' : G.input.RelMap Language.adj ![u 0, u 1] := hadj
    exact ⟨u 0, u 1, hlt', hadj'⟩
  · rintro ⟨x, y, hlt, hadj⟩
    let S : ∀ i, Set (Fin (witnessArity i) → G) := fun _ => {t | t 0 = x}
    refine ⟨S, ?_⟩
    let _ := ESO.varLanguage.structure S
    refine (FO.realize_closeEx (Fin 2) forwardEdgeBody).mpr ⟨![x, y], ?_⟩
    rw [forwardEdgeBody]
    simp only [Formula.realize_inf, Formula.realize_not, FO.realize_rel₂, FO.realize_rel₁]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · change x < y
      exact hlt
    · change G.input.RelMap Language.adj ![x, y]
      exact hadj
    · change x = x
      rfl
    · change ¬ (y = x)
      exact ne_of_gt hlt

theorem forwardArc3_realizes_witness :
    letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
      (ESO.orderRelOfEquiv (Equiv.refl forwardArc3));
    forwardEdgeWitnessSentence.Realize forwardArc3 :=
  (realize_forwardEdgeWitnessSentence_iff forwardArc3).mpr
    ⟨(0 : Fin 3), (2 : Fin 3), by decide, rfl⟩

theorem backwardArc3_not_realizes_witness :
    letI := ESO.varLanguage.structure (arity := fun _ : Unit => 2)
      (ESO.orderRelOfEquiv (Equiv.refl backwardArc3));
    ¬ forwardEdgeWitnessSentence.Realize backwardArc3 := by
  intro h
  obtain ⟨x, y, hlt, hadj⟩ := (realize_forwardEdgeWitnessSentence_iff backwardArc3).mp h
  change Fin 3 at x y
  fin_cases x <;> fin_cases y
  all_goals
    first
    | exact absurd hlt (by decide)
    | exact absurd hadj Bool.false_ne_true

/-- The grounded interpretation of `forwardEdgeWitnessSentence` is certified `BIT`-free `qfp`. -/
theorem isQF_forwardEdgeWitness :
    forwardEdgeWitnessSentence.groundQFInterpretation.IsQFProjection :=
  forwardEdgeWitnessSentence.isQFProjection_groundQFInterpretation

/-- Grounding maps `forwardArc3` into `Ordered.SAT` while rejecting the unordered-isomorphic
control `backwardArc3`. -/
theorem grounded_separates_forward_and_backward :
    let hI := forwardEdgeWitnessSentence.groundQFInterpretation.admissible_toDomainInterpretation
      forwardEdgeWitnessSentence.groundDim_pos
    let Mpos := forwardEdgeWitnessSentence.groundQFInterpretation.toDomainInterpretation.map
      hI forwardArc3
    let Mneg := forwardEdgeWitnessSentence.groundQFInterpretation.toDomainInterpretation.map
      hI backwardArc3
    Mpos ∈ Ordered.SAT ∧ Mneg ∉ Ordered.SAT :=
  ⟨(forwardEdgeWitnessSentence.mem_SAT_groundQFInterpretation forwardArc3).mpr
      forwardArc3_realizes_witness,
    mt (forwardEdgeWitnessSentence.mem_SAT_groundQFInterpretation backwardArc3).mp
      backwardArc3_not_realizes_witness⟩

/-! ### 2. Concrete evaluation and semantic tests of `cnfToOrdered` -/

/-- Empty CNF formula `[]` maps to universe size `2` with pure self-tautologies on `0` and `1`. -/
example : cnfToOrderedSize ([] : PL.CNF ℕ) = 2 := rfl

example : cnfToOrdered ([] : PL.CNF ℕ) =
    (2, [ [true, false, false, true], [true, false, false, true] ]) := rfl

theorem cnfToOrdered_empty_mem_SAT :
    cnfToOrdered ([] : PL.CNF ℕ) ∈ Ordered.SAT.encodedLanguage FO.cnf.vocabulary :=
  (cnfToOrdered_mem_iff []).mpr ⟨fun _ => false, rfl⟩

/-- Single empty clause `[[]]` maps to universe size `2` with an empty clause at `0` and a
self-tautology at `1`. -/
example : cnfToOrderedSize ([ [ ] ] : PL.CNF ℕ) = 2 := rfl

example : cnfToOrdered ([ [ ] ] : PL.CNF ℕ) =
    (2, [ [false, false, false, true], [false, false, false, true] ]) := rfl

theorem cnfToOrdered_emptyClause_not_mem_SAT :
    cnfToOrdered ([ [ ] ] : PL.CNF ℕ) ∉ Ordered.SAT.encodedLanguage FO.cnf.vocabulary := by
  rw [cnfToOrdered_mem_iff, Complexity.mem_SAT]
  rintro ⟨σ, hσ⟩
  have hcl := (PL.CNF.eval_eq_true_iff σ [ [ ] ]).mp hσ [] (List.mem_singleton_self _)
  obtain ⟨_, hmem, _⟩ := (PL.Clause.eval_eq_true_iff σ []).mp hcl
  exact List.not_mem_nil hmem

/-- Satisfiable multi-clause formula with non-contiguous variable numbers `10` and `25`. -/
def satSparseCNF : PL.CNF ℕ :=
  [ [(10, true), (25, false)], [(25, true)] ]

example : cnfToOrderedSize satSparseCNF = 4 := rfl

theorem satSparseCNF_mem_SAT : satSparseCNF ∈ Complexity.SAT :=
  ⟨fun v => v == 10 || v == 25, by decide⟩

theorem cnfToOrdered_satSparseCNF_mem :
    cnfToOrdered satSparseCNF ∈ Ordered.SAT.encodedLanguage FO.cnf.vocabulary :=
  (cnfToOrdered_mem_iff satSparseCNF).mpr satSparseCNF_mem_SAT

/-- Unsatisfiable unit contradiction `(x₇) ∧ (¬ x₇)`. -/
def unsatUnitCNF : PL.CNF ℕ :=
  [ [(7, true)], [(7, false)] ]

example : cnfToOrderedSize unsatUnitCNF = 3 := rfl

theorem unsatUnitCNF_not_mem_SAT : unsatUnitCNF ∉ Complexity.SAT := by
  rw [Complexity.mem_SAT]
  rintro ⟨σ, hσ⟩
  have ht := (PL.CNF.eval_eq_true_iff σ unsatUnitCNF).mp hσ [(7, true)] (by decide)
  have hf := (PL.CNF.eval_eq_true_iff σ unsatUnitCNF).mp hσ [(7, false)] (by decide)
  obtain ⟨⟨v₁, b₁⟩, hm₁, hs₁⟩ := (PL.Clause.eval_eq_true_iff σ [(7, true)]).mp ht
  obtain ⟨⟨v₂, b₂⟩, hm₂, hs₂⟩ := (PL.Clause.eval_eq_true_iff σ [(7, false)]).mp hf
  rcases List.mem_singleton.mp hm₁ with ⟨rfl, rfl⟩
  rcases List.mem_singleton.mp hm₂ with ⟨rfl, rfl⟩
  change σ 7 = true at hs₁
  change σ 7 = false at hs₂
  rw [hs₁] at hs₂
  exact Bool.false_ne_true hs₂.symm

theorem cnfToOrdered_unsatUnitCNF_not_mem :
    cnfToOrdered unsatUnitCNF ∉ Ordered.SAT.encodedLanguage FO.cnf.vocabulary :=
  mt (cnfToOrdered_mem_iff unsatUnitCNF).mp unsatUnitCNF_not_mem_SAT

/-- Universes of size `< 2` are rejected by `Ordered.SAT.encodedLanguage`. -/
theorem size_one_not_mem_orderedSAT :
    ((1, [ [true], [true] ]) : EncodedStructure) ∉
      Ordered.SAT.encodedLanguage FO.cnf.vocabulary :=
  Query.not_mem_encodedLanguage_of_lt_two Ordered.SAT FO.cnf.vocabulary (by decide)

/-! ### 3. Unconditional `≤_qfp`, `≤_fop`, and `≤_fo` completeness instantiated on an
order-dependent query -/

/-- Ordered query asking whether a directed graph on `Fin n` has at least one forward arc
`x → y` with `x < y`. -/
def ForwardEdgeQuery : Ordered.Query Language.graph :=
  {G | ∃ x y : Fin G.size, x < y ∧ G.input.RelMap Language.adj ![x, y]}

theorem forwardEdgeQuery_qfReduces_SAT : QFProjectionReduces ForwardEdgeQuery Ordered.SAT :=
  qfProjectionReduces_SAT_of_orderSentence forwardEdgeWitnessSentence fun G =>
    (realize_forwardEdgeWitnessSentence_iff G).symm

theorem forwardEdgeQuery_mem_NP :
    ForwardEdgeQuery.encodedLanguage graphVocabulary ∈ NP encStructure :=
  (qfProjectionReduces_SAT_iff_encodedLanguage_mem_NP graphVocabulary).mp
    forwardEdgeQuery_qfReduces_SAT

theorem forwardEdgeQuery_esoDefinable : Ordered.ESODefinable ForwardEdgeQuery :=
  (esoDefinable_iff_qfProjectionReduces_SAT graphVocabulary).mpr
    forwardEdgeQuery_qfReduces_SAT

/-- By `≤_qfp`-completeness, `ForwardEdgeQuery` quantifier-free projection reduces to all seven
canonical ordered `NP`-complete problems, separating `forwardArc3` from `backwardArc3` in each
target problem. -/
theorem forwardEdgeQuery_qfReduces_all_seven :
    QFProjectionReduces ForwardEdgeQuery Ordered.SAT ∧
    QFProjectionReduces ForwardEdgeQuery Ordered.ThreeSAT ∧
    QFProjectionReduces ForwardEdgeQuery Ordered.SimpleThreeColorable ∧
    QFProjectionReduces ForwardEdgeQuery Ordered.ThreeColorable ∧
    QFProjectionReduces ForwardEdgeQuery Ordered.IndependentSet ∧
    QFProjectionReduces ForwardEdgeQuery Ordered.Clique ∧
    QFProjectionReduces ForwardEdgeQuery Ordered.VertexCover :=
  ⟨(qfProjectionReduces_SAT_iff_encodedLanguage_mem_NP graphVocabulary).mpr
      forwardEdgeQuery_mem_NP,
    (qfProjectionReduces_ThreeSAT_iff_encodedLanguage_mem_NP graphVocabulary).mpr
      forwardEdgeQuery_mem_NP,
    (qfProjectionReduces_SimpleThreeColorable_iff_encodedLanguage_mem_NP graphVocabulary).mpr
      forwardEdgeQuery_mem_NP,
    (qfProjectionReduces_ThreeColorable_iff_encodedLanguage_mem_NP graphVocabulary).mpr
      forwardEdgeQuery_mem_NP,
    (qfProjectionReduces_IndependentSet_iff_encodedLanguage_mem_NP graphVocabulary).mpr
      forwardEdgeQuery_mem_NP,
    (qfProjectionReduces_Clique_iff_encodedLanguage_mem_NP graphVocabulary).mpr
      forwardEdgeQuery_mem_NP,
    (qfProjectionReduces_VertexCover_iff_encodedLanguage_mem_NP graphVocabulary).mpr
      forwardEdgeQuery_mem_NP⟩

/-- Concrete separation of `forwardArc3` vs `backwardArc3` transported into `Ordered.ThreeColorable`
via the `≤_qfp`-completeness witness. -/
theorem forward_vs_backward_in_ThreeColorable :
    ∃ f : Ordered.Structure Language.graph → Ordered.Structure Language.graph,
      IsQFProjectionMap f ∧
      f forwardArc3 ∈ Ordered.ThreeColorable ∧
      f backwardArc3 ∉ Ordered.ThreeColorable := by
  obtain ⟨f, hf, hiff⟩ :=
    (qfProjectionReduces_ThreeColorable_iff_encodedLanguage_mem_NP graphVocabulary).mpr
      forwardEdgeQuery_mem_NP
  refine ⟨f, hf, (hiff forwardArc3).mp ?_, mt (hiff backwardArc3).mpr ?_⟩
  · exact ⟨(0 : Fin 3), (2 : Fin 3), by decide, rfl⟩
  · rintro ⟨x, y, hlt, hadj⟩
    change Fin 3 at x y
    fin_cases x <;> fin_cases y
    all_goals
      first
      | exact absurd hlt (by decide)
      | exact absurd hadj Bool.false_ne_true

/-! ### 4. Machine-level `NPComplete encStructure` and bidirectional `PolyTimeReducible` bridges -/

/-- All seven canonical ordered queries are `NPComplete encStructure`. -/
theorem all_seven_ordered_npComplete :
    NPComplete encStructure (Ordered.SAT.encodedLanguage FO.cnf.vocabulary) ∧
    NPComplete encStructure (Ordered.ThreeSAT.encodedLanguage FO.cnf.vocabulary) ∧
    NPComplete encStructure (Ordered.SimpleThreeColorable.encodedLanguage graphVocabulary) ∧
    NPComplete encStructure (Ordered.ThreeColorable.encodedLanguage graphVocabulary) ∧
    NPComplete encStructure (Ordered.IndependentSet.encodedLanguage sizedGraphVocabulary) ∧
    NPComplete encStructure (Ordered.Clique.encodedLanguage sizedGraphVocabulary) ∧
    NPComplete encStructure (Ordered.VertexCover.encodedLanguage sizedGraphVocabulary) :=
  ⟨sat_npComplete,
    threeSAT_npComplete,
    simpleThreeColorable_npComplete,
    threeColorable_npComplete,
    independentSet_npComplete,
    clique_npComplete,
    vertexCover_npComplete⟩

/-- Transporting `satSparseCNF` and `unsatUnitCNF` round-trip through
`cnf_polyTimeReducible_orderedSAT` and `orderedSAT_polyTimeReducible_cnf` preserves satisfiability
and unsatisfiability. -/
theorem roundtrip_sat_polyTime_bridges :
    ∃ (f : PL.CNF ℕ → EncodedStructure) (g : EncodedStructure → PL.CNF ℕ),
      ComputableInPolyTime f encCNF encStructure ∧
      ComputableInPolyTime g encStructure encCNF ∧
      g (f satSparseCNF) ∈ Complexity.SAT ∧
      g (f unsatUnitCNF) ∉ Complexity.SAT := by
  obtain ⟨f, hf, hiff_f⟩ := cnf_polyTimeReducible_orderedSAT
  obtain ⟨g, hg, hiff_g⟩ := orderedSAT_polyTimeReducible_cnf
  exact ⟨f, g, hf, hg,
    (hiff_g (f satSparseCNF)).mp ((hiff_f satSparseCNF).mp satSparseCNF_mem_SAT),
    mt (fun h => (hiff_f unsatUnitCNF).mpr ((hiff_g (f unsatUnitCNF)).mpr h))
      unsatUnitCNF_not_mem_SAT⟩

/-- Bidirectional `PolyTimeReducible` equivalences hold for all remaining canonical problem pairs
(`ThreeSAT`, `SimpleThreeColorable`, `ThreeColorable`, `IndependentSet`, `Clique`,
`VertexCover`). -/
theorem all_polyTime_problem_bridges :
    (PolyTimeReducible encCNF encStructure
        Complexity.ThreeSAT (Ordered.ThreeSAT.encodedLanguage FO.cnf.vocabulary) ∧
      PolyTimeReducible encStructure encCNF
        (Ordered.ThreeSAT.encodedLanguage FO.cnf.vocabulary) Complexity.ThreeSAT) ∧
    (PolyTimeReducible encGraph encStructure
        Complexity.ThreeColoring
        (Ordered.SimpleThreeColorable.encodedLanguage graphVocabulary) ∧
      PolyTimeReducible encStructure encGraph
        (Ordered.SimpleThreeColorable.encodedLanguage graphVocabulary)
        Complexity.ThreeColoring) ∧
    (PolyTimeReducible encGraph encStructure
        Complexity.ThreeColoring (Ordered.ThreeColorable.encodedLanguage graphVocabulary) ∧
      PolyTimeReducible encStructure encGraph
        (Ordered.ThreeColorable.encodedLanguage graphVocabulary) Complexity.ThreeColoring) ∧
    (PolyTimeReducible (encPair encGraph encNat) encStructure
        Complexity.IndependentSet
        (Ordered.IndependentSet.encodedLanguage sizedGraphVocabulary) ∧
      PolyTimeReducible encStructure (encPair encGraph encNat)
        (Ordered.IndependentSet.encodedLanguage sizedGraphVocabulary)
        Complexity.IndependentSet) ∧
    (PolyTimeReducible (encPair encGraph encNat) encStructure
        Complexity.Clique (Ordered.Clique.encodedLanguage sizedGraphVocabulary) ∧
      PolyTimeReducible encStructure (encPair encGraph encNat)
        (Ordered.Clique.encodedLanguage sizedGraphVocabulary) Complexity.Clique) ∧
    (PolyTimeReducible (encPair encGraph encNat) encStructure
        Complexity.VertexCover (Ordered.VertexCover.encodedLanguage sizedGraphVocabulary) ∧
      PolyTimeReducible encStructure (encPair encGraph encNat)
        (Ordered.VertexCover.encodedLanguage sizedGraphVocabulary) Complexity.VertexCover) :=
  ⟨⟨threeSAT_polyTimeReducible_orderedThreeSAT, orderedThreeSAT_polyTimeReducible_threeSAT⟩,
    ⟨threeColoring_polyTimeReducible_orderedSimpleThreeColorable,
      orderedSimpleThreeColorable_polyTimeReducible_threeColoring⟩,
    ⟨threeColoring_polyTimeReducible_orderedThreeColorable,
      orderedThreeColorable_polyTimeReducible_threeColoring⟩,
    ⟨independentSet_polyTimeReducible_orderedIndependentSet,
      orderedIndependentSet_polyTimeReducible_independentSet⟩,
    ⟨clique_polyTimeReducible_orderedClique, orderedClique_polyTimeReducible_clique⟩,
    ⟨vertexCover_polyTimeReducible_orderedVertexCover,
      orderedVertexCover_polyTimeReducible_vertexCover⟩⟩

end Cslib.Tests.OrderedNPCompleteness
