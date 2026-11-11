/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Projection
import CslibFrontierTests.OrderedProjection

/-!
# Tests for ordered projection composition and reducibility

Concrete checks for `CslibFrontier/Logics/FirstOrder/Ordered/Projection/Composition.lean`,
`CslibFrontier/Logics/FirstOrder/Ordered/Projection/Reduction.lean`, and
`CslibFrontier/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered/Projection.lean`:

* identity projection maps and `@[refl]` instances of `ProjectionReduces` and
  `QFProjectionReduces`, evaluated on concrete graphs;
* M1's off-diagonal graph complement composed with itself via `IsProjection.comp` in dimension
  `1 * 1 = 1`, agreeing with the input graph off the diagonal and remaining false on a self-loop
  on `Fin 3`;
* M1's two-dimensional edge-copy composed with the off-diagonal complement on `Fin 3`, checked at
  exact lexicographic rank `5` (`![1, 2]`) and at diagonal rank `0` (`![0, 0]`);
* concrete query reductions across distinct vocabularies (`Language.graph` and `unary`), composed
  by `ProjectionReduces.trans`, refined by `.reduces` to pull back first-order definability, and
  lifted to `encStructure` logspace reductions via `ProjectionReduces.logSpaceReducible` and
  `QFProjectionReduces.logSpaceReducible`;
* negative controls showing that non-empty queries do not projection-reduce to the empty query and
  that composing a non-projection with the identity does not produce a projection map.
-/

namespace CslibFrontierTests.OrderedProjectionReduction

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered
open CslibFrontierTests.OrderedProjection

/-! ### Identity projections and reflexivity -/

/-- The image of `FullTupleInterpretation.id` fixes concrete ordered graphs. -/
example : (FullTupleInterpretation.id Language.graph).toDomainInterpretation.map
    ((FullTupleInterpretation.id Language.graph).admissible_toDomainInterpretation one_pos)
    edge12 = edge12 :=
  FullTupleInterpretation.map_id Language.graph edge12

/-- `IsQFProjectionMap.id` and `IsProjectionMap.id` on distinct relational vocabularies. -/
example : IsQFProjectionMap (_root_.id : Ordered.Structure Language.graph → _) ∧
    IsProjectionMap (_root_.id : Ordered.Structure unary → _) :=
  ⟨IsQFProjectionMap.id, IsProjectionMap.id⟩

/-! ### Off-diagonal complement composed with itself on `Fin 3` -/

/-- The image map of M1's off-diagonal complement. -/
noncomputable abbrev complementMap :
    Ordered.Structure Language.graph → Ordered.Structure Language.graph :=
  complement.toDomainInterpretation.map (complement.admissible_toDomainInterpretation one_pos)

theorem isQFProjectionMap_complementMap : IsQFProjectionMap complementMap :=
  isQFProjection_complement.isQFProjectionMap one_pos

/-- Composing the off-diagonal complement with itself via `IsProjection.comp` yields a
dimension-`1` projection witness that agrees with the input graph off the diagonal and erases
self-loops on the diagonal for every `n ≥ 2`. -/
theorem exists_doubleComplement :
    ∃ K : FullTupleInterpretation Language.graph Language.graph 1, K.IsProjection ∧
      (∀ {n : ℕ} [Fact (2 ≤ n)] (E : Fin n → Fin n → Prop) (a b : Fin n),
        letI : Language.graph.Structure (Fin n) := graphStructure n E
        (K.rel Language.adj).Realize (fun p => (![a, b] : Fin 2 → Fin n) p.1) ↔
          a ≠ b ∧ E a b) := by
  obtain ⟨K, hK, hKrel⟩ := FullTupleInterpretation.IsProjection.comp
    isQFProjection_complement.isProjection one_pos isQFProjection_complement.isProjection
  refine ⟨K, hK, fun {n} _ E a b => ?_⟩
  let := graphStructure n E
  let v : Fin 2 → Fin 1 → Fin 1 → Fin n := fun i _ _ => (![a, b] : Fin 2 → Fin n) i
  have hv : (fun p : Fin 2 × Fin (1 * 1) => (![a, b] : Fin 2 → Fin n) p.1) =
      fun p => flattenTuple (v p.1) p.2 := by
    funext ⟨i, _⟩
    rfl
  rw [hKrel, hv, complement.realize_comp_rel complement one_pos Language.adj v]
  let := complement.inputStructure (n := n)
  let : Fact (2 ≤ n ^ 1) := ⟨FullTupleInterpretation.two_le_pow (n := n) one_pos⟩
  rw [realize_complement]
  have hlex (i : Fin 2) :
      lexEquiv (v i 0) = Fin.cast (pow_one n).symm ((![a, b] : Fin 2 → Fin n) i) := by
    apply Fin.ext
    change lexRank (v i 0) = ((![a, b] : Fin 2 → Fin n) i).val
    rw [lexRank_apply, Fin.sum_univ_one]
    simp only [v, Fin.rev, Fin.val_zero, zero_add, tsub_self, pow_zero, mul_one]
  have hneq :
      (lexEquiv (v 0 0) ≠ lexEquiv (v 1 0)) ↔ a ≠ b := by
    rw [hlex 0, hlex 1]
    exact ⟨fun h hab => h (congrArg _ hab), fun h h' => h (Fin.cast_injective _ h')⟩
  have hadj :
      RelMap Language.adj (fun i : Fin 2 => lexEquiv (v i 0)) ↔ (a ≠ b ∧ ¬ E a b) := by
    change (complement.rel Language.adj).Realize
      (fun p : Fin 2 × Fin 1 => lexEquiv.symm (lexEquiv (v p.1 0)) p.2) ↔ _
    simp only [Equiv.symm_apply_apply]
    rw [realize_complement, relMap_graphStructure]
    rfl
  rw [hneq, hadj]
  by_cases hab : a = b
  · simp only [hab, ne_eq, not_true_eq_false, false_and, not_false_eq_true, and_true]
  · simp only [hab, ne_eq, not_false_eq_true, true_and, Classical.not_not]

/-- Concrete evaluation on `Fin 3` with edge `1 → 2` and self-loop `1 → 1`: the double complement
keeps `1 → 2`, keeps `2 → 1` absent, and drops the diagonal loop `1 → 1`. -/
example :
    ∃ K : FullTupleInterpretation Language.graph Language.graph 1, K.IsProjection ∧
      (letI := graphStructure 3 (fun a b => (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 1))
       (K.rel Language.adj).Realize (fun p => (![1, 2] : Fin 2 → Fin 3) p.1) ∧
       ¬ (K.rel Language.adj).Realize (fun p => (![2, 1] : Fin 2 → Fin 3) p.1) ∧
       ¬ (K.rel Language.adj).Realize (fun _ => (1 : Fin 3))) := by
  obtain ⟨K, hK, hspec⟩ := exists_doubleComplement
  refine ⟨K, hK, ?_⟩
  let E : Fin 3 → Fin 3 → Prop := fun a b => (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 1)
  have h12 := hspec E 1 2
  have h21 := hspec E 2 1
  have h11 := hspec E 1 1
  have hdiag : (fun _ : Fin 2 × Fin 1 => (1 : Fin 3)) =
      (fun p => (![1, 1] : Fin 2 → Fin 3) p.1) := by
    funext ⟨i, _⟩
    fin_cases i <;> rfl
  let := graphStructure 3 E
  rw [hdiag, h12, h21, h11]
  decide

/-! ### Dimension-2 `copy ∘ complement` at lexicographic rank `5` (`![1, 2]`) on `Fin 3` -/

/-- `copyMap ∘ complementMap` is a first-order projection map, with a composite projection witness
of dimension `2 * 1 = 2`. -/
theorem isProjectionMap_copy_comp_complement : IsProjectionMap (copyMap ∘ complementMap) :=
  isQFProjectionMap_complementMap.isProjectionMap.comp isProjectionMap_copyMap

example : ∃ K : FullTupleInterpretation Language.graph unary 2, K.IsProjection ∧
    ∀ {n : ℕ} [Fact (2 ≤ n)] [Language.graph.Structure (Fin n)] (R : unary.Relations 1)
      (x : Fin 1 × Fin 2 → Fin n),
      (K.rel R).Realize x ↔ ((copy.comp complement).rel R).Realize x := by
  obtain ⟨K, hK, hKrel⟩ := FullTupleInterpretation.IsProjection.comp
    isProjection_copy one_pos isQFProjection_complement.isProjection
  exact ⟨K, hK, fun R x => hKrel R x⟩

/-- Size equality `(complementMap M).size = M.size`. -/
theorem size_complementMap (M : Ordered.Structure Language.graph) :
    (complementMap M).size = M.size :=
  (FullTupleInterpretation.card_toDomainInterpretation M).trans (pow_one M.size)

/-- Relation characterization of `complementMap M`. -/
theorem relMap_complementMap (M : Ordered.Structure Language.graph) (a b : Fin M.size) :
    RelMap (M := complementMap M) Language.adj
      ![Fin.cast (size_complementMap M).symm a, Fin.cast (size_complementMap M).symm b] ↔
      a ≠ b ∧ ¬ RelMap Language.adj ![a, b] := by
  let hc : (complementMap M).size = M.size ^ 1 :=
    FullTupleInterpretation.card_toDomainInterpretation M
  refine (complement.relMap_map_toDomainInterpretation one_pos Language.adj _).trans ?_
  change (complement.rel Language.adj).Realize
    (fun p => lexEquiv.symm (Fin.cast hc
      (![Fin.cast (size_complementMap M).symm a,
         Fin.cast (size_complementMap M).symm b] p.1)) p.2) ↔ _
  rw [realize_complement]
  have hcoord (i : Fin 2) :
      lexEquiv.symm (Fin.cast hc
        (![Fin.cast (size_complementMap M).symm a,
           Fin.cast (size_complementMap M).symm b] i)) 0 = (![a, b] : Fin 2 → Fin M.size) i := by
    apply Fin.ext
    rw [lexEquiv_symm_apply_val]
    simp only [Fin.rev, Fin.val_zero, zero_add, tsub_self, pow_zero, Nat.div_one, Fin.val_cast]
    fin_cases i
    · exact Nat.mod_eq_of_lt a.isLt
    · exact Nat.mod_eq_of_lt b.isLt
  rw [hcoord 0, hcoord 1]
  refine and_congr Iff.rfl (not_congr (iff_of_eq (congrArg (RelMap Language.adj) ?_)))
  funext i
  exact hcoord i

/-- On `Fin 3`, the element of `(copyMap ∘ complementMap) M` corresponding to `![1, 2]` has exact
lexicographic rank `5`; it is `False` on `edge12`, `True` on `noEdges`, and diagonal rank `0`
(`![0, 0]`) is `False` on `noEdges`. -/
example :
    let a12 (M : Ordered.Structure Language.graph) (hM : M.size = 3) :
        (copyMap ∘ complementMap) M :=
      pairElt (complementMap M)
        (Fin.cast (size_complementMap M).symm ⟨1, by lia⟩)
        (Fin.cast (size_complementMap M).symm ⟨2, by lia⟩)
    let a00 : (copyMap ∘ complementMap) noEdges :=
      pairElt (complementMap noEdges)
        (Fin.cast (size_complementMap noEdges).symm ⟨0, by decide⟩)
        (Fin.cast (size_complementMap noEdges).symm ⟨0, by decide⟩)
    (a12 edge12 rfl).val = 5 ∧
      (a12 noEdges rfl).val = 5 ∧
      a00.val = 0 ∧
      ¬ RelMap (M := (copyMap ∘ complementMap) edge12) uRel ![a12 edge12 rfl] ∧
      RelMap (M := (copyMap ∘ complementMap) noEdges) uRel ![a12 noEdges rfl] ∧
      ¬ RelMap (M := (copyMap ∘ complementMap) noEdges) uRel ![a00] := by
  dsimp only [Function.comp_apply]
  have hval12 (M : Ordered.Structure Language.graph) (hM : M.size = 3) :
      (pairElt (complementMap M)
        (Fin.cast (size_complementMap M).symm ⟨1, by lia⟩)
        (Fin.cast (size_complementMap M).symm ⟨2, by lia⟩)).val = 5 := by
    change lexRank ![Fin.cast (size_complementMap M).symm ⟨1, by lia⟩,
      Fin.cast (size_complementMap M).symm ⟨2, by lia⟩] = 5
    rw [lexRank_apply, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_cast, size_complementMap, hM,
      Fin.rev, Fin.val_zero, Fin.val_one]
    decide
  have hval00 :
      (pairElt (complementMap noEdges)
        (Fin.cast (size_complementMap noEdges).symm ⟨0, by decide⟩)
        (Fin.cast (size_complementMap noEdges).symm ⟨0, by decide⟩)).val = 0 := by
    change lexRank ![Fin.cast (size_complementMap noEdges).symm ⟨0, by decide⟩,
      Fin.cast (size_complementMap noEdges).symm ⟨0, by decide⟩] = 0
    rw [lexRank_apply, Fin.sum_univ_two]
    simp only [Fin.val_cast, Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, add_zero]
  refine ⟨hval12 edge12 rfl, hval12 noEdges rfl, hval00, ?_, ?_, ?_⟩
  · rw [relMap_copyMap, relMap_complementMap, relMap_graphOn]
    dsimp only [edge12, graphOn]
    decide
  · rw [relMap_copyMap, relMap_complementMap, relMap_graphOn]
    dsimp only [noEdges, graphOn]
    decide
  · rw [relMap_copyMap, relMap_complementMap, relMap_graphOn]
    dsimp only [noEdges, graphOn]
    decide

/-! ### Projection reductions, transitivity, FO refinement, and logspace lift -/

/-- Element `0` of an ordered structure. -/
def zeroElt {L : Language} (M : Ordered.Structure L) : Fin M.size :=
  ⟨0, by have := M.size_ge_two; lia⟩

/-- Element `1` of an ordered structure (`M.size ≥ 2`). -/
def oneElt {L : Language} (M : Ordered.Structure L) : Fin M.size :=
  ⟨1, M.size_ge_two⟩

/-- Ordered graphs with an edge `0 → 1`. -/
def hasEdge01 : Query Language.graph :=
  {M | RelMap Language.adj ![zeroElt M, oneElt M]}

/-- Ordered graphs without an edge `0 → 1`. -/
def missingEdge01 : Query Language.graph :=
  {M | ¬ RelMap Language.adj ![zeroElt M, oneElt M]}

/-- Ordered `unary`-structures where `uRel` holds at element `1` (the lexicographic rank of
`![0, 1]` in `Fin n × Fin n` for every `n ≥ 2`). -/
def hasPair01 : Query unary :=
  {M | RelMap uRel ![oneElt M]}

/-- `ProjectionReduces.refl`, `QFProjectionReduces.refl` (`@[refl]`), and `.compl` on concrete
queries. -/
example : QFProjectionReduces hasEdge01 hasEdge01 ∧
    ProjectionReduces hasPair01 hasPair01 ∧
    QFProjectionReduces hasEdge01ᶜ hasEdge01ᶜ :=
  ⟨by rfl, by rfl, (QFProjectionReduces.refl hasEdge01).compl⟩

/-- Concrete membership sanity check on `Fin 2` and `Fin 3`. -/
example : edge01 ∈ hasEdge01 ∧ edge01 ∉ missingEdge01 ∧ edge12 ∈ missingEdge01 := by
  change RelMap Language.adj ![zeroElt edge01, oneElt edge01] ∧
    ¬ ¬ RelMap Language.adj ![zeroElt edge01, oneElt edge01] ∧
    ¬ RelMap Language.adj ![zeroElt edge12, oneElt edge12]
  rw [relMap_graphOn, relMap_graphOn]
  dsimp only [edge01, edge12, graphOn, zeroElt, oneElt]
  decide

/-- `missingEdge01 ≤_qfp hasEdge01` via M1's off-diagonal complement. -/
theorem qfProjectionReduces_missingEdge01_hasEdge01 :
    QFProjectionReduces missingEdge01 hasEdge01 := by
  refine QFProjectionReduces.of_qfProjection isQFProjection_complement one_pos fun M => ?_
  change ¬ RelMap Language.adj ![zeroElt M, oneElt M] ↔
    RelMap (M := complementMap M) Language.adj
      ![zeroElt (complementMap M), oneElt (complementMap M)]
  have hz : zeroElt (complementMap M) = Fin.cast (size_complementMap M).symm (zeroElt M) :=
    Fin.ext rfl
  have ho : oneElt (complementMap M) = Fin.cast (size_complementMap M).symm (oneElt M) :=
    Fin.ext rfl
  rw [hz, ho, relMap_complementMap]
  have hne : zeroElt M ≠ oneElt M := fun h => by
    have hval := congrArg Fin.val h
    simp only [zeroElt, oneElt] at hval
    lia
  exact ⟨fun h => ⟨hne, h⟩, And.right⟩

/-- `hasEdge01 ≤_fop hasPair01` across distinct vocabularies via the 2-dimensional `copy`. -/
theorem projectionReduces_hasEdge01_hasPair01 :
    ProjectionReduces hasEdge01 hasPair01 := by
  refine ProjectionReduces.of_projection isProjection_copy two_pos fun M => ?_
  change RelMap Language.adj ![zeroElt M, oneElt M] ↔
    RelMap (M := copyMap M) uRel ![oneElt (copyMap M)]
  have hp : oneElt (copyMap M) = pairElt M (zeroElt M) (oneElt M) := by
    apply Fin.ext
    change 1 = lexRank ![zeroElt M, oneElt M]
    rw [lexRank_apply, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zeroElt, oneElt, zero_mul, zero_add,
      Fin.rev, Fin.val_one, tsub_self, pow_zero, mul_one]
  rw [hp, relMap_copyMap]

/-- Composing `missingEdge01 ≤_qfp hasEdge01` and `hasEdge01 ≤_fop hasPair01` via
`QFProjectionReduces.projectionReduces` and `ProjectionReduces.trans`. -/
theorem projectionReduces_missingEdge01_hasPair01 :
    ProjectionReduces missingEdge01 hasPair01 :=
  qfProjectionReduces_missingEdge01_hasEdge01.projectionReduces.trans
    projectionReduces_hasEdge01_hasPair01

/-- Refining to `Ordered.Reduces` and pulling back first-order definability along the composite
projection reduction. -/
theorem definable_hasPair01 : Ordered.Definable hasPair01 := by
  refine ⟨Relations.formula₁ (Sum.inl uRel : (language unary).Relations 1) (Ordered.one unary),
    fun M => ?_⟩
  change RelMap (L := language unary) (Sum.inl uRel) ![oneElt M] ↔
    (Relations.formula₁ (Sum.inl uRel : (language unary).Relations 1) (Ordered.one unary)).Realize
      (default : Empty → Fin M.size)
  refine (iff_of_eq (congrArg
    (RelMap (L := language unary) (Sum.inl uRel)) (funext fun i => ?_))).trans
    Formula.realize_rel₁.symm
  fin_cases i
  exact Fin.ext rfl

example : Reduces missingEdge01 hasEdge01 ∧
    Reduces missingEdge01 hasPair01 ∧
    Ordered.Definable missingEdge01 :=
  ⟨qfProjectionReduces_missingEdge01_hasEdge01.reduces,
   projectionReduces_missingEdge01_hasPair01.reduces,
   Definable.of_reduces projectionReduces_missingEdge01_hasPair01.reduces definable_hasPair01⟩

/-- Concrete vocabularies for `Language.graph` and `unary` to instantiate `encStructure` logspace
reductions. -/
def graphVocab : Vocabulary Language.graph where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨2, .adj⟩
      invFun := fun _ => 0
      left_inv := fun i => Subsingleton.elim _ i
      right_inv := fun ⟨_, R⟩ => by cases R; rfl }

def unaryVocab : Vocabulary unary where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨1, .u⟩
      invFun := fun _ => 0
      left_inv := fun i => Subsingleton.elim _ i
      right_inv := fun ⟨_, R⟩ => by cases R; rfl }

/-- Both `QFProjectionReduces.logSpaceReducible` and `ProjectionReduces.logSpaceReducible` yield
logspace reductions at `encStructure`. -/
example :
    Cslib.Complexity.LogSpaceReducible encStructure encStructure
      (missingEdge01.encodedLanguage graphVocab) (hasEdge01.encodedLanguage graphVocab) ∧
    Cslib.Complexity.LogSpaceReducible encStructure encStructure
      (missingEdge01.encodedLanguage graphVocab) (hasPair01.encodedLanguage unaryVocab) :=
  ⟨qfProjectionReduces_missingEdge01_hasEdge01.logSpaceReducible graphVocab graphVocab,
   projectionReduces_missingEdge01_hasPair01.logSpaceReducible graphVocab unaryVocab⟩

/-! ### Negative controls -/

/-- A non-empty query cannot projection-reduce to the empty query. -/
theorem not_projectionReduces_univ_empty :
    ¬ ProjectionReduces (Set.univ : Query Language.graph) (∅ : Query unary) := by
  rintro ⟨f, _, hf⟩
  exact (hf noEdges).mp trivial

theorem not_qfProjectionReduces_univ_empty :
    ¬ QFProjectionReduces (Set.univ : Query Language.graph) (∅ : Query Language.graph) := by
  intro h
  exact (let ⟨f, _, hf⟩ := h.projectionReduces; (hf noEdges).mp trivial)

/-- Pre-composing a non-projection (`conjMap`) with the identity still fails to be a projection
map. -/
theorem not_isProjectionMap_conjMap_comp_id :
    ¬ IsProjectionMap (conjMap ∘ (_root_.id : Ordered.Structure pq → _)) :=
  not_isProjectionMap_conjMap

end CslibFrontierTests.OrderedProjectionReduction
