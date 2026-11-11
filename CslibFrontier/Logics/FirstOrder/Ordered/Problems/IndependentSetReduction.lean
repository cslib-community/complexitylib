/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Problems.CNF
public import CslibFrontier.Logics.FirstOrder.Ordered.Problems.SizedGraph
import CslibFrontier.Logics.FirstOrder.Ordered.Projection.Tagged
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Quantifier-free projection from ordered `SAT` to `IndependentSet`, `Clique`, and `VertexCover`

On unordered finite structures, `FO.cnf.SAT` cannot reduce to `FO.sizedGraph.IndependentSet` on all
inputs because singleton structures collapse (`FO.cnf.not_reduces_SAT_IndependentSet`). On
canonically ordered structures (`2 ≤ n`), the endpoint constants `0` and `max` in
`qfNumericLanguage` (without `BIT`) suffice to build a **quantifier-free projection** of dimension
`4` from `Ordered.SAT` to `Ordered.IndependentSet`.

Each vertex tuple `u : Fin 4 → Fin n` has coordinates `(role, c, x, s)`:
* For each clause `c : Fin n`, the block `{u | u 0 = 0 ∧ u 1 = c}` is a clique of candidate literal
  occurrences `(0, c, x, s)`, where `s = 0` represents positive occurrence `pos(c, x)` and `s = max`
  represents negative occurrence `neg(c, x)`.
* The remaining tuples `{u | u 0 ≠ 0}` form one additional clique containing the distinguished
  anchor `anchor = (max, 0, 0, 0)`. Every non-anchor tuple in `{u | u 0 ≠ 0}` is joined to all
  clause-block vertices, while `anchor` is joined to `(0, c, x, 0)` iff `¬ pos(c, x)`, to
  `(0, c, x, max)` iff `¬ neg(c, x)`, and to `(0, c, x, s)` unconditionally for `s ∉ {0, max}`.
* Between distinct clause blocks, `(0, c₁, x, 0)` is joined to `(0, c₂, x, max)` to forbid
  assigning complementary truth values to variable `x`.
* The unary `size` relation holds on `(0, c, 0, 0)` for all `c : Fin n` and on `anchor`, asking for
  an independent set of cardinality `n + 1`. Any independent set of size `n + 1` meets each of the
  `n + 1` cliques in exactly one vertex, forcing `anchor` into the set (since `n ≥ 2`) and selecting
  one satisfied literal from every clause consistently.

Composing with the dimension-1 `sizedGraph` projections yields `SAT ≤_qfp Clique` and
`SAT ≤_qfp VertexCover`.

## Main definitions

* `Cslib.Logic.FO.Ordered.satToIndependentSetFormula`,
  `Cslib.Logic.FO.Ordered.satToIndependentSetInterpretation`: dimension-4 `BIT`-free quantifier-free
  projection from `Ordered.SAT` to `Ordered.IndependentSet`.

## Main results

* `Cslib.Logic.FO.Ordered.isQFProjection_satToIndependentSetInterpretation`:
  `satToIndependentSetInterpretation` is a quantifier-free projection (`IsQFProjection`).
* `Cslib.Logic.FO.Ordered.mem_IndependentSet_satToIndependentSetInterpretation`,
  `Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_IndependentSet`: `Ordered.SAT` quantifier-free
  projection reduces to `Ordered.IndependentSet`.
* `Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_Clique`,
  `Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_VertexCover`: transitive `≤_qfp` reductions to
  `Ordered.Clique` and `Ordered.VertexCover`.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995],
  Definition 3.6 and Proposition 3.7.
-/

public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure CategoryTheory

section SatToIndependentSet

private def isAnchor0 : qfNumericLanguage.Formula (Fin 2 × Fin 4) :=
  QFNumeric.isMax (0, 0) ⊓
    (QFNumeric.isZero (0, 1) ⊓ (QFNumeric.isZero (0, 2) ⊓ QFNumeric.isZero (0, 3)))

private def conflictGuard : qfNumericLanguage.Formula (Fin 2 × Fin 4) :=
  QFNumeric.varEq (0, 2) (1, 2) ⊓
    (QFNumeric.isZero (0, 3) ⊓ QFNumeric.isMax (1, 3))

private def sizeClauseGuard : qfNumericLanguage.Formula (Fin 1 × Fin 4) :=
  QFNumeric.isZero (0, 0) ⊓ (QFNumeric.isZero (0, 2) ⊓ QFNumeric.isZero (0, 3))

private def sizeAnchorGuard : qfNumericLanguage.Formula (Fin 1 × Fin 4) :=
  QFNumeric.isMax (0, 0) ⊓
    (QFNumeric.isZero (0, 1) ⊓ (QFNumeric.isZero (0, 2) ⊓ QFNumeric.isZero (0, 3)))

private theorem isQF_isAnchor0 : isAnchor0.IsQF :=
  (QFNumeric.isQF_isMax _).inf
    ((QFNumeric.isQF_isZero _).inf ((QFNumeric.isQF_isZero _).inf (QFNumeric.isQF_isZero _)))

private theorem isQF_conflictGuard : conflictGuard.IsQF :=
  (QFNumeric.isQF_varEq _ _).inf ((QFNumeric.isQF_isZero _).inf (QFNumeric.isQF_isMax _))

private theorem isQF_sizeClauseGuard : sizeClauseGuard.IsQF :=
  (QFNumeric.isQF_isZero _).inf ((QFNumeric.isQF_isZero _).inf (QFNumeric.isQF_isZero _))

private theorem isQF_sizeAnchorGuard : sizeAnchorGuard.IsQF :=
  (QFNumeric.isQF_isMax _).inf
    ((QFNumeric.isQF_isZero _).inf ((QFNumeric.isQF_isZero _).inf (QFNumeric.isQF_isZero _)))

private def anchorToClauseFormula :
    ProjectionFormula qfNumericLanguage FO.cnf (Fin 2 × Fin 4) :=
  .branch (QFNumeric.isZero (1, 3))
    (.negLit FO.cnf.pos ![(1, 1), (1, 2)])
    (.branch (QFNumeric.isMax (1, 3))
      (.negLit FO.cnf.neg ![(1, 1), (1, 2)])
      (.const true))

private theorem isQF_anchorToClauseFormula : anchorToClauseFormula.IsQF :=
  ⟨QFNumeric.isQF_isZero _, ProjectionFormula.isQF_negLit _ _,
    ⟨QFNumeric.isQF_isMax _, ProjectionFormula.isQF_negLit _ _,
      ProjectionFormula.isQF_const true⟩⟩

/-- Quantifier-free projection formulas for the dimension-4 `SAT → IndependentSet` reduction. -/
def satToIndependentSetFormula :
    ∀ {r : ℕ}, FO.sizedGraph.Relations r →
      ProjectionFormula qfNumericLanguage FO.cnf (Fin r × Fin 4)
  | _, .adj =>
    .branch (QFNumeric.isZero (0, 0))
      (.branch (QFNumeric.isZero (1, 0))
        (.branch (QFNumeric.varEq (0, 1) (1, 1))
          (.const true)
          (.guardAnd conflictGuard (.const true)))
        (.const false))
      (.branch (QFNumeric.isZero (1, 0))
        (.branch isAnchor0 anchorToClauseFormula (.const true))
        (.const true))
  | _, .size =>
    .branch sizeClauseGuard (.const true) (.guardAnd sizeAnchorGuard (.const true))

/-- Dimension-4 full-tuple interpretation reducing `Ordered.SAT` to `Ordered.IndependentSet`
without `BIT`. -/
noncomputable def satToIndependentSetInterpretation :
    FullTupleInterpretation FO.cnf FO.sizedGraph 4 :=
  FullTupleInterpretation.ofQFProjection satToIndependentSetFormula

theorem isQFProjection_satToIndependentSetInterpretation :
    satToIndependentSetInterpretation.IsQFProjection := by
  refine FullTupleInterpretation.isQFProjection_ofQFProjection satToIndependentSetFormula
    fun R => ?_
  cases R
  · exact ⟨QFNumeric.isQF_isZero _,
      ⟨QFNumeric.isQF_isZero _,
        ⟨QFNumeric.isQF_varEq _ _, ProjectionFormula.isQF_const true,
          ProjectionFormula.IsQF.guardAnd isQF_conflictGuard (ProjectionFormula.isQF_const true)⟩,
        ProjectionFormula.isQF_const false⟩,
      ⟨QFNumeric.isQF_isZero _,
        ⟨isQF_isAnchor0, isQF_anchorToClauseFormula, ProjectionFormula.isQF_const true⟩,
        ProjectionFormula.isQF_const true⟩⟩
  · exact ⟨isQF_sizeClauseGuard, ProjectionFormula.isQF_const true,
      ProjectionFormula.IsQF.guardAnd isQF_sizeAnchorGuard (ProjectionFormula.isQF_const true)⟩

/-! ### Tuple-level structure and clique-partition proof -/

private def anchorTuple (n : ℕ) [Fact (2 ≤ n)] : Fin 4 → Fin n :=
  ![QFNumeric.maxFin n, 0, 0, 0]

private def sizeRep {n : ℕ} [Fact (2 ≤ n)] : Option (Fin n) → (Fin 4 → Fin n)
  | some c => ![0, c, 0, 0]
  | none => anchorTuple n

private def blockOf {n : ℕ} [Fact (2 ≤ n)] (u : Fin 4 → Fin n) : Option (Fin n) :=
  if u 0 = 0 then some (u 1) else none

private theorem tuple4_ext {α : Type*} {u v : Fin 4 → α}
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) (h3 : u 3 = v 3) : u = v := by
  funext i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2
  | ⟨3, _⟩ => exact h3

private theorem eq_anchorTuple_iff {n : ℕ} [Fact (2 ≤ n)] (u : Fin 4 → Fin n) :
    (u 0 = QFNumeric.maxFin n ∧ (u 1 = 0 ∧ (u 2 = 0 ∧ u 3 = 0))) ↔ u = anchorTuple n := by
  refine ⟨fun ⟨h0, h1, h2, h3⟩ => tuple4_ext h0 h1 h2 h3, ?_⟩
  rintro rfl
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem pair_arg1_12 {n : ℕ} (u v : Fin 4 → Fin n) :
    (fun i : Fin 2 =>
      (![u, v] (![((1 : Fin 2), (1 : Fin 4)), (1, 2)] i).1)
        (![((1 : Fin 2), (1 : Fin 4)), (1, 2)] i).2) = ![v 1, v 2] := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i' => have hi : i' = 0 := Subsingleton.elim _ _; subst hi; rfl

private theorem realize_isAnchor0 {n : ℕ} [Fact (2 ≤ n)] (u v : Fin 4 → Fin n) :
    isAnchor0.Realize (fun p : Fin 2 × Fin 4 => (![u, v] p.1) p.2) ↔ u = anchorTuple n := by
  simp only [isAnchor0, Formula.realize_inf, QFNumeric.realize_isMax, QFNumeric.realize_isZero,
    Matrix.cons_val_zero]
  exact eq_anchorTuple_iff u

private theorem realize_anchorToClause {n : ℕ} [Fact (2 ≤ n)] [FO.cnf.Structure (Fin n)]
    (u v : Fin 4 → Fin n) :
    anchorToClauseFormula.toFormula.Realize (fun p : Fin 2 × Fin 4 => (![u, v] p.1) p.2) ↔
      (v 3 = 0 ∧ ¬ RelMap FO.cnf.pos ![v 1, v 2]) ∨
        (v 3 ≠ 0 ∧ ((v 3 = QFNumeric.maxFin n ∧ ¬ RelMap FO.cnf.neg ![v 1, v 2]) ∨
          v 3 ≠ QFNumeric.maxFin n)) := by
  simp only [anchorToClauseFormula, ProjectionFormula.realize_toFormula_branch,
    QFNumeric.realize_isZero, QFNumeric.realize_isMax, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ProjectionFormula.realize_negLit, pair_arg1_12, ProjectionFormula.realize_const_true, and_true]

private theorem relMap_size_iff (M : Structure FO.cnf) (u : Fin 4 → Fin M.size) :
    (satToIndependentSetInterpretation.tupleStructure M).RelMap FO.sizedGraph.size ![u] ↔
      (u 0 = 0 ∧ u 2 = 0 ∧ u 3 = 0) ∨ u = anchorTuple M.size := by
  rw [satToIndependentSetInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection, satToIndependentSetFormula]
  simp only [ProjectionFormula.realize_toFormula_branch, ProjectionFormula.realize_guardAnd,
    sizeClauseGuard, sizeAnchorGuard, Formula.realize_inf, QFNumeric.realize_isZero,
    QFNumeric.realize_isMax, Matrix.cons_val_zero, ProjectionFormula.realize_const_true, and_true,
    eq_anchorTuple_iff]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact .inl h
    · exact .inr h
  · rintro (h | rfl)
    · exact .inl h
    · refine .inr ⟨fun hc => QFNumeric.zero_ne_maxFin hc.1.symm, rfl⟩

private theorem ncard_size_satToIndependentSet (M : Structure FO.cnf) :
    {u : Fin 4 → Fin M.size |
      (satToIndependentSetInterpretation.tupleStructure M).RelMap FO.sizedGraph.size ![u]}.ncard =
      Nat.card (Option (Fin M.size)) := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun x => blockOf x.1
      invFun := fun o => ⟨sizeRep o, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [Set.mem_ofPred_eq, relMap_size_iff]
    cases o with
    | some c => exact .inl ⟨rfl, rfl, rfl⟩
    | none => exact .inr rfl
  · rintro ⟨u, hu⟩
    rw [Set.mem_ofPred_eq, relMap_size_iff] at hu
    apply Subtype.ext
    rcases hu with ⟨h0, h2, h3⟩ | rfl
    · simp only [blockOf, h0, ↓reduceIte, sizeRep]
      exact tuple4_ext h0.symm rfl h2.symm h3.symm
    · have hne : (anchorTuple M.size) 0 ≠ 0 := QFNumeric.zero_ne_maxFin.symm
      simp [blockOf, hne, sizeRep]
  · intro o
    cases o with
    | some c => simp [blockOf, sizeRep]
    | none =>
      have hne : (anchorTuple M.size) 0 ≠ 0 := QFNumeric.zero_ne_maxFin.symm
      simp [blockOf, sizeRep, hne]

private theorem adj_same_clause (M : Structure FO.cnf) {u v : Fin 4 → Fin M.size}
    (hu0 : u 0 = 0) (hv0 : v 0 = 0) (h1 : u 1 = v 1) :
    (satToIndependentSetInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj ![u, v] := by
  rw [satToIndependentSetInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection, satToIndependentSetFormula]
  simp [ProjectionFormula.realize_toFormula_branch, hu0, hv0, h1]

private theorem adj_top_block (M : Structure FO.cnf) {u v : Fin 4 → Fin M.size}
    (hu0 : u 0 ≠ 0) (hv0 : v 0 ≠ 0) :
    (satToIndependentSetInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj ![u, v] := by
  rw [satToIndependentSetInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection, satToIndependentSetFormula]
  simp [ProjectionFormula.realize_toFormula_branch, hu0, hv0]

private theorem adj_junk_to_clause (M : Structure FO.cnf) {u v : Fin 4 → Fin M.size}
    (hu0 : u 0 ≠ 0) (huan : u ≠ anchorTuple M.size) (hv0 : v 0 = 0) :
    (satToIndependentSetInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj ![u, v] := by
  rw [satToIndependentSetInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection, satToIndependentSetFormula]
  simp [ProjectionFormula.realize_toFormula_branch, hu0, hv0, realize_isAnchor0, huan]

private theorem adj_anchor_to_clause_iff (M : Structure FO.cnf) {v : Fin 4 → Fin M.size}
    (hv0 : v 0 = 0) :
    (satToIndependentSetInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj
        ![anchorTuple M.size, v] ↔
      (v 3 = 0 ∧ ¬ RelMap (M := M) FO.cnf.pos ![v 1, v 2]) ∨
        (v 3 ≠ 0 ∧ ((v 3 = QFNumeric.maxFin M.size ∧ ¬ RelMap (M := M) FO.cnf.neg ![v 1, v 2]) ∨
          v 3 ≠ QFNumeric.maxFin M.size)) := by
  have han0 : (anchorTuple M.size) 0 ≠ 0 := QFNumeric.zero_ne_maxFin.symm
  rw [satToIndependentSetInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection, satToIndependentSetFormula]
  simp only [ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_isZero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, han0, hv0, false_and,
    not_false_eq_true, true_and, not_true_eq_false, ProjectionFormula.realize_const_true, and_true,
    or_false, false_or, realize_isAnchor0, realize_anchorToClause]

private theorem not_adj_clause_to_top (M : Structure FO.cnf) {u v : Fin 4 → Fin M.size}
    (hu0 : u 0 = 0) (hv0 : v 0 ≠ 0) :
    ¬ (satToIndependentSetInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj ![u, v] := by
  rw [satToIndependentSetInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection, satToIndependentSetFormula]
  simp [ProjectionFormula.realize_toFormula_branch, hu0, hv0]

private theorem adj_clause_to_clause_iff (M : Structure FO.cnf) {u v : Fin 4 → Fin M.size}
    (hu0 : u 0 = 0) (hv0 : v 0 = 0) :
    (satToIndependentSetInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj ![u, v] ↔
      u 1 = v 1 ∨ (u 1 ≠ v 1 ∧ u 2 = v 2 ∧ u 3 = 0 ∧ v 3 = QFNumeric.maxFin M.size) := by
  rw [satToIndependentSetInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection, satToIndependentSetFormula]
  simp only [ProjectionFormula.realize_toFormula_branch, QFNumeric.realize_isZero,
    QFNumeric.realize_varEq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    hu0, hv0, true_and, not_true_eq_false, false_and, or_false,
    ProjectionFormula.realize_const_true, ProjectionFormula.realize_const_false, and_true,
    ProjectionFormula.realize_guardAnd, conflictGuard, Formula.realize_inf,
    QFNumeric.realize_isMax]

end SatToIndependentSet

private theorem mem_SAT_iff_mem_IndependentSet
    {hI : satToIndependentSetInterpretation.toDomainInterpretation.Admissible}
    (M : Structure FO.cnf) :
    M ∈ SAT ↔
      satToIndependentSetInterpretation.toDomainInterpretation.map hI M ∈ IndependentSet := by
  have hiso := satToIndependentSetInterpretation.mem_of_isoClosed
    FO.sizedGraph.isoClosed_IndependentSet (by decide) (hI := hI) M
  change _ ↔ satToIndependentSetInterpretation.toDomainInterpretation.map hI M ∈
    {N : Structure FO.sizedGraph | Bundled.of (c := FO.sizedGraph.Structure) N ∈
      FO.sizedGraph.IndependentSet}
  rw [← hiso, mem_SAT]
  change FO.cnf.Satisfiable M ↔ ∃ s : Set (Fin 4 → Fin M.size),
    s.ncard = {u | (satToIndependentSetInterpretation.tupleStructure M).RelMap FO.sizedGraph.size
      ![u]}.ncard ∧
    s.Pairwise fun u v =>
      ¬ (satToIndependentSetInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj ![u, v]
  rw [ncard_size_satToIndependentSet M]
  constructor
  · rintro ⟨A, hA⟩
    have hsat : ∀ c : Fin M.size,
        ∃ (b : Bool) (x : Fin M.size),
          RelMap (M := M) (FO.cnf.lit b) ![c, x] ∧ (A x ↔ b = true) := by
      intro c
      obtain ⟨⟨b, x⟩, hlit, htr⟩ := (FO.cnf.clauseSatisfied_iff A c).mp (hA c)
      exact ⟨b, x, hlit, htr⟩
    choose b x hlit htrue using hsat
    let pick (c : Fin M.size) : Fin 4 → Fin M.size :=
      ![0, c, x c, if b c then 0 else QFNumeric.maxFin M.size]
    have hpick0 (c : Fin M.size) : (pick c) 0 = 0 := rfl
    have hpick1 (c : Fin M.size) : (pick c) 1 = c := rfl
    have hpick_spec (c : Fin M.size) :
        ((pick c) 3 = 0 ∧ RelMap (M := M) FO.cnf.pos ![c, (pick c) 2] ∧ A ((pick c) 2)) ∨
        ((pick c) 3 = QFNumeric.maxFin M.size ∧
          RelMap (M := M) FO.cnf.neg ![c, (pick c) 2] ∧ ¬ A ((pick c) 2)) := by
      have hl := hlit c
      have ht := htrue c
      cases hbc : b c
      · rw [hbc, FO.cnf.lit_false] at hl
        rw [hbc] at ht
        exact .inr ⟨by simp [pick, hbc], hl, fun hAx => Bool.false_ne_true (ht.mp hAx)⟩
      · rw [hbc, FO.cnf.lit_true] at hl
        rw [hbc] at ht
        exact .inl ⟨by simp [pick, hbc], hl, ht.mpr rfl⟩
    let f : Option (Fin M.size) → (Fin 4 → Fin M.size)
      | some c => pick c
      | none => anchorTuple M.size
    have hf_block (o : Option (Fin M.size)) : blockOf (f o) = o := by
      cases o with
      | some c => simp [f, blockOf, hpick0 c, hpick1 c]
      | none =>
        have hne : (anchorTuple M.size) 0 ≠ 0 := QFNumeric.zero_ne_maxFin.symm
        simp [f, blockOf, hne]
    have hf_inj : Function.Injective f := Function.LeftInverse.injective hf_block
    refine ⟨Set.range f, ?_, ?_⟩
    · rw [← Set.image_univ, Set.ncard_image_of_injective _ hf_inj, Set.ncard_univ]
    · rintro _ ⟨o₁, rfl⟩ _ ⟨o₂, rfl⟩ hne hadj
      have ho_ne : o₁ ≠ o₂ := fun h => hne (congrArg f h)
      cases o₁ with
      | some c₁ =>
        cases o₂ with
        | some c₂ =>
          have hc_ne : c₁ ≠ c₂ := fun h => ho_ne (congrArg some h)
          dsimp only [f] at hadj
          rw [adj_clause_to_clause_iff M (hpick0 c₁) (hpick0 c₂), hpick1 c₁, hpick1 c₂] at hadj
          obtain ⟨_, hx_eq, hs1, hs2⟩ := hadj.resolve_left hc_ne
          rcases hpick_spec c₁ with ⟨_, _, hA1⟩ | ⟨hbad, _, _⟩
          · rcases hpick_spec c₂ with ⟨hbad, _, _⟩ | ⟨_, _, hnA2⟩
            · exact QFNumeric.zero_ne_maxFin (hbad.symm.trans hs2)
            · rw [hx_eq] at hA1
              exact hnA2 hA1
          · exact QFNumeric.zero_ne_maxFin (hs1.symm.trans hbad)
        | none =>
          dsimp only [f] at hadj
          have han0 : (anchorTuple M.size) 0 ≠ 0 := QFNumeric.zero_ne_maxFin.symm
          exact not_adj_clause_to_top M (hpick0 c₁) han0 hadj
      | none =>
        cases o₂ with
        | none => exact ho_ne rfl
        | some c₂ =>
          dsimp only [f] at hadj
          rw [adj_anchor_to_clause_iff M (hpick0 c₂), hpick1 c₂] at hadj
          rcases hpick_spec c₂ with ⟨hs, hpos, _⟩ | ⟨hs, hneg, _⟩
          · rcases hadj with ⟨_, hnpos⟩ | ⟨hne0, _⟩
            · exact hnpos hpos
            · exact hne0 hs
          · rcases hadj with ⟨hz, _⟩ | ⟨_, ⟨_, hnneg⟩ | hnemax⟩
            · exact QFNumeric.zero_ne_maxFin (hz.symm.trans hs)
            · exact hnneg hneg
            · exact hnemax hs
  · rintro ⟨s, hs_card, hind⟩
    have hinj : Function.Injective (fun a : s => blockOf a.val) := by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ hblk
      by_contra hne
      have huv : u ≠ v := fun h => hne (Subtype.ext h)
      dsimp only [blockOf] at hblk
      by_cases hu0 : u 0 = 0 <;> by_cases hv0 : v 0 = 0
      · simp only [hu0, hv0, ↓reduceIte, Option.some.injEq] at hblk
        exact hind hu hv huv (adj_same_clause M hu0 hv0 hblk)
      · simp [hu0, hv0] at hblk
      · simp [hu0, hv0] at hblk
      · exact hind hu hv huv (adj_top_block M hu0 hv0)
    obtain ⟨-, hsurj⟩ := hinj.bijective_of_nat_card_le (by rw [Nat.card_coe_set_eq, hs_card])
    obtain ⟨⟨uTop, huTop⟩, hTopBlk⟩ := hsurj none
    have huTop0 : uTop 0 ≠ 0 := by
      intro hz
      simp [blockOf, hz] at hTopBlk
    obtain ⟨⟨uZero, huZero⟩, hZeroBlk⟩ := hsurj (some 0)
    have huZero0 : uZero 0 = 0 := by
      by_contra hnz
      simp [blockOf, hnz] at hZeroBlk
    have hTop_ne_Zero : uTop ≠ uZero := fun h => huTop0 (h ▸ huZero0)
    have huTop_eq : uTop = anchorTuple M.size := by
      by_contra huan
      exact hind huTop huZero hTop_ne_Zero (adj_junk_to_clause M huTop0 huan huZero0)
    have han_mem : anchorTuple M.size ∈ s := huTop_eq ▸ huTop
    let A (x : Fin M.size) : Prop := ∃ u ∈ s, u 0 = 0 ∧ u 2 = x ∧ u 3 = 0
    refine ⟨A, fun c => ?_⟩
    obtain ⟨⟨v, hv⟩, hvBlk⟩ := hsurj (some c)
    have hv0 : v 0 = 0 := by
      by_contra hnz
      simp [blockOf, hnz] at hvBlk
    have hv1 : v 1 = c := by
      simp only [blockOf, hv0, ↓reduceIte, Option.some.injEq] at hvBlk
      exact hvBlk
    have han_ne_v : anchorTuple M.size ≠ v := by
      intro h
      have := congrFun h 0
      rw [hv0] at this
      exact QFNumeric.zero_ne_maxFin this.symm
    have hnadj_an :
        ¬ (satToIndependentSetInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj
          ![anchorTuple M.size, v] :=
      hind han_mem hv han_ne_v
    rw [adj_anchor_to_clause_iff M hv0, hv1] at hnadj_an
    by_cases hv3_zero : v 3 = 0
    · have hpos : RelMap (M := M) FO.cnf.pos ![c, v 2] := by
        by_contra hnpos
        exact hnadj_an (.inl ⟨hv3_zero, hnpos⟩)
      exact ⟨v 2, .inl ⟨hpos, ⟨v, hv, hv0, rfl, hv3_zero⟩⟩⟩
    · by_cases hv3_max : v 3 = QFNumeric.maxFin M.size
      · have hneg : RelMap (M := M) FO.cnf.neg ![c, v 2] := by
          by_contra hnneg
          exact hnadj_an (.inr ⟨hv3_zero, .inl ⟨hv3_max, hnneg⟩⟩)
        refine ⟨v 2, .inr ⟨hneg, ?_⟩⟩
        rintro ⟨u, hu, hu0, hu2, hu3⟩
        have huv : u ≠ v := by
          intro h
          have h3 := congrFun h 3
          rw [hu3, hv3_max] at h3
          exact QFNumeric.zero_ne_maxFin h3
        refine hind hu hv huv ((adj_clause_to_clause_iff M hu0 hv0).mpr ?_)
        by_cases hc : u 1 = v 1
        · exact .inl hc
        · exact .inr ⟨hc, hu2, hu3, hv3_max⟩
      · exact False.elim (hnadj_an (.inr ⟨hv3_zero, .inr hv3_max⟩))

/-- **Exact `IndependentSet` preservation of `satToIndependentSetInterpretation`**: on every ordered
`FO.cnf` structure `M`, the dimension-4 image belongs to `Ordered.IndependentSet` if and only if
`M ∈ Ordered.SAT`. -/
theorem mem_IndependentSet_satToIndependentSetInterpretation
    {hI : satToIndependentSetInterpretation.toDomainInterpretation.Admissible}
    (M : Structure FO.cnf) :
    satToIndependentSetInterpretation.toDomainInterpretation.map hI M ∈ IndependentSet ↔
      M ∈ SAT :=
  (mem_SAT_iff_mem_IndependentSet M).symm

/-- **`Ordered.SAT` quantifier-free projection reduces to `Ordered.IndependentSet`**
(without `BIT`). -/
theorem sat_qfProjectionReduces_IndependentSet : QFProjectionReduces SAT IndependentSet :=
  QFProjectionReduces.of_qfProjection isQFProjection_satToIndependentSetInterpretation (by decide)
    mem_SAT_iff_mem_IndependentSet

/-- **`Ordered.SAT` quantifier-free projection reduces to `Ordered.Clique`** (without `BIT`). -/
theorem sat_qfProjectionReduces_Clique : QFProjectionReduces SAT Clique :=
  sat_qfProjectionReduces_IndependentSet.trans independentSet_qfProjectionReduces_Clique

/-- **`Ordered.SAT` quantifier-free projection reduces to `Ordered.VertexCover`**
(without `BIT`). -/
theorem sat_qfProjectionReduces_VertexCover : QFProjectionReduces SAT VertexCover :=
  sat_qfProjectionReduces_IndependentSet.trans independentSet_qfProjectionReduces_VertexCover

end Cslib.Logic.FO.Ordered
