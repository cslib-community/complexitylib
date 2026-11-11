/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Projection.Reduction
public import CslibFrontier.Logics.FirstOrder.Problems.SizedGraph
import CslibFrontier.Logics.FirstOrder.Ordered.Projection.Tagged

/-!
# Canonical ordered independent set, clique, and vertex cover

Over `Cslib.Logic.FO.sizedGraph` (a binary edge relation `adj` and a unary relation `size` whose
cardinality specifies the target set size), `Ordered.IndependentSet`, `Ordered.Clique`, and
`Ordered.VertexCover` are the canonical ordered queries corresponding to
`FO.sizedGraph.IndependentSet`, `FO.sizedGraph.Clique`, and `FO.sizedGraph.VertexCover` on
universes `Fin n` with `2 ≤ n`.

All six pairwise reductions among the three problems are certified **quantifier-free projections**
(`QFProjectionReduces`, `≤_qfp`, without `BIT`) of dimension `1`:
* `complementEdgesInterpretation` branches on the numeric equality guard `x = y` (emitting `false`
  on the diagonal and `¬ adj(x, y)` off the diagonal) while copying `size(x)`, giving
  `IndependentSet ≤_qfp Clique` and `Clique ≤_qfp IndependentSet`.
* `complementSizeInterpretation` copies `adj(x, y)` and negates `size(x)`, giving
  `IndependentSet ≤_qfp VertexCover` and `VertexCover ≤_qfp IndependentSet`.
* Transitivity (`QFProjectionReduces.trans`) gives `Clique ≤_qfp VertexCover` and
  `VertexCover ≤_qfp Clique`.

For existential second-order definability and native `NP` membership at `encStructure`, see
`CslibFrontier.Computability.Complexity.Fagin.Ordered.Problems`.

## Main definitions

* `Cslib.Logic.FO.Ordered.sizedGraphVocabulary`: canonical vocabulary for `FO.sizedGraph` (`adj` at
  index `0`, `size` at index `1`).
* `Cslib.Logic.FO.Ordered.IndependentSet`, `Cslib.Logic.FO.Ordered.Clique`,
  `Cslib.Logic.FO.Ordered.VertexCover`: canonical ordered queries over `FO.sizedGraph`.
* `Cslib.Logic.FO.Ordered.complementEdgesFormula`,
  `Cslib.Logic.FO.Ordered.complementEdgesInterpretation`: dimension-1 quantifier-free projection
  complementing off-diagonal edges.
* `Cslib.Logic.FO.Ordered.complementSizeFormula`,
  `Cslib.Logic.FO.Ordered.complementSizeInterpretation`: dimension-1 quantifier-free projection
  complementing the unary `size` relation.

## Main results

* `Cslib.Logic.FO.Ordered.isQFProjection_complementEdgesInterpretation`,
  `Cslib.Logic.FO.Ordered.isQFProjection_complementSizeInterpretation`: both interpretations are
  `BIT`-free quantifier-free projections.
* `Cslib.Logic.FO.Ordered.independentSet_qfProjectionReduces_Clique`,
  `Cslib.Logic.FO.Ordered.clique_qfProjectionReduces_IndependentSet`,
  `Cslib.Logic.FO.Ordered.independentSet_qfProjectionReduces_VertexCover`,
  `Cslib.Logic.FO.Ordered.vertexCover_qfProjectionReduces_IndependentSet`,
  `Cslib.Logic.FO.Ordered.clique_qfProjectionReduces_VertexCover`,
  `Cslib.Logic.FO.Ordered.vertexCover_qfProjectionReduces_Clique`: pairwise `≤_qfp`
  interreducibility of ordered independent set, clique, and vertex cover.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [N. Immerman and S. Landau, *The Complexity of Iterated Multiplication*][ImmermanLandau1995],
  Definition 3.6 and Proposition 3.7.
-/

public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure CategoryTheory

/-- Canonical vocabulary for `FO.sizedGraph`: index `0` is `adj` (arity `2`) and index `1` is
`size` (arity `1`). -/
@[expose] def sizedGraphVocabulary : Vocabulary FO.sizedGraph where
  count := 2
  symbol :=
    { toFun
        | ⟨0, _⟩ => ⟨2, FO.sizedGraph.adj⟩
        | ⟨1, _⟩ => ⟨1, FO.sizedGraph.size⟩
      invFun
        | ⟨_, .adj⟩ => ⟨0, by decide⟩
        | ⟨_, .size⟩ => ⟨1, by decide⟩
      left_inv := by
        rintro ⟨i, hi⟩
        match i, hi with
        | 0, _ | 1, _ => rfl
      right_inv := by
        rintro ⟨_, r⟩
        cases r <;> rfl }

/-- **Canonical ordered independent set**: an ordered `sizedGraph` structure belongs to
`IndependentSet` when it has an independent set of cardinality `|size|`. -/
@[expose] def IndependentSet : Query FO.sizedGraph :=
  {M | ∃ s : Set M,
    s.ncard = {x : M | RelMap FO.sizedGraph.size ![x]}.ncard ∧
      s.Pairwise fun x y => ¬ RelMap FO.sizedGraph.adj ![x, y]}

/-- **Canonical ordered clique**: an ordered `sizedGraph` structure belongs to `Clique` when it has
a clique of cardinality `|size|`. -/
@[expose] def Clique : Query FO.sizedGraph :=
  {M | ∃ s : Set M,
    s.ncard = {x : M | RelMap FO.sizedGraph.size ![x]}.ncard ∧
      s.Pairwise fun x y => RelMap FO.sizedGraph.adj ![x, y]}

/-- **Canonical ordered vertex cover**: an ordered `sizedGraph` structure belongs to `VertexCover`
when it has a vertex cover of cardinality `|size|`. -/
@[expose] def VertexCover : Query FO.sizedGraph :=
  {M | ∃ s : Set M,
    s.ncard = {x : M | RelMap FO.sizedGraph.size ![x]}.ncard ∧
      ∀ x y, x ≠ y → RelMap FO.sizedGraph.adj ![x, y] → x ∈ s ∨ y ∈ s}

theorem mem_IndependentSet {M : Structure FO.sizedGraph} :
    M ∈ IndependentSet ↔ ∃ s : Set M,
      s.ncard = {x : M | RelMap FO.sizedGraph.size ![x]}.ncard ∧
        s.Pairwise fun x y => ¬ RelMap FO.sizedGraph.adj ![x, y] :=
  Iff.rfl

theorem mem_Clique {M : Structure FO.sizedGraph} :
    M ∈ Clique ↔ ∃ s : Set M,
      s.ncard = {x : M | RelMap FO.sizedGraph.size ![x]}.ncard ∧
        s.Pairwise fun x y => RelMap FO.sizedGraph.adj ![x, y] :=
  Iff.rfl

theorem mem_VertexCover {M : Structure FO.sizedGraph} :
    M ∈ VertexCover ↔ ∃ s : Set M,
      s.ncard = {x : M | RelMap FO.sizedGraph.size ![x]}.ncard ∧
        ∀ x y, x ≠ y → RelMap FO.sizedGraph.adj ![x, y] → x ∈ s ∨ y ∈ s :=
  Iff.rfl

/-! ### Off-diagonal edge complement (`IndependentSet ↔_qfp Clique`) -/

/-- Quantifier-free projection formulas complementing `adj` off the diagonal and preserving `size`.
-/
def complementEdgesFormula :
    ∀ {r : ℕ}, FO.sizedGraph.Relations r →
      ProjectionFormula qfNumericLanguage FO.sizedGraph (Fin r × Fin 1)
  | _, .adj =>
    .branch (QFNumeric.varEq (0, 0) (1, 0))
      (.const false)
      (.negLit FO.sizedGraph.adj ![(0, 0), (1, 0)])
  | _, .size => .posLit FO.sizedGraph.size ![(0, 0)]

/-- Dimension-1 full-tuple interpretation complementing edges off the diagonal. -/
noncomputable def complementEdgesInterpretation :
    FullTupleInterpretation FO.sizedGraph FO.sizedGraph 1 :=
  FullTupleInterpretation.ofQFProjection complementEdgesFormula

theorem isQFProjection_complementEdgesInterpretation :
    complementEdgesInterpretation.IsQFProjection :=
  FullTupleInterpretation.isQFProjection_ofQFProjection complementEdgesFormula fun R => by
    cases R
    · exact ⟨QFNumeric.isQF_varEq _ _, ProjectionFormula.isQF_const false,
        ProjectionFormula.isQF_negLit _ _⟩
    · exact ProjectionFormula.isQF_posLit _ _

section ComplementProofs

private def singletonTupleEquiv (n : ℕ) : Fin n ≃ (Fin 1 → Fin n) where
  toFun x _ := x
  invFun u := u 0
  left_inv _ := rfl
  right_inv u := funext fun i => congrArg u (Subsingleton.elim 0 i)

private theorem pair_args_eq {α : Type*} (u v : Fin 1 → α) :
    (fun i : Fin 2 =>
      (![u, v] (![((0 : Fin 2), (0 : Fin 1)), (1, 0)] i).1)
        (![((0 : Fin 2), (0 : Fin 1)), (1, 0)] i).2) = ![u 0, v 0] := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i' =>
    have hi : i' = 0 := Subsingleton.elim _ _
    subst hi
    rfl

private theorem single_args_eq {α : Type*} (u : Fin 1 → α) :
    (fun i : Fin 1 =>
      (![u] (![((0 : Fin 1), (0 : Fin 1))] i).1)
        (![((0 : Fin 1), (0 : Fin 1))] i).2) = ![u 0] := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rfl

private theorem relMap_complementEdges_adj (M : Structure FO.sizedGraph)
    (u v : Fin 1 → Fin M.size) :
    (complementEdgesInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj ![u, v] ↔
      u ≠ v ∧ ¬ RelMap (M := M) FO.sizedGraph.adj ![u 0, v 0] := by
  rw [complementEdgesInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection,
    complementEdgesFormula, ProjectionFormula.realize_toFormula_branch]
  have heq : u 0 = v 0 ↔ u = v :=
    ⟨fun h => (singletonTupleEquiv M.size).symm.injective h, fun h => congrFun h 0⟩
  simp only [QFNumeric.realize_varEq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, heq, ProjectionFormula.realize_const_false, and_false, false_or,
    ProjectionFormula.realize_negLit, pair_args_eq]

private theorem relMap_complementEdges_size (M : Structure FO.sizedGraph)
    (u : Fin 1 → Fin M.size) :
    (complementEdgesInterpretation.tupleStructure M).RelMap FO.sizedGraph.size ![u] ↔
      RelMap (M := M) FO.sizedGraph.size ![u 0] := by
  rw [complementEdgesInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection,
    complementEdgesFormula, ProjectionFormula.realize_posLit, single_args_eq]

private theorem ncard_size_eq_of_iff (M : Structure FO.sizedGraph)
    (S : FO.sizedGraph.Structure (Fin 1 → Fin M.size))
    (hsize : ∀ u : Fin 1 → Fin M.size, S.RelMap FO.sizedGraph.size ![u] ↔
      RelMap (M := M) FO.sizedGraph.size ![u 0]) :
    {u : Fin 1 → Fin M.size | S.RelMap FO.sizedGraph.size ![u]}.ncard =
      {x : M | RelMap FO.sizedGraph.size ![x]}.ncard := by
  have himg : {u : Fin 1 → Fin M.size | S.RelMap FO.sizedGraph.size ![u]} =
      singletonTupleEquiv M.size '' {x : M | RelMap FO.sizedGraph.size ![x]} := by
    ext u
    simp only [Set.mem_ofPred_eq, hsize u, Set.mem_image]
    exact ⟨fun h => ⟨u 0, h, (singletonTupleEquiv M.size).apply_symm_apply u⟩,
      fun ⟨x, hx, hxu⟩ => hxu ▸ hx⟩
  rw [himg, Set.ncard_image_of_injective _ (singletonTupleEquiv M.size).injective]

theorem mem_Clique_complementEdgesInterpretation
    {hI : complementEdgesInterpretation.toDomainInterpretation.Admissible}
    (M : Structure FO.sizedGraph) :
    complementEdgesInterpretation.toDomainInterpretation.map hI M ∈ Clique ↔
      M ∈ IndependentSet := by
  have hiso := complementEdgesInterpretation.mem_of_isoClosed FO.sizedGraph.isoClosed_Clique
    (by decide) (hI := hI) M
  change complementEdgesInterpretation.toDomainInterpretation.map hI M ∈
    {N : Structure FO.sizedGraph | Bundled.of (c := FO.sizedGraph.Structure) N ∈
      FO.sizedGraph.Clique} ↔ _
  rw [← hiso, mem_IndependentSet]
  change (∃ t : Set (Fin 1 → Fin M.size),
    t.ncard = {u | (complementEdgesInterpretation.tupleStructure M).RelMap FO.sizedGraph.size
      ![u]}.ncard ∧
    t.Pairwise fun u v =>
      (complementEdgesInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj ![u, v]) ↔ _
  rw [ncard_size_eq_of_iff M _ (relMap_complementEdges_size M)]
  let e := singletonTupleEquiv M.size
  constructor
  · rintro ⟨t, ht, hcl⟩
    refine ⟨e.symm '' t, (Set.ncard_image_of_injective t e.symm.injective).trans ht, ?_⟩
    rw [e.symm.injective.injOn.pairwise_image]
    intro u hu v hv huv
    obtain ⟨-, hnadj⟩ := (relMap_complementEdges_adj M u v).mp (hcl hu hv huv)
    exact hnadj
  · rintro ⟨s, hs, hind⟩
    refine ⟨e '' s, (Set.ncard_image_of_injective s e.injective).trans hs, ?_⟩
    rw [e.injective.injOn.pairwise_image]
    intro x hx y hy hxy
    exact (relMap_complementEdges_adj M (e x) (e y)).mpr
      ⟨e.injective.ne hxy, hind hx hy hxy⟩

theorem mem_IndependentSet_complementEdgesInterpretation
    {hI : complementEdgesInterpretation.toDomainInterpretation.Admissible}
    (M : Structure FO.sizedGraph) :
    complementEdgesInterpretation.toDomainInterpretation.map hI M ∈ IndependentSet ↔
      M ∈ Clique := by
  have hiso := complementEdgesInterpretation.mem_of_isoClosed
    FO.sizedGraph.isoClosed_IndependentSet (by decide) (hI := hI) M
  change complementEdgesInterpretation.toDomainInterpretation.map hI M ∈
    {N : Structure FO.sizedGraph | Bundled.of (c := FO.sizedGraph.Structure) N ∈
      FO.sizedGraph.IndependentSet} ↔ _
  rw [← hiso, mem_Clique]
  change (∃ t : Set (Fin 1 → Fin M.size),
    t.ncard = {u | (complementEdgesInterpretation.tupleStructure M).RelMap FO.sizedGraph.size
      ![u]}.ncard ∧
    t.Pairwise fun u v =>
      ¬ (complementEdgesInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj ![u, v]) ↔ _
  rw [ncard_size_eq_of_iff M _ (relMap_complementEdges_size M)]
  let e := singletonTupleEquiv M.size
  constructor
  · rintro ⟨t, ht, hind⟩
    refine ⟨e.symm '' t, (Set.ncard_image_of_injective t e.symm.injective).trans ht, ?_⟩
    rw [e.symm.injective.injOn.pairwise_image]
    intro u hu v hv huv
    by_contra hnadj
    exact hind hu hv huv ((relMap_complementEdges_adj M u v).mpr ⟨huv, hnadj⟩)
  · rintro ⟨s, hs, hcl⟩
    refine ⟨e '' s, (Set.ncard_image_of_injective s e.injective).trans hs, ?_⟩
    rw [e.injective.injOn.pairwise_image]
    intro x hx y hy hxy hbad
    obtain ⟨-, hnadj⟩ := (relMap_complementEdges_adj M (e x) (e y)).mp hbad
    exact hnadj (hcl hx hy hxy)

end ComplementProofs

/-- **`Ordered.IndependentSet` quantifier-free projection reduces to `Ordered.Clique`.** -/
theorem independentSet_qfProjectionReduces_Clique :
    QFProjectionReduces IndependentSet Clique :=
  QFProjectionReduces.of_qfProjection isQFProjection_complementEdgesInterpretation (by decide)
    fun M => (mem_Clique_complementEdgesInterpretation M).symm

/-- **`Ordered.Clique` quantifier-free projection reduces to `Ordered.IndependentSet`.** -/
theorem clique_qfProjectionReduces_IndependentSet :
    QFProjectionReduces Clique IndependentSet :=
  QFProjectionReduces.of_qfProjection isQFProjection_complementEdgesInterpretation (by decide)
    fun M => (mem_IndependentSet_complementEdgesInterpretation M).symm

/-! ### Size complement (`IndependentSet ↔_qfp VertexCover`) -/

/-- Quantifier-free projection formulas preserving `adj` and complementing `size`. -/
def complementSizeFormula :
    ∀ {r : ℕ}, FO.sizedGraph.Relations r →
      ProjectionFormula qfNumericLanguage FO.sizedGraph (Fin r × Fin 1)
  | _, .adj => .posLit FO.sizedGraph.adj ![(0, 0), (1, 0)]
  | _, .size => .negLit FO.sizedGraph.size ![(0, 0)]

/-- Dimension-1 full-tuple interpretation complementing the unary `size` relation. -/
noncomputable def complementSizeInterpretation :
    FullTupleInterpretation FO.sizedGraph FO.sizedGraph 1 :=
  FullTupleInterpretation.ofQFProjection complementSizeFormula

theorem isQFProjection_complementSizeInterpretation :
    complementSizeInterpretation.IsQFProjection :=
  FullTupleInterpretation.isQFProjection_ofQFProjection complementSizeFormula fun R => by
    cases R
    · exact ProjectionFormula.isQF_posLit _ _
    · exact ProjectionFormula.isQF_negLit _ _

section ComplementSizeProofs

private theorem relMap_complementSize_adj (M : Structure FO.sizedGraph)
    (u v : Fin 1 → Fin M.size) :
    (complementSizeInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj ![u, v] ↔
      RelMap (M := M) FO.sizedGraph.adj ![u 0, v 0] := by
  rw [complementSizeInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection,
    complementSizeFormula, ProjectionFormula.realize_posLit, pair_args_eq]

private theorem relMap_complementSize_size (M : Structure FO.sizedGraph)
    (u : Fin 1 → Fin M.size) :
    (complementSizeInterpretation.tupleStructure M).RelMap FO.sizedGraph.size ![u] ↔
      ¬ RelMap (M := M) FO.sizedGraph.size ![u 0] := by
  rw [complementSizeInterpretation,
    FullTupleInterpretation.relMap_tupleStructure_ofQFProjection,
    complementSizeFormula, ProjectionFormula.realize_negLit, single_args_eq]

private theorem ncard_size_complementSize (M : Structure FO.sizedGraph) :
    {u : Fin 1 → Fin M.size |
      (complementSizeInterpretation.tupleStructure M).RelMap FO.sizedGraph.size ![u]}.ncard =
      ({x : M | RelMap FO.sizedGraph.size ![x]}ᶜ).ncard := by
  let e := singletonTupleEquiv M.size
  have himg : {u : Fin 1 → Fin M.size |
      (complementSizeInterpretation.tupleStructure M).RelMap FO.sizedGraph.size ![u]} =
      e '' ({x : M | RelMap FO.sizedGraph.size ![x]}ᶜ) := by
    ext u
    simp only [Set.mem_ofPred_eq, relMap_complementSize_size M u, Set.mem_image,
      Set.mem_compl_iff]
    exact ⟨fun h => ⟨u 0, h, e.apply_symm_apply u⟩, fun ⟨x, hx, hxu⟩ => hxu ▸ hx⟩
  rw [himg, Set.ncard_image_of_injective _ e.injective]

theorem mem_VertexCover_complementSizeInterpretation
    {hI : complementSizeInterpretation.toDomainInterpretation.Admissible}
    (M : Structure FO.sizedGraph) :
    complementSizeInterpretation.toDomainInterpretation.map hI M ∈ VertexCover ↔
      M ∈ IndependentSet := by
  have hiso := complementSizeInterpretation.mem_of_isoClosed
    FO.sizedGraph.isoClosed_VertexCover (by decide) (hI := hI) M
  change complementSizeInterpretation.toDomainInterpretation.map hI M ∈
    {N : Structure FO.sizedGraph | Bundled.of (c := FO.sizedGraph.Structure) N ∈
      FO.sizedGraph.VertexCover} ↔ _
  rw [← hiso, mem_IndependentSet]
  change (∃ t : Set (Fin 1 → Fin M.size),
    t.ncard = {u | (complementSizeInterpretation.tupleStructure M).RelMap FO.sizedGraph.size
      ![u]}.ncard ∧
    ∀ u v, u ≠ v →
      (complementSizeInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj ![u, v] →
      u ∈ t ∨ v ∈ t) ↔ _
  rw [ncard_size_complementSize M]
  let e := singletonTupleEquiv M.size
  constructor
  · rintro ⟨t, ht, hcov⟩
    let s : Set M := (e.symm '' t)ᶜ
    have hsc : sᶜ = e.symm '' t := compl_compl _
    refine ⟨s, FO.sizedGraph.ncard_compl_eq_iff.mp
      (by rw [hsc, Set.ncard_image_of_injective _ e.symm.injective, ht]),
      (FO.sizedGraph.pairwise_not_adj_iff_compl s).mpr fun x y hxy hadj => ?_⟩
    rw [hsc]
    have ht_or := hcov (e x) (e y) (e.injective.ne hxy)
      ((relMap_complementSize_adj M (e x) (e y)).mpr hadj)
    refine ht_or.imp (fun hx => ?_) (fun hy => ?_)
    · rw [← e.symm_apply_apply x]
      exact Set.mem_image_of_mem e.symm hx
    · rw [← e.symm_apply_apply y]
      exact Set.mem_image_of_mem e.symm hy
  · rintro ⟨s, hs, hind⟩
    refine ⟨e '' sᶜ, (Set.ncard_image_of_injective _ e.injective).trans
      (FO.sizedGraph.ncard_compl_eq_iff.mpr hs), fun u v huv hadj => ?_⟩
    have hcov := (FO.sizedGraph.pairwise_not_adj_iff_compl s).mp hind (u 0) (v 0)
      (e.symm.injective.ne huv) ((relMap_complementSize_adj M u v).mp hadj)
    refine hcov.imp (fun hu => ?_) (fun hv => ?_)
    · rw [← e.apply_symm_apply u]
      exact Set.mem_image_of_mem e hu
    · rw [← e.apply_symm_apply v]
      exact Set.mem_image_of_mem e hv

theorem mem_IndependentSet_complementSizeInterpretation
    {hI : complementSizeInterpretation.toDomainInterpretation.Admissible}
    (M : Structure FO.sizedGraph) :
    complementSizeInterpretation.toDomainInterpretation.map hI M ∈ IndependentSet ↔
      M ∈ VertexCover := by
  have hiso := complementSizeInterpretation.mem_of_isoClosed
    FO.sizedGraph.isoClosed_IndependentSet (by decide) (hI := hI) M
  change complementSizeInterpretation.toDomainInterpretation.map hI M ∈
    {N : Structure FO.sizedGraph | Bundled.of (c := FO.sizedGraph.Structure) N ∈
      FO.sizedGraph.IndependentSet} ↔ _
  rw [← hiso, mem_VertexCover]
  change (∃ t : Set (Fin 1 → Fin M.size),
    t.ncard = {u | (complementSizeInterpretation.tupleStructure M).RelMap FO.sizedGraph.size
      ![u]}.ncard ∧
    t.Pairwise fun u v =>
      ¬ (complementSizeInterpretation.tupleStructure M).RelMap FO.sizedGraph.adj ![u, v]) ↔ _
  rw [ncard_size_complementSize M]
  let e := singletonTupleEquiv M.size
  constructor
  · rintro ⟨t, ht, hind⟩
    let s : Set M := (e.symm '' t)ᶜ
    have hsc : sᶜ = e.symm '' t := compl_compl _
    refine ⟨s, FO.sizedGraph.ncard_compl_eq_iff.mp
      (by rw [hsc, Set.ncard_image_of_injective _ e.symm.injective, ht]), fun x y hxy hadj => ?_⟩
    by_contra hboth
    simp only [s, Set.mem_compl_iff, not_or, not_not] at hboth
    obtain ⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩⟩ := hboth
    exact hind hu hv (ne_of_apply_ne e.symm hxy) ((relMap_complementSize_adj M u v).mpr hadj)
  · rintro ⟨s, hs, hcov⟩
    refine ⟨e '' sᶜ, (Set.ncard_image_of_injective _ e.injective).trans
      (FO.sizedGraph.ncard_compl_eq_iff.mpr hs), ?_⟩
    rw [e.injective.injOn.pairwise_image]
    intro x hx y hy hxy hadj
    rcases hcov x y hxy ((relMap_complementSize_adj M (e x) (e y)).mp hadj) with hxs | hys
    · exact hx hxs
    · exact hy hys

end ComplementSizeProofs

/-- **`Ordered.IndependentSet` quantifier-free projection reduces to `Ordered.VertexCover`.** -/
theorem independentSet_qfProjectionReduces_VertexCover :
    QFProjectionReduces IndependentSet VertexCover :=
  QFProjectionReduces.of_qfProjection isQFProjection_complementSizeInterpretation (by decide)
    fun M => (mem_VertexCover_complementSizeInterpretation M).symm

/-- **`Ordered.VertexCover` quantifier-free projection reduces to `Ordered.IndependentSet`.** -/
theorem vertexCover_qfProjectionReduces_IndependentSet :
    QFProjectionReduces VertexCover IndependentSet :=
  QFProjectionReduces.of_qfProjection isQFProjection_complementSizeInterpretation (by decide)
    fun M => (mem_IndependentSet_complementSizeInterpretation M).symm

/-- **`Ordered.Clique` quantifier-free projection reduces to `Ordered.VertexCover`.** -/
theorem clique_qfProjectionReduces_VertexCover :
    QFProjectionReduces Clique VertexCover :=
  clique_qfProjectionReduces_IndependentSet.trans independentSet_qfProjectionReduces_VertexCover

/-- **`Ordered.VertexCover` quantifier-free projection reduces to `Ordered.Clique`.** -/
theorem vertexCover_qfProjectionReduces_Clique :
    QFProjectionReduces VertexCover Clique :=
  vertexCover_qfProjectionReduces_IndependentSet.trans independentSet_qfProjectionReduces_Clique

end Cslib.Logic.FO.Ordered
