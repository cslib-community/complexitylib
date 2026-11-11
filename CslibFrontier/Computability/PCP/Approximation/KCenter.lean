/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.KCenter.DominatingSet
public import CslibFrontier.Computability.Complexity.Problems.DominatingSet
public import CslibFrontier.Computability.Complexity.Problems.TSP.Approximation
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.GetD

/-!
# Metric k-center is NP-hard to approximate within a factor below 2

A polynomial-time algorithm for metric k-center whose radius is always within a factor `ρ < 2` of
the optimum decides the NP-complete dominating set problem, so it gives `P = NP`
([WilliamsonShmoys2011], Theorem 2.4, attributed there to [HsuNemhauser1979]). A graph `G` becomes
the k-center instance `domMatrix G` on its distinct declared vertices, at distance `0` from
themselves, `1` from adjacent vertices and `2` from the other vertices. When `G` has a dominating
set of at most `k` vertices the optimal radius is `1`, and a radius below `2 · 1` is a radius of
`1`, so the centers that the algorithm chooses dominate `G`; this is the gap
`Cslib.Algorithms.Lean.KCenter.isDominatingSet_of_radius_le_mul`. The decider checks whether they
do. Gonzalez's algorithm (`CslibFrontier.Algorithms.Lean.KCenter.Gonzalez`) meets the hypotheses
with `ρ = 2` apart from running time, which is not certified there, so the factor `2` is the
threshold.

## Model

An instance is a matrix `D` of natural distances, given as a list of rows, and a number `k` of
centers, both in binary: `KCenter.encKCenter` pairs the matrix encoding `KCenter.encDistMatrix`
(a framed list of framed lists of binary entries) with `encNat`. The points are the row
indices. The metric
instances (`KCenter.IsInstance`) are the square matrices with zero diagonal, symmetric and
satisfying the triangle inequality: the model of Section 2.2 of [WilliamsonShmoys2011], with
natural distances. The algorithm `A` returns a list of point indices; `KCenter.centers D l` is
the set of points named by `l`, so out-of-range indices and repetitions are ignored.

The hypotheses on `A` are required only on metric instances with `1 ≤ k ≤ D.length`, the
instances of Section 2.2, where `k` centers are chosen among the points:

* it chooses at most `k` centers (implied by `(A (D, k)).length ≤ k`, see
  `KCenter.card_centers_le`); with `k ≤ D.length` points, adding centers does not increase the
  radius, so this matches the `k` centers of the source;
* its radius is at most `ρ * r` for every bound `r` on the optimal radius, with distances in `ℝ`.
  With `k ≥ 1` the optimum is finite, so this is radius `≤ ρ · OPT`, stated as in
  `Cslib.Algorithms.Lean.KCenter.isDominatingSet_of_radius_le_mul` without multiplication in
  `WithTop ℝ`.

Natural distances and these restrictions only weaken the hypotheses, so the theorem implies the
corresponding statement for algorithms on instances with real distances and any `k`.

NP-hardness of dominating set on the library's encoded graphs is
`Cslib.Complexity.DominatingSet_npComplete`, through a reduction from vertex cover; Williamson and
Shmoys take it from the literature.

## Main definitions

* `Cslib.Complexity.KCenter.IsInstance`: metric k-center instances.
* `Cslib.Complexity.KCenter.centers`: the centers named by a list of indices.
* `Cslib.Complexity.KCenter.domMatrix`: the `{0, 1, 2}` distance matrix of a graph.
* `Cslib.Complexity.KCenter.decideDominatingSet`: the decider built from a k-center algorithm.

## Main results

* `Cslib.Complexity.KCenter.isInstance_domMatrix`,
  `Cslib.Complexity.KCenter.computableInPolyTime_domMatrix`: the distance matrix of a graph is a
  metric instance, computable in polynomial time.
* `Cslib.Complexity.KCenter.decideDominatingSet_iff`: the decider decides `DominatingSet`.
* `Cslib.Complexity.KCenter.computableInPolyTime_decideDominatingSet`: it is polynomial-time when
  the algorithm is.
* `Cslib.Complexity.P_eq_NP_of_kCenter_approx`: **Theorem 2.4**: a polynomial-time
  `ρ`-approximation algorithm for metric k-center with `ρ < 2` gives `P = NP`.

## References

* [W.-L. Hsu and G. L. Nemhauser, *Easy and hard bottleneck location
  problems*][HsuNemhauser1979]
* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011], Section 2.2.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Algorithms.Lean.KCenter

namespace KCenter

/-- A distance matrix: a framed list of rows, each a framed list of binary natural entries. -/
abbrev encDistMatrix : List (List ℕ) ↪ List Bool := encList (encList encNat)

/-- A k-center instance: the distance matrix (`encDistMatrix`) paired with the binary number `k`
of centers. -/
abbrev encKCenter : List (List ℕ) × ℕ ↪ List Bool := encPair encDistMatrix encNat

/-- A **metric k-center instance**: a square matrix of natural distances, with rows indexed by the
points `0, …, D.length - 1`, zero on the diagonal, symmetric and satisfying the triangle
inequality ([WilliamsonShmoys2011], Section 2.2). -/
structure IsInstance (D : List (List ℕ)) : Prop where
  /-- Every row lists the distances to all the points. -/
  length_row : ∀ row ∈ D, row.length = D.length
  /-- Every point is at distance `0` from itself. -/
  dist_self : ∀ i < D.length, TSP.dist D i i = 0
  /-- The distances are symmetric and satisfy the triangle inequality. -/
  isMetric : TSP.IsMetric D

/-- The centers chosen by a list `l` of indices: the points `i` of `D` with `i ∈ l`. Indices out of
range are ignored. -/
def centers (D : List (List ℕ)) (l : List ℕ) : Finset (Fin D.length) :=
  Finset.univ.filter fun i => (i : ℕ) ∈ l

@[simp]
theorem mem_centers {D : List (List ℕ)} {l : List ℕ} {i : Fin D.length} :
    i ∈ centers D l ↔ (i : ℕ) ∈ l := by
  simp only [centers, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A list of indices names at most as many centers as its length. -/
theorem card_centers_le (D : List (List ℕ)) (l : List ℕ) : (centers D l).card ≤ l.length := by
  refine (Finset.card_le_card_of_injOn (t := l.toFinset) (fun i : Fin D.length => (i : ℕ))
    (fun i hi => ?_) (fun _ _ _ _ h => Fin.val_injective h)).trans (List.toFinset_card_le l)
  rw [Finset.mem_coe, mem_centers] at hi
  exact Finset.mem_coe.2 (List.mem_toFinset.2 hi)

/-- The **`{0, 1, 2}` distance matrix of a graph** ([WilliamsonShmoys2011], Theorem 2.4): the
points are the distinct declared vertices, at distance `0` from themselves, `1` from adjacent
vertices and `2` from the other vertices. -/
@[expose] def domMatrix (G : Graph) : List (List ℕ) :=
  G.distinctVertices.map fun u =>
    G.distinctVertices.map fun v => if u = v then 0 else if G.adjBool u v then 1 else 2

/-- The vertices of `G` named by the indices that `A` returns on `(domMatrix G, k)`. -/
@[expose] def centerLabels (A : List (List ℕ) × ℕ → List ℕ) (G : Graph) (k : ℕ) : List ℕ :=
  ((A (domMatrix G, k)).filter fun i => decide (i < G.distinctVertices.length)).map
    fun i => G.distinctVertices.getD i 0

/-- The decider for `DominatingSet` built from a k-center algorithm `A`: accept `x` when
`x.bound` is at most the number of distinct vertices of `x.graph`, `x.bound > 0` unless `x.graph`
has no vertices, and the vertices named by the centers that `A` chooses on
`(domMatrix x.graph, x.bound)` dominate `x.graph`. -/
@[expose] def decideDominatingSet (A : List (List ℕ) × ℕ → List ℕ)
    (x : DominatingSetInstance) : Bool :=
  decide (x.bound ≤ x.graph.distinctVertices.length) &&
    (decide (x.graph.distinctVertices.length = 0) || decide (0 < x.bound)) &&
      DominatingSet.isDominating x.graph (centerLabels A x.graph x.bound)

@[simp]
theorem length_domMatrix (G : Graph) : (domMatrix G).length = G.distinctVertices.length :=
  List.length_map _

private theorem dist_domMatrix {G : Graph} {i j : ℕ} (hi : i < G.distinctVertices.length)
    (hj : j < G.distinctVertices.length) :
    TSP.dist (domMatrix G) i j =
      if i = j then 0 else if G.adjBool G.distinctVertices[i] G.distinctVertices[j] then 1
        else 2 := by
  simp only [domMatrix, TSP.dist, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some,
    G.nodup_distinctVertices.getElem_inj_iff]

/-- The graph on the points of `domMatrix G` whose adjacency is that of the corresponding vertices
of `G`. -/
private def indexGraph (G : Graph) : SimpleGraph (Fin (domMatrix G).length) :=
  G.toSimpleGraph.comap fun i => G.distinctVertices.getD i 0

private theorem finDist_domMatrix (G : Graph) [DecidableRel (indexGraph G).Adj]
    (i j : Fin (domMatrix G).length) :
    TSP.finDist (domMatrix G) i j = domDist (indexGraph G) i j := by
  have hi : (i : ℕ) < G.distinctVertices.length := by simpa using i.2
  have hj : (j : ℕ) < G.distinctVertices.length := by simpa using j.2
  rw [TSP.finDist, dist_domMatrix hi hj, domDist]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
  · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    have hadj : (indexGraph G).Adj i j ↔
        G.adjBool G.distinctVertices[(i : ℕ)] G.distinctVertices[(j : ℕ)] = true := by
      simp only [indexGraph, SimpleGraph.comap_adj, List.getD_eq_getElem _ _ hi,
        List.getD_eq_getElem _ _ hj, Graph.adjBool_eq_true_iff]
    rw [ite_eq_right hij, ite_eq_right hij']
    by_cases h : (indexGraph G).Adj i j
    · rw [ite_eq_left h, ite_eq_left (hadj.1 h)]
    · rw [ite_eq_right h, ite_eq_right (mt hadj.2 h)]

/-- The distance matrix of a graph is a metric k-center instance. -/
theorem isInstance_domMatrix (G : Graph) : IsInstance (domMatrix G) := by
  classical
  have hfin : ∀ i j : Fin (domMatrix G).length, TSP.dist (domMatrix G) i j =
      domDist (α := ℕ) (indexGraph G) i j := finDist_domMatrix G
  refine ⟨fun row hrow => ?_, fun i hi => ?_, ⟨fun i hi j hj => ?_, fun i hi j hj l hl => ?_⟩⟩
  · obtain ⟨u, -, rfl⟩ := List.mem_map.1 hrow
    simp only [List.length_map, length_domMatrix]
  · rw [hfin ⟨i, hi⟩ ⟨i, hi⟩, domDist, ite_eq_left rfl]
  · rw [hfin ⟨i, hi⟩ ⟨j, hj⟩, hfin ⟨j, hj⟩ ⟨i, hi⟩, domDist_symm]
  · rw [hfin ⟨i, hi⟩ ⟨l, hl⟩, hfin ⟨i, hi⟩ ⟨j, hj⟩, hfin ⟨j, hj⟩ ⟨l, hl⟩]
    exact domDist_triangle _ _ _

private theorem cast_finDist_domMatrix (G : Graph) [DecidableRel (indexGraph G).Adj] :
    (fun i j => (TSP.finDist (domMatrix G) i j : ℝ)) = domDist (indexGraph G) := by
  funext i j
  rw [finDist_domMatrix, domDist, domDist]
  split_ifs <;> simp

private theorem mem_centerLabels {A : List (List ℕ) × ℕ → List ℕ} {G : Graph} {k v : ℕ} :
    v ∈ centerLabels A G k ↔ ∃ i ∈ centers (domMatrix G) (A (domMatrix G, k)),
      G.distinctVertices.getD i 0 = v := by
  simp only [centerLabels, mem_centers, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨hi, hlt⟩, rfl⟩
    exact ⟨⟨i, by simpa using hlt⟩, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, ⟨hi, by simpa using i.2⟩, rfl⟩

/-- **The decider is correct** ([WilliamsonShmoys2011], Theorem 2.4): if, on metric instances
with `1 ≤ k ≤ D.length`, `A` returns at most `k` centers with a radius within a factor `ρ < 2` of
the optimum, then `decideDominatingSet A` decides `DominatingSet`. -/
theorem decideDominatingSet_iff {A : List (List ℕ) × ℕ → List ℕ} {ρ : ℝ} (hρ : ρ < 2)
    (hcard : ∀ D k, IsInstance D → 0 < k → k ≤ D.length → (centers D (A (D, k))).card ≤ k)
    (hratio : ∀ D k [NeZero D.length], IsInstance D → 0 < k → k ≤ D.length → ∀ r : ℝ,
      optRadius (fun i j => (TSP.finDist D i j : ℝ)) k ≤ r →
        radius (fun i j => (TSP.finDist D i j : ℝ)) (centers D (A (D, k))) ≤ ((ρ * r : ℝ) :
          WithTop ℝ))
    (x : DominatingSetInstance) : decideDominatingSet A x = true ↔ x ∈ DominatingSet := by
  obtain ⟨G, k⟩ := x
  classical
  rw [mem_DominatingSet_iff_exists_card_le, ← Graph.length_distinctVertices]
  simp only [decideDominatingSet, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    DominatingSet.isDominating_eq_true_iff]
  have hfs : (centerLabels A G k).toFinset = (centers (domMatrix G) (A (domMatrix G, k))).image
      fun i : Fin (domMatrix G).length => G.distinctVertices.getD i 0 := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_image, mem_centerLabels]
  constructor
  · rintro ⟨⟨hk, hpos⟩, hdom⟩
    refine ⟨hk, (centerLabels A G k).toFinset, fun v hv => ?_, fun v hv => ?_, ?_⟩
    · obtain ⟨i, -, rfl⟩ := mem_centerLabels.1 (List.mem_toFinset.1 hv)
      exact G.vertexEquiv_apply (Fin.cast (length_domMatrix G) i) ▸ (G.vertexEquiv _).2
    · simpa only [List.mem_toFinset] using hdom v hv
    · rw [hfs]
      refine Finset.card_image_le.trans ?_
      rcases hpos with h0 | h0
      · have : (centers (domMatrix G) (A (domMatrix G, k))) = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun i _ => ?_
          have := i.2
          simp only [length_domMatrix, h0] at this
          omega
        rw [this, Finset.card_empty]
        exact Nat.zero_le k
      · exact hcard _ _ (isInstance_domMatrix G) h0 (by simpa using hk)
  · rintro ⟨hk, S, hSV, hS, hSk⟩
    have hpos : G.distinctVertices.length = 0 ∨ 0 < k := by
      rcases Nat.eq_zero_or_pos G.distinctVertices.length with h | h
      · exact Or.inl h
      · right
        by_contra hk0
        have hk0 : k = 0 := by omega
        subst hk0
        have hS0 : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hSk)
        subst hS0
        obtain ⟨v, hv⟩ := List.exists_mem_of_length_pos h
        rcases hS v (Graph.mem_distinctVertices.1 hv) with h' | ⟨s, hs, -⟩
        · exact Finset.notMem_empty v h'
        · exact Finset.notMem_empty s hs
    refine ⟨⟨hk, hpos⟩, fun v hv => ?_⟩
    have hvL : v ∈ G.distinctVertices := Graph.mem_distinctVertices.2 hv
    have hn : 0 < G.distinctVertices.length := List.length_pos_of_mem hvL
    have hk0 : 0 < k := hpos.resolve_left (by omega)
    have : NeZero (domMatrix G).length := ⟨by simp only [length_domMatrix]; omega⟩
    let f : Fin (domMatrix G).length → ℕ := fun i => G.distinctVertices.getD i 0
    -- `f` is `Graph.vertexEquiv` after reindexing by `length_domMatrix`
    let e := (finCongr (length_domMatrix G)).trans G.vertexEquiv
    have hfe (i : Fin (domMatrix G).length) : f i = e i :=
      (G.vertexEquiv_apply (Fin.cast (length_domMatrix G) i)).symm
    have hfinj : Function.Injective f := fun i j h =>
      e.injective (Subtype.ext ((hfe i).symm.trans (h.trans (hfe j))))
    have hsurj : ∀ u ∈ G.distinctVertices, ∃ i : Fin (domMatrix G).length, f i = u := fun u hu =>
      let ⟨i, hi⟩ := e.surjective ⟨u, Graph.mem_distinctVertices.1 hu⟩
      ⟨i, (hfe i).trans (congrArg Subtype.val hi)⟩
    let T : Finset (Fin (domMatrix G).length) := Finset.univ.filter fun i => f i ∈ S
    have hT : T.card ≤ k := by
      refine le_trans ?_ hSk
      exact Finset.card_le_card_of_injOn f (fun i hi => by simpa [T] using hi)
        (hfinj.injOn)
    have hTdom : (indexGraph G).IsDominatingSet T := by
      refine SimpleGraph.isDominatingSet_iff.2 fun i => ?_
      have hfiV : f i ∈ G.1 := hfe i ▸ (e i).2
      rcases hS (f i) hfiV with h | ⟨s, hs, hadj⟩
      · exact Or.inl (by simpa [T] using h)
      · obtain ⟨j, rfl⟩ := hsurj s (Graph.mem_distinctVertices.2 (hSV s hs))
        exact Or.inr ⟨j, by simpa [T] using hs, hadj⟩
    have happrox := hratio (domMatrix G) k (isInstance_domMatrix G) hk0 (by simpa using hk)
    rw [cast_finDist_domMatrix G] at happrox
    have hC := isDominatingSet_of_radius_le_mul hρ happrox ⟨T, hT, hTdom⟩
    obtain ⟨i, rfl⟩ := hsurj v hvL
    rcases SimpleGraph.isDominatingSet_iff.1 hC i with h | ⟨j, hj, hadj⟩
    · exact Or.inl (mem_centerLabels.2 ⟨i, h, rfl⟩)
    · exact Or.inr ⟨f j, mem_centerLabels.2 ⟨j, hj, rfl⟩, hadj⟩

/-- The distance matrix of a graph is computable in polynomial time, with binary entries. -/
theorem computableInPolyTime_domMatrix :
    ComputableInPolyTime domMatrix encGraph encDistMatrix := by
  have hV : ComputableInPolyTime Graph.distinctVertices encGraph (encList encNat) :=
    Graph.computableInPolyTime_distinctVertices
  have hentry : ComputableInPolyTime
      (fun q : (Graph × ℕ) × ℕ => if q.1.2 = q.2 then 0 else if q.1.1.adjBool q.1.2 q.2 then 1
        else 2) (encPair (encPair encGraph encNat) encNat) encNat :=
    ite_decide (decide_eq' ((snd _ _).comp (fst _ _)) (snd _ _)) (const 0)
      ((Graph.computableInPolyTime_adjBool_comp ((fst _ _).comp (fst _ _))
        ((snd _ _).comp (fst _ _)) (snd _ _)).ite (const 1) (const 2))
  have hrow : ComputableInPolyTime
      (fun p : Graph × ℕ => p.1.distinctVertices.map fun v =>
        if p.2 = v then 0 else if p.1.adjBool p.2 v then 1 else 2)
      (encPair encGraph encNat) (encList encNat) :=
    mapWithInput (hV.comp (fst _ _)) hentry
  exact mapWithInput hV hrow

/-- The decider built from a polynomial-time k-center algorithm is polynomial-time. -/
theorem computableInPolyTime_decideDominatingSet {A : List (List ℕ) × ℕ → List ℕ}
    (hA : ComputableInPolyTime A encKCenter (encList encNat)) :
    ComputableInPolyTime (decideDominatingSet A) encDominatingSet encBool := by
  have hg : ComputableInPolyTime DominatingSetInstance.graph encDominatingSet encGraph := by
    fun_prop
  have hb : ComputableInPolyTime DominatingSetInstance.bound encDominatingSet encNat := by
    fun_prop
  have hV : ComputableInPolyTime (fun x : DominatingSetInstance => x.graph.distinctVertices)
      encDominatingSet (encList encNat) :=
    Graph.computableInPolyTime_distinctVertices.comp hg
  have hAx : ComputableInPolyTime (fun x : DominatingSetInstance => A (domMatrix x.graph, x.bound))
      encDominatingSet (encList encNat) :=
    hA.comp ((computableInPolyTime_domMatrix.comp hg).prod hb)
  have hlabels : ComputableInPolyTime (fun x : DominatingSetInstance =>
      centerLabels A x.graph x.bound) encDominatingSet (encList encNat) := by
    unfold centerLabels
    have hfilter : ComputableInPolyTime (fun x : DominatingSetInstance =>
        (A (domMatrix x.graph, x.bound)).filter fun i =>
          decide (i < x.graph.distinctVertices.length))
        encDominatingSet (encList encNat) :=
      filterWithInput hAx (binary_lt' (snd _ _)
        ((length_list_binary encNat).comp (hV.comp (fst _ _))))
    exact mapWithInput hfilter (listGetD_binary 0 (hV.comp (fst _ _)) (snd _ _))
  unfold decideDominatingSet
  exact bool_and' (bool_and' (binary_le' hb ((length_list_binary encNat).comp hV))
    (bool_or.comp (((length_list_binary encNat).comp hV |>.decide_eq' (const 0)).prod
      (binary_lt' (const 0) hb))))
    (DominatingSet.computableInPolyTime_isDominating.comp (hg.prod hlabels))

end KCenter

/-- **No `ρ`-approximation for metric k-center with `ρ < 2` unless `P = NP`**
([WilliamsonShmoys2011], Theorem 2.4; [HsuNemhauser1979]). Let `A` be a polynomial-time algorithm
that, on every metric instance `(D, k)` with `1 ≤ k ≤ D.length`, chooses at most `k` centers whose
radius is at most `ρ` times every bound on the optimal radius, with `ρ < 2`. Then `P = NP`.
Distances are natural numbers in binary; see the module docstring for why the restrictions only
strengthen the statement. -/
theorem P_eq_NP_of_kCenter_approx {A : List (List ℕ) × ℕ → List ℕ} {ρ : ℝ} (hρ : ρ < 2)
    (hA : ComputableInPolyTime A KCenter.encKCenter (encList encNat))
    (hcard : ∀ D k, KCenter.IsInstance D → 0 < k → k ≤ D.length →
      (KCenter.centers D (A (D, k))).card ≤ k)
    (hratio : ∀ D k [NeZero D.length], KCenter.IsInstance D → 0 < k → k ≤ D.length →
      ∀ r : ℝ,
      optRadius (fun i j => (TSP.finDist D i j : ℝ)) k ≤ r →
        radius (fun i j => (TSP.finDist D i j : ℝ)) (KCenter.centers D (A (D, k))) ≤
          ((ρ * r : ℝ) : WithTop ℝ))
    {α : Type} (enc : α ↪ List Bool) : P enc = NP enc :=
  DominatingSet_npComplete.P_eq_NP_of_mem_P
    ⟨_, KCenter.computableInPolyTime_decideDominatingSet hA,
      fun x => (KCenter.decideDominatingSet_iff hρ hcard hratio x).symm⟩ enc

end Cslib.Complexity
