/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Approximation.MaxExactThreeSAT
public import Complexity.Computability.Complexity.Problems.Clique
public import Complexity.Computability.Complexity.Problems.VertexCover

/-!
# Independent Set, Clique and Vertex Cover are NP-hard to approximate

The values of a graph (`Cslib.Complexity.Graph`, read on its declared vertices) are its
independence number `Graph.indepNum`, its clique number `Graph.cliqueNum` and its vertex cover
number `Graph.vertexCoverNum`, the extreme targets of the decision problems `IndependentSet`,
`Clique` and `VertexCover`. The gap problems ask, for an instance `(G, k)`:

* `GapIndependentSet s`: is `indepNum G ≥ k`, or `indepNum G ≤ s * k`?
* `GapClique s`: is `cliqueNum G ≥ k`, or `cliqueNum G ≤ s * k`?
* `GapVertexCover r`: is `vertexCoverNum G ≤ k`, or `vertexCoverNum G ≥ r * k`?

The yes-instances of the first two are exactly `IndependentSet` and `Clique`.

The reductions use Karp's graph of a formula (`Cslib.Complexity.SAT.toIndependentSet`: a vertex
for each occurrence of a literal, edges inside clauses and between complementary occurrences), not
the graph of Feige, Goldwasser, Lovász, Safra and Szegedy built from a PCP verifier
[FeigeGoldwasserLovaszSafraSzegedy1996]. An independent set of Karp's graph picks consistent
literals in distinct clauses, so it has at most as many vertices as some assignment satisfies
clauses (`Cslib.Complexity.SAT.exists_card_add_countUnsat_le`). Hence the gap of MAX-3SAT
(`Cslib.Complexity.GapThreeSAT`) [Arora, Lund, Motwani, Sudan and
Szegedy][AroraLundMotwaniSudanSzegedy1998] transfers to independent sets with the same soundness,
and to cliques of the complement graph (`Cslib.Complexity.Graph.compl`) [Arora and Barak,
Chapter 11][AroraBarak09].

A vertex cover is the complement of an independent set, so `vertexCoverNum G = n - indepNum G` for
the number `n` of distinct declared vertices (`Graph.vertexCoverNum_eq_card_sub_indepNum`). For a
formula with `m` clauses of exactly three, not necessarily distinct, literals
(`Cslib.Complexity.GapExactThreeSAT`), Karp's graph has `n = 3 m` vertices, a satisfiable formula
has a cover of `2 m` vertices, and if every assignment satisfies at most `s * m` clauses every
cover has at least `(3 - s) * m = (1 + (1 - s) / 2) * 2 m` vertices [Arora and Barak, Chapter
11][AroraBarak09].

From the gap `1 - 1 / (3 * 2 ^ 77)` of MAX-3SAT (`Cslib.Complexity.GapThreeSAT_npHard`), it is
NP-hard to approximate the independence number and the clique number within `1 - 1 / (3 * 2 ^ 77)`
and the vertex cover number within `1 + 1 / (3 * 2 ^ 78)`. The constants are far from the best
known; amplification to every constant (and beyond) for Independent Set and Clique, as in Feige,
Goldwasser, Lovász, Safra and Szegedy, is not proved here.

## Main definitions

* `Cslib.Complexity.GapIndependentSet`, `Cslib.Complexity.GapClique`,
  `Cslib.Complexity.GapVertexCover`: the gap problems.

## Main results

* `Cslib.Complexity.SAT.card_toFinset_vertices_toIndependentSet`: Karp's graph of a formula with
  clauses of three literals has three vertices per clause.
* `Cslib.Complexity.SAT.indepNum_toIndependentSet_le`: the independence number of Karp's graph is
  at most `(1 - unsatVal φ) * m`.
* `Cslib.Complexity.yes_GapIndependentSet`, `Cslib.Complexity.yes_GapClique`: the yes-instances.
* `Cslib.Complexity.polyTimeReducible_GapThreeSAT_GapIndependentSet`,
  `Cslib.Complexity.polyTimeReducible_GapIndependentSet_GapClique`,
  `Cslib.Complexity.polyTimeReducible_GapExactThreeSAT_GapVertexCover`: the gap-preserving
  reductions.
* `Cslib.Complexity.GapIndependentSet_npHard`, `Cslib.Complexity.GapClique_npHard`,
  `Cslib.Complexity.GapVertexCover_npHard`: constant-factor inapproximability.
* `Cslib.Complexity.GapIndependentSet_notMem_PromiseP`,
  `Cslib.Complexity.GapClique_notMem_PromiseP`,
  `Cslib.Complexity.GapVertexCover_notMem_PromiseP`: unless `P = NP`, no polynomial-time algorithm
  separates the gap problems.

## References

* [S. Arora, C. Lund, R. Motwani, M. Sudan, M. Szegedy, *Proof verification and the hardness of
  approximation problems*][AroraLundMotwaniSudanSzegedy1998]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 11][AroraBarak09]
* [U. Feige, S. Goldwasser, L. Lovász, S. Safra, M. Szegedy, *Interactive proofs and the hardness
  of approximating cliques*][FeigeGoldwasserLovaszSafraSzegedy1996]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Karp's graph of a formula -/

namespace SAT

/-- Every occurrence of a formula whose clauses have exactly three literals is a vertex of
Karp's graph, and there are `3 m` of them for `m` clauses. -/
theorem card_toFinset_vertices_toIndependentSet {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3) :
    (toIndependentSet φ).1.1.toFinset.card = 3 * φ.length := by
  have hset : (toIndependentSet φ).1.1.toFinset =
      (Finset.range φ.length ×ˢ Finset.range 3).image fun p => Nat.pair p.1 p.2 := by
    ext v
    rw [List.mem_toFinset, Finset.mem_image]
    simp only [toIndependentSet, List.mem_map]
    constructor
    · rintro ⟨⟨i, j, l⟩, ho, rfl⟩
      obtain ⟨hi, hj, -⟩ := mem_occurrences.1 ho
      exact ⟨(i, j), Finset.mem_product.2 ⟨Finset.mem_range.2 hi,
        Finset.mem_range.2 ((h3 _ (List.getElem_mem hi)) ▸ hj)⟩, rfl⟩
    · rintro ⟨⟨i, j⟩, hij, rfl⟩
      obtain ⟨hi, hj⟩ := Finset.mem_product.1 hij
      rw [Finset.mem_range] at hi hj
      have hj' : j < φ[i].length := (h3 _ (List.getElem_mem hi)).symm ▸ hj
      exact ⟨(i, j, φ[i][j]), mem_occurrences.2 ⟨hi, hj', rfl⟩, rfl⟩
  rw [hset, Finset.card_image_of_injective _ fun p q h => Prod.ext (Nat.pair_eq_pair.1 h).1
    (Nat.pair_eq_pair.1 h).2, Finset.card_product, Finset.card_range, Finset.card_range,
    Nat.mul_comm]

private theorem toIndependentSet_snd (φ : CNF ℕ) : (toIndependentSet φ).2 = φ.length :=
  rfl

/-- **The independence number of Karp's graph is at most the largest number of clauses an
assignment satisfies**, which is at most `(1 - unsatVal φ) * m` for `m` clauses. -/
theorem indepNum_toIndependentSet_le (φ : CNF ℕ) :
    ((toIndependentSet φ).1.indepNum : ℝ) ≤ (1 - φ.unsatVal) * φ.length := by
  obtain ⟨S, hSV, hS⟩ :=
    mem_IndependentSet_iff.1 (Graph.indepNum_mem_IndependentSet (toIndependentSet φ).1)
  obtain ⟨σ, hσ⟩ := exists_card_add_countUnsat_le hSV hS.isIndepSet
  have hc : S.card = (toIndependentSet φ).1.indepNum := hS.card_eq
  rw [← hc]
  have hcast : ((S.card + φ.countUnsat σ : ℕ) : ℝ) ≤ φ.length := by exact_mod_cast hσ
  push_cast at hcast
  have hle : φ.unsatVal * φ.length ≤ φ.countUnsat σ := by
    rcases Nat.eq_zero_or_pos φ.length with h0 | h0
    · simp [h0]
    · have h0' : (0 : ℝ) < φ.length := by exact_mod_cast h0
      have := φ.unsatVal_le σ
      rwa [le_div_iff₀ h0'] at this
  linarith

end SAT

/-! ### Gap problems -/

/-- The gap problem of **maximum independent set** with soundness `s`: on an instance `(G, k)`,
the yes-instances have an independent set of `k` declared vertices, and the no-instances have no
independent set of more than `s * k` declared vertices. -/
noncomputable def GapIndependentSet (s : ℝ) : PromiseProblem (Graph × ℕ) :=
  PromiseProblem.gapMax (fun x => x.1.indepNum) (fun x => x.2) (fun x => s * x.2)

/-- The gap problem of **maximum clique** with soundness `s`: on an instance `(G, k)`, the
yes-instances have a clique of `k` declared vertices, and the no-instances have no clique of more
than `s * k` declared vertices. -/
noncomputable def GapClique (s : ℝ) : PromiseProblem (Graph × ℕ) :=
  PromiseProblem.gapMax (fun x => x.1.cliqueNum) (fun x => x.2) (fun x => s * x.2)

/-- The gap problem of **minimum vertex cover** with ratio `r`: on an instance `(G, k)`, the
yes-instances have a vertex cover of at most `k` declared vertices, and the no-instances have no
vertex cover of fewer than `r * k` declared vertices. -/
noncomputable def GapVertexCover (r : ℝ) : PromiseProblem (Graph × ℕ) :=
  PromiseProblem.gapMin (fun x => x.1.vertexCoverNum) (fun x => x.2) (fun x => r * x.2)

variable {s r : ℝ}

/-- The yes-instances of `GapIndependentSet` are the members of `IndependentSet`. -/
theorem yes_GapIndependentSet : (GapIndependentSet s).yes = IndependentSet := by
  ext ⟨G, k⟩
  simp only [GapIndependentSet, PromiseProblem.mem_yes_gapMax, Nat.cast_le, Graph.le_indepNum_iff]

/-- The yes-instances of `GapClique` are the members of `Clique`. -/
theorem yes_GapClique : (GapClique s).yes = Clique := by
  ext ⟨G, k⟩
  simp only [GapClique, PromiseProblem.mem_yes_gapMax, Nat.cast_le, Graph.le_cliqueNum_iff]

/-! ### Reductions -/

/-- **MAX-3SAT reduces to maximum independent set with the same gap**, by Karp's graph: a
satisfiable formula has an independent set with a vertex in each clause, and an independent set
gives an assignment satisfying as many clauses. -/
theorem polyTimeReducible_GapThreeSAT_GapIndependentSet (hs : s < 1) :
    PromiseProblem.PolyTimeReducible encCNF (encPair encGraph encNat) (GapThreeSAT s)
      (GapIndependentSet s) := by
  refine ⟨SAT.toIndependentSet, SAT.computableInPolyTime_toIndependentSet,
    fun φ hφ => ?_, fun φ hφ => ?_⟩
  · rw [yes_GapThreeSAT] at hφ
    rw [yes_GapIndependentSet]
    exact (SAT.toIndependentSet_mem_iff φ).2 hφ.2
  · obtain ⟨-, hval⟩ := (mem_no_GapThreeSAT hs).1 hφ
    have hm : (0 : ℝ) < φ.length := by
      exact_mod_cast CNF.length_pos_of_unsatVal_pos (by linarith)
    have hα := SAT.indepNum_toIndependentSet_le φ
    refine (PromiseProblem.mem_no_gapMax_of_lt ?_).2 ?_
    · change s * (φ.length : ℝ) < φ.length
      nlinarith
    · change ((SAT.toIndependentSet φ).1.indepNum : ℝ) ≤ s * φ.length
      nlinarith

/-- **Maximum independent set reduces to maximum clique with the same gap**, by complementing the
graph on its declared vertices. -/
theorem polyTimeReducible_GapIndependentSet_GapClique :
    PromiseProblem.PolyTimeReducible (encPair encGraph encNat) (encPair encGraph encNat)
      (GapIndependentSet s) (GapClique s) :=
  ⟨fun x => (x.1.compl, x.2), by fun_prop,
    fun x hx => by simpa [GapIndependentSet, GapClique, Graph.cliqueNum_compl] using hx,
    fun x hx => by simpa [GapIndependentSet, GapClique, Graph.cliqueNum_compl] using hx⟩

/-- **MAX-E3SAT reduces to minimum vertex cover**: Karp's graph of a formula with `m` clauses of
three, not necessarily distinct, literals has `3 m` vertices, so the target `m` of an independent
set becomes the target `2 m` of a vertex cover (`IndependentSet.toVertexCover`), and soundness `s`
for MAX-E3SAT becomes the ratio `1 + (1 - s) / 2` for vertex covers. -/
theorem polyTimeReducible_GapExactThreeSAT_GapVertexCover (hs : s < 1) :
    PromiseProblem.PolyTimeReducible encCNF (encPair encGraph encNat) (GapExactThreeSAT s)
      (GapVertexCover (1 + (1 - s) / 2)) := by
  have hred (φ : CNF ℕ) (h3 : ∀ c ∈ φ, c.length = 3) :
      IndependentSet.toVertexCover (SAT.toIndependentSet φ) =
        ((SAT.toIndependentSet φ).1, 2 * φ.length) := by
    rw [IndependentSet.toVertexCover, SAT.card_toFinset_vertices_toIndependentSet h3,
      SAT.toIndependentSet_snd, ite_eq_left (show φ.length ≤ 3 * φ.length by omega)]
    congr 1
    omega
  have hτ (φ : CNF ℕ) (h3 : ∀ c ∈ φ, c.length = 3) :
      ((SAT.toIndependentSet φ).1.vertexCoverNum : ℝ) =
        3 * φ.length - (SAT.toIndependentSet φ).1.indepNum := by
    have hle := Graph.indepNum_le_card (SAT.toIndependentSet φ).1
    rw [SAT.card_toFinset_vertices_toIndependentSet h3] at hle
    rw [Graph.vertexCoverNum_eq_card_sub_indepNum, SAT.card_toFinset_vertices_toIndependentSet h3,
      Nat.cast_sub hle]
    push_cast
    ring
  refine ⟨fun φ => IndependentSet.toVertexCover (SAT.toIndependentSet φ),
    IndependentSet.computableInPolyTime_toVertexCover.comp
      SAT.computableInPolyTime_toIndependentSet, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · rw [yes_GapExactThreeSAT] at hφ
    obtain ⟨h3, hsat⟩ := hφ
    have hα : (φ.length : ℝ) ≤ (SAT.toIndependentSet φ).1.indepNum := by
      exact_mod_cast Graph.le_indepNum_iff.2 ((SAT.toIndependentSet_mem_iff φ).2 hsat)
    simp only [GapVertexCover, PromiseProblem.mem_yes_gapMin, hred φ h3, hτ φ h3]
    push_cast
    linarith
  · obtain ⟨h3, hval⟩ := (mem_no_GapExactThreeSAT hs).1 hφ
    have hm : (0 : ℝ) < φ.length := by
      exact_mod_cast CNF.length_pos_of_unsatVal_pos (by linarith)
    have hα := SAT.indepNum_toIndependentSet_le φ
    simp only [GapVertexCover, PromiseProblem.mem_no_gapMin, hred φ h3, hτ φ h3]
    push_cast
    constructor <;> nlinarith

/-! ### Inapproximability -/

/-- **Maximum independent set is NP-hard to approximate** within `1 - 1 / (3 * 2 ^ 77)`: given a
graph and a target `k`, distinguishing graphs with an independent set of `k` vertices from graphs
without an independent set of more than `(1 - 1 / (3 * 2 ^ 77)) * k` vertices is NP-hard. The gap
comes from MAX-3SAT [AroraLundMotwaniSudanSzegedy1998] through Karp's graph. -/
theorem GapIndependentSet_npHard :
    PromiseProblem.NPHard (encPair encGraph encNat) (GapIndependentSet (1 - 1 / (3 * 2 ^ 77))) :=
  GapThreeSAT_npHard.trans (polyTimeReducible_GapThreeSAT_GapIndependentSet (by norm_num))

/-- **Maximum clique is NP-hard to approximate** within `1 - 1 / (3 * 2 ^ 77)`: given a graph and
a target `k`, distinguishing graphs with a clique of `k` vertices from graphs without a clique of
more than `(1 - 1 / (3 * 2 ^ 77)) * k` vertices is NP-hard. The gap of maximum independent set
transfers to the complement graph. -/
theorem GapClique_npHard :
    PromiseProblem.NPHard (encPair encGraph encNat) (GapClique (1 - 1 / (3 * 2 ^ 77))) :=
  GapIndependentSet_npHard.trans polyTimeReducible_GapIndependentSet_GapClique

/-- **Minimum vertex cover is NP-hard to approximate** within `1 + 1 / (3 * 2 ^ 78)`
[AroraLundMotwaniSudanSzegedy1998]: given a graph and a target `k`, distinguishing graphs with a
vertex cover of at most `k` vertices from graphs without a vertex cover of fewer than
`(1 + 1 / (3 * 2 ^ 78)) * k` vertices is NP-hard. -/
theorem GapVertexCover_npHard :
    PromiseProblem.NPHard (encPair encGraph encNat) (GapVertexCover (1 + 1 / (3 * 2 ^ 78))) := by
  have h := polyTimeReducible_GapExactThreeSAT_GapVertexCover
    (s := 1 - 1 / (3 * 2 ^ 77)) (by norm_num)
  rw [show (1 + (1 - (1 - 1 / (3 * 2 ^ 77))) / 2 : ℝ) = 1 + 1 / (3 * 2 ^ 78) by norm_num] at h
  intro _ enc A hA
  exact (GapExactThreeSAT_npHard enc A hA).trans h

/-- Unless `P = NP`, no polynomial-time algorithm distinguishes graphs with an independent set of
`k` vertices from graphs without one of more than `(1 - 1 / (3 * 2 ^ 77)) * k` vertices. -/
theorem GapIndependentSet_notMem_PromiseP {β : Type} {enc : β ↪ List Bool} (h : P enc ≠ NP enc) :
    GapIndependentSet (1 - 1 / (3 * 2 ^ 77)) ∉ PromiseP (encPair encGraph encNat) :=
  GapIndependentSet_npHard.notMem_PromiseP h

/-- Unless `P = NP`, no polynomial-time algorithm distinguishes graphs with a clique of `k`
vertices from graphs without one of more than `(1 - 1 / (3 * 2 ^ 77)) * k` vertices. -/
theorem GapClique_notMem_PromiseP {β : Type} {enc : β ↪ List Bool} (h : P enc ≠ NP enc) :
    GapClique (1 - 1 / (3 * 2 ^ 77)) ∉ PromiseP (encPair encGraph encNat) :=
  GapClique_npHard.notMem_PromiseP h

/-- Unless `P = NP`, no polynomial-time algorithm distinguishes graphs with a vertex cover of at
most `k` vertices from graphs without one of fewer than `(1 + 1 / (3 * 2 ^ 78)) * k` vertices. -/
theorem GapVertexCover_notMem_PromiseP {β : Type} {enc : β ↪ List Bool} (h : P enc ≠ NP enc) :
    GapVertexCover (1 + 1 / (3 * 2 ^ 78)) ∉ PromiseP (encPair encGraph encNat) :=
  GapVertexCover_npHard.notMem_PromiseP h

end Cslib.Complexity
