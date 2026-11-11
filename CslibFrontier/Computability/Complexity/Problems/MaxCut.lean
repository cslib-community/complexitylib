/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Partition
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Data.List.GetD

/-!
# Weighted maximum cut

`MaxCut` is the set of `MaxCutInstance` values `(edges, bound)` such that some set `S` of
vertices cuts edges of total weight at least `bound` [Karp1972]
[Garey and Johnson, Problem ND16][GareyJohnson1979]: an edge crosses the cut when exactly one of
its endpoints lies in `S`. Vertices, weights and the bound are natural numbers in binary
(`encNat`). The edge list is a weighted multigraph of `MaxCut.WeightedEdge`: parallel edges add
their weights and self-loops never cross a cut. Weights may be zero. `MaxCut.cutWeight` reads the
weight of a cut from an encodable edge list, without a vertex type; `Cslib.WeightedCut.cutWeight`
is the corresponding weight for a weight matrix on a `Fintype`.

Karp's reduction from `Partition` takes the complete graph on the positions `0, …, n - 1` of the
numbers `a`, with weight `a[i] * a[j]` on the edge between positions `i < j`
(`Partition.toMaxCut`). A cut putting numbers of sum `x` on one side has weight `x * (σ - x)`,
where `σ = a.sum` (`Partition.cutWeight_productEdges`), and `x * (σ - x) ≥ ⌈σ² / 4⌉` holds
exactly when `2 * x = σ`. The bound is `⌈σ² / 4⌉ = (σ * σ + 3) / 4`. All weights are products
of two input numbers, so the reduction is polynomial in the binary encoding.

## Main definitions

* `Cslib.Complexity.MaxCut.WeightedEdge`, `Cslib.Complexity.MaxCut.encWeightedEdge`: weighted
  edges and their binary encoding.
* `Cslib.Complexity.MaxCut.crosses`, `Cslib.Complexity.MaxCut.cutWeight`: edges crossing a cut
  and the weight of a cut.
* `Cslib.Complexity.MaxCutInstance`, `Cslib.Complexity.encMaxCut`, `Cslib.Complexity.MaxCut`:
  problem instances, binary encoding and decision set.
* `Cslib.Complexity.MaxCut.verifier`: a subset verifier selecting the side `S` of the cut among
  the endpoints.
* `Cslib.Complexity.Partition.productEdges`, `Cslib.Complexity.Partition.toMaxCut`: Karp's
  reduction.

## Main results

* `Cslib.Complexity.MaxCut.isVerifier`, `Cslib.Complexity.MaxCut.mem_NP`:
  `MaxCut ∈ NP encMaxCut`.
* `Cslib.Complexity.mem_Partition_iff_exists_side`: a partition is a set of positions holding
  half of the total sum.
* `Cslib.Complexity.Partition.cutWeight_productEdges`: a cut of the complete graph has the weight
  of the product of the two sides.
* `Cslib.Complexity.Partition.toMaxCut_mem_iff`: correctness of the reduction.
* `Cslib.Complexity.polyTimeReducible_Partition_MaxCut`, `Cslib.Complexity.MaxCut_npHard`,
  `Cslib.Complexity.MaxCut_npComplete`: `MaxCut` is `NP`-complete.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

namespace MaxCut

/-- A weighted edge between `u` and `v` of weight `weight`. -/
structure WeightedEdge where
  /-- The first endpoint. -/
  u : ℕ
  /-- The second endpoint. -/
  v : ℕ
  /-- The edge weight. -/
  weight : ℕ
  deriving DecidableEq, Repr

/-- Weighted edges are encoded as `(u, v, weight)` in binary. -/
enc_structure encWeightedEdge : WeightedEdge where
  u : encNat, v : encNat, weight : encNat

/-- Reading the first endpoint `u` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_weightedEdge_u :
    ComputableInPolyTime WeightedEdge.u encWeightedEdge encNat :=
  encWeightedEdge_u_deg.computableInPolyTime

/-- Reading the second endpoint `v` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_weightedEdge_v :
    ComputableInPolyTime WeightedEdge.v encWeightedEdge encNat :=
  encWeightedEdge_v_deg.computableInPolyTime

/-- Reading the weight `weight` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_weightedEdge_weight :
    ComputableInPolyTime WeightedEdge.weight encWeightedEdge encNat :=
  encWeightedEdge_weight_deg.computableInPolyTime

/-- Constructing a `WeightedEdge` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_weightedEdge_mk {γ : Type} {enc : γ ↪ List Bool}
    {u v w : γ → ℕ} (hu : ComputableInPolyTime u enc encNat)
    (hv : ComputableInPolyTime v enc encNat)
    (hw : ComputableInPolyTime w enc encNat) :
    ComputableInPolyTime (fun x => WeightedEdge.mk (u x) (v x) (w x)) enc encWeightedEdge :=
  encWeightedEdge_mk_deg.computableInPolyTime.comp (hu.prod (hv.prod hw))

/-- Whether the edge `e` crosses the cut whose sides are given by `side`. -/
@[expose] def crosses (side : ℕ → Bool) (e : WeightedEdge) : Bool := side e.u != side e.v

/-- The weight of the cut `side` in the weighted edges `E`: the total weight of the crossing
edges. Parallel edges add their weights; self-loops never cross. -/
@[expose] def cutWeight (E : List WeightedEdge) (side : ℕ → Bool) : ℕ :=
  ((E.filter fun e => crosses side e).map WeightedEdge.weight).sum

/-- The endpoints of the weighted edges `E`, in order and with repetitions. -/
@[expose] def endpoints (E : List WeightedEdge) : List ℕ := E.flatMap fun e => [e.u, e.v]

theorem cutWeight_append (E F : List WeightedEdge) (side : ℕ → Bool) :
    cutWeight (E ++ F) side = cutWeight E side + cutWeight F side := by
  simp only [cutWeight, List.filter_append, List.map_append, List.sum_append]

/-- The weight of a cut depends only on the sides of the endpoints. -/
theorem cutWeight_congr {E : List WeightedEdge} {side side' : ℕ → Bool}
    (h : ∀ v ∈ endpoints E, side v = side' v) : cutWeight E side = cutWeight E side' := by
  unfold cutWeight
  congr 2
  refine List.filter_congr fun e he => ?_
  have h₁ : e.u ∈ endpoints E := List.mem_flatMap.2 ⟨e, he, by simp⟩
  have h₂ : e.v ∈ endpoints E := List.mem_flatMap.2 ⟨e, he, by simp⟩
  simp only [crosses, h _ h₁, h _ h₂]

theorem length_endpoints (E : List WeightedEdge) : (endpoints E).length = 2 * E.length := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    simp only [endpoints, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

end MaxCut

/-- An instance of **weighted maximum cut**: a list of weighted edges and a target cut weight
bound. -/
structure MaxCutInstance where
  /-- The weighted edges of the multigraph. -/
  edges : List MaxCut.WeightedEdge
  /-- The target cut weight bound. -/
  bound : ℕ
  deriving DecidableEq, Repr

/-- Instances of `MaxCut` are encoded as the framed list of weighted edges followed by the bound,
all in binary. -/
enc_structure encMaxCut : MaxCutInstance where
  edges : (encList MaxCut.encWeightedEdge), bound : encNat

/-- **Weighted maximum cut** [Karp1972]: the weighted edges `edges` have a cut of weight at least
`bound`, a set `S` of vertices such that the edges with exactly one endpoint in `S` have total
weight at least `bound`. -/
@[expose] def MaxCut : Set MaxCutInstance :=
  {x | ∃ S : Finset ℕ, x.bound ≤ MaxCut.cutWeight x.edges (fun v => decide (v ∈ S))}

namespace MaxCut

/-- Reading the edge list `edges` of a `MaxCutInstance` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_edges :
    ComputableInPolyTime MaxCutInstance.edges encMaxCut (encList encWeightedEdge) :=
  encMaxCut_edges_deg.computableInPolyTime

/-- Reading the bound `bound` of a `MaxCutInstance` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_bound :
    ComputableInPolyTime MaxCutInstance.bound encMaxCut encNat :=
  encMaxCut_bound_deg.computableInPolyTime

/-- Constructing a `MaxCutInstance` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_mk {γ : Type} {enc : γ ↪ List Bool}
    {edges : γ → List WeightedEdge} {bound : γ → ℕ}
    (hedges : ComputableInPolyTime edges enc (encList encWeightedEdge))
    (hbound : ComputableInPolyTime bound enc encNat) :
    ComputableInPolyTime (fun x => MaxCutInstance.mk (edges x) (bound x)) enc encMaxCut :=
  encMaxCut_mk_deg.computableInPolyTime.comp (hedges.prod hbound)

/-- The check of a side `S` of a cut, given as a list: the cut has weight at least the bound. -/
@[expose] def check (x : MaxCutInstance) (S : List ℕ) : Bool :=
  decide (x.bound ≤ cutWeight x.edges fun v => decide (v ∈ S))

/-- The verifier for `MaxCut`, a subset verifier (`Cslib.Complexity.subsetVerifier`): select the
side of the cut among the endpoints and check the weight of the cut. -/
@[expose] def verifier : MaxCutInstance × List Bool → Bool :=
  subsetVerifier (fun x => endpoints x.edges) (Function.uncurry check)

/-- The check of a side of a cut is polynomial-time. -/
theorem computableInPolyTime_check :
    ComputableInPolyTime (Function.uncurry check) (encPair encMaxCut (encList encNat))
      encBool := by
  unfold Function.uncurry check cutWeight crosses
  fun_prop

/-- The `MaxCut` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encMaxCut encBits) encBool :=
  computableInPolyTime_subsetVerifier (encγ := encNat)
    (by unfold endpoints; fun_prop) computableInPolyTime_check

/-- A side of a cut may be taken among the endpoints. -/
theorem mem_MaxCut_iff_endpoints {x : MaxCutInstance} :
    x ∈ MaxCut ↔ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ endpoints x.edges) ∧
      x.bound ≤ cutWeight x.edges (fun v => decide (v ∈ S)) := by
  classical
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S.filter (· ∈ endpoints x.edges), fun v hv => (Finset.mem_filter.1 hv).2, ?_⟩
    rwa [cutWeight_congr (side' := fun v => decide (v ∈ S)) fun v hv => by
      simp [Finset.mem_filter, hv]]
  · rintro ⟨S, -, hS⟩
    exact ⟨S, hS⟩

/-- `MaxCut.verifier` verifies `MaxCut` with certificates of twice the length of the encoded
instance. -/
theorem isVerifier : IsVerifier encMaxCut (2 * Polynomial.X) verifier MaxCut := by
  have hset : MaxCut = {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ endpoints x.edges) ∧
      x.bound ≤ cutWeight x.edges (fun v => decide (v ∈ S))} :=
    Set.ext fun _ => mem_MaxCut_iff_endpoints
  rw [hset]
  refine isVerifier_subsetVerifier (fun x => ?_) fun x l _ _ => ?_
  · rw [encMaxCut_apply]
    have : x.edges.length ≤ (encMaxCutFields (x.edges, x.bound)).length :=
      length_le_length_encPair encWeightedEdge encNat (x.edges, x.bound)
    simp only [length_endpoints, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  · simp only [Function.uncurry_apply_pair, check, decide_eq_true_eq, List.mem_toFinset]

/-- `MaxCut` belongs to `NP`. -/
theorem mem_NP : MaxCut ∈ NP encMaxCut :=
  ⟨2 * Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end MaxCut

/-- A partition is a set of positions holding half of the total sum. -/
theorem mem_Partition_iff_exists_side {a : List ℕ} :
    a ∈ Partition ↔ ∃ side : ℕ → Bool,
      2 * (((List.range a.length).filter side).map (a.getD · 0)).sum = a.sum := by
  have hmask (w : List Bool) : maskSelect a w =
      ((List.range a.length).filter fun i => w.getD i false).map (a.getD · 0) := by
    have hz : a.zipIdx = (List.range a.length).map fun i => (a.getD i 0, i) := by
      refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
      simp [List.getElem?_eq_getElem (List.length_zipIdx ▸ h₁ : i < a.length)]
    simp only [maskSelect, hz, List.filter_map, List.map_map, Function.comp_def]
  rw [mem_Partition_iff_sublist]
  constructor
  · rintro ⟨s, hs, hsum⟩
    obtain ⟨w, -, rfl⟩ := exists_maskSelect_eq hs
    exact ⟨fun i => w.getD i false, by rwa [← hmask]⟩
  · rintro ⟨side, hside⟩
    refine ⟨_, ?_, hside⟩
    conv_rhs => rw [← List.map_getD_range a 0]
    exact List.filter_sublist.map _

namespace Partition

/-- The weighted edges of the complete graph on the positions `0, …, n - 1` of the numbers `a`:
the edge between positions `i < j` has weight `a[i] * a[j]`. -/
@[expose] def productEdges (a : List ℕ) (n : ℕ) : List MaxCut.WeightedEdge :=
  (List.range n).flatMap fun j => (List.range j).map fun i => ⟨i, j, a.getD i 0 * a.getD j 0⟩

/-- **Karp's reduction from `Partition` to `MaxCut`** [Karp1972]: the complete graph on the
positions of the numbers `a`, weighted by products, with bound `⌈a.sum² / 4⌉`. -/
@[expose] def toMaxCut (a : List ℕ) : MaxCutInstance :=
  ⟨productEdges a a.length, (a.sum * a.sum + 3) / 4⟩

/-- A cut of the complete graph weighted by products has the weight of the product of the sums
of its two sides. -/
theorem cutWeight_productEdges (a : List ℕ) (side : ℕ → Bool) (n : ℕ) :
    MaxCut.cutWeight (productEdges a n) side =
      (((List.range n).filter side).map (a.getD · 0)).sum *
        (((List.range n).filter fun i => !side i).map (a.getD · 0)).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep : productEdges a (n + 1) = productEdges a n ++
        (List.range n).map fun i => ⟨i, n, a.getD i 0 * a.getD n 0⟩ := by
      simp only [productEdges, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
    rw [hstep, MaxCut.cutWeight_append, ih]
    simp only [MaxCut.cutWeight, MaxCut.crosses, List.filter_map, List.map_map,
      Function.comp_def, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil,
      List.map_append, List.sum_append]
    cases h : side n
    · simp only [Bool.not_false, Bool.bne_false, ite_true, Bool.false_eq_true, ite_false,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.sum_map_mul_right]
      ring
    · simp only [Bool.not_true, Bool.bne_true, ite_true, Bool.false_eq_true, ite_false,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.sum_map_mul_right]
      ring

/-- `A * B` reaches `⌈(A + B)² / 4⌉` only when `A = B`, since `(A + B)² = 4 * A * B + (A - B)²`. -/
private theorem ceil_quarter_sq_le_mul_iff (A B : ℕ) :
    ((A + B) * (A + B) + 3) / 4 ≤ A * B ↔ A = B := by
  constructor
  · intro h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      have hsq : (A + (A + d + 1)) * (A + (A + d + 1)) =
          4 * (A * (A + d + 1)) + (d + 1) * (d + 1) := by ring
      have hd : 1 ≤ (d + 1) * (d + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
      rw [hsq] at h
      omega
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      have hsq : (B + d + 1 + B) * (B + d + 1 + B) =
          4 * ((B + d + 1) * B) + (d + 1) * (d + 1) := by ring
      have hd : 1 ≤ (d + 1) * (d + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
      rw [hsq] at h
      omega
  · rintro rfl
    have hsq : (A + A) * (A + A) = 4 * (A * A) := by ring
    rw [hsq]
    omega

/-- **Correctness of the reduction to `MaxCut`.** -/
theorem toMaxCut_mem_iff (a : List ℕ) : toMaxCut a ∈ MaxCut ↔ a ∈ Partition := by
  classical
  have hsplit (side : ℕ → Bool) :
      (((List.range a.length).filter side).map (a.getD · 0)).sum +
        (((List.range a.length).filter fun i => !side i).map (a.getD · 0)).sum = a.sum := by
    conv_rhs => rw [← List.map_getD_range a 0]
    simpa using List.sum_map_filter_add_sum_map_filter_not (fun i => side i = true) (a.getD · 0)
      (List.range a.length)
  rw [mem_Partition_iff_exists_side]
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨fun v => decide (v ∈ S), ?_⟩
    simp only [toMaxCut, cutWeight_productEdges] at hS
    rw [← hsplit fun v => decide (v ∈ S), ceil_quarter_sq_le_mul_iff] at hS
    have := hsplit fun v => decide (v ∈ S)
    omega
  · rintro ⟨side, hside⟩
    set S := ((List.range a.length).filter side).toFinset with hS
    refine ⟨S, ?_⟩
    have hcongr (p q : ℕ → Bool) (hp : ∀ i < a.length, p i = q i) :
        (List.range a.length).filter p = (List.range a.length).filter q :=
      List.filter_congr fun i hi => hp i (List.mem_range.1 hi)
    have h₁ : (List.range a.length).filter (fun v => decide (v ∈ S)) =
        (List.range a.length).filter side :=
      hcongr _ _ fun i hi => by simp [hS, hi]
    have h₂ : (List.range a.length).filter (fun v => !decide (v ∈ S)) =
        (List.range a.length).filter (fun v => !side v) :=
      hcongr _ _ fun i hi => by simp [hS, hi]
    simp only [toMaxCut, cutWeight_productEdges]
    rw [h₁, h₂, ← hsplit side, ceil_quarter_sq_le_mul_iff]
    have := hsplit side
    omega

/-- The reduction `toMaxCut` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toMaxCut :
    ComputableInPolyTime toMaxCut (encList encNat) encMaxCut := by
  unfold toMaxCut productEdges
  fun_prop

end Partition

/-- `Partition` reduces to `MaxCut` in polynomial time. -/
theorem polyTimeReducible_Partition_MaxCut :
    PolyTimeReducible (encList encNat) encMaxCut Partition MaxCut :=
  ⟨Partition.toMaxCut, Partition.computableInPolyTime_toMaxCut,
    fun a => (Partition.toMaxCut_mem_iff a).symm⟩

/-- `MaxCut` is `NP`-hard. -/
theorem MaxCut_npHard : NPHard encMaxCut MaxCut :=
  Partition_npHard.trans polyTimeReducible_Partition_MaxCut

/-- **Weighted maximum cut is NP-complete**, with the weights in binary [Karp1972]. -/
theorem MaxCut_npComplete : NPComplete encMaxCut MaxCut :=
  ⟨MaxCut.mem_NP, MaxCut_npHard⟩

end Cslib.Complexity
