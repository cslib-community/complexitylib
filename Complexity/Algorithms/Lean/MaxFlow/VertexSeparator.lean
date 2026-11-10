/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.MaxFlow.EdmondsKarp
public import Complexity.Foundations.Combinatorics.SimpleGraph.Separator
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Minimum vertex separators by vertex splitting

Given a simple graph `G` on `Fin n` and three vertex sets `Z`, `A` and `B` (Boolean vectors),
`Cslib.Algorithms.Lean.MaxFlow.minSeparatorM` computes a set `X` of vertices outside `Z` of
minimum size such that `Z ∪ X` separates `A` from `B` (`SimpleGraph.IsSeparator`). The vertices of
`Z` are forbidden in `X`, but walks may not pass through them either: `X` is a minimum separator of
`A \ Z` from `B \ Z` in `G - Z`.

## Construction

The *split network* (`Cslib.Algorithms.Lean.MaxFlow.vertexSplitNetwork`) has a source, a sink,
and an in-copy and an out-copy of every vertex (`Cslib.Algorithms.Lean.MaxFlow.SplitNode`), with
capacities (`Cslib.Algorithms.Lean.MaxFlow.vertexSplitCap`)

* `n + 1` from the source to the in-copy of each vertex of `A`;
* `n + 1` from the out-copy of each vertex of `B` to the sink;
* `1` from the in-copy to the out-copy of each vertex outside `Z`;
* `n + 1` from the out-copy of `u` to the in-copy of `v` for each edge `G.Adj u v`.

This is the standard vertex-splitting construction. The library's Edmonds–Karp solver
(`Cslib.Algorithms.Lean.MaxFlow.edmondsKarpDenseM`) returns a minimum cut `S` of this network. The
separator is the set of vertices `v ∉ Z` whose in-copy lies in `S` and whose out-copy does not, and
`side v` records whether the out-copy of `v` lies in `S`.

*Correctness.* The cut that contains the in-copies of all vertices has capacity at most `n`. So a
minimum cut is crossed by no arc of capacity `n + 1`. Therefore `side` is constant along the edges
of `G - (Z ∪ X)`, true on `A \ (Z ∪ X)` and false on `B`, which certifies separation
(`Cslib.Algorithms.Lean.MaxFlow.minSeparatorM_isSeparator`). Conversely, a separator `Z ∪ Y` gives
a cut of capacity at most `|Y|`: it contains the vertices reached from `A` avoiding `Z ∪ Y`. The
crossing unit arcs of a cut bound the separator, so `|X| ≤ |Y|`
(`Cslib.Algorithms.Lean.MaxFlow.minSeparatorM_length_sep_le`).

## Cost model

`minSeparatorM` runs `edmondsKarpDenseM` on the split network, reindexed to `Fin (2n + 2)`. It
inherits that solver's cost model: unit-cost `Vector` access, `ℕ` arithmetic and capacity
evaluation. A capacity of the split network is evaluated in `O(1)`, from the index arithmetic of
`Cslib.Algorithms.Lean.MaxFlow.SplitNode.equivFin`, one adjacency test and one `Vector` lookup. The
cut is then read off in `4n + 2` further ticks (`Cslib.Algorithms.Lean.MaxFlow.minSeparatorCost`).
These are `O(n^5)` steps in total. That is a polynomial bound, not the `O(k(n + m))` of `k`
augmenting-path rounds.

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.SplitNode`, `Cslib.Algorithms.Lean.MaxFlow.vertexSplitCap`,
  `Cslib.Algorithms.Lean.MaxFlow.vertexSplitNetwork`: the split network.
* `Cslib.Algorithms.Lean.MaxFlow.SeparatorOutput`: a separator with its side labelling.
* `Cslib.Algorithms.Lean.MaxFlow.minSeparatorM`: the minimum vertex separator in `TimeM ℕ`.
* `Cslib.Algorithms.Lean.MaxFlow.minSeparatorCost`: its charged running time.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.minSeparatorM_isSeparator`: the output separates.
* `Cslib.Algorithms.Lean.MaxFlow.minSeparatorM_length_sep_le`: the output is a minimum separator.
* `Cslib.Algorithms.Lean.MaxFlow.minSeparatorM_nodup_sep`,
  `Cslib.Algorithms.Lean.MaxFlow.minSeparatorM_vget_eq_false_of_mem_sep`: the output is a list of
  distinct vertices outside `Z`.
* `Cslib.Algorithms.Lean.MaxFlow.minSeparatorM_side_eq_of_adj`,
  `Cslib.Algorithms.Lean.MaxFlow.minSeparatorM_side_eq_true`,
  `Cslib.Algorithms.Lean.MaxFlow.minSeparatorM_side_eq_false`: the side labelling certificate.
* `Cslib.Algorithms.Lean.MaxFlow.time_minSeparatorM_le`: the running time.

## References

* [J. Edmonds and R. M. Karp, *Theoretical Improvements in Algorithmic Efficiency for Network Flow
  Problems*][EdmondsKarp1972]
* [L. R. Ford, Jr. and D. R. Fulkerson, *Flows in Networks*][FordFulkerson1962]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

open SimpleGraph

/-- The nodes of the split network of a graph on `Fin n`. -/
inductive SplitNode (n : ℕ) where
  /-- The source. -/
  | src : SplitNode n
  /-- The sink. -/
  | snk : SplitNode n
  /-- The in-copy of a vertex. -/
  | inV : Fin n → SplitNode n
  /-- The out-copy of a vertex. -/
  | outV : Fin n → SplitNode n
  deriving DecidableEq, Fintype

namespace SplitNode

/-- The index of a split node: the source is `0`, the sink `1`, the in-copies `2, …, n + 1` and
the out-copies `n + 2, …, 2n + 1`. -/
def toFin {n : ℕ} : SplitNode n → Fin (n + n + 2)
  | src => ⟨0, by omega⟩
  | snk => ⟨1, by omega⟩
  | inV v => ⟨v.1 + 2, by have := v.2; omega⟩
  | outV v => ⟨v.1 + n + 2, by have := v.2; omega⟩

/-- The split node with a given index, inverse to `toFin`. -/
def ofFin {n : ℕ} (i : Fin (n + n + 2)) : SplitNode n :=
  if h0 : i.1 = 0 then src
  else if h1 : i.1 = 1 then snk
  else if h : i.1 < n + 2 then inV ⟨i.1 - 2, by omega⟩
  else outV ⟨i.1 - n - 2, by have := i.2; omega⟩

/-- Split nodes are indexed by `Fin (n + n + 2)`. -/
@[expose] def equivFin (n : ℕ) : SplitNode n ≃ Fin (n + n + 2) where
  toFun := toFin
  invFun := ofFin
  left_inv x := by
    cases x with
    | src => rfl
    | snk => rfl
    | inV v =>
      have := v.2
      simp only [toFin, ofFin, show v.1 + 2 ≠ 0 by omega, show v.1 + 2 ≠ 1 by omega,
        show v.1 + 2 < n + 2 by omega, ↓reduceDIte, inV.injEq]
      exact Fin.ext (by simp)
    | outV v =>
      have := v.2
      simp only [toFin, ofFin, show v.1 + n + 2 ≠ 0 by omega, show v.1 + n + 2 ≠ 1 by omega,
        show ¬(v.1 + n + 2 < n + 2) by omega, ↓reduceDIte, outV.injEq]
      exact Fin.ext (by dsimp only; omega)
  right_inv i := by
    have := i.2
    apply Fin.ext
    simp only [ofFin]
    split_ifs <;> simp only [toFin] <;> omega

end SplitNode

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Capacities of the split network: `n + 1` from the source to the in-copies of `A`, from the
out-copies of `B` to the sink and from the out-copy of `u` to the in-copy of `v` for each edge
`G.Adj u v`; `1` from the in-copy to the out-copy of each vertex outside `Z`; `0` otherwise. -/
@[expose] def vertexSplitCap (Z A B : Vector Bool n) : SplitNode n → SplitNode n → ℕ
  | .src, .inV v => if vget A v = true then n + 1 else 0
  | .outV u, .snk => if vget B u = true then n + 1 else 0
  | .inV u, .outV v => if u = v ∧ vget Z u = false then 1 else 0
  | .outV u, .inV v => if G.Adj u v then n + 1 else 0
  | _, _ => 0

/-- The split network of `G` for the vertex sets `Z`, `A` and `B` (`vertexSplitCap`). -/
@[expose] def vertexSplitNetwork (Z A B : Vector Bool n) : Network (SplitNode n) where
  cap := vertexSplitCap G Z A B
  s := .src
  t := .snk

/-- The output of `minSeparatorM`. -/
structure SeparatorOutput (n : ℕ) where
  /-- The separator, without repetitions. -/
  sep : List (Fin n)
  /-- The side labelling: `true` on the vertices reached from `A` in `G - (Z ∪ sep)`. -/
  side : Vector Bool n

/-- A minimum set `X` of vertices outside `Z` such that `Z ∪ X` separates `A` from `B`, by a
minimum cut of the split network (Edmonds–Karp on `Fin (2n + 2)`). Reading off `sep` and `side`
from the cut is charged `4n + 2` ticks: `2n + 2` to tabulate the cut over the split nodes and `2n`
to scan the vertices. -/
@[expose] def minSeparatorM (Z A B : Vector Bool n) : TimeM ℕ (SeparatorOutput n) := do
  let out ← edmondsKarpDenseM ((vertexSplitNetwork G Z A B).reindex (SplitNode.equivFin n))
  let S := Network.cutOfReindex (SplitNode.equivFin n) out.cut
  ✓[4 * n + 2] pure
    { sep := (List.finRange n).filter fun v =>
        !vget Z v && decide (SplitNode.inV v ∈ S) && !decide (SplitNode.outV v ∈ S)
      side := Vector.ofFn fun v => decide (SplitNode.outV v ∈ S) }

/-- The charged running time of `minSeparatorM` on `n` vertices: the `edmondsKarpDenseM` bound on
`2n + 2` nodes, plus `4n + 2`. -/
@[expose] def minSeparatorCost (n : ℕ) : ℕ :=
  ((n + n + 2) * (n + n + 2) * ((n + n + 2) / 2) + 2) *
      ((n + n + 2) * (n + n + 2) + 5 * (n + n + 2)) + (4 * n + 2)

/-! ### Correctness -/

section Correctness

variable {G} {Z A B : Vector Bool n}

/-- The minimum cut found by `minSeparatorM`, on split nodes. -/
private def minCut (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (Z A B : Vector Bool n) :
    Finset (SplitNode n) :=
  Network.cutOfReindex (SplitNode.equivFin n)
    (edmondsKarpDenseM ((vertexSplitNetwork G Z A B).reindex (SplitNode.equivFin n))).ret.cut

private theorem ret_sep : (minSeparatorM G Z A B).ret.sep = (List.finRange n).filter fun v =>
    !vget Z v && decide (SplitNode.inV v ∈ minCut G Z A B) &&
      !decide (SplitNode.outV v ∈ minCut G Z A B) := rfl

private theorem vget_ret_side (v : Fin n) :
    vget (minSeparatorM G Z A B).ret.side v = decide (SplitNode.outV v ∈ minCut G Z A B) := by
  simp only [minSeparatorM, TimeM.ret_bind, TimeM.ret_pure, vget, Vector.getElem_ofFn]
  rfl

private theorem mem_sep_iff {v : Fin n} : v ∈ (minSeparatorM G Z A B).ret.sep ↔
    vget Z v = false ∧ SplitNode.inV v ∈ minCut G Z A B ∧ SplitNode.outV v ∉ minCut G Z A B := by
  rw [ret_sep, List.mem_filter]
  simp only [List.mem_finRange, true_and, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, and_assoc]

private theorem reindex_s_ne_t :
    ((vertexSplitNetwork G Z A B).reindex (SplitNode.equivFin n)).s ≠
      ((vertexSplitNetwork G Z A B).reindex (SplitNode.equivFin n)).t :=
  (SplitNode.equivFin n).injective.ne (by simp [vertexSplitNetwork])

private theorem isMinCut_minCut : (vertexSplitNetwork G Z A B).IsMinCut (minCut G Z A B) := by
  set e := SplitNode.equivFin n
  set N := vertexSplitNetwork G Z A B
  obtain ⟨-, hmin, -⟩ := edmondsKarpDenseM_correct (N := N.reindex e) reindex_s_ne_t
  refine ⟨Network.isCut_cutOfReindex e hmin.1, fun T hT => ?_⟩
  have hT' : (N.reindex e).IsCut (T.map e.toEmbedding) := by
    simp only [Network.IsCut, Network.reindex, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    exact hT
  have h := hmin.2 _ hT'
  rw [← Network.cutCapacity_cutOfReindex, ← Network.cutCapacity_cutOfReindex] at h
  have hround : Network.cutOfReindex e (T.map e.toEmbedding) = T := by
    ext x
    simp [Network.cutOfReindex]
  rwa [hround] at h

/-- The positive capacities of the split network. -/
private theorem vertexSplitCap_ne_zero {x y : SplitNode n} (h : vertexSplitCap G Z A B x y ≠ 0) :
    (∃ v, x = .src ∧ y = .inV v ∧ vget A v = true) ∨
    (∃ u, x = .outV u ∧ y = .snk ∧ vget B u = true) ∨
    (∃ u, x = .inV u ∧ y = .outV u ∧ vget Z u = false) ∨
    (∃ u v, x = .outV u ∧ y = .inV v ∧ G.Adj u v) := by
  rcases x with _ | _ | u | u <;> rcases y with _ | _ | v | v <;> simp_all [vertexSplitCap]

/-- A single arc leaving a cut is bounded by the cut capacity. -/
private theorem cap_le_cutCapacity {N : Network (SplitNode n)} {S : Finset (SplitNode n)}
    {x y : SplitNode n} (hx : x ∈ S) (hy : y ∉ S) : N.cap x y ≤ N.cutCapacity S := by
  unfold Network.cutCapacity
  calc N.cap x y ≤ ∑ y' ∈ Finset.univ \ S, N.cap x y' :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simpa using hy)
    _ ≤ ∑ x' ∈ S, ∑ y' ∈ Finset.univ \ S, N.cap x' y' :=
        Finset.single_le_sum (f := fun x' => ∑ y' ∈ Finset.univ \ S, N.cap x' y')
          (fun _ _ => Nat.zero_le _) hx

/-- The unit arcs leaving a cut bound its capacity from below. -/
private theorem card_le_cutCapacity {S : Finset (SplitNode n)} {X : Finset (Fin n)}
    (hX : ∀ v ∈ X, vget Z v = false ∧ SplitNode.inV v ∈ S ∧ SplitNode.outV v ∉ S) :
    X.card ≤ (vertexSplitNetwork G Z A B).cutCapacity S := by
  unfold Network.cutCapacity
  rw [← Finset.sum_product' (f := fun x y => (vertexSplitNetwork G Z A B).cap x y)]
  calc X.card = ∑ v ∈ X, (vertexSplitNetwork G Z A B).cap (.inV v) (.outV v) := by
        rw [Finset.card_eq_sum_ones]
        refine Finset.sum_congr rfl fun v hv => ?_
        simp [vertexSplitNetwork, vertexSplitCap, (hX v hv).1]
    _ = ∑ p ∈ X.image (fun v => (SplitNode.inV v, SplitNode.outV v)),
          (vertexSplitNetwork G Z A B).cap p.1 p.2 :=
        (Finset.sum_image (f := fun p => (vertexSplitNetwork G Z A B).cap p.1 p.2)
          (g := fun v => (SplitNode.inV v, SplitNode.outV v))
          fun a _ b _ h => by simpa using h).symm
    _ ≤ ∑ p ∈ S ×ˢ (Finset.univ \ S), (vertexSplitNetwork G Z A B).cap p.1 p.2 := by
        refine Finset.sum_le_sum_of_subset fun p hp => ?_
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact (hX v hv).2

/-- Membership in the cut of a separator: the source, the in-copies of `A` and of the neighbours
of `R`, and the out-copies of `R`. -/
private def sepCutPred (G : SimpleGraph (Fin n)) (A : Vector Bool n) (R : Set (Fin n)) :
    SplitNode n → Prop
  | .src => True
  | .snk => False
  | .inV v => vget A v = true ∨ ∃ u ∈ R, G.Adj u v
  | .outV v => v ∈ R

/-- A separator `Z ∪ Y` gives a cut of capacity at most `|Y|`: the source, the in-copies of `A`
and of the neighbours of `R`, and the out-copies of `R`, for `R` the vertices reached from `A`
avoiding `Z ∪ Y`. -/
private theorem exists_isCut_cutCapacity_le {Y : Finset (Fin n)}
    (hY : G.IsSeparator {v | vget A v = true} {v | vget B v = true}
      ({v | vget Z v = true} ∪ ↑Y)) :
    ∃ T, (vertexSplitNetwork G Z A B).IsCut T ∧
      (vertexSplitNetwork G Z A B).cutCapacity T ≤ Y.card := by
  classical
  set R := G.reachAvoiding {v | vget A v = true} ({v | vget Z v = true} ∪ ↑Y) with hR
  set T := Finset.univ.filter (sepCutPred G A R)
  have hmem : ∀ x, x ∈ T ↔ sepCutPred G A R x := fun x => by simp [T]
  refine ⟨T, ⟨(hmem _).mpr trivial, fun h => (hmem _).mp h⟩, ?_⟩
  unfold Network.cutCapacity
  rw [← Finset.sum_product' (f := fun x y => (vertexSplitNetwork G Z A B).cap x y)]
  calc ∑ p ∈ T ×ˢ (Finset.univ \ T), (vertexSplitNetwork G Z A B).cap p.1 p.2
      ≤ ∑ p ∈ Y.image (fun u => (SplitNode.inV u, SplitNode.outV u)),
          (vertexSplitNetwork G Z A B).cap p.1 p.2 := by
        refine Finset.sum_le_sum_of_ne_zero fun p hp hne => ?_
        simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and, hmem] at hp
        obtain ⟨hx, hy⟩ := hp
        rcases vertexSplitCap_ne_zero hne with ⟨v, hpx, hpy, hA⟩ | ⟨u, hpx, hpy, hB⟩ |
            ⟨u, hpx, hpy, hZ⟩ | ⟨u, v, hpx, hpy, huv⟩
        · rw [hpy] at hy
          exact (hy (Or.inl hA)).elim
        · rw [hpx] at hx
          exact (isSeparator_iff_forall_notMem_reachAvoiding.mp hY u hB hx).elim
        · rw [hpx] at hx
          rw [hpy] at hy
          refine Finset.mem_image.mpr ⟨u, ?_, Prod.ext hpx.symm hpy.symm⟩
          by_contra huY
          have hu : u ∉ ({v | vget Z v = true} ∪ ↑Y : Set (Fin n)) := by
            simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe, not_or, hZ]
            exact ⟨Bool.false_ne_true, huY⟩
          rcases hx with hA | ⟨w, hw, hwu⟩
          · exact hy (mem_reachAvoiding_of_mem hA hu)
          · exact hy (mem_reachAvoiding_of_adj hw hwu hu)
        · rw [hpx] at hx
          rw [hpy] at hy
          exact (hy (Or.inr ⟨u, hx, huv⟩)).elim
    _ = ∑ u ∈ Y, (vertexSplitNetwork G Z A B).cap (.inV u) (.outV u) :=
        Finset.sum_image (f := fun p => (vertexSplitNetwork G Z A B).cap p.1 p.2)
          (g := fun v => (SplitNode.inV v, SplitNode.outV v))
          fun a _ b _ h => by simpa using h
    _ ≤ ∑ _u ∈ Y, 1 := Finset.sum_le_sum fun u _ => by
        simp only [vertexSplitNetwork, vertexSplitCap, true_and]
        split_ifs <;> omega
    _ = Y.card := (Finset.card_eq_sum_ones Y).symm

private theorem cutCapacity_minCut_le {Y : Finset (Fin n)}
    (hY : G.IsSeparator {v | vget A v = true} {v | vget B v = true}
      ({v | vget Z v = true} ∪ ↑Y)) :
    (vertexSplitNetwork G Z A B).cutCapacity (minCut G Z A B) ≤ Y.card := by
  obtain ⟨T, hT, hcap⟩ := exists_isCut_cutCapacity_le hY
  exact (isMinCut_minCut.2 T hT).trans hcap

private theorem cutCapacity_minCut_le_n :
    (vertexSplitNetwork G Z A B).cutCapacity (minCut G Z A B) ≤ n := by
  have h := cutCapacity_minCut_le (G := G) (Z := Z) (A := A) (B := B) (Y := Finset.univ)
    (isSeparator_of_subset_left fun a _ => Or.inr (Finset.mem_coe.mpr (Finset.mem_univ a)))
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- Arcs of capacity `n + 1` do not leave the minimum cut. -/
private theorem mem_minCut_of_cap {x y : SplitNode n} (hx : x ∈ minCut G Z A B)
    (hcap : vertexSplitCap G Z A B x y = n + 1) : y ∈ minCut G Z A B := by
  by_contra hy
  have h :=
    (cap_le_cutCapacity (N := vertexSplitNetwork G Z A B) hx hy).trans cutCapacity_minCut_le_n
  change vertexSplitCap G Z A B x y ≤ n at h
  omega

private theorem src_mem_minCut : SplitNode.src ∈ minCut G Z A B :=
  (isMinCut_minCut (G := G) (Z := Z) (A := A) (B := B)).1.1

private theorem snk_notMem_minCut : SplitNode.snk ∉ minCut G Z A B :=
  (isMinCut_minCut (G := G) (Z := Z) (A := A) (B := B)).1.2

variable (G Z A B)

/-- The separator has no repetitions. -/
theorem minSeparatorM_nodup_sep : (minSeparatorM G Z A B).ret.sep.Nodup :=
  (List.nodup_finRange n).filter _

variable {G Z A B}

/-- The separator avoids `Z`. -/
theorem minSeparatorM_vget_eq_false_of_mem_sep {v : Fin n}
    (hv : v ∈ (minSeparatorM G Z A B).ret.sep) : vget Z v = false :=
  (mem_sep_iff.mp hv).1

/-- The side labelling is constant along the edges of `G - (Z ∪ sep)`. -/
theorem minSeparatorM_side_eq_of_adj {u v : Fin n} (huv : G.Adj u v) (hu : vget Z u = false)
    (hv : vget Z v = false) (hus : u ∉ (minSeparatorM G Z A B).ret.sep)
    (hvs : v ∉ (minSeparatorM G Z A B).ret.sep) :
    vget (minSeparatorM G Z A B).ret.side u = vget (minSeparatorM G Z A B).ret.side v := by
  have step : ∀ {a b : Fin n}, G.Adj a b → vget Z b = false →
      b ∉ (minSeparatorM G Z A B).ret.sep →
      SplitNode.outV a ∈ minCut G Z A B → SplitNode.outV b ∈ minCut G Z A B := by
    intro a b hab hb hbs ha
    have hin : SplitNode.inV b ∈ minCut G Z A B :=
      mem_minCut_of_cap ha (by simp [vertexSplitCap, hab])
    by_contra hout
    exact hbs (mem_sep_iff.mpr ⟨hb, hin, hout⟩)
  rw [vget_ret_side, vget_ret_side]
  exact decide_eq_decide.mpr ⟨step huv hv hvs, step huv.symm hu hus⟩

/-- The side labelling is true on the vertices of `A` outside `Z ∪ sep`. -/
theorem minSeparatorM_side_eq_true {v : Fin n} (hA : vget A v = true) (hZ : vget Z v = false)
    (hvs : v ∉ (minSeparatorM G Z A B).ret.sep) :
    vget (minSeparatorM G Z A B).ret.side v = true := by
  rw [vget_ret_side, decide_eq_true_iff]
  have hin : SplitNode.inV v ∈ minCut G Z A B :=
    mem_minCut_of_cap src_mem_minCut (by simp [vertexSplitCap, hA])
  by_contra hout
  exact hvs (mem_sep_iff.mpr ⟨hZ, hin, hout⟩)

/-- The side labelling is false on `B`. -/
theorem minSeparatorM_side_eq_false {v : Fin n} (hB : vget B v = true) :
    vget (minSeparatorM G Z A B).ret.side v = false := by
  rw [vget_ret_side, decide_eq_false_iff_not]
  intro hout
  exact snk_notMem_minCut (mem_minCut_of_cap hout (by simp [vertexSplitCap, hB]))

/-- **Separation.** `Z ∪ sep` separates `A` from `B`. -/
theorem minSeparatorM_isSeparator :
    G.IsSeparator {v | vget A v = true} {v | vget B v = true}
      ({v | vget Z v = true} ∪ {v | v ∈ (minSeparatorM G Z A B).ret.sep}) := by
  refine isSeparator_of_forall_adj (fun v => vget (minSeparatorM G Z A B).ret.side v)
    (fun u v huv hu hv => ?_) (fun a ha ha' => ?_) fun b hb _ => minSeparatorM_side_eq_false hb
  · simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, Bool.not_eq_true] at hu hv
    exact minSeparatorM_side_eq_of_adj huv hu.1 hv.1 hu.2 hv.2
  · simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, Bool.not_eq_true] at ha'
    exact minSeparatorM_side_eq_true ha ha'.1 ha'.2

/-- **Minimality.** If `Z ∪ Y` separates `A` from `B`, the separator has at most `|Y|` vertices. -/
theorem minSeparatorM_length_sep_le {Y : Finset (Fin n)}
    (hY : G.IsSeparator {v | vget A v = true} {v | vget B v = true}
      ({v | vget Z v = true} ∪ ↑Y)) :
    (minSeparatorM G Z A B).ret.sep.length ≤ Y.card := by
  classical
  rw [← List.toFinset_card_of_nodup (minSeparatorM_nodup_sep G Z A B)]
  refine le_trans ?_ (cutCapacity_minCut_le hY)
  exact card_le_cutCapacity fun v hv => mem_sep_iff.mp (List.mem_toFinset.mp hv)

/-- **Running time.** `minSeparatorM` takes at most `minSeparatorCost n` ticks. -/
theorem time_minSeparatorM_le : (minSeparatorM G Z A B).time ≤ minSeparatorCost n := by
  have h := edmondsKarpDenseM_time_le ((vertexSplitNetwork G Z A B).reindex (SplitNode.equivFin n))
  simp only [minSeparatorM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, Nat.add_zero,
    minSeparatorCost]
  exact Nat.add_le_add_right h _

end Correctness

end Cslib.Algorithms.Lean.MaxFlow
