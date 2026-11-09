/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Metric.lean`)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

/-!
# Balls that are paths

A map `φ : ℤ → V` is a *ball path* of radius `r` over the parameter interval `[lo, hi]`
(`SimpleGraph.IsBallPath G r lo hi φ`, with `-r ≤ lo ≤ 0 ≤ hi ≤ r`) when it is injective on
`[lo, hi]`, two of its points are adjacent exactly when their parameters are consecutive, and every
neighbour of a point with parameter strictly between `-r` and `r` is again a point of the path. The
closed ball `{x | G.edist (φ 0) x ≤ k}` of every radius `k ≤ r` is then the image of the parameters
of absolute value at most `k` (`SimpleGraph.IsBallPath.edist_le_iff`); for `k = r` it is the image
of `[lo, hi]`. So the radius-`r` ball around `φ 0` induces a path on `hi - lo + 1` vertices with
`φ 0` at position `-lo`.

The radius-`r` balls of the cycle graph `cycleGraph N` with `N ≥ 2r + 2` are ball paths over
`[-r, r]` (`SimpleGraph.exists_isBallPath_cycleGraph`). Around vertex `j` of the path graph
`pathGraph N`, the radius-`r` ball is a ball path over `[-min r j, min r (N - 1 - j)]`
(`SimpleGraph.exists_isBallPath_pathGraph`). The bound `N ≥ 2r + 2` is needed: in `cycleGraph 3`
the radius-`1` ball is the whole triangle, which is not a path. Distances in `pathGraph N` are
differences of indices (`SimpleGraph.edist_pathGraph`).

These descriptions are the cycle-graph distance computations behind Hanf-locality proofs that
connectivity, acyclicity and being a tree are not first-order definable, and the path-graph
distances behind Gaifman-locality proofs that transitive closure and reachability are not.

## Main definitions

* `SimpleGraph.IsBallPath`: a path parametrization of a ball.

## Main results

* `SimpleGraph.IsBallPath.edist_le_iff`: the balls of radius `k ≤ r` around the center.
* `SimpleGraph.IsBallPath.sumInl`, `SimpleGraph.IsBallPath.sumInr`: ball paths in a disjoint union.
* `SimpleGraph.exists_isBallPath_cycleGraph`: balls in cycle graphs.
* `SimpleGraph.exists_isBallPath_pathGraph`: balls in path graphs.
* `SimpleGraph.edist_pathGraph`: distances in path graphs.
-/

public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- `φ` parametrizes the radius-`r` ball around `φ 0` in `G` as a path over `[lo, hi]`: it is
injective there, adjacency is consecutiveness of parameters, and the neighbours of interior points
(parameter strictly between `-r` and `r`) stay on the path. -/
structure IsBallPath (G : SimpleGraph V) (r : ℕ) (lo hi : ℤ) (φ : ℤ → V) : Prop where
  /-- The left end is at most `r` steps from the center. -/
  neg_le_lo : -(r : ℤ) ≤ lo
  /-- The left end is not right of the center. -/
  lo_nonpos : lo ≤ 0
  /-- The right end is not left of the center. -/
  hi_nonneg : 0 ≤ hi
  /-- The right end is at most `r` steps from the center. -/
  hi_le : hi ≤ r
  /-- Distinct parameters give distinct vertices. -/
  injOn : Set.InjOn φ (Set.Icc lo hi)
  /-- Two points are adjacent exactly when their parameters are consecutive. -/
  adj_iff : ∀ ⦃s t⦄, s ∈ Set.Icc lo hi → t ∈ Set.Icc lo hi →
    (G.Adj (φ s) (φ t) ↔ s + 1 = t ∨ t + 1 = s)
  /-- Every neighbour of an interior point is a point of the path. -/
  exists_of_adj : ∀ ⦃s⦄, s ∈ Set.Icc lo hi → -(r : ℤ) < s → s < r → ∀ ⦃y⦄, G.Adj (φ s) y →
    ∃ t ∈ Set.Icc lo hi, y = φ t

namespace IsBallPath

variable {r : ℕ} {lo hi : ℤ} {φ : ℤ → V}

private theorem edist_le_of_nonneg (hφ : IsBallPath G r lo hi φ) :
    ∀ n : ℕ, (n : ℤ) ≤ hi → G.edist (φ 0) (φ n) ≤ n
  | 0, _ => by simp
  | n + 1, hn => by
    have ih := edist_le_of_nonneg hφ n (by omega)
    have hadj : G.Adj (φ n) (φ (n + 1 : ℕ)) :=
      (hφ.adj_iff ⟨by have := hφ.lo_nonpos; omega, by omega⟩
        ⟨by have := hφ.lo_nonpos; omega, hn⟩).2 (.inl (by push_cast; ring))
    calc G.edist (φ 0) (φ (n + 1 : ℕ)) ≤ G.edist (φ 0) (φ n) + G.edist (φ n) (φ (n + 1 : ℕ)) :=
          SimpleGraph.edist_triangle
      _ ≤ n + 1 := add_le_add ih (edist_eq_one_iff_adj.2 hadj).le
      _ = ((n + 1 : ℕ) : ℕ∞) := by push_cast; rfl

private theorem edist_le_of_nonpos (hφ : IsBallPath G r lo hi φ) :
    ∀ n : ℕ, lo ≤ -(n : ℤ) → G.edist (φ 0) (φ (-(n : ℤ))) ≤ n
  | 0, _ => by simp
  | n + 1, hn => by
    have ih := edist_le_of_nonpos hφ n (by omega)
    have hadj : G.Adj (φ (-(n : ℤ))) (φ (-((n + 1 : ℕ) : ℤ))) :=
      (hφ.adj_iff ⟨by omega, by have := hφ.hi_nonneg; omega⟩
        ⟨hn, by have := hφ.hi_nonneg; omega⟩).2 (.inr (by push_cast; ring))
    calc G.edist (φ 0) (φ (-((n + 1 : ℕ) : ℤ))) ≤
          G.edist (φ 0) (φ (-(n : ℤ))) + G.edist (φ (-(n : ℤ))) (φ (-((n + 1 : ℕ) : ℤ))) :=
          SimpleGraph.edist_triangle
      _ ≤ n + 1 := add_le_add ih (edist_eq_one_iff_adj.2 hadj).le
      _ = ((n + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-- The point of a ball path at parameter `s` is within distance `|s|` of the center. -/
theorem edist_le (hφ : IsBallPath G r lo hi φ) {s : ℤ} (hs : s ∈ Set.Icc lo hi) {k : ℕ}
    (hk : -(k : ℤ) ≤ s ∧ s ≤ k) : G.edist (φ 0) (φ s) ≤ k := by
  rcases le_total 0 s with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    exact (edist_le_of_nonneg hφ n hs.2).trans (by exact_mod_cast (by omega : n ≤ k))
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat h
    subst hn
    exact (edist_le_of_nonpos hφ n hs.1).trans (by exact_mod_cast (by omega : n ≤ k))

/-- The closed ball of radius `k ≤ r` around the center `φ 0` of a ball path is the image of the
parameters of absolute value at most `k`. -/
theorem edist_le_iff (hφ : IsBallPath G r lo hi φ) {k : ℕ} (hk : k ≤ r) {x : V} :
    G.edist (φ 0) x ≤ k ↔ ∃ s ∈ Set.Icc lo hi, (-(k : ℤ) ≤ s ∧ s ≤ k) ∧ x = φ s := by
  refine ⟨fun h => ?_, fun ⟨s, hs, hsk, hx⟩ => hx ▸ hφ.edist_le hs hsk⟩
  induction k generalizing x with
  | zero =>
    refine ⟨0, ⟨hφ.lo_nonpos, hφ.hi_nonneg⟩, by simp, ?_⟩
    have : G.edist (φ 0) x = 0 := nonpos_iff_eq_zero.1 (by exact_mod_cast h)
    exact (edist_eq_zero_iff.1 this).symm
  | succ k ih =>
    obtain ⟨d, hd⟩ : ∃ d : ℕ, G.edist (φ 0) x = d :=
      ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top _) h) |>.imp
        fun _ h => h.symm
    rcases Nat.lt_or_ge d (k + 1) with hdk | hdk
    · obtain ⟨s, hs, hsk, rfl⟩ := ih (by omega) (by rw [hd]; exact_mod_cast (by omega : d ≤ k))
      exact ⟨s, hs, ⟨by omega, by omega⟩, rfl⟩
    · have hd' : d = k + 1 := le_antisymm (by rw [hd] at h; exact_mod_cast h) hdk
      subst hd'
      obtain ⟨v, hvx, hv⟩ := exists_adj_edist_eq_of_edist_eq_add_one (by rw [hd]; push_cast; rfl)
      obtain ⟨s, hs, hsk, rfl⟩ := ih (by omega) hv.le
      obtain ⟨t, ht, rfl⟩ := hφ.exists_of_adj hs (by omega) (by omega) hvx
      have := (hφ.adj_iff hs ht).1 hvx
      exact ⟨t, ht, ⟨by omega, by omega⟩, rfl⟩

/-- The closed ball of radius `r` around the center `φ 0` of a ball path is the image of
`[lo, hi]`. -/
theorem edist_le_radius_iff (hφ : IsBallPath G r lo hi φ) {x : V} :
    G.edist (φ 0) x ≤ r ↔ ∃ s ∈ Set.Icc lo hi, x = φ s := by
  rw [hφ.edist_le_iff le_rfl]
  exact ⟨fun ⟨s, hs, _, hx⟩ => ⟨s, hs, hx⟩, fun ⟨s, hs, hx⟩ =>
    ⟨s, hs, ⟨(hφ.neg_le_lo).trans hs.1, hs.2.trans hφ.hi_le⟩, hx⟩⟩

/-- A ball path of `G` is a ball path of `G ⊕g H` through `Sum.inl`. -/
theorem sumInl (hφ : IsBallPath G r lo hi φ) : IsBallPath (G ⊕g H) r lo hi (Sum.inl ∘ φ) where
  neg_le_lo := hφ.neg_le_lo
  lo_nonpos := hφ.lo_nonpos
  hi_nonneg := hφ.hi_nonneg
  hi_le := hφ.hi_le
  injOn := Sum.inl_injective.comp_injOn hφ.injOn
  adj_iff _ _ hs ht := by simpa only [Function.comp_apply, sum_adj_inl] using hφ.adj_iff hs ht
  exists_of_adj s hs h1 h2 y hy := by
    rcases y with y | y
    · obtain ⟨t, ht, rfl⟩ := hφ.exists_of_adj hs h1 h2 (sum_adj_inl.1 hy)
      exact ⟨t, ht, rfl⟩
    · exact absurd hy (not_adj_sum_inl_inr _ _)

/-- A ball path of `H` is a ball path of `G ⊕g H` through `Sum.inr`. -/
theorem sumInr {ψ : ℤ → W} (hψ : IsBallPath H r lo hi ψ) :
    IsBallPath (G ⊕g H) r lo hi (Sum.inr ∘ ψ) where
  neg_le_lo := hψ.neg_le_lo
  lo_nonpos := hψ.lo_nonpos
  hi_nonneg := hψ.hi_nonneg
  hi_le := hψ.hi_le
  injOn := Sum.inr_injective.comp_injOn hψ.injOn
  adj_iff _ _ hs ht := by simpa only [Function.comp_apply, sum_adj_inr] using hψ.adj_iff hs ht
  exists_of_adj s hs h1 h2 y hy := by
    rcases y with y | y
    · exact absurd hy.symm (not_adj_sum_inl_inr _ _)
    · obtain ⟨t, ht, rfl⟩ := hψ.exists_of_adj hs h1 h2 (sum_adj_inr.1 hy)
      exact ⟨t, ht, rfl⟩

end IsBallPath

section Cycle

open scoped Fin.IntCast

private theorem fin_intCast_eq_zero {N : ℕ} [NeZero N] {z : ℤ} (h1 : -(N : ℤ) < z)
    (h2 : z < N) : (z : Fin N) = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, fun h => by subst h; rfl⟩
  have hv := congrArg Fin.val h
  rw [Fin.val_intCast, Fin.val_zero] at hv
  have hN : (0 : ℤ) < N := by omega
  have hmod : z % N = 0 := by
    have := Int.emod_nonneg z hN.ne'
    omega
  exact Int.eq_zero_of_abs_lt_dvd (Int.dvd_of_emod_eq_zero hmod) (abs_lt.2 ⟨h1, h2⟩)

/-- Around every vertex `c` of the cycle graph on `N ≥ 2r + 2` vertices, `s ↦ c + s` is a ball
path over `[-r, r]`. -/
private theorem isBallPath_cycleGraph_add {N r : ℕ} [NeZero N] (hN : 2 * r + 2 ≤ N) (c : Fin N) :
    IsBallPath (cycleGraph N) r (-r) r (fun s => c + (s : Fin N)) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  let := Fin.instCommRing (k + 2)
  have key : ∀ z : ℤ, -(2 * r + 1 : ℤ) ≤ z → z ≤ 2 * r + 1 → ((z : Fin (k + 2)) = 0 ↔ z = 0) :=
    fun z h1 h2 => fin_intCast_eq_zero (by push_cast; omega) (by push_cast; omega)
  refine ⟨by omega, by omega, by omega, le_rfl, fun s hs t ht hst => ?_, fun s t hs ht => ?_,
    fun s hs h1 h2 y hy => ?_⟩
  · have hst' : ((s - t : ℤ) : Fin (k + 2)) = 0 := by
      push_cast
      exact sub_eq_zero.2 (add_left_cancel hst)
    have := (key _ (by simp only [Set.mem_Icc] at hs ht; omega)
      (by simp only [Set.mem_Icc] at hs ht; omega)).1 hst'
    omega
  · simp only [Set.mem_Icc] at hs ht
    rw [cycleGraph_adj]
    have e1 : c + (s : Fin (k + 2)) - (c + (t : Fin (k + 2))) - 1 =
        ((s - t - 1 : ℤ) : Fin (k + 2)) := by
      push_cast; ring
    have e2 : c + (t : Fin (k + 2)) - (c + (s : Fin (k + 2))) - 1 =
        ((t - s - 1 : ℤ) : Fin (k + 2)) := by
      push_cast; ring
    rw [← sub_eq_zero, e1, ← sub_eq_zero (a := c + (t : Fin (k + 2)) - _), e2,
      key _ (by omega) (by omega), key _ (by omega) (by omega)]
    omega
  · rw [← mem_neighborSet, cycleGraph_neighborSet] at hy
    simp only [Set.mem_Icc] at hs
    rcases hy with rfl | rfl
    · exact ⟨s - 1, ⟨by omega, by omega⟩, by push_cast; ring⟩
    · exact ⟨s + 1, ⟨by omega, by omega⟩, by push_cast; ring⟩

/-- **Balls in cycle graphs.** Around every vertex `c` of the cycle graph on `N ≥ 2r + 2`
vertices, the radius-`r` ball is the path `c - r, …, c + r` on `2r + 1` vertices. -/
theorem exists_isBallPath_cycleGraph {N r : ℕ} (hN : 2 * r + 2 ≤ N) (c : Fin N) :
    ∃ φ : ℤ → Fin N, φ 0 = c ∧ IsBallPath (cycleGraph N) r (-r) r φ := by
  have : NeZero N := ⟨by omega⟩
  exact ⟨_, Fin.ext (by simp [Fin.val_add, Nat.mod_eq_of_lt c.2]), isBallPath_cycleGraph_add hN c⟩

end Cycle

section Path

/-- The vertex of the path graph on `Fin N` at offset `s` from `j`, clamped to the vertex set. -/
private def pathAt {N : ℕ} (j : Fin N) (s : ℤ) : Fin N :=
  ⟨min (j + s).toNat (N - 1), by have := j.2; omega⟩

/-- **Balls in path graphs.** Around vertex `j` of the path graph on `N` vertices, the radius-`r`
ball is the path from `j - min r j` to `j + min r (N - 1 - j)`. -/
theorem exists_isBallPath_pathGraph {N r : ℕ} (j : Fin N) {lo hi : ℤ}
    (hlo : lo = -(min r j : ℕ)) (hhi : hi = (min r (N - 1 - j) : ℕ)) :
    ∃ φ : ℤ → Fin N, φ 0 = j ∧ IsBallPath (pathGraph N) r lo hi φ := by
  subst hlo hhi
  have hj := j.2
  have hv : ∀ s : ℤ, ((pathAt j s : Fin N) : ℕ) = min (j + s).toNat (N - 1) := fun _ => rfl
  refine ⟨pathAt j, Fin.ext (by rw [hv]; omega), by omega, by omega, by omega, by omega,
    fun s hs t ht hst => ?_, fun s t hs ht => ?_, fun s hs h1 h2 y hy => ?_⟩
  · simp only [Set.mem_Icc] at hs ht
    have := congrArg Fin.val hst
    rw [hv, hv] at this
    omega
  · simp only [Set.mem_Icc] at hs ht
    rw [pathGraph_adj, hv, hv]
    omega
  · simp only [Set.mem_Icc] at hs
    rw [pathGraph_adj, hv] at hy
    rcases hy with hy | hy
    · exact ⟨s + 1, ⟨by omega, by omega⟩, Fin.ext (by rw [hv]; omega)⟩
    · exact ⟨s - 1, ⟨by omega, by omega⟩, Fin.ext (by rw [hv]; omega)⟩

/-- Every walk in `pathGraph N` is at least as long as the distance of the endpoint indices. -/
private theorem pathGraph_length_walk {N : ℕ} {i j : Fin N} (p : (pathGraph N).Walk i j) :
    (j : ℕ) - i + (i - j) ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [pathGraph_adj] at h
    rw [Walk.length_cons]
    omega

/-- The vertex `d` steps after `i` in `pathGraph N` is at distance at most `d` from `i`. -/
private theorem edist_pathGraph_add_le {N : ℕ} :
    ∀ (d : ℕ) (i : Fin N) (hi : i + d < N), (pathGraph N).edist i ⟨i + d, hi⟩ ≤ d
  | 0, i, _ => by simp
  | d + 1, i, hi => by
    have h1 := edist_pathGraph_add_le d i (by omega)
    have h2 : (pathGraph N).edist ⟨i + d, by omega⟩ ⟨i + (d + 1), hi⟩ ≤ 1 :=
      edist_le_one_iff_adj_or_eq.2 (.inl (pathGraph_adj.2 (.inl rfl)))
    calc (pathGraph N).edist i ⟨i + (d + 1), hi⟩
        ≤ (pathGraph N).edist i ⟨i + d, by omega⟩ +
          (pathGraph N).edist ⟨i + d, by omega⟩ ⟨i + (d + 1), hi⟩ := SimpleGraph.edist_triangle
      _ ≤ d + 1 := add_le_add h1 h2
      _ = ((d + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-- **Distances in path graphs.** The distance between `i` and `j` in `pathGraph N` is
`|j - i|`, written `(j - i) + (i - j)` in truncated subtraction. -/
theorem edist_pathGraph {N : ℕ} (i j : Fin N) :
    (pathGraph N).edist i j = ((j : ℕ) - i + (i - j) : ℕ) := by
  refine le_antisymm ?_ ?_
  · rcases le_total (i : ℕ) j with h | h
    · have := edist_pathGraph_add_le (j - i) i (by omega)
      rw [show (⟨i + (j - i), by omega⟩ : Fin N) = j from Fin.ext (by simp only; omega)] at this
      rwa [show (j : ℕ) - i + (i - j) = j - i by omega]
    · have := edist_pathGraph_add_le (i - j) j (by omega)
      rw [show (⟨j + (i - j), by omega⟩ : Fin N) = i from Fin.ext (by simp only; omega),
        edist_comm] at this
      rwa [show (j : ℕ) - i + (i - j) = i - j by omega]
  · have : NeZero N := ⟨by have := i.2; omega⟩
    obtain ⟨p, hp⟩ := ((connected_pathGraph.2 (by have := i.2; omega)).preconnected i j)
      |>.exists_walk_length_eq_edist
    rw [← hp]
    exact_mod_cast pathGraph_length_walk p

end Path

end SimpleGraph
