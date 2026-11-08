/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.TSP.Shortcut
public import Complexity.Algorithms.Lean.VertexCover.Matching
import Mathlib.Data.List.MinMax

/-!
# Minimum-weight perfect matchings and the matching bound for metric TSP

A **perfect matching** on a duplicate-free list `O` of vertices is a list of edges `M` whose
endpoints (`Cslib.Algorithms.Lean.VertexCover.endpoints`) are a permutation of `O`: every vertex
of `O` is an endpoint of exactly one edge, and no other vertex is. Its weight under a cost `δ` is
`(M.map fun e => δ e.1 e.2).sum`.

The key inequality of Christofides' algorithm ([WilliamsonShmoys2011], proof of Theorem 2.13) is
`two_mul_sum_le_cycleCost`: under the triangle inequality, a minimum-weight perfect matching on
`O` costs at most half of any tour visiting every vertex of `O`. The tour, shortcut to `O`, has an
even number of edges, which alternate between two perfect matchings on `O`.

`minPerfectMatching` computes a minimum-weight perfect matching by exhaustive search.

## Model

Vertices form any type with decidable equality, and costs are natural numbers. Perfect matchings
are lists of ordered pairs; for a symmetric cost the orientation of an edge does not matter.

## Limitations

`minPerfectMatching` tries every way to match the first vertex and recurses, so on `2k` vertices
it examines `(2k - 1)!! = (2k - 1) (2k - 3) ⋯ 1` matchings. A polynomial-time algorithm
(Edmonds' weighted blossom algorithm, [Edmonds1965]) is not formalized; the results here certify
optimality, not running time.

## Main definitions

* `Cslib.Algorithms.Lean.TSP.minPerfectMatching`: a minimum-weight perfect matching by exhaustive
  search.

## Main results

* `Cslib.Algorithms.Lean.Euler.degree_eq_count_endpoints`: the degree of a vertex in a multigraph
  counts its occurrences among the endpoints.
* `two_mul_sum_le_cycleCost`: a minimum-weight perfect matching on `O` costs at most half of any
  closed walk without repetitions that visits every vertex of `O`.
* `endpoints_minPerfectMatching_perm`: exhaustive search returns a perfect matching on lists of
  even length.
* `sum_minPerfectMatching_le`: for a symmetric cost, it weighs at most any perfect matching.

## References

* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011], Section 2.4.
* [J. Edmonds, *Maximum matching and a polyhedron with 0,1-vertices*][Edmonds1965]
-/

public section

namespace Cslib.Algorithms.Lean.Euler

open Cslib.Algorithms.Lean.VertexCover

/-- The degree of a vertex in a multigraph is its number of occurrences among the endpoints. -/
theorem degree_eq_count_endpoints {α : Type*} [DecidableEq α] (M : List (α × α)) (x : α) :
    degree M x = (endpoints M).count x := by
  induction M with
  | nil => rfl
  | cons e M ih =>
    simp only [degree_cons, ih, endpoints, List.count_cons, ends, beq_iff_eq]
    by_cases h1 : x = e.1 <;> by_cases h2 : x = e.2 <;> simp [h1, h2, eq_comm] <;> omega

end Cslib.Algorithms.Lean.Euler

namespace Cslib.Algorithms.Lean.TSP

open Cslib.Algorithms.Lean.VertexCover

variable {α : Type*}

/-! ### The matching bound -/

/-- Pair up consecutive entries: `[a, b, c, d, …] ↦ [(a, b), (c, d), …]`. -/
private def pairUp : List α → List (α × α)
  | a :: b :: l => (a, b) :: pairUp l
  | _ => []

private theorem endpoints_pairUp : ∀ {l : List α}, Even l.length → endpoints (pairUp l) = l
  | [], _ => rfl
  | [_], h => absurd h (by simp)
  | a :: b :: l, h => by
    have hl : Even l.length := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k - 1, by simp only [List.length_cons] at hk; omega⟩
    simp only [pairUp, endpoints, endpoints_pairUp hl]

/-- The two alternating matchings of a closed walk through `x :: L ++ [z]` together cost as much as
the walk. -/
private theorem sum_pairUp_add_sum_pairUp (δ : α → α → ℕ) :
    ∀ (x z : α) (L : List α), Odd L.length →
      ((pairUp (x :: L)).map fun e => δ e.1 e.2).sum +
          ((pairUp (L ++ [z])).map fun e => δ e.1 e.2).sum =
        (List.zipWith δ (x :: L) (L ++ [z])).sum
  | _, _, [], h => absurd h (by simp)
  | x, z, [b], _ => by simp [pairUp]
  | x, z, b :: c :: L, h => by
    have hL : Odd L.length := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k - 1, by simp only [List.length_cons] at hk; omega⟩
    have ih := sum_pairUp_add_sum_pairUp δ c z L hL
    simp only [pairUp, List.cons_append, List.map_cons, List.sum_cons,
      List.zipWith_cons_cons] at ih ⊢
    omega

/-- **The matching bound** ([WilliamsonShmoys2011], proof of Theorem 2.13): under the triangle
inequality, a minimum-weight perfect matching on the vertices of `O`, all visited by a closed walk
`q` without repetitions, costs at most half of `q`. Shortcut `q` to the vertices of `O`; the
resulting closed walk has an even number of edges, which split into two perfect matchings on `O`.
No symmetry of `δ` is needed. -/
theorem two_mul_sum_le_cycleCost {δ : α → α → ℕ} (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    {O : List α} (hO : O.Nodup) {M : List (α × α)} (hM : (endpoints M).Perm O)
    (hmin : ∀ M' : List (α × α), (endpoints M').Perm O →
      (M.map fun e => δ e.1 e.2).sum ≤ (M'.map fun e => δ e.1 e.2).sum)
    {q : List α} (hq : q.Nodup) (hOq : ∀ x ∈ O, x ∈ q) :
    2 * (M.map fun e => δ e.1 e.2).sum ≤ cycleCost δ q := by
  classical
  have hrq : (q.filter (· ∈ O)).Sublist q := List.filter_sublist
  have hrO : (q.filter (· ∈ O)).Perm O :=
    (List.perm_ext_iff_of_nodup (hrq.nodup hq) hO).2 fun x => by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨hOq x h, h⟩⟩
  have hlen : Even (q.filter (· ∈ O)).length := by
    rw [hrO.length_eq, ← hM.length_eq, length_endpoints]
    exact even_two_mul _
  refine le_trans ?_ (cycleCost_le_of_sublist δ htri hrq)
  generalize q.filter (· ∈ O) = r at hrO hlen
  cases r with
  | nil =>
    have := hmin [] hrO
    simp only [List.map_nil, List.sum_nil, Nat.le_zero] at this
    rw [this]
    exact Nat.zero_le _
  | cons a L =>
    have hodd : Odd L.length := by
      rw [List.length_cons] at hlen
      exact Nat.odd_iff.2 (by obtain ⟨k, hk⟩ := hlen; omega)
    have h1 := hmin _ (by rw [endpoints_pairUp hlen]; exact hrO)
    have h2 := hmin (pairUp (L ++ [a])) (by
      rw [endpoints_pairUp (by simpa [Nat.even_add_one] using hodd)]
      exact List.perm_append_singleton a L |>.trans hrO)
    have hsplit := sum_pairUp_add_sum_pairUp δ a a L hodd
    have hcyc : cycleCost δ (a :: L) = (List.zipWith δ (a :: L) (L ++ [a])).sum := by
      rw [cycleCost, show (a :: L).rotate 1 = L ++ [a] by simp [List.rotate_cons_succ]]
    omega

/-! ### Exhaustive search -/

variable [DecidableEq α]

/-- **Minimum-weight perfect matching by exhaustive search**: match the first vertex with each
other vertex in turn, match the rest recursively, and keep a lightest result (the first one among
ties). The recursion makes at most `fuel` rounds; fuel `k` suffices for lists of length at most
`2 * k`. This takes exponential time; see the module docstring. -/
@[expose] def minPerfectMatching (δ : α → α → ℕ) : (fuel : ℕ) → List α → List (α × α)
  | 0, _ => []
  | _, [] => []
  | k + 1, a :: L =>
    ((L.map fun b => (a, b) :: minPerfectMatching δ k (L.erase b)).argmin
      fun M => (M.map fun e => δ e.1 e.2).sum).getD []

omit [DecidableEq α] in
private theorem getD_argmin_mem {β : Type*} {f : β → ℕ} {l : List β} (hl : l ≠ []) (d : β) :
    (l.argmin f).getD d ∈ l := by
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1 (mt (List.argmin_eq_none (f := f)).1 hl)
  rw [hm, Option.getD_some]
  exact List.argmin_mem hm

omit [DecidableEq α] in
private theorem getD_argmin_le {β : Type*} {f : β → ℕ} {l : List β} {x : β} (hx : x ∈ l)
    (d : β) : f ((l.argmin f).getD d) ≤ f x := by
  obtain ⟨m, hm⟩ :=
    Option.ne_none_iff_exists'.1 (mt (List.argmin_eq_none (f := f)).1 (List.ne_nil_of_mem hx))
  rw [hm, Option.getD_some]
  exact List.le_of_mem_argmin hx hm

/-- With fuel for half its length, exhaustive search returns a perfect matching on a list of even
length. -/
theorem endpoints_minPerfectMatching_perm (δ : α → α → ℕ) {k : ℕ} {O : List α}
    (hk : O.length ≤ 2 * k) (heven : Even O.length) :
    (endpoints (minPerfectMatching δ k O)).Perm O := by
  induction k generalizing O with
  | zero =>
    rw [List.eq_nil_of_length_eq_zero (by omega : O.length = 0)]
    rfl
  | succ k ih =>
    cases O with
    | nil => rfl
    | cons a L =>
      have hL : L ≠ [] := by
        rintro rfl
        simp at heven
      obtain ⟨M₀, hM₀mem, hM₀⟩ :
          ∃ M₀ ∈ L.map fun b => (a, b) :: minPerfectMatching δ k (L.erase b),
            minPerfectMatching δ (k + 1) (a :: L) = M₀ :=
        ⟨_, getD_argmin_mem (by simpa using hL) [], rfl⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hM₀mem
      rw [hM₀]
      have hlen : (L.erase b).length + 1 = L.length := List.length_erase_add_one hb
      have := ih (O := L.erase b) (by simp only [List.length_cons] at hk; omega)
        (by
          obtain ⟨j, hj⟩ := heven
          exact ⟨j - 1, by simp only [List.length_cons] at hj; omega⟩)
      exact ((this.cons b).trans (List.perm_cons_erase hb).symm).cons a

omit [DecidableEq α] in
/-- A vertex of a matching splits off its edge, oriented from that vertex. -/
private theorem exists_perm_cons_cons {δ : α → α → ℕ} (hsymm : ∀ x y, δ x y = δ y x)
    {M : List (α × α)} {a : α} (ha : a ∈ endpoints M) :
    ∃ b N, (endpoints M).Perm (a :: b :: endpoints N) ∧
      (M.map fun e => δ e.1 e.2).sum = δ a b + (N.map fun e => δ e.1 e.2).sum := by
  obtain ⟨e, he, hae⟩ := mem_endpoints.1 ha
  obtain ⟨M₁, M₂, rfl⟩ := List.append_of_mem he
  have hperm : (endpoints (M₁ ++ e :: M₂)).Perm (e.1 :: e.2 :: endpoints (M₁ ++ M₂)) := by
    rw [endpoints_append, endpoints_append, endpoints]
    exact List.perm_middle.trans (List.perm_middle.cons _)
  have hw : ((M₁ ++ e :: M₂).map fun e => δ e.1 e.2).sum =
      δ e.1 e.2 + ((M₁ ++ M₂).map fun e => δ e.1 e.2).sum := by
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    omega
  rcases hae with rfl | rfl
  · exact ⟨e.2, M₁ ++ M₂, hperm, hw⟩
  · exact ⟨e.1, M₁ ++ M₂, hperm.trans (List.Perm.swap _ _ _), by rw [hw, hsymm]⟩

/-- **Optimality of exhaustive search**: for symmetric `δ` and fuel for half the length of `O`,
`minPerfectMatching` weighs at most any perfect matching on `O`. -/
theorem sum_minPerfectMatching_le {δ : α → α → ℕ} (hsymm : ∀ x y, δ x y = δ y x) {k : ℕ}
    {O : List α} (hk : O.length ≤ 2 * k) {M : List (α × α)} (hM : (endpoints M).Perm O) :
    ((minPerfectMatching δ k O).map fun e => δ e.1 e.2).sum ≤ (M.map fun e => δ e.1 e.2).sum := by
  induction k generalizing O M with
  | zero => simp [minPerfectMatching]
  | succ k ih =>
    cases O with
    | nil => simp [minPerfectMatching]
    | cons a L =>
      obtain ⟨b, N, hperm, hw⟩ :=
        exists_perm_cons_cons hsymm (hM.symm.subset List.mem_cons_self)
      have hbN : (b :: endpoints N).Perm L := (hperm.symm.trans hM).cons_inv
      have hb : b ∈ L := hbN.subset List.mem_cons_self
      have hN : (endpoints N).Perm (L.erase b) :=
        (hbN.trans (List.perm_cons_erase hb)).cons_inv
      have hlen : (L.erase b).length + 1 = L.length := List.length_erase_add_one hb
      have hih := ih (O := L.erase b) (by simp only [List.length_cons] at hk; omega) hN
      have hle := getD_argmin_le (f := fun M => (M.map fun e => δ e.1 e.2).sum)
        (List.mem_map_of_mem (f := fun b => (a, b) :: minPerfectMatching δ k (L.erase b)) hb) []
      refine hle.trans ?_
      simp only [List.map_cons, List.sum_cons]
      omega

end Cslib.Algorithms.Lean.TSP
