/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.KCenter.Basic
public import Mathlib.Data.List.MinMax

/-!
# Gonzalez's farthest-first traversal for k-center

Gonzalez's algorithm picks a first center and then, `k - 1` times, adds a point farthest from
the centers chosen so far ([Gonzalez1985]; [WilliamsonShmoys2011], Algorithm 2.1). On a
symmetric distance with the triangle inequality its radius is at most twice the optimal
k-center radius ([WilliamsonShmoys2011], Theorem 2.3). The factor `2` cannot be improved in
polynomial time unless `P = NP`: the combinatorial core of that hardness result is
`CslibFrontier.Algorithms.Lean.KCenter.DominatingSet`, and the statement on encoded instances is
`Cslib.Complexity.P_eq_NP_of_kCenter_approx`.

## Algorithm and source mapping

`gonzalez d P k` runs `k` rounds of `farthestStep d P` from no centers. A round appends a point
of the list `P` maximizing the distance `centerDist` to the current centers, the first such point
in the order of `P` (`List.argmax`). In the first round every point is at distance `⊤` from no
centers, so the first center is the first point of `P`; Algorithm 2.1 picks it arbitrarily. The
algorithm is total: it returns `k` centers whenever `P` is nonempty (`length_gonzalez`), and the
loop "while `|S| < k`" of Algorithm 2.1 becomes a fixed number of rounds. Under a distance that
vanishes exactly on the diagonal the centers are distinct (`nodup_gonzalez`).

The analysis is stated for every *farthest-first traversal* (`IsFarthestFirst`), whatever its
first center and tie-breaking. It follows the pigeonhole form of the argument of Theorem 2.3: if
a point `v` were farther than `2 r` from all `k` centers, then the centers followed by `v` would be
`k + 1` points pairwise farther than `2 r` apart (`IsFarthestFirst.pairwise_lt`), because each
center was at least as far from the earlier centers as `v` is; but at most `k` centers covering
within `r` cannot cover such points (`length_le_card_of_pairwise_lt`). Williamson and Shmoys
phrase the same argument through the clusters of an optimal solution.

## Limitations

The algorithm is a pure Lean function; no machine-level running time is certified. The
competing centers `C` in `centerDist_gonzalez_le_two_mul` are arbitrary points of the space, not
only points of `P`. The alternative threshold 2-approximation of [HochbaumShmoys1985] (see the
chapter notes of [WilliamsonShmoys2011], Chapter 2) is not formalized.

## Main definitions

* `Cslib.Algorithms.Lean.KCenter.IsFarthestFirst`: a farthest-first traversal of a list of points.
* `Cslib.Algorithms.Lean.KCenter.farthestStep`: add a farthest point to the centers.
* `Cslib.Algorithms.Lean.KCenter.gonzalez`: Gonzalez's algorithm with `k` centers.

## Main results

* `isFarthestFirst_gonzalez`, `mem_of_mem_gonzalez`, `length_gonzalez`, `length_gonzalez_le`,
  `card_toFinset_gonzalez_le`: Gonzalez's algorithm is a farthest-first traversal of at most `k`
  points of `P`, exactly `k` when `P` is nonempty.
* `nodup_gonzalez`, `card_toFinset_gonzalez`: under a distance vanishing exactly on the diagonal
  the centers are `k` distinct points when `P` has at least `k` distinct points.
* `IsFarthestFirst.pairwise_lt`: separation of a farthest-first traversal.
* `IsFarthestFirst.centerDist_le_two_mul`, `centerDist_gonzalez_le_two_mul`: every point of `P` is
  within `2 r` of the centers when some `k` centers cover `P` within `r`.
* `radius_gonzalez_le_two_mul`, `radius_gonzalez_le_two_mul_radius`,
  `radius_gonzalez_le_two_mul_optRadius`: on a finite space the radius is at most twice the
  optimum, and at most twice the radius of every set of at most `k` centers.

## References

* [T. F. Gonzalez, *Clustering to minimize the maximum intercluster distance*][Gonzalez1985]
* [D. S. Hochbaum and D. B. Shmoys, *A best possible heuristic for the k-center
  problem*][HochbaumShmoys1985]
* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011], Section 2.2.
-/

public section

namespace Cslib.Algorithms.Lean.KCenter

variable {V α : Type*}

/-! ### The algorithm -/

section Algorithm

variable [LinearOrder α] [DecidableEq V]

/-- `IsFarthestFirst d P L` says that the list `L` of centers is a **farthest-first traversal** of
the points `P`: every center is a point of `P` that, among the points of `P`, is farthest from the
centers before it. The first center is therefore an arbitrary point of `P`. -/
inductive IsFarthestFirst (d : V → V → α) (P : List V) : List V → Prop
  /-- No centers. -/
  | nil : IsFarthestFirst d P []
  /-- Append a point of `P` farthest from the current centers. -/
  | snoc {L : List V} {x : V} : IsFarthestFirst d P L → x ∈ P →
      (∀ y ∈ P, centerDist d L.toFinset y ≤ centerDist d L.toFinset x) →
      IsFarthestFirst d P (L ++ [x])

variable {d : V → V → α} {P : List V}

/-- The centers of a farthest-first traversal are points of `P`. -/
theorem IsFarthestFirst.subset {L : List V} (h : IsFarthestFirst d P L) : ∀ x ∈ L, x ∈ P := by
  induction h with
  | nil => simp
  | snoc _ hx _ ih =>
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact ih y hy
    · rw [List.mem_singleton.1 hy]
      exact hx

/-- One round of the farthest-first traversal: append a point of `P` farthest from the current
centers, the first such point in the order of `P`. Nothing is appended when `P` is empty. -/
@[expose] def farthestStep (d : V → V → α) (P : List V) (L : List V) : List V :=
  match P.argmax (centerDist d L.toFinset) with
  | some x => L ++ [x]
  | none => L

/-- **Gonzalez's algorithm** ([Gonzalez1985]; [WilliamsonShmoys2011], Algorithm 2.1): `k` rounds of
the farthest-first traversal from no centers. The first round picks the first point of `P`. -/
@[expose] def gonzalez (d : V → V → α) (P : List V) (k : ℕ) : List V :=
  (farthestStep d P)^[k] []

theorem gonzalez_zero (d : V → V → α) (P : List V) : gonzalez d P 0 = [] := rfl

theorem gonzalez_succ (d : V → V → α) (P : List V) (k : ℕ) :
    gonzalez d P (k + 1) = farthestStep d P (gonzalez d P k) :=
  Function.iterate_succ_apply' _ _ _

theorem IsFarthestFirst.farthestStep {L : List V} (h : IsFarthestFirst d P L) :
    IsFarthestFirst d P (farthestStep d P L) := by
  unfold KCenter.farthestStep
  match hm : P.argmax (centerDist d L.toFinset) with
  | some x => exact h.snoc (List.argmax_mem hm) fun y hy => List.le_of_mem_argmax hy hm
  | none => exact h

/-- Gonzalez's algorithm computes a farthest-first traversal. -/
theorem isFarthestFirst_gonzalez (d : V → V → α) (P : List V) (k : ℕ) :
    IsFarthestFirst d P (gonzalez d P k) := by
  induction k with
  | zero => exact .nil
  | succ k ih =>
    rw [gonzalez_succ]
    exact ih.farthestStep

theorem length_farthestStep (hP : P ≠ []) (L : List V) :
    (farthestStep d P L).length = L.length + 1 := by
  unfold farthestStep
  match hm : P.argmax (centerDist d L.toFinset) with
  | some x => rw [List.length_append, List.length_singleton]
  | none => exact absurd (List.argmax_eq_none.1 hm) hP

/-- On a nonempty list of points, Gonzalez's algorithm chooses exactly `k` centers. Repetitions
occur only when the distance vanishes between distinct points or `k` exceeds the number of distinct
points of `P`; see `nodup_gonzalez`. -/
theorem length_gonzalez (hP : P ≠ []) (k : ℕ) : (gonzalez d P k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [gonzalez_succ, length_farthestStep hP, ih]

@[simp] theorem gonzalez_nil (d : V → V → α) (k : ℕ) : gonzalez d [] k = [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [gonzalez_succ, ih]
    rfl

/-- The centers are points of `P`. -/
theorem mem_of_mem_gonzalez {k : ℕ} {x : V} (hx : x ∈ gonzalez d P k) : x ∈ P :=
  (isFarthestFirst_gonzalez d P k).subset x hx

theorem length_gonzalez_le (d : V → V → α) (P : List V) (k : ℕ) : (gonzalez d P k).length ≤ k := by
  rcases eq_or_ne P [] with rfl | hP
  · rw [gonzalez_nil]
    exact Nat.zero_le k
  · exact (length_gonzalez hP k).le

/-- **Feasibility:** Gonzalez's algorithm chooses at most `k` centers. -/
theorem card_toFinset_gonzalez_le (d : V → V → α) (P : List V) (k : ℕ) :
    (gonzalez d P k).toFinset.card ≤ k :=
  (List.toFinset_card_le _).trans (length_gonzalez_le d P k)

/-- **The centers are distinct** under a distance that vanishes exactly on the diagonal, as long
as `P` has at least `k` distinct points: when a round would repeat a center, every point of `P` is
at distance `0` from the centers, hence is one of them. -/
theorem nodup_gonzalez [Zero α] (hself : ∀ x, d x x = 0) (hpos : ∀ x y, x ≠ y → 0 < d x y)
    {k : ℕ} (hk : k ≤ P.toFinset.card) : (gonzalez d P k).Nodup := by
  induction k with
  | zero => exact List.nodup_nil
  | succ k ih =>
    have hP : P ≠ [] := by grind [List.toFinset_nil, Finset.card_empty]
    rw [gonzalez_succ]
    unfold farthestStep
    match hm : P.argmax (centerDist d (gonzalez d P k).toFinset) with
    | none => exact absurd (List.argmax_eq_none.1 hm) hP
    | some x =>
      refine List.nodup_append.2 ⟨ih (Nat.le_of_succ_le hk), List.nodup_singleton x, ?_⟩
      rintro a ha b hb rfl
      rw [List.mem_singleton.1 hb] at ha
      have hsub : P.toFinset ⊆ (gonzalez d P k).toFinset := by
        intro y hy
        have hx0 : centerDist d (gonzalez d P k).toFinset x ≤ ((0 : α) : WithTop α) :=
          centerDist_le_coe_iff.2 ⟨x, List.mem_toFinset.2 ha, (hself x).le⟩
        obtain ⟨c, hc, hyc⟩ :=
          centerDist_le_coe_iff.1 ((List.le_of_mem_argmax (List.mem_toFinset.1 hy) hm).trans hx0)
        by_cases hyc' : y = c
        · exact hyc' ▸ hc
        · exact absurd (hpos y c hyc') (not_lt.2 hyc)
      have hcard := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
      rw [length_gonzalez hP] at hcard
      omega

/-- Under a distance that vanishes exactly on the diagonal, Gonzalez's algorithm chooses exactly
`k` distinct centers when `P` has at least `k` distinct points. -/
theorem card_toFinset_gonzalez [Zero α] (hself : ∀ x, d x x = 0)
    (hpos : ∀ x y, x ≠ y → 0 < d x y) {k : ℕ} (hk : k ≤ P.toFinset.card) :
    (gonzalez d P k).toFinset.card = k := by
  rcases eq_or_ne P [] with rfl | hP
  · rw [List.toFinset_nil, Finset.card_empty, Nat.le_zero] at hk
    subst hk
    rfl
  · rw [List.toFinset_card_of_nodup (nodup_gonzalez hself hpos hk), length_gonzalez hP]

end Algorithm

/-! ### The 2-approximation -/

section Approximation

variable [LinearOrder α] [DecidableEq V] {d : V → V → α} {P : List V}

/-- **Separation of a farthest-first traversal.** If a point `v` of `P` is farther than `r` from
every center of a farthest-first traversal `L`, then the centers of `L` followed by `v` are
pairwise farther than `r` apart: each center was at least as far from the earlier centers as `v`
is from them. -/
theorem IsFarthestFirst.pairwise_lt {L : List V} (h : IsFarthestFirst d P L)
    (hsymm : ∀ x y, d x y = d y x) {v : V} {r : α} (hv : v ∈ P)
    (hr : (r : WithTop α) < centerDist d L.toFinset v) :
    (L ++ [v]).Pairwise fun a b => r < d a b := by
  induction h generalizing v with
  | nil => exact List.pairwise_singleton _ _
  | @snoc L x hL hx hmax ih =>
    have hsub : L.toFinset ⊆ (L ++ [x]).toFinset := by
      intro y hy
      rw [List.mem_toFinset] at hy ⊢
      exact List.mem_append_left _ hy
    have hxr : (r : WithTop α) < centerDist d L.toFinset x :=
      (hr.trans_le (centerDist_anti hsub v)).trans_le (hmax v hv)
    rw [List.pairwise_append]
    refine ⟨ih hx hxr, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton.1 hb, hsymm]
    exact coe_lt_centerDist_iff.1 hr a (List.mem_toFinset.2 ha)

variable [Semiring α] [IsOrderedAddMonoid α]

/-- **The 2-approximation for farthest-first traversals** ([WilliamsonShmoys2011], Theorem 2.3):
if some set `C` of at most `|L|` centers covers every point of `P` within `r`, then every point of
`P` is within `2 r` of a center of the farthest-first traversal `L`. -/
theorem IsFarthestFirst.centerDist_le_two_mul {L : List V} (h : IsFarthestFirst d P L)
    (hsymm : ∀ x y, d x y = d y x) (htri : ∀ x y z, d x z ≤ d x y + d y z) {C : Finset V}
    (hC : C.card ≤ L.length) {r : α} (hr : ∀ v ∈ P, ∃ c ∈ C, d v c ≤ r) {v : V} (hv : v ∈ P) :
    centerDist d L.toFinset v ≤ ((2 * r : α) : WithTop α) := by
  by_contra hlt
  have hlen := length_le_card_of_pairwise_lt hsymm htri (C := C) (M := L ++ [v])
    (fun w hw => by
      rcases List.mem_append.1 hw with hw | hw
      · exact hr w (h.subset w hw)
      · rw [List.mem_singleton.1 hw]
        exact hr v hv)
    (h.pairwise_lt hsymm hv (not_le.1 hlt))
  rw [List.length_append, List.length_singleton] at hlen
  omega

/-- **Gonzalez's algorithm is a 2-approximation** ([WilliamsonShmoys2011], Theorem 2.3;
[Gonzalez1985]): for a symmetric distance with the triangle inequality, if some set `C` of at most
`k` points of the space covers every point of `P` within `r`, then every point of `P` is within
`2 r` of the `k` centers chosen by `gonzalez d P k`. -/
theorem centerDist_gonzalez_le_two_mul (hsymm : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) {k : ℕ} {C : Finset V} (hC : C.card ≤ k) {r : α}
    (hr : ∀ v ∈ P, ∃ c ∈ C, d v c ≤ r) {v : V} (hv : v ∈ P) :
    centerDist d (gonzalez d P k).toFinset v ≤ ((2 * r : α) : WithTop α) :=
  (isFarthestFirst_gonzalez d P k).centerDist_le_two_mul hsymm htri
    (hC.trans (length_gonzalez (List.ne_nil_of_mem hv) k).ge) hr hv

variable [Fintype V] [Nonempty V]

/-- **Gonzalez's algorithm is a 2-approximation for k-center** ([WilliamsonShmoys2011],
Theorem 2.3; [Gonzalez1985]): on a finite space with a symmetric distance satisfying the triangle
inequality, run on a list `P` of all the points, the `k` chosen centers have radius at most `2 r`
for every bound `r` on the optimal radius. -/
theorem radius_gonzalez_le_two_mul (hsymm : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) (hP : ∀ v, v ∈ P) {k : ℕ} {r : α}
    (hr : optRadius d k ≤ r) : radius d (gonzalez d P k).toFinset ≤ ((2 * r : α) : WithTop α) := by
  obtain ⟨C, hC, hCr⟩ := optRadius_le_iff.1 hr
  rw [radius_le_coe_iff] at hCr
  exact radius_le_iff.2 fun v =>
    centerDist_gonzalez_le_two_mul hsymm htri hC (fun w _ => hCr w) (hP v)

/-- **The 2-approximation against every feasible solution:** the radius of Gonzalez's centers is
at most twice the radius of every set of at most `k` centers. -/
theorem radius_gonzalez_le_two_mul_radius (hsymm : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) (hP : ∀ v, v ∈ P) {k : ℕ} {S : Finset V}
    (hS : S.card ≤ k) {r : α} (hr : radius d S ≤ r) :
    radius d (gonzalez d P k).toFinset ≤ ((2 * r : α) : WithTop α) :=
  radius_gonzalez_le_two_mul hsymm htri hP ((optRadius_le_radius hS).trans hr)

/-- **The 2-approximation against the optimum value:** with `k ≥ 1` centers the optimal radius
is finite, and Gonzalez's radius is at most twice it. -/
theorem radius_gonzalez_le_two_mul_optRadius (hsymm : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) (hP : ∀ v, v ∈ P) {k : ℕ} (hk : 0 < k) :
    radius d (gonzalez d P k).toFinset ≤
      ((2 * (optRadius d k).untop (optRadius_lt_top hk).ne : α) : WithTop α) :=
  radius_gonzalez_le_two_mul hsymm htri hP (WithTop.coe_untop _ _).ge

end Approximation

end Cslib.Algorithms.Lean.KCenter
