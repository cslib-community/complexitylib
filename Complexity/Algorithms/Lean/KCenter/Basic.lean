/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.WithBot

/-!
# The k-center problem

Given points with a distance `d : V → V → α` and a number `k`, the *k-center problem* asks for a
set `S` of at most `k` centers minimizing the largest distance from a point to its nearest center
([WilliamsonShmoys2011], Section 2.2). This module defines the objective and proves the packing
lower bound shared by the 2-approximation algorithms.

## Model

Distances take values in a linear order `α`; the bounds additionally use a semiring structure
(`ℕ`, `ℚ`, `ℝ`, …) to write `2 * r`. No metric axioms are part of the definitions: the results
that need them take symmetry `d x y = d y x` and the triangle inequality `d x z ≤ d x y + d y z`
as hypotheses, so a Mathlib `PseudoMetricSpace` instantiates them with `dist`. The distance from
a point to a set of centers lives in `WithTop α` and is `⊤` for the empty set.

The radius and the optimum are defined on a finite nonempty type of points, with centers allowed
anywhere among them. The optimum ranges over center sets of *at most* `k` points; when
`k ≤ Fintype.card V` this is the same optimum as over sets of exactly `k` points, as in
[WilliamsonShmoys2011], since adding centers never increases the radius (`radius_anti`).

## Main definitions

* `Cslib.Algorithms.Lean.KCenter.centerDist`: the distance `d(v, S)` from a point to its nearest
  center.
* `Cslib.Algorithms.Lean.KCenter.radius`: the radius `max_v d(v, S)` of a set of centers.
* `Cslib.Algorithms.Lean.KCenter.optRadius`: the optimal radius over at most `k` centers.

## Main results

* `centerDist_le_coe_iff`, `coe_lt_centerDist_iff`, `centerDist_lt_coe_iff`: `d(v, S)` compared
  with a value.
* `radius_le_coe_iff`, `optRadius_le_iff`, `le_optRadius_iff`, `exists_radius_eq_optRadius`:
  the radius and the optimum compared with a value; the optimum is attained.
* `radius_anti`, `optRadius_antitone`, `optRadius_zero`, `optRadius_lt_top`: monotonicity and the
  degenerate cases.
* `length_le_card_of_pairwise_lt`: **packing**: points pairwise farther than `2 r` apart need
  distinct centers within `r`.
* `lt_optRadius_of_pairwise_lt`: `k + 1` points pairwise farther than `2 r` apart force an
  optimal radius above `r`.

## References

* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011], Section 2.2.
-/

public section

namespace Cslib.Algorithms.Lean.KCenter

variable {V α : Type*}

/-! ### Distance to a set of centers -/

section CenterDist

variable [LinearOrder α]

/-- The distance `d(v, S) = min_{c ∈ S} d v c` from `v` to its nearest center in `S`, in
`WithTop α`. It is `⊤` when `S` is empty. -/
@[expose] def centerDist (d : V → V → α) (S : Finset V) (v : V) : WithTop α :=
  S.inf fun c => (d v c : WithTop α)

variable {d : V → V → α} {S T : Finset V} {v c : V} {r : α}

/-- `d(v, S) ≤ r` exactly when some center of `S` is within `r` of `v`. -/
theorem centerDist_le_coe_iff : centerDist d S v ≤ r ↔ ∃ c ∈ S, d v c ≤ r := by
  rw [centerDist, Finset.inf_le_iff (WithTop.coe_lt_top r)]
  simp only [WithTop.coe_le_coe]

/-- `r < d(v, S)` exactly when every center of `S` is farther than `r` from `v`. -/
theorem coe_lt_centerDist_iff : (r : WithTop α) < centerDist d S v ↔ ∀ c ∈ S, r < d v c := by
  rw [centerDist, Finset.lt_inf_iff (WithTop.coe_lt_top r)]
  simp only [WithTop.coe_lt_coe]

/-- `d(v, S) < r` exactly when some center of `S` is closer than `r` to `v`. -/
theorem centerDist_lt_coe_iff : centerDist d S v < r ↔ ∃ c ∈ S, d v c < r := by
  rw [centerDist, Finset.inf_lt_iff]
  simp only [WithTop.coe_lt_coe]

/-- A point is at most as far from a set as from each of its centers. -/
theorem centerDist_le_of_mem (hc : c ∈ S) : centerDist d S v ≤ d v c :=
  Finset.inf_le (f := fun c => (d v c : WithTop α)) hc

/-- Adding centers brings every point closer. -/
theorem centerDist_anti (h : S ⊆ T) (v : V) : centerDist d T v ≤ centerDist d S v :=
  Finset.inf_mono h

@[simp] theorem centerDist_empty (d : V → V → α) (v : V) : centerDist d ∅ v = ⊤ := rfl

@[simp] theorem centerDist_singleton (d : V → V → α) (c v : V) : centerDist d {c} v = d v c :=
  Finset.inf_singleton

end CenterDist

/-! ### Packing -/

section Packing

variable [LinearOrder α] [Semiring α] [IsOrderedAddMonoid α] {d : V → V → α}

/-- **Packing** ([WilliamsonShmoys2011], proof of Theorem 2.3): if every entry of a list `M` is
within `r` of a center of `C`, and the entries of `M` are pairwise farther than `2 r` apart, then
`M` has at most `|C|` entries. By the triangle inequality, two points within `r` of the same
center are at most `2 r` apart. -/
theorem length_le_card_of_pairwise_lt (hsymm : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) {C : Finset V} {r : α} {M : List V}
    (hcov : ∀ v ∈ M, ∃ c ∈ C, d v c ≤ r) (hM : M.Pairwise fun a b => 2 * r < d a b) :
    M.length ≤ C.card := by
  classical
  induction M generalizing C with
  | nil => exact Nat.zero_le _
  | cons a M ih =>
    rw [List.pairwise_cons] at hM
    obtain ⟨c, hc, hac⟩ := hcov a List.mem_cons_self
    -- the other entries are covered by the remaining centers
    have hcov' : ∀ v ∈ M, ∃ c' ∈ C.erase c, d v c' ≤ r := by
      intro v hv
      obtain ⟨c', hc', hvc'⟩ := hcov v (List.mem_cons_of_mem a hv)
      refine ⟨c', Finset.mem_erase.2 ⟨fun hcc => ?_, hc'⟩, hvc'⟩
      subst hcc
      have hav : d a v ≤ 2 * r := by
        rw [two_mul]
        exact (htri a c' v).trans (add_le_add hac (hsymm c' v ▸ hvc'))
      exact absurd hav (not_le.2 (hM.1 v hv))
    have hlen := ih hcov' hM.2
    rw [Finset.card_erase_of_mem hc] at hlen
    have hpos := Finset.card_pos.2 ⟨c, hc⟩
    rw [List.length_cons]
    omega

end Packing

/-! ### Radius and optimum on a finite space -/

section Finite

variable [Fintype V] [Nonempty V] [LinearOrder α]

/-- The **radius** `max_v d(v, S)` of a set `S` of centers in a finite space: the largest distance
from a point to its nearest center. It is `⊤` exactly when `S` is empty. -/
@[expose] def radius (d : V → V → α) (S : Finset V) : WithTop α :=
  Finset.univ.sup' Finset.univ_nonempty (centerDist d S)

/-- The **optimal k-center radius** `min_{|S| ≤ k} radius S` of a finite space. It is `⊤` exactly
when `k = 0`. -/
@[expose] def optRadius (d : V → V → α) (k : ℕ) : WithTop α :=
  (Finset.univ.filter fun S : Finset V => S.card ≤ k).inf (radius d)

variable {d : V → V → α} {S T : Finset V} {k : ℕ}

theorem radius_le_iff {r : WithTop α} : radius d S ≤ r ↔ ∀ v, centerDist d S v ≤ r := by
  rw [radius, Finset.sup'_le_iff]
  simp only [Finset.mem_univ, true_implies]

/-- The radius of `S` is at most `r` exactly when every point is within `r` of a center. -/
theorem radius_le_coe_iff {r : α} : radius d S ≤ r ↔ ∀ v, ∃ c ∈ S, d v c ≤ r := by
  simp only [radius_le_iff, centerDist_le_coe_iff]

theorem radius_lt_iff {r : WithTop α} : radius d S < r ↔ ∀ v, centerDist d S v < r := by
  rw [radius, Finset.sup'_lt_iff]
  simp only [Finset.mem_univ, true_implies]

theorem centerDist_le_radius (v : V) : centerDist d S v ≤ radius d S :=
  Finset.le_sup' (centerDist d S) (Finset.mem_univ v)

/-- Adding centers never increases the radius. -/
theorem radius_anti (h : S ⊆ T) : radius d T ≤ radius d S :=
  radius_le_iff.2 fun v => (centerDist_anti h v).trans (centerDist_le_radius v)

@[simp] theorem radius_empty (d : V → V → α) : radius d ∅ = ⊤ :=
  top_unique (by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact (centerDist_empty d v).symm.le.trans (centerDist_le_radius v))

/-- A nonempty set of centers has finite radius. -/
theorem radius_lt_top (hS : S.Nonempty) : radius d S < ⊤ := by
  obtain ⟨c, hc⟩ := hS
  exact radius_lt_iff.2 fun v => (centerDist_le_of_mem hc).trans_lt (WithTop.coe_lt_top _)

theorem optRadius_le_radius (hS : S.card ≤ k) : optRadius d k ≤ radius d S :=
  Finset.inf_le (f := radius d) (s := Finset.univ.filter fun S : Finset V => S.card ≤ k)
    (Finset.mem_filter.2 ⟨Finset.mem_univ S, hS⟩)

/-- Some set of at most `k` centers attains the optimal radius. -/
theorem exists_radius_eq_optRadius (d : V → V → α) (k : ℕ) :
    ∃ S : Finset V, S.card ≤ k ∧ radius d S = optRadius d k := by
  obtain ⟨S, hS, h⟩ := Finset.exists_mem_eq_inf (Finset.univ.filter fun S : Finset V => S.card ≤ k)
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.zero_le k⟩⟩ (radius d)
  exact ⟨S, (Finset.mem_filter.1 hS).2, h.symm⟩

theorem optRadius_le_iff {r : WithTop α} :
    optRadius d k ≤ r ↔ ∃ S : Finset V, S.card ≤ k ∧ radius d S ≤ r := by
  constructor
  · intro h
    obtain ⟨S, hS, hSr⟩ := exists_radius_eq_optRadius d k
    exact ⟨S, hS, hSr ▸ h⟩
  · rintro ⟨S, hS, hSr⟩
    exact (optRadius_le_radius hS).trans hSr

theorem le_optRadius_iff {r : WithTop α} :
    r ≤ optRadius d k ↔ ∀ S : Finset V, S.card ≤ k → r ≤ radius d S := by
  rw [optRadius, Finset.le_inf_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Allowing more centers never increases the optimal radius. -/
theorem optRadius_antitone (d : V → V → α) : Antitone (optRadius d) := fun _ _ hkl =>
  le_optRadius_iff.2 fun _ hS => optRadius_le_radius (hS.trans hkl)

/-- Without centers, the radius is `⊤`. -/
@[simp] theorem optRadius_zero (d : V → V → α) : optRadius d 0 = ⊤ := by
  obtain ⟨S, hS, h⟩ := exists_radius_eq_optRadius d 0
  rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hS), radius_empty] at h
  exact h.symm

/-- With at least one center, the optimal radius is finite. -/
theorem optRadius_lt_top (hk : 0 < k) : optRadius d k < ⊤ := by
  obtain ⟨c⟩ := ‹Nonempty V›
  refine (optRadius_le_radius (S := {c}) ?_).trans_lt (radius_lt_top (Finset.singleton_nonempty c))
  rw [Finset.card_singleton]
  exact hk

/-- **A lower bound on the optimum** ([WilliamsonShmoys2011], proof of Theorem 2.3): if more than
`k` points are pairwise farther than `2 r` apart, every set of at most `k` centers has radius
greater than `r`. -/
theorem lt_optRadius_of_pairwise_lt [Semiring α] [IsOrderedAddMonoid α]
    (hsymm : ∀ x y, d x y = d y x) (htri : ∀ x y z, d x z ≤ d x y + d y z) {r : α}
    {M : List V} (hM : M.Pairwise fun a b => 2 * r < d a b) (hk : k < M.length) :
    (r : WithTop α) < optRadius d k := by
  rw [← not_le, optRadius_le_iff]
  rintro ⟨S, hS, hSr⟩
  have := length_le_card_of_pairwise_lt hsymm htri
    (fun v _ => radius_le_coe_iff.1 hSr v) hM
  omega

end Finite

end Cslib.Algorithms.Lean.KCenter
