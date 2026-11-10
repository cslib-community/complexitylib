/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Periodic points: perturbation and monotone quantities

Two facts about the periodic points (`Function.periodicPts`) of an endomap `f` of an arbitrary
type, complementing the finite-orbit API of `Complexity.Foundations.Combinatorics.FunctionalGraph`
and `Complexity.Foundations.Combinatorics.FunctionalGraph.Cycle`:

* if `g` agrees with `f` at the first `m` points of the orbit of `x`, the `m`-th iterates agree
  (`iterate_eq_of_forall_lt`); consequently, if `g` agrees with `f` at every periodic point of
  `f`, every periodic point of `f` is periodic for `g` (`periodicPts_subset_of_eqOn`);
* a quantity that never decreases along `f` on an `f`-invariant set is constant on the cycles
  inside that set (`apply_le_of_mem_periodicPts`).

The first is used for top trading cycles, where one agent's misreport changes the pointer map
at that agent only, and the second for budget balance of competitive housing allocations.

## Main results

* `Cslib.FunctionalGraph.iterate_eq_of_forall_lt`: iterates agree while the maps agree on the
  orbit.
* `Cslib.FunctionalGraph.periodicPts_subset_of_eqOn`: agreement on the periodic points of `f`
  preserves them.
* `Cslib.FunctionalGraph.apply_le_of_mem_periodicPts`: a quantity nondecreasing along `f` does not
  increase in one step from a periodic point.
-/

public section

namespace Cslib.FunctionalGraph

open Function

universe u v

variable {α : Type u} {f g : α → α}

/-- If `g` agrees with `f` at the first `m` points of the orbit of `x` under `f`, then the `m`-th
iterates of `f` and `g` agree at `x`. -/
theorem iterate_eq_of_forall_lt {x : α} {m : ℕ} (h : ∀ j < m, f (f^[j] x) = g (f^[j] x)) :
    f^[m] x = g^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ← ih fun j hj => h j (by omega)]
    exact h m (by omega)

/-- If `g` agrees with `f` at every periodic point of `f`, then every periodic point of `f` is a
periodic point of `g`. -/
theorem periodicPts_subset_of_eqOn (h : Set.EqOn f g (periodicPts f)) :
    periodicPts f ⊆ periodicPts g := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := mem_periodicPts.1 hx
  refine mk_mem_periodicPts hp ?_
  change g^[p] x = x
  rw [← iterate_eq_of_forall_lt fun j _ => h ((bijOn_periodicPts f).mapsTo.iterate j hx)]
  exact hpx

/-- A quantity `q` that never decreases along `f` on an `f`-invariant set `s` does not increase in
one step from a periodic point in `s`; hence it is constant on every cycle of `f` inside `s`. -/
theorem apply_le_of_mem_periodicPts {β : Type v} [Preorder β] {s : Set α}
    (hs : Set.MapsTo f s s) {q : α → β} (hq : ∀ y ∈ s, q y ≤ q (f y)) {x : α}
    (hx : x ∈ periodicPts f) (hxs : x ∈ s) : q (f x) ≤ q x := by
  obtain ⟨p, hp, hpx⟩ := mem_periodicPts.1 hx
  have key : ∀ m, f^[m] (f x) ∈ s ∧ q (f x) ≤ q (f^[m] (f x)) := by
    intro m
    induction m with
    | zero => exact ⟨hs hxs, le_rfl⟩
    | succ m ih =>
      rw [iterate_succ_apply']
      exact ⟨hs ih.1, ih.2.trans (hq _ ih.1)⟩
  have h := (key (p - 1)).2
  rwa [← iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp, hpx.eq] at h

end Cslib.FunctionalGraph
