/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.ModEq

/-!
# Canonical cycles in finite functional graphs

Every orbit of a map on a finite type ends in a cycle (`cycleSet`), the same for all states of
the orbit (`cycleSet_iterate`). Past the transient, two times give the same state exactly when
they agree modulo the cycle length (`iterate_eq_iterate_iff_modEq`). Given a linear order on the
states, the least state of the cycle
is a canonical representative (`canonicalCycle`): a periodic state is reachable from `x` exactly
when the two have the same representative (`exists_iterate_eq_iff_canonicalCycle_eq`). The first
visit to the representative (`canonicalTime`) occurs before the number of states, and before the
cycle length for a periodic state; the phase of a state on its cycle is the negative of that
time modulo the cycle length (`phase`).

These labels depend only on the map and the order, not on any representation of the states.

## Main definitions

* `Cslib.FunctionalGraph.cycleSet`: the eventual cycle.
* `Cslib.FunctionalGraph.canonicalCycle`: its least state.
* `Cslib.FunctionalGraph.canonicalTime`: the first visit to that state.
* `Cslib.FunctionalGraph.phase`: the position on the cycle.

## Main results

* `Cslib.FunctionalGraph.iterate_eq_iterate_iff_modEq`: equality past the transient.
* `Cslib.FunctionalGraph.mem_cycleSet_iff`: the cycle is the periodic orbit reached.
* `Cslib.FunctionalGraph.exists_iterate_eq_iff_canonicalCycle_eq`: reachability of periodic
  states.
* `Cslib.FunctionalGraph.transientDepth_le_canonicalTime`,
  `Cslib.FunctionalGraph.canonicalTime_lt_card`,
  `Cslib.FunctionalGraph.canonicalTime_lt_cycleLength`: bounds on the first visit.

## References

* Adapted from lean/Proofs/CycleLabels.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph

open Function

universe u
variable {α : Type u} [Finite α] (f : α → α)

omit [Finite α] in
/-- Periodic points reached at different times along one orbit have the same minimal period. -/
theorem minimalPeriod_eq_of_periodic_iterates (x : α) {a b : ℕ}
    (ha : f^[a] x ∈ periodicPts f) (hb : f^[b] x ∈ periodicPts f) :
    minimalPeriod f (f^[a] x) = minimalPeriod f (f^[b] x) := by
  rcases le_total a b with h | h
  · have ht : f^[b] x = f^[b - a] (f^[a] x) := by
      rw [← iterate_add_apply, Nat.sub_add_cancel h]
    rw [ht, minimalPeriod_apply_iterate ha]
  · have ht : f^[a] x = f^[a - b] (f^[b] x) := by
      rw [← iterate_add_apply, Nat.sub_add_cancel h]
    rw [ht, minimalPeriod_apply_iterate hb]

/-- Advancing along the orbit does not change the cycle length. -/
@[simp] theorem cycleLength_iterate (x : α) (t : ℕ) :
    cycleLength f (f^[t] x) = cycleLength f x := by
  unfold cycleLength
  rw [← iterate_add_apply]
  apply minimalPeriod_eq_of_periodic_iterates
  · rw [iterate_add_apply]
    exact iterate_transientDepth_mem_periodicPts f _
  · exact iterate_transientDepth_mem_periodicPts f x

/-- Every periodic state on the orbit of `x` has the cycle length of `x` as minimal period. -/
theorem minimalPeriod_at_periodic_iterate (x : α) {t : ℕ}
    (ht : f^[t] x ∈ periodicPts f) :
    minimalPeriod f (f^[t] x) = cycleLength f x :=
  minimalPeriod_eq_of_periodic_iterates f x ht (iterate_transientDepth_mem_periodicPts f x)

/-- Past the transient, two times give the same state exactly when they agree modulo the cycle
length. -/
theorem iterate_eq_iterate_iff_modEq (x : α) {a b : ℕ}
    (ha : transientDepth f x ≤ a) (hb : transientDepth f x ≤ b) :
    f^[a] x = f^[b] x ↔ a ≡ b [MOD cycleLength f x] := by
  set μ := transientDepth f x
  set ell := cycleLength f x
  have hp := isPeriodicPt_cycleLength f x
  have hreduce {c : ℕ} (hc : μ ≤ c) : f^[c] x = f^[(c - μ) % ell] (f^[μ] x) := by
    rw [hp.iterate_mod_apply, ← iterate_add_apply, Nat.sub_add_cancel hc]
  have hi := iterate_eq_iterate_iff_of_lt_minimalPeriod (f := f) (x := f^[μ] x)
    (m := (a - μ) % ell) (n := (b - μ) % ell)
    (Nat.mod_lt _ (cycleLength_pos f x)) (Nat.mod_lt _ (cycleLength_pos f x))
  rw [hreduce ha, hreduce hb, hi]
  constructor
  · intro h
    simpa only [Nat.sub_add_cancel ha, Nat.sub_add_cancel hb] using
      (show (a - μ) ≡ (b - μ) [MOD ell] from h).add_right μ
  · intro h
    exact h.sub ha hb Nat.ModEq.rfl

open scoped Classical in
/-- The eventual cycle of `x`, as a finite set. -/
noncomputable def cycleSet (x : α) : Finset α :=
  (periodicOrbit f (f^[transientDepth f x] x)).toFinset

/-- The eventual cycle of `x` is the periodic orbit of the state at its transient depth. -/
@[simp] theorem mem_cycleSet_iff (x y : α) :
    y ∈ cycleSet f x ↔ y ∈ periodicOrbit f (f^[transientDepth f x] x) := by
  classical
  exact Multiset.mem_toFinset

/-- The eventual cycle is nonempty. -/
theorem cycleSet_nonempty (x : α) : (cycleSet f x).Nonempty := by
  classical
  exact ⟨_, (mem_cycleSet_iff f x _).mpr
    (self_mem_periodicOrbit (iterate_transientDepth_mem_periodicPts f x))⟩

/-- Advancing along the orbit does not change the eventual cycle. -/
@[simp] theorem cycleSet_iterate (x : α) (t : ℕ) : cycleSet f (f^[t] x) = cycleSet f x := by
  classical
  ext y
  rw [mem_cycleSet_iff, mem_cycleSet_iff, ← iterate_add_apply]
  let a := transientDepth f (f^[t] x) + t
  let b := transientDepth f x
  have ha : f^[a] x ∈ periodicPts f := by
    dsimp [a]
    rw [iterate_add_apply]
    exact iterate_transientDepth_mem_periodicPts f _
  have hb : f^[b] x ∈ periodicPts f := iterate_transientDepth_mem_periodicPts f x
  change y ∈ periodicOrbit f (f^[a] x) ↔ y ∈ periodicOrbit f (f^[b] x)
  rcases le_total a b with h | h
  · have ht : f^[b] x = f^[b - a] (f^[a] x) := by
      rw [← iterate_add_apply, Nat.sub_add_cancel h]
    rw [ht, periodicOrbit_apply_iterate_eq ha]
  · have ht : f^[a] x = f^[a - b] (f^[b] x) := by
      rw [← iterate_add_apply, Nat.sub_add_cancel h]
    rw [ht, periodicOrbit_apply_iterate_eq hb]

/-- Every state on the eventual cycle of `x` is periodic and reachable from `x`. -/
theorem cycleSet_spec {x y : α} (hy : y ∈ cycleSet f x) :
    y ∈ periodicPts f ∧ ∃ t, f^[t] x = y := by
  obtain ⟨n, rfl⟩ := (mem_periodicOrbit_iff (iterate_transientDepth_mem_periodicPts f x)).mp
    ((mem_cycleSet_iff f x y).mp hy)
  constructor
  · obtain ⟨p, hp, hper⟩ := mem_periodicPts.mp (iterate_transientDepth_mem_periodicPts f x)
    exact mk_mem_periodicPts hp (hper.apply_iterate n)
  · exact ⟨n + transientDepth f x, iterate_add_apply _ _ _ _⟩

variable [LinearOrder α]

/-- The least element of the eventual cycle in the chosen state order. -/
noncomputable def canonicalCycle (x : α) : α := (cycleSet f x).min' (cycleSet_nonempty f x)

/-- The canonical representative lies on the eventual cycle. -/
theorem canonicalCycle_mem (x : α) : canonicalCycle f x ∈ cycleSet f x :=
  Finset.min'_mem _ _

/-- The canonical representative is at most every state of the eventual cycle. -/
theorem canonicalCycle_le (x : α) {y : α} (hy : y ∈ cycleSet f x) : canonicalCycle f x ≤ y :=
  Finset.min'_le _ _ hy

/-- Advancing along the orbit does not change the canonical representative. -/
@[simp] theorem canonicalCycle_iterate (x : α) (t : ℕ) :
    canonicalCycle f (f^[t] x) = canonicalCycle f x := by
  unfold canonicalCycle
  simp only [cycleSet_iterate]

/-- The canonical representative is periodic. -/
theorem canonicalCycle_periodic (x : α) : canonicalCycle f x ∈ periodicPts f :=
  (cycleSet_spec f (canonicalCycle_mem f x)).1

/-- The canonical representative is reachable from `x`. -/
theorem canonicalCycle_reachable (x : α) : ∃ t, f^[t] x = canonicalCycle f x :=
  (cycleSet_spec f (canonicalCycle_mem f x)).2

/-- A canonical representative completely identifies the eventual cycle. -/
theorem exists_iterate_eq_iff_canonicalCycle_eq (x y : α) (hy : y ∈ periodicPts f) :
    (∃ t, f^[t] x = y) ↔ canonicalCycle f x = canonicalCycle f y := by
  constructor
  · rintro ⟨t, rfl⟩
    exact (canonicalCycle_iterate f x t).symm
  · intro he
    obtain ⟨a, ha⟩ := canonicalCycle_reachable f x
    obtain ⟨b, hb⟩ := canonicalCycle_reachable f y
    have hp := isPeriodicPt_minimalPeriod f y
    let d := minimalPeriod f y
    have hd : 0 < d := minimalPeriod_pos_of_mem_periodicPts hy
    have hback : f^[d - b % d] (canonicalCycle f y) = y := by
      rw [← hb, ← hp.iterate_mod_apply b, ← iterate_add_apply,
        Nat.sub_add_cancel (Nat.mod_lt b hd).le]
      exact hp
    refine ⟨(d - b % d) + a, ?_⟩
    rw [iterate_add_apply, ha, he]
    exact hback

/-- The first visit to the canonical cycle representative, always below the state count. -/
noncomputable def canonicalTime (x : α) : ℕ := Nat.find (canonicalCycle_reachable f x)

/-- At the canonical time, the orbit of `x` is at its canonical representative. -/
theorem canonicalTime_spec (x : α) : f^[canonicalTime f x] x = canonicalCycle f x :=
  Nat.find_spec (canonicalCycle_reachable f x)

/-- Before the canonical time, the orbit of `x` avoids its canonical representative. -/
theorem canonicalTime_min (x : α) {j : ℕ} (hj : j < canonicalTime f x) :
    f^[j] x ≠ canonicalCycle f x := Nat.find_min (canonicalCycle_reachable f x) hj

/-- The canonical time is at least the transient depth. -/
theorem transientDepth_le_canonicalTime (x : α) : transientDepth f x ≤ canonicalTime f x := by
  rw [← iterate_mem_periodicPts_iff, canonicalTime_spec]
  exact canonicalCycle_periodic f x

/-- For a periodic state, the canonical time is less than the cycle length. -/
theorem canonicalTime_lt_cycleLength (x : α) (hx : x ∈ periodicPts f) :
    canonicalTime f x < cycleLength f x := by
  have hp : IsPeriodicPt f (cycleLength f x) x := by
    simpa only [transientDepth_eq_zero_of_mem_periodicPts f hx, iterate_zero_apply]
      using isPeriodicPt_cycleLength f x
  have ht := (hp.iterate_mod_apply (canonicalTime f x)).trans (canonicalTime_spec f x)
  exact (Nat.find_min' (canonicalCycle_reachable f x) ht).trans_lt
    (Nat.mod_lt _ (cycleLength_pos f x))

/-- The canonical time is less than the number of states. -/
theorem canonicalTime_lt_card [Fintype α] (x : α) : canonicalTime f x < Fintype.card α := by
  obtain ⟨t, ht, hp, _⟩ := exists_first_visit f (fun y => y = canonicalCycle f x) x
    (canonicalCycle_reachable f x)
  exact (Nat.find_min' (canonicalCycle_reachable f x) hp).trans_lt ht

/-- The phase of `x` on its cycle: the negative of the canonical hitting time modulo the cycle
length. -/
noncomputable def phase (x : α) : ℕ :=
  (cycleLength f x - canonicalTime f x % cycleLength f x) % cycleLength f x

/-- The phase is less than the cycle length. -/
theorem phase_lt (x : α) : phase f x < cycleLength f x := Nat.mod_lt _ (cycleLength_pos f x)

end Cslib.FunctionalGraph
