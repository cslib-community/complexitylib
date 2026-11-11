/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.Cycle
public import CslibFrontier.Foundations.Data.Nat.ArithmeticProgression
public import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

/-!
# Phases, first hitting times, and visit schedules in finite functional graphs

Past the transient, two times give the same state exactly when they agree modulo the cycle
length (`iterate_eq_iterate_iff_modEq`). Given a linear order on the states, every state past
the transient is determined by the canonical cycle representative and its phase
(`iterate_eq_iterate_phase`), and iterating shifts the phase (`phase_iterate`).

These identities give the first hitting time of any target `y` from `x` in closed form
(`hittingTime_spec`). A periodic target is reached exactly when both have the same canonical
representative, first after the transient of `x` and the phase difference (`cyclicDistance`).
A transient target is reached only at the difference of the transient depths. In both cases the
time is below the number of states.

After the first visit to a target, subsequent visits form an arithmetic progression with step
`Function.minimalPeriod f y`, where period zero makes a single visit a special case of the same
formula (`visit_schedule_of_first`, `visit_schedule`), and the number of visits up to a deadline
`T` is given by `Cslib.arithmeticProgressionCount` (`visit_count_of_first`).

The state type may live in any universe; it is finite, and representatives use a linear order.

## Main definitions

* `Cslib.FunctionalGraph.cyclicDistance`: the phase difference from `x` to a target on its cycle.
* `Cslib.FunctionalGraph.reaches`: whether the orbit of `x` reaches `y`, in closed form.
* `Cslib.FunctionalGraph.hittingTime`: the first hitting time, in closed form.

## Main results

* `Cslib.FunctionalGraph.iterate_eq_iterate_phase`: states past the transient by phase.
* `Cslib.FunctionalGraph.phase_iterate`: iterating shifts the phase.
* `Cslib.FunctionalGraph.cyclic_first_hit`: the first hit of a periodic target.
* `Cslib.FunctionalGraph.reaches_iff`, `Cslib.FunctionalGraph.hittingTime_spec`: reachability
  and the exact first hitting time.
* `Cslib.FunctionalGraph.visit_schedule_of_first`,
  `Cslib.FunctionalGraph.visit_before_deadline_of_first`,
  `Cslib.FunctionalGraph.visit_schedule`: complete schedules of visits.
* `Cslib.FunctionalGraph.visit_count_of_first`: counting visits up to a deadline.

## References

* Adapted from lean/Proofs/{HittingTimes,Navigation,VisitSchedules,VisitCounts}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph

open Function

universe u
variable {α : Type u} [Finite α] (f : α → α)

/-- Every state of the orbit of a periodic state lies on its cycle. -/
theorem iterate_mem_cycleSet {x : α} (hx : x ∈ periodicPts f) (j : ℕ) : f^[j] x ∈ cycleSet f x := by
  rw [mem_cycleSet_iff, transientDepth_eq_zero_of_mem_periodicPts f hx, iterate_zero_apply]
  exact iterate_mem_periodicOrbit hx j

variable [LinearOrder α]

/-- The phase cancels the time of the first visit to the representative. -/
theorem phase_add_canonicalTime_modEq (x : α) :
    phase f x + canonicalTime f x ≡ 0 [MOD cycleLength f x] := by
  unfold Nat.ModEq phase
  calc
    _ = (cycleLength f x - canonicalTime f x % cycleLength f x +
        canonicalTime f x % cycleLength f x) % cycleLength f x := by
      simp only [Nat.add_mod, Nat.mod_mod]
    _ = _ := by rw [Nat.sub_add_cancel (Nat.mod_lt _ (cycleLength_pos f x)).le]; simp

/-- Past the transient, the state is the representative advanced by the phase plus the time. -/
theorem iterate_eq_iterate_phase (x : α) {t : ℕ} (ht : transientDepth f x ≤ t) :
    f^[t] x = f^[(phase f x + t) % cycleLength f x] (canonicalCycle f x) := by
  rw [← canonicalTime_spec f x, ← iterate_add_apply]
  apply (iterate_eq_iterate_iff_modEq f x ht
    ((transientDepth_le_canonicalTime f x).trans (Nat.le_add_left _ _))).mpr
  have hm : (phase f x + t) % cycleLength f x ≡ phase f x + t [MOD cycleLength f x] :=
    Nat.mod_modEq _ _
  have hc : (phase f x + t) + canonicalTime f x ≡ t [MOD cycleLength f x] := by
    have := (phase_add_canonicalTime_modEq f x).add_right t
    rwa [Nat.zero_add, Nat.add_right_comm] at this
  exact ((hm.add_right _).trans hc).symm

/-- Any visit to the representative determines the phase. -/
theorem phase_eq_of_iterate_eq_canonicalCycle (x : α) {t : ℕ}
    (ht : f^[t] x = canonicalCycle f x) :
    phase f x = (cycleLength f x - t % cycleLength f x) % cycleLength f x := by
  have hd : transientDepth f x ≤ t := by
    rw [← iterate_mem_periodicPts_iff, ht]
    exact canonicalCycle_periodic f x
  have hm := (iterate_eq_iterate_iff_modEq f x hd (transientDepth_le_canonicalTime f x)).mp
    (ht.trans (canonicalTime_spec f x).symm)
  unfold phase
  rw [hm]

/-- Iterating shifts the phase by the number of steps. -/
@[simp] theorem phase_iterate (x : α) (t : ℕ) :
    phase f (f^[t] x) = (phase f x + t) % cycleLength f x := by
  set y := f^[t] x
  set b := canonicalTime f y
  set ell := cycleLength f x
  have hb : f^[b + t] x = canonicalCycle f x := by
    rw [iterate_add_apply, canonicalTime_spec, canonicalCycle_iterate]
  have hd : transientDepth f x ≤ b + t := by
    rw [← iterate_mem_periodicPts_iff, hb]
    exact canonicalCycle_periodic f x
  have hm : b + t ≡ canonicalTime f x [MOD ell] :=
    (iterate_eq_iterate_iff_modEq f x hd (transientDepth_le_canonicalTime f x)).mp
      (hb.trans (canonicalTime_spec f x).symm)
  have hx := phase_add_canonicalTime_modEq f x
  have hy := phase_add_canonicalTime_modEq f y
  rw [cycleLength_iterate] at hy
  have hboth : phase f y + (b + t) ≡ (phase f x + t) + (b + t) [MOD ell] := by
    have hxt : phase f x + (b + t) ≡ 0 [MOD ell] := (hm.add_left (phase f x)).trans hx
    have hc : (phase f x + t) + b ≡ 0 [MOD ell] := by
      convert hxt using 1
      ac_rfl
    convert (hy.trans hc.symm).add_right t using 1 <;> ac_rfl
  have he := Nat.ModEq.add_right_cancel' (b + t) hboth
  have hlt : phase f y < ell := by simpa only [y, ell, cycleLength_iterate] using phase_lt f y
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hlt] using he

/-- The number of steps after the transient of `x` to a target on the same cycle: the phase
difference modulo the cycle length. -/
noncomputable def cyclicDistance (x y : α) : ℕ :=
  (phase f y + cycleLength f x - (phase f x + transientDepth f x) % cycleLength f x) %
    cycleLength f x

/-- **First hit of a periodic target.** If `y` is periodic with the same canonical
representative as `x`, the orbit of `x` first reaches `y` after its transient and the cyclic
distance. -/
theorem cyclic_first_hit (x y : α) (hy : y ∈ periodicPts f)
    (hc : canonicalCycle f x = canonicalCycle f y) :
    f^[transientDepth f x + cyclicDistance f x y] x = y ∧
      ∀ j < transientDepth f x + cyclicDistance f x y, f^[j] x ≠ y := by
  obtain ⟨a, ha⟩ := (exists_iterate_eq_iff_canonicalCycle_eq f x y hy).mpr hc
  have hel : cycleLength f y = cycleLength f x := by rw [← ha, cycleLength_iterate]
  set ell := cycleLength f x
  set z := (phase f x + transientDepth f x) % ell
  set d := cyclicDistance f x y
  have hell : 0 < ell := cycleLength_pos f x
  have hz : z < ell := Nat.mod_lt _ hell
  have hphase : phase f y < ell := by simpa only [hel] using phase_lt f y
  have hd : d < ell := Nat.mod_lt _ hell
  have hsum : z + d ≡ phase f y [MOD ell] := by
    change (z + (phase f y + ell - z) % ell) % ell = phase f y % ell
    rw [Nat.add_mod_mod, Nat.add_sub_of_le (show z ≤ phase f y + ell by omega),
      Nat.add_mod_right]
  have hend : phase f x + (transientDepth f x + d) ≡ phase f y [MOD ell] := by
    rw [← Nat.add_assoc]
    exact ((Nat.mod_modEq _ _).symm.add_right d).trans hsum
  have hyrepr : y = f^[phase f y] (canonicalCycle f x) := by
    have h := iterate_eq_iterate_phase f y (t := 0)
      (by rw [transientDepth_eq_zero_of_mem_periodicPts f hy])
    simpa only [Nat.add_zero, Nat.mod_eq_of_lt (phase_lt f y), iterate_zero_apply, ← hc] using h
  constructor
  · rw [iterate_eq_iterate_phase f x (by omega), hend, Nat.mod_eq_of_lt hphase, ← hyrepr]
  · intro j hj he
    have hjμ : transientDepth f x ≤ j := by
      rw [← iterate_mem_periodicPts_iff, he]
      exact hy
    have hjmod : phase f x + j ≡ phase f y [MOD ell] := by
      rw [← he, phase_iterate]
      exact Nat.mod_modEq _ _ |>.symm
    have hc1 := Nat.ModEq.add_left_cancel' (phase f x) (hend.trans hjmod.symm)
    have hc2 : d ≡ j - transientDepth f x [MOD ell] := by
      apply Nat.ModEq.add_left_cancel' (transientDepth f x)
      rwa [Nat.add_sub_of_le hjμ]
    have hdle : d ≤ j - transientDepth f x := by
      change d % ell = (j - transientDepth f x) % ell at hc2
      rw [Nat.mod_eq_of_lt hd] at hc2
      exact hc2 ▸ Nat.mod_le _ _
    omega

/-- Whether the orbit of `x` reaches `y`: for a periodic target, whether both have the same
canonical representative; for a transient target, whether the state at the difference of the
transient depths is `y`. -/
noncomputable def reaches (x y : α) : Bool :=
  if transientDepth f y = 0 then decide (canonicalCycle f x = canonicalCycle f y)
  else decide (transientDepth f y ≤ transientDepth f x) &&
    decide (f^[transientDepth f x - transientDepth f y] x = y)

/-- The first hitting time from `x` to `y` when `y` is reachable: the transient and the cyclic
distance for a periodic target, the difference of the transient depths otherwise. -/
noncomputable def hittingTime (x y : α) : ℕ :=
  if transientDepth f y = 0 then transientDepth f x + cyclicDistance f x y
  else transientDepth f x - transientDepth f y

/-- `reaches f x y` holds exactly when the orbit of `x` visits `y`. -/
theorem reaches_iff (x y : α) : reaches f x y = true ↔ ∃ t, f^[t] x = y := by
  unfold reaches
  split_ifs with hy
  · rw [decide_eq_true_eq]
    exact (exists_iterate_eq_iff_canonicalCycle_eq f x y
      ((transientDepth_eq_zero_iff f y).mp hy)).symm
  · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact (exists_iterate_eq_iff_of_not_mem_periodicPts f x y
      fun h => hy ((transientDepth_eq_zero_iff f y).mpr h)).symm

/-- **First hitting times.** If `y` is reachable from `x`, then `hittingTime f x y` is the first
time the orbit of `x` visits `y`, and it is below the number of states. Nothing is claimed about
`hittingTime f x y` when `y` is unreachable. -/
theorem hittingTime_spec [Fintype α] (x y : α) (h : reaches f x y = true) :
    f^[hittingTime f x y] x = y ∧ (∀ j < hittingTime f x y, f^[j] x ≠ y) ∧
      hittingTime f x y < Fintype.card α := by
  have hr := (reaches_iff f x y).mp h
  have hfirst : f^[hittingTime f x y] x = y ∧ ∀ j < hittingTime f x y, f^[j] x ≠ y := by
    unfold hittingTime
    split_ifs with hy
    · have hp := (transientDepth_eq_zero_iff f y).mp hy
      exact cyclic_first_hit f x y hp ((exists_iterate_eq_iff_canonicalCycle_eq f x y hp).mp hr)
    · obtain ⟨-, he⟩ := (exists_iterate_eq_iff_of_not_mem_periodicPts f x y
        fun hp => hy ((transientDepth_eq_zero_iff f y).mpr hp)).mp hr
      refine ⟨he, fun j hj hjy => ?_⟩
      have hd := transientDepth_iterate f x j
      rw [hjy] at hd
      omega
  obtain ⟨t, ht, hty, hmin⟩ := exists_first_visit f (fun z => z = y) x hr
  have he : t = hittingTime f x y := by
    apply Nat.le_antisymm
    · by_contra hle
      exact hmin _ (by omega) hfirst.1
    · by_contra hle
      exact hfirst.2 _ (by omega) hty
  exact ⟨hfirst.1, hfirst.2, he ▸ ht⟩

/-! ### Complete visit schedules and bounded visit counts -/

omit [Finite α] [LinearOrder α] in
/-- After the first visit to `y` at time `d`, subsequent visits form an arithmetic progression
with step `Function.minimalPeriod f y`, where period zero makes a single visit a special case of
the same formula. -/
theorem visit_schedule_of_first (x y : α) (d : ℕ)
    (hd : f^[d] x = y) (hfirst : ∀ j < d, f^[j] x ≠ y) (t : ℕ) :
    f^[t] x = y ↔ ∃ k, t = d + k * Function.minimalPeriod f y := by
  constructor
  · intro ht
    have hle : d ≤ t := by by_contra h; exact hfirst t (by lia) ht
    have hp : Function.IsPeriodicPt f (t - d) y := by
      change f^[t - d] y = y
      rw [← hd, ← Function.iterate_add_apply, Nat.sub_add_cancel hle]
      exact ht.trans hd.symm
    obtain ⟨k, hk⟩ := Function.isPeriodicPt_iff_minimalPeriod_dvd.mp hp
    exact ⟨k, by rw [Nat.mul_comm] at hk; lia⟩
  · rintro ⟨k, rfl⟩
    rw [Nat.add_comm, Function.iterate_add_apply, hd]
    exact (Function.isPeriodicPt_minimalPeriod f y).const_mul k

omit [Finite α] [LinearOrder α] in
/-- When `d` is the first visit time to `y`, a visit occurs on or before `T` iff `d ≤ T`. -/
theorem visit_before_deadline_of_first (x y : α) (d : ℕ)
    (hd : f^[d] x = y) (hfirst : ∀ j < d, f^[j] x ≠ y) (T : ℕ) :
    (∃ t ≤ T, f^[t] x = y) ↔ d ≤ T := by
  constructor
  · rintro ⟨t, ht, hy⟩
    obtain ⟨k, rfl⟩ := (visit_schedule_of_first f x y d hd hfirst t).mp hy
    lia
  · exact fun h => ⟨d, h, hd⟩

/-- Complete visit schedule from `x` to `y` in terms of `reaches`, `hittingTime`, and
`Function.minimalPeriod`. -/
theorem visit_schedule (x y : α) (t : ℕ) :
    f^[t] x = y ↔ reaches f x y = true ∧
      ∃ k, t = hittingTime f x y + k * Function.minimalPeriod f y := by
  let _ := Fintype.ofFinite α
  constructor
  · intro ht
    have hr := (reaches_iff f x y).mpr ⟨t, ht⟩
    have hd := hittingTime_spec f x y hr
    exact ⟨hr, (visit_schedule_of_first f x y _ hd.1 hd.2.1 t).mp ht⟩
  · rintro ⟨hr, ht⟩
    have hd := hittingTime_spec f x y hr
    exact (visit_schedule_of_first f x y _ hd.1 hd.2.1 t).mpr ht

omit [Finite α] [LinearOrder α] in
/-- Number of visits from `x` to `y` up to time `T` when `d` is the first visit time. -/
theorem visit_count_of_first (x y : α) (d : ℕ)
    (hd : f^[d] x = y) (hfirst : ∀ j < d, f^[j] x ≠ y) (T : ℕ) :
    Set.ncard {t : ℕ | t ≤ T ∧ f^[t] x = y} =
      arithmeticProgressionCount d (Function.minimalPeriod f y) T := by
  classical
  have he : {t : ℕ | t ≤ T ∧ f^[t] x = y} =
      {t : ℕ | t ≤ T ∧ ∃ k, t = d + k * Function.minimalPeriod f y} := by
    ext t
    simp only [Set.mem_ofPred_eq, visit_schedule_of_first f x y d hd hfirst t]
  rw [he, arithmeticProgressionCount_spec]

end Cslib.FunctionalGraph
