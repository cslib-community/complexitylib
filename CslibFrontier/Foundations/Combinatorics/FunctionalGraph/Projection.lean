/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# The cycle projection and eventual behaviour

For `f` on a finite type, the iterate `f^[(card α)!]` is an idempotent retraction onto the
periodic points (`cycleProjection`). An orbit agrees with the orbit of its projection exactly
from the transient depth on (`iterate_eq_projection_iff`), so questions about the eventual
behaviour of an orbit become questions about one periodic orbit: whether a target recurs
arbitrarily late (`recurring_target_iff`) or holds from some time on
(`eventually_always_target_iff`). Two orbits meet at a common time exactly when they agree at
time `card α` (`exists_iterate_eq_iterate_iff`), and every time can be replaced by one below
`2 * card α` (`iterate_normalizedTime`).

When a target is reachable, making it absorbing turns its first visit into the transient depth of
the absorbing map (`first_target_depth`); for a map that already fixes its halting states, the
first halting time is the transient depth itself (`halting_depth`).

The state type may live in any universe. No order on it is needed.

## Main definitions

* `Cslib.FunctionalGraph.cycleProjection`: the retraction `f^[(card α)!]`.
* `Cslib.FunctionalGraph.normalizedTime`: a time below `2 * card α` with the same state.

## Main results

* `Cslib.FunctionalGraph.iterate_eq_projection_iff`: orbits agree from cycle entry onward.
* `Cslib.FunctionalGraph.exists_iterate_eq_iterate_iff`: synchronous coalescence at one time.
* `Cslib.FunctionalGraph.iterate_normalizedTime`, `Cslib.FunctionalGraph.normalizedTime_lt`.
* `Cslib.FunctionalGraph.recurring_target_iff`,
  `Cslib.FunctionalGraph.eventually_always_target_iff`: eventual target queries.
* `Cslib.FunctionalGraph.first_target_depth`, `Cslib.FunctionalGraph.halting_depth`: first
  visits as transient depths.

## References

* Adapted from lean/Proofs/{CycleProjection,TargetTimes}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph

open Function

universe u
variable {α : Type u} (f : α → α)

/-- Two periodic points with the same state after `t` steps are equal. -/
theorem eq_of_iterate_eq_of_mem_periodicPts {x y : α} (hx : x ∈ periodicPts f)
    (hy : y ∈ periodicPts f) (t : ℕ) (he : f^[t] x = f^[t] y) : x = y :=
  ((bijOn_periodicPts f).iterate t).injOn hx hy he

section Fintype

variable [Fintype α]

/-- After as many steps as there are states, every orbit is at a periodic point. -/
theorem iterate_card_mem_periodicPts (x : α) : f^[Fintype.card α] x ∈ periodicPts f :=
  (iterate_mem_periodicPts_iff f x _).mpr (transientDepth_lt_card f x).le

/-- The cycle projection `f^[(card α)!]`: it fixes exactly the periodic points and maps every
state to a periodic point of its orbit. -/
def cycleProjection (x : α) : α := f^[(Fintype.card α).factorial] x

/-- The cycle projection of every state is periodic. -/
theorem cycleProjection_mem_periodicPts (x : α) : cycleProjection f x ∈ periodicPts f :=
  (iterate_mem_periodicPts_iff f x _).mpr
    ((transientDepth_lt_card f x).le.trans (Nat.self_le_factorial _))

/-- The cycle projection fixes `x` exactly when `x` is periodic. -/
theorem cycleProjection_eq_self_iff (x : α) : cycleProjection f x = x ↔ x ∈ periodicPts f :=
  mem_periodicPts_iff_isPeriodicPt_factorial_card.symm

/-- The cycle projection is idempotent. -/
@[simp] theorem cycleProjection_cycleProjection (x : α) :
    cycleProjection f (cycleProjection f x) = cycleProjection f x :=
  (cycleProjection_eq_self_iff f _).mpr (cycleProjection_mem_periodicPts f x)

/-- The cycle projection commutes with iterating `f`. -/
@[simp] theorem cycleProjection_iterate (x : α) (t : ℕ) :
    cycleProjection f (f^[t] x) = f^[t] (cycleProjection f x) := by
  unfold cycleProjection
  rw [← iterate_add_apply, ← iterate_add_apply, Nat.add_comm]

/-- **Cycle entry.** The orbit of `x` agrees with the orbit of its projection exactly from the
transient depth onward. -/
theorem iterate_eq_projection_iff (x : α) (t : ℕ) :
    f^[t] x = f^[t] (cycleProjection f x) ↔ transientDepth f x ≤ t := by
  rw [← cycleProjection_iterate, eq_comm, cycleProjection_eq_self_iff,
    iterate_mem_periodicPts_iff]

/-- **Synchronous coalescence.** Two orbits are ever in the same state at the same time exactly
when they are at time `card α`. -/
theorem exists_iterate_eq_iterate_iff (x y : α) :
    (∃ t, f^[t] x = f^[t] y) ↔ f^[Fintype.card α] x = f^[Fintype.card α] y := by
  constructor
  · rintro ⟨t, ht⟩
    by_cases hle : t ≤ Fintype.card α
    · have h := congrArg (f^[Fintype.card α - t]) ht
      simpa only [← iterate_add_apply, Nat.sub_add_cancel hle] using h
    · apply eq_of_iterate_eq_of_mem_periodicPts f (iterate_card_mem_periodicPts f x)
        (iterate_card_mem_periodicPts f y) (t - Fintype.card α)
      simpa only [← iterate_add_apply, Nat.sub_add_cancel (by omega : Fintype.card α ≤ t)]
        using ht
  · exact fun h => ⟨_, h⟩

/-- A time below `2 * card α` at which the orbit of `x` is in the same state as at time `t`:
`t` itself if it is below `card α`, and otherwise `card α` plus the remaining time modulo the
cycle length. -/
noncomputable def normalizedTime (x : α) (t : ℕ) : ℕ :=
  if t < Fintype.card α then t else Fintype.card α + (t - Fintype.card α) % cycleLength f x

/-- The normalized time is less than twice the number of states. -/
theorem normalizedTime_lt (x : α) (t : ℕ) : normalizedTime f x t < 2 * Fintype.card α := by
  unfold normalizedTime
  split_ifs with ht
  · omega
  · have hp := Nat.mod_lt (t - Fintype.card α) (cycleLength_pos f x)
    have hc := transientDepth_add_cycleLength_le_card f x
    omega

/-- At the normalized time, the orbit of `x` is in the same state as at time `t`. -/
theorem iterate_normalizedTime (x : α) (t : ℕ) : f^[normalizedTime f x t] x = f^[t] x := by
  unfold normalizedTime
  split_ifs with ht
  · rfl
  · have hd := transientDepth_lt_card f x
    have hdiv := Nat.div_add_mod (t - Fintype.card α) (cycleLength f x)
    have hr := Nat.mod_le (t - Fintype.card α) (cycleLength f x)
    rcases (show Fintype.card α + (t - Fintype.card α) % cycleLength f x ≤ t by omega).lt_or_eq
      with hlt | heq
    · exact (iterate_apply_eq_iterate_apply_iff f x hlt).mpr
        ⟨by omega, ⟨(t - Fintype.card α) / cycleLength f x, by omega⟩⟩
    · rw [heq]

/-- **Recurring targets.** A target is visited at arbitrarily late times exactly when the orbit
of the cycle projection visits it. -/
theorem recurring_target_iff (P : α → Prop) (x : α) :
    (∀ a, ∃ t, a ≤ t ∧ P (f^[t] x)) ↔ ∃ t, P (f^[t] (cycleProjection f x)) := by
  constructor
  · intro h
    obtain ⟨t, ht, hp⟩ := h (Fintype.card α).factorial
    refine ⟨t - (Fintype.card α).factorial, ?_⟩
    simpa only [cycleProjection, ← iterate_add_apply, Nat.sub_add_cancel ht] using hp
  · rintro ⟨t, ht⟩ a
    obtain ⟨p, hp, hperiod⟩ := mem_periodicPts.mp (cycleProjection_mem_periodicPts f x)
    refine ⟨a * p + t + (Fintype.card α).factorial, ?_, ?_⟩
    · have := Nat.mul_le_mul_left a hp
      omega
    · have he : f^[a * p + t + (Fintype.card α).factorial] x = f^[t] (cycleProjection f x) := by
        rw [iterate_add_apply, iterate_add_apply, Nat.mul_comm]
        exact (hperiod.apply_iterate t).mul_const a
      rwa [he]

/-- **Eventually permanent targets.** A target holds from some time on exactly when the orbit of
the cycle projection never leaves it. -/
theorem eventually_always_target_iff (P : α → Prop) (x : α) :
    (∃ a, ∀ t, a ≤ t → P (f^[t] x)) ↔ ¬∃ t, ¬P (f^[t] (cycleProjection f x)) := by
  rw [← recurring_target_iff f (fun y => ¬P y) x]
  simp only [not_forall, not_exists, not_and, not_not]

end Fintype

/-! ### First visits as transient depths -/

section Finite

variable [Finite α]

/-- **First targets.** If the orbit of `x` reaches `P`, it first does so at the transient depth
of `x` under the map that stops at `P`. -/
theorem first_target_depth (P : α → Prop) [DecidablePred P] (x : α) (h : ∃ t, P (f^[t] x)) :
    P (f^[transientDepth (absorb f P) x] x) ∧
      ∀ j < transientDepth (absorb f P) x, ¬P (f^[j] x) := by
  have := Fintype.ofFinite α
  obtain ⟨t, -, hp, hfirst⟩ := exists_first_visit f P x h
  set g := absorb f P
  have hbefore : g^[t] x = f^[t] x := absorb_iterate_of_forall_not f P x t hfirst
  have hfixed : IsFixedPt g (f^[t] x) := by simp only [IsFixedPt, g, absorb, hp, ite_true]
  have hcyclic : f^[t] x ∈ periodicPts g := mk_mem_periodicPts one_pos (hfixed.isPeriodicPt 1)
  have hle : transientDepth g x ≤ t := by
    rw [← iterate_mem_periodicPts_iff, hbefore]
    exact hcyclic
  have hcancel : g^[transientDepth g x] x = f^[t] x := by
    apply eq_of_iterate_eq_of_mem_periodicPts g (iterate_transientDepth_mem_periodicPts g x)
      hcyclic (t - transientDepth g x)
    rw [← iterate_add_apply, Nat.sub_add_cancel hle, hbefore]
    exact (hfixed.iterate _).symm
  have hbefore' : g^[transientDepth g x] x = f^[transientDepth g x] x :=
    absorb_iterate_of_forall_not f P x _ fun j hj => hfirst j (hj.trans_le hle)
  exact ⟨by rw [← hbefore', hcancel]; exact hp, fun j hj => hfirst j (hj.trans_le hle)⟩

/-- **Halting depth.** If `f` fixes every halting state and the orbit of `x` halts, it first
halts at the transient depth of `x`. -/
theorem halting_depth (H : α → Prop) (hstop : ∀ x, H x → f x = x) (x : α)
    (h : ∃ t, H (f^[t] x)) :
    H (f^[transientDepth f x] x) ∧ ∀ j < transientDepth f x, ¬H (f^[j] x) := by
  classical
  have he : absorb f H = f := by
    funext y
    by_cases hy : H y
    · simp only [absorb, hy, ite_true, hstop y hy]
    · simp only [absorb, hy, ite_false]
  simpa only [he] using first_target_depth f H x h

end Finite

end Cslib.FunctionalGraph
