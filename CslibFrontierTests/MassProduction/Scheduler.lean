/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.MassProduction.Scheduler
import Mathlib.Algebra.Field.ZMod

/-!
# Scheduler clients

These clients exercise the scheduler specification with zero requests, where every circuit is a
scheduler, and the scheduler theorem on a concrete field: over `ZMod 2` in dimension two, the two
unit directions form a universal menu for one request and one occupied line, so the hypothesis of
`exists_isScheduler` holds and the theorem yields a concrete scheduler for one request. Repeated
targets are allowed: two requests at one point are served by disjoint lines through it, which
the scheduler specification and the clean flags of a phase accept.
-/

namespace ComplexityTests.MassProduction.Scheduler

open Cslib Cslib.BitString Cslib.LineCode Cslib.Circuits Cslib.Circuits.Boolean
  Cslib.Circuits.Boolean.MassProduction

/-! ### Zero requests -/

-- With no requests every circuit is a scheduler.
example {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ b s : ℕ}
    (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (c : Circuit signature (0 * (ℓ * b)) (0 * (s * (ℓ * b)))) : IsScheduler bits scalar c :=
  fun _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    funext fun q => (Fin.cast (Nat.zero_mul _) q).elim0⟩

/-! ### A concrete field -/

/-- The bit of an element of `ZMod 2`. -/
def bits : ZMod 2 ≃+ BitString 1 where
  toFun z _ := decide (z = 1)
  invFun x := if x 0 then 1 else 0
  left_inv := by decide
  right_inv x := by
    funext i
    obtain rfl := Subsingleton.elim i 0
    cases h : x 0 <;> simp [h]
  map_add' := by decide

/-- The single nonzero scalar of `ZMod 2`. -/
def scalar : Fin 1 ≃ {c : ZMod 2 // c ≠ 0} where
  toFun _ := ⟨1, by decide⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv := by
    rintro ⟨c, hc⟩
    apply Subtype.ext
    revert c
    decide

/-- The two unit directions of `(ZMod 2) ^ 2`, one menu entry each. -/
def menu : Fin 2 → Fin 1 → Fin 2 → ZMod 2 := fun e _ => Pi.single e 1

-- Over `ZMod 2` a punctured line is a single point.
theorem puncturedLine_eq (u v : Fin 2 → ZMod 2) : puncturedLine u v = {u + v} := by
  rw [puncturedLine, show (Finset.univ : Finset (ZMod 2)).erase 0 = {1} by decide,
    Finset.image_singleton, one_smul]

-- One occupied line covers at most one point.
theorem eq_of_mem_occupiedPoints {lines : Fin 1 → Option ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))}
    {w w' : Fin 2 → ZMod 2} (hw : w ∈ occupiedPoints lines) (hw' : w' ∈ occupiedPoints lines) :
    w = w' := by
  simp only [occupiedPoints, Finset.mem_biUnion, Finset.mem_univ, true_and] at hw hw'
  obtain ⟨i, hi⟩ := hw
  obtain ⟨i', hi'⟩ := hw'
  obtain rfl := Subsingleton.elim i 0
  obtain rfl := Subsingleton.elim i' 0
  cases h : lines 0 with
  | none => simp [h] at hi
  | some line =>
    simp only [h, Option.elim_some, puncturedLine_eq, Finset.mem_singleton] at hi hi'
    rw [hi, hi']

-- For one request and one occupied line, one of the two unit directions is clean.
theorem isUniversalMenu_menu : IsUniversalMenu 1 menu := by
  refine ⟨by decide, fun lines targets => ?_⟩
  have hclean (e : Fin 2) (he : targets 0 + menu e 0 ∉ occupiedPoints lines) :
      ∃ e, ∃ clean : Finset (Fin 1), 1 ≤ 2 * clean.card ∧
        ∀ i ∈ clean, IsClean (occupiedPoints lines) targets (menu e) i :=
    ⟨e, Finset.univ, by decide, fun i _ => by
      obtain rfl := Subsingleton.elim i 0
      refine ⟨?_, fun j hj => absurd (Subsingleton.elim j 0) hj⟩
      rw [puncturedLine_eq, Finset.disjoint_singleton_left]
      exact he⟩
  by_cases h : targets 0 + menu 0 0 ∈ occupiedPoints lines
  · refine hclean 1 fun h' => ?_
    have := add_left_cancel (eq_of_mem_occupiedPoints h h')
    exact absurd this (by decide)
  · exact hclean 0 h

-- The menu hypothesis of the scheduler theorem holds for one request.
theorem hmenu : ∀ k, 0 < k → k ≤ 2 ^ 0 → ∃ r, k * r ≤ 2 ^ 0 * (2 + 3 * (2 * 1)) + 2 * k ∧
    ∃ menu : Fin r → Fin k → Fin 2 → ZMod 2, IsUniversalMenu (2 ^ 0) menu := by
  intro k hk hk'
  obtain rfl : k = 1 := by simp at hk'; lia
  exact ⟨2, by decide, menu, isUniversalMenu_menu⟩

-- The hypothesis-to-conclusion chain: a scheduler for one request over `ZMod 2`.
example : ∃ c : Circuit signature (2 ^ 0 * (2 * 1)) (2 ^ 0 * (1 * (2 * 1))),
    IsScheduler bits scalar c ∧ c.size ≤ schedulerBound 0 2 1 1 :=
  exists_isScheduler bits scalar hmenu

example : schedulerBound 0 2 1 1 = 1073741824 := by decide

/-! ### Repeated targets -/

-- Two requests at the same point are served by disjoint lines through it.
example : Disjoint (puncturedLine (0 : Fin 2 → ZMod 2) (menu 0 0))
    (puncturedLine (0 : Fin 2 → ZMod 2) (menu 1 0)) := by
  rw [puncturedLine_eq, puncturedLine_eq, Finset.disjoint_singleton]
  decide

-- The scheduler accepts repeated targets: for two requests at one point, every scheduler lists
-- disjoint lines through it with nonzero directions.
example {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ b s : ℕ}
    (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (c : Circuit signature (2 * (ℓ * b)) (2 * (s * (ℓ * b)))) (hc : IsScheduler bits scalar c)
    (u : Fin ℓ → K) : ∃ v w : Fin ℓ → K, v ≠ 0 ∧ w ≠ 0 ∧
      Disjoint (puncturedLine u v) (puncturedLine u w) := by
  obtain ⟨directions, hne, hdisj, -⟩ := hc fun _ => u
  exact ⟨directions 0, directions 1, hne 0, hne 1, hdisj 0 1 (by decide)⟩

-- In a phase, clean flags are exactly `IsClean`, for any targets, repeated or not.
example {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ b s D p a r : ℕ}
    (hk : a + BitonicSort.arity p = 2 ^ D) (bits : K ≃+ BitString b)
    (scalar : Fin s ≃ {c : K // c ≠ 0}) (menu : Fin r → Fin (BitonicSort.arity p) → Fin ℓ → K)
    (hmenu : ∀ e i, menu e i ≠ 0) {targets : Fin (2 ^ D) → Fin ℓ → K}
    {x : BitString (2 ^ D * Scheduler.width D (ℓ * b) s)}
    (hx : Scheduler.Good bits scalar targets a x) (e : Fin r) (i : Fin (BitonicSort.arity p)) :
    ∃ T dirs : Fin (2 ^ D) → Fin ℓ → K,
      (Scheduler.clean hk bits scalar menu x e i = true ↔
        IsClean (occupiedPoints (Scheduler.acceptedLines a T dirs))
          (fun i => T (Scheduler.pending hk i)) (menu e) i) := by
  obtain ⟨π, dirs, -, htarget, hline, -⟩ := hx
  exact ⟨_, dirs, Scheduler.clean_iff bits scalar menu htarget hline hmenu e i⟩

end ComplexityTests.MassProduction.Scheduler
