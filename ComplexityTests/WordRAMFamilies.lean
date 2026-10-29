/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.MapOp

/-!
# Width conditions and nonuniform word-RAM families

Exercise code selection, logarithmic upper intervals, squared-logarithmic lower bounds,
width-dependent budgets, schedule asymptotics, and all-input correctness of asymptotic contracts.
-/

namespace ComplexityTests.WordRAMFamilies

open Cslib.WordRAM

/-- Width chooses a literal, without a width instruction in the selected program. -/
private def advice : WordSizeDependentProgram .arithmetic 1 := fun w =>
  [.op (.const 0 (if w = 2 then 1 else 0)), .halt 0]

example : advice.BoundedCode ∧ advice 1 ≠ advice 2 := by
  refine ⟨⟨2, fun w => by simp [advice]⟩, ?_⟩
  decide

/-- Both schedule values fit; the family uses its width-specific literal as the answer. -/
example : DecidableInTime .arithmetic {b : Bool | b = true} (fun _ _ => [])
    (fun _ w => w + 2) (fun b w => w = if b then 2 else 1) := by
  refine ⟨1, advice, ⟨2, fun w => by simp [advice]⟩, ?_⟩
  intro b w hw _
  subst w
  cases b
  · exact ⟨0, 2, .of_run (fuel := 2) (by decide), by decide, by decide, by decide⟩
  · exact ⟨1, 2, .of_run (fuel := 2) (by decide), by decide, by decide, by decide⟩

private def accept : Program .standard 1 := [.op (.const 0 1), .halt 0]

private theorem accepts : accept.DecidesInTime (fun _ n => [n]) Set.univ
    (fun _ w => w + 2) (fun _ _ => True) := by
  intro n w _ hi
  have h1 : Fits w 1 := hi.1
  refine ⟨1, 2, .of_run (fuel := 2) ?_, by change 2 ≤ w + 2; omega, le_rfl, by simp⟩
  simp [WordSizeDependentProgram.const, run, step, accept, Op.eval, Data.put, h1, Data.set,
    State.init]

/-- Logarithmic upper intervals and squared-logarithmic lower bounds as width conditions, with
concrete fitting witnesses. -/
example :
    UniformDecidableInTime .standard Set.univ (fun _ n => [n]) (fun _ w => w + 2)
      (fun n w => logWidth 1 n ≤ w ∧ w ≤ logWidth 3 n) ∧
    ((logWidth 1 5 ≤ 3 ∧ 3 ≤ logWidth 3 5) ∧ InputFits 3 [5]) ∧
    UniformDecidableInTime .standard Set.univ (fun _ n => [n]) (fun _ w => w + 2)
      (fun n w => logWidth 1 n ^ 2 ≤ w) ∧
    (logWidth 1 3 ^ 2 ≤ 4 ∧ InputFits 4 [3]) :=
  ⟨⟨1, accept, accepts.mono (fun _ _ => le_rfl) (fun _ _ _ => trivial)⟩,
   by decide,
   ⟨1, accept, accepts.mono (fun _ _ => le_rfl) (fun _ _ _ => trivial)⟩,
   by decide⟩

/-- Runtime constants are shared by all widths. -/
example : DecidableInO .standard Set.univ (fun _ n => [n]) id (fun _ w => w + 2)
    (fun _ _ => True) := by
  refine ⟨fun _ w => w + 2, ?_, 1, 0, by decide, ?_⟩
  · exact UniformDecidableInTime.decidableInTime ⟨1, accept, accepts⟩
  · intro n w _ _
    simp

/-- Big-O width schedules yield eventual explicit upper conditions. Reversing the functions
expresses Omega, including fractional lower constants. -/
example (W : ℕ → ℕ)
    (h : Asymptotics.IsBigO Filter.atTop (fun n => (W n : ℝ))
      (fun n => (logWidth 1 n : ℝ))) :
    ∃ k : ℕ, 0 < k ∧ ∀ᶠ n in Filter.atTop,
      W n ≤ logWidth k n := by
  simpa only [logWidth, Nat.one_mul] using
    (isBigO_natCast_iff_eventually_le_mul W (logWidth 1)).mp h

/-- A squared-logarithmic Omega assumption on a schedule allows a fractional lower constant. -/
example (W : ℕ → ℕ)
    (h : Asymptotics.IsBigO Filter.atTop (fun n => ((logWidth 1 n ^ 2 : ℕ) : ℝ))
      (fun n => (W n : ℝ))) :
    ∃ k : ℕ, 0 < k ∧ ∀ᶠ n in Filter.atTop, logWidth 1 n ^ 2 ≤ k * W n :=
  (isBigO_natCast_iff_eventually_le_mul (fun n => logWidth 1 n ^ 2) W).mp h

/-- Bounded size does not erase correctness in an asymptotic certificate. -/
example (T : ℕ → ℕ → ℕ) :
    ¬DecidableInO .standard {b : Bool | b = true} (fun _ _ => []) (fun _ => 0) T
      (fun _ _ => True) := by
  rintro ⟨time, ⟨r, P, _, hP⟩, _⟩
  have hi : InputFits 1 [] := by decide
  obtain ⟨v₀, _, he₀, _, _, hb₀⟩ := hP false 1 trivial hi
  obtain ⟨v₁, _, he₁, _, _, hb₁⟩ := hP true 1 trivial hi
  have hv := (he₀.unique he₁).1
  have : false = true := hb₀.mp (hv.trans (hb₁.mpr rfl))
  cases this

/-- info: 'Cslib.WordRAM.UniformDecidableInTime.decidableInTime' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.WordRAM.UniformDecidableInTime.decidableInTime

/-- info: 'Cslib.WordRAM.UniformDecidableInO.decidableInO' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.WordRAM.UniformDecidableInO.decidableInO

end ComplexityTests.WordRAMFamilies
