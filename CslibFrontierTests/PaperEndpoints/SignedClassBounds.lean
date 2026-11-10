/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.PolyTime.CNF.SignedClassBounds
meta import CslibFrontier.Computability.PolyTime.CNF.SignedClassBounds

/-! # Actual signed class bounds, with no unary expansion -/

public section
open Cslib.Logic.PL.SignedClassBounds
set_option linter.hashCommand false

/-- info: [(0, 0), (1, 0), (3, 2), (0, 4)] -/
#guard_msgs in
#eval normalize [(-3, 0), (-5, -1), (3, 2), (-2 ^ 512, 4)]

/-- info: ([], true) -/
#guard_msgs in
#eval (normalize [], (normalize [(0, 2 ^ 512)]).headD (1, 0) == (0, 2 ^ 512))

example : ¬ ∀ i : Fin 2, (-1 : ℤ) ≤ ((fun _ => 0 : Fin 2 → ℕ) i : ℤ) ∧
    ((fun _ => 0 : Fin 2 → ℕ) i : ℤ) ≤ -1 := by
  intro h
  have hh := (h 0).2
  omega

example (size : Fin 3 → ℕ)
    (h : ∀ i, (pair ((-5 : ℤ), -1)).1 ≤ size i ∧ size i ≤ (pair (-5, -1)).2) : False := by
  have hh := (bounds_iff (fun _ : Fin 3 => -5) (fun _ => -1) size).mp h
  have hn := (hh 0).2
  omega
