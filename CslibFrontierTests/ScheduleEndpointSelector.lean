/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointSelector

open Turing Turing.MultiTapeTM ScheduleEndpointSelector

example : decode 2 5 = some 5 := by decide
example : decode 2 6 = none := by decide
example : decode 0 0 = none := by decide
example : ScheduleEndpointSelector.head (k := 2) (5 : Fin 6) = 1 := by decide
example : port (k := 2) (5 : Fin 6) = 2 := by decide
example : word 2 5 = List.replicate 6 true := by decide
example : word 2 (2 ^ 128) = [] := by decide

-- The same constant-time native preparer handles a valid last selector and an arbitrarily large
-- invalid selector. Neither input width nor value changes its machine or clock.
example : ∃ (K : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM K Bool Q)
    (source target : Fin K) (c : ℕ), source ≠ target ∧
    (∀ input out, RunsBetween tm
      (tapesCfg input (Function.update (fun _ => []) source (5 : ℕ).bits) 0 0 out)
      (tapesCfg input
        (Function.update (Function.update (fun _ => []) source (5 : ℕ).bits)
          target (List.replicate 6 true)) 0 0 out) c (K * (c + 1))) ∧
    (∀ input out, RunsBetween tm
      (tapesCfg input (Function.update (fun _ => []) source ((2 : ℕ) ^ 128).bits) 0 0 out)
      (tapesCfg input (Function.update (fun _ => []) source ((2 : ℕ) ^ 128).bits) 0 0 out)
      c (K * (c + 1))) := by
  obtain ⟨K, Q, hQ, tm, source, target, c, hne, h⟩ := exists_prepare 2
  refine ⟨K, Q, hQ, tm, source, target, c, hne, ?_, ?_⟩
  · intro input out
    exact h input out 5
  · intro input out
    have hr := h input out (2 ^ 128)
    have hw : word 2 (2 ^ 128) = [] := by decide
    have hu : Function.update (Function.update (fun _ : Fin K => []) source ((2 : ℕ) ^ 128).bits)
        target [] = Function.update (fun _ => []) source ((2 : ℕ) ^ 128).bits := by
      apply Function.update_eq_self_iff.mpr
      simp [hne.symm]
    simpa only [hw, hu] using hr
