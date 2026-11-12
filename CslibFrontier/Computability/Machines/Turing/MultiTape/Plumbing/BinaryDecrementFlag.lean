/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.BinaryDecrement
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape

/-!
# Keeping the decrement flag on a work tape

Redirecting the native decrement's single output bit onto a fresh tape preserves its exact
clock and leaves the real output empty. The flag cursor ends at cell one. A surrounding selector
must read and clear that flag and charge its constant overhead before reusing the fresh tape.
-/

public section

namespace Turing.MultiTapeTM

open Cslib.BitString

/-- A decrement with work-tape underflow reporting has the same clock and emits no output. -/
theorem runFrom_binaryDecrement_outputToTape {input : List Bool}
    (ip : Fin (input.length + 2)) (w : List Bool) :
    binaryDecrement.outputToTape.runFrom
      ⟨some binaryDecrement.q₀, ip, Fin.lastCases (tapeOfList []) (fun _ => tapeOfList w),
        fun _ => 0, []⟩
      (2 * BinaryDecrement.zeros w + 3) =
      ⟨none, ip, Fin.lastCases (tapeOfList [decide (lsbValue w = 0)])
        (fun _ => tapeOfList (decrement w)), Fin.lastCases 1 (fun _ => 0), []⟩ := by
  have h := runFrom_map (outCfgHom binaryDecrement)
    (⟨some binaryDecrement.q₀, ip, fun _ => tapeOfList w, fun _ => 0, []⟩ :
      Cfg 1 Bool _ input) (2 * BinaryDecrement.zeros w + 3)
  rw [runFrom_binaryDecrement] at h
  simp only [outCfgHom_apply, outCfg, List.nil_append, List.length_nil,
    List.length_singleton] at h
  rw [BinaryDecrement.underflow_eq] at h
  have hz : (fun i : Fin 2 => Fin.lastCases (motive := fun _ => ℤ) 0 (fun _ : Fin 1 => 0) i) =
      fun _ => (0 : ℤ) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · simp only [Fin.lastCases_castSucc]
  simpa only [hz, Nat.cast_zero, Nat.cast_one] using h

end Turing.MultiTapeTM
