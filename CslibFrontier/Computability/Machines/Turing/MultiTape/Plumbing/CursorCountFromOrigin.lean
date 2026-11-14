/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.CursorCount
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ForwardWork
import Mathlib.Tactic.FinCases

/-!
# Counting a pair word from its origin

`CursorCount.fromOrigin` first moves to the source word's right blank, then reuses the existing
amortized pair counter. For a word of length `2*q`, it writes the canonical binary count `q.bits`
on a blank second tape and restores both heads to zero. The source and prior output are
preserved. The complete native clock is `10*q+4`, including the forward pass and both blank
tests. Even source length is a precondition; this machine does not validate an encoding.
-/

public section

namespace Turing.MultiTapeTM.CursorCount

/-- Count a dense pair word from head position zero, using a blank second tape. -/
noncomputable def fromOrigin :=
  ((forwardWork Bool).extendTapes (tapeEmb (0 : Fin 2))).seq machine

private theorem runsBetween_forward (input source out : List Bool) :
    RunsBetween ((forwardWork Bool).extendTapes (tapeEmb (0 : Fin 2)))
      (config input source [] 0 out) (config input source [] source.length out)
      (source.length + 1) (2 * (source.length + 2)) := by
  let final : Cfg 1 Bool Unit input :=
    tapesCfg input (fun _ => source) 0 (fun _ => source.length) out
  have h : RunsBetween (forwardWork Bool)
      (viewCfg (tapeEmb (0 : Fin 2)) (config input source [] 0 out)) final
      (source.length + 1) (1 * (source.length + 1 + 1)) := by
    apply RunsBetween.of_runFrom
    simpa [viewCfg, config, tapesCfg, Cfg.withState, final] using
      runFrom_forwardWork (input := input) (Symbol := Bool) 1 source out
        (p := 0) (n := source.length) (by omega)
  have he := h.extendTapes (tapeEmb (0 : Fin 2))
  have hf : embed (tapeEmb (0 : Fin 2)) final
      (config input source [] 0 out).workTapes (config input source [] 0 out).workTapePos =
      config input source [] source.length out := by
    rw [embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;>
      simp [final, config, tapesCfg]
  rw [hf] at he
  exact (RunsBetween.of_runFrom he.1).mono le_rfl (by omega)

/-- The actual source length pays for both passes. The finite machine is independent of the
word and its pair count, preserves all source cells and output, and restores both heads. -/
theorem runsBetween_fromOrigin (input source out : List Bool) (q : ℕ)
    (hsource : source.length = 2 * q) :
    RunsBetween fromOrigin (config input source [] 0 out) (config input source q.bits 0 out)
      (10 * q + 4) (2 * (10 * q + 5)) := by
  have hf := runsBetween_forward input source out
  rw [hsource] at hf
  have hc := runsBetween input source out q hsource.ge
  have h := RunsBetween.of_runFrom (hf.seq hc).1
  simpa only [fromOrigin, show 2 * q + 1 + (8 * q + 3) = 10 * q + 4 by omega,
    show 10 * q + 4 + 1 = 10 * q + 5 by omega] using h

end Turing.MultiTapeTM.CursorCount
