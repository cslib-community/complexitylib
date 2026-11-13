/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween

/-!
# Capturing output during a run between configurations

Output redirection is valid for arbitrary work-tape layouts and head positions. The original
output word occupies the new last tape with its cursor at the write frontier. The actual output
retains a separately supplied prefix. The native transition count is unchanged.
-/

public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}
  {tm : MultiTapeTM k Symbol State} {c c' : Cfg k Symbol Unit input} {t s : ℕ}

/-- Redirect the run's output to a new work tape while preserving a separate output prefix.
This version records the general work-space bound of one cell per tape and transition. -/
theorem RunsBetween.captureOutput (h : RunsBetween tm c c' t s) (out : List Symbol) :
    RunsBetween tm.outputToTape ((outCfg c).prependOutput out)
      ((outCfg c').prependOutput out) t ((k + 1) * (t + 1)) := by
  have hr := runFrom_map (outCfgHom tm) (c.withState (some tm.q₀)) t
  rw [h.1] at hr
  simp only [outCfgHom_apply] at hr
  have hp := runFrom_map (tm.outputToTape.prependOutputHom out)
    (outCfg (c.withState (some tm.q₀))) t
  rw [hr] at hp
  simp only [MultiTapeNTM.prependOutputHom_apply] at hp
  apply RunsBetween.of_runFrom
  have hq : tm.outputToTape.q₀ = tm.q₀ := rfl
  rw [hq]
  exact hp

/-- The original tapes and heads, plus the emitted word at the origin of a fresh last tape.
The fresh head is zero and the actual output is the supplied prefix. -/
@[expose] def capturedOutput (c : Cfg k Symbol Unit input) (out : List Symbol) :
    Cfg (k + 1) Symbol Unit input :=
  ⟨none, c.inputPos, (outCfg c).workTapes, Fin.lastCases 0 c.workTapePos, out⟩

private theorem runsBetween_rewindOutput (c : Cfg k Symbol Unit input) (out : List Symbol) :
    RunsBetween ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k)))
      ((outCfg c).prependOutput out) (capturedOutput c out)
      (c.output.length + 2) ((k + 1) * (c.output.length + 3)) := by
  let finish : Cfg 1 Symbol Unit input :=
    ⟨none, c.inputPos, fun _ => tapeOfList c.output, fun _ => 0, out⟩
  have hr : RunsBetween (rewindWork Symbol)
      (viewCfg (tapeEmb (Fin.last k)) ((outCfg c).prependOutput out)) finish
      (c.output.length + 2) (1 * (c.output.length + 3)) := by
    apply RunsBetween.of_runFrom
    have h := runFrom_rewindWork_none c.inputPos (tapeOfList c.output) out rfl le_rfl
    simpa [viewCfg, finish, Cfg.prependOutput, outCfg, Cfg.withState] using h
  have he := hr.extendTapes (tapeEmb (Fin.last k))
  have hf : embed (tapeEmb (Fin.last k)) finish
      ((outCfg c).prependOutput out).workTapes ((outCfg c).prependOutput out).workTapePos =
      capturedOutput c out := by
    rw [embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
      simp [finish, capturedOutput, outCfg, Cfg.prependOutput]
  rw [hf] at he
  exact RunsBetween.of_runFrom he.1

/-- Redirect a run's output to a fresh work word and rewind that word, preserving every old
work-tape head and a separate output prefix. The extra time is final output word length plus two. -/
theorem RunsBetween.captureOutputWord (h : RunsBetween tm c c' t s) (out : List Symbol) :
    RunsBetween tm.outputToWord ((outCfg c).prependOutput out) (capturedOutput c' out)
      (t + c'.output.length + 2) ((k + 1) * (t + c'.output.length + 3)) := by
  have hr := (h.captureOutput out).seq (runsBetween_rewindOutput c' out)
  have hb := RunsBetween.of_runFrom hr.1
  simpa only [outputToWord, Nat.add_assoc] using hb

end Turing.MultiTapeTM
