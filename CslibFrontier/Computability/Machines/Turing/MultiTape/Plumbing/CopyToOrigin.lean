/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.AppendWord
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.FromLeftBlank
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
import Mathlib.Tactic.FinCases

/-!
# Copying a suffix to a blank work tape

The existing raw append loop copies the unread source suffix; the existing rewind machine returns
the destination head to zero. The source is preserved, with its head at the right blank. The host
input starts and ends at its left blank. The clock includes both host-head movements.
-/

public section

namespace Turing.MultiTapeTM.CopyToOrigin

/-- Copy from tape zero to blank tape one, and rewind the destination. -/
noncomputable def machine :=
  ((AppendWord.machine false).seq
    ((rewindWork Bool).extendTapes (tapeEmb (1 : Fin 2)))).fromLeftBlank

/-- Source prefix already traversed, source suffix still to copy, and blank destination. -/
@[expose] def initial (input pre word out : List Bool) : Cfg 2 Bool Unit input :=
  { AppendWord.config input (pre ++ word) [] pre.length out with inputPos := 0 }

/-- The source stays intact and ends at its right blank; the copied suffix starts at head zero. -/
@[expose] def final (input pre word out : List Bool) : Cfg 2 Bool Unit input :=
  { tapesCfg input ![pre ++ word, word] 0 ![((pre ++ word).length : ℤ), 0] out
    with inputPos := 0 }

/-- The physical copy takes `2 * length + 5` transitions, independently of the source prefix. -/
theorem runsBetween (input pre word out : List Bool) :
    RunsBetween machine (initial input pre word out) (final input pre word out)
      (2 * word.length + 5) (4 * word.length + 18) := by
  let start := AppendWord.config input (pre ++ word) [] pre.length out
  let mid := AppendWord.config input (pre ++ word) word (pre.length + word.length) out
  let finish := tapesCfg input ![pre ++ word, word] 0 ![((pre ++ word).length : ℤ), 0] out
  have hcopy : RunsBetween (AppendWord.machine false) start mid (word.length + 1)
      (2 * (word.length + 2)) := by
    apply RunsBetween.of_runFrom
    simpa [start, mid, AppendWord.machine, AppendWord.clock, AppendWord.fragment] using
      AppendWord.runFrom false input pre word [] out
  have hrewind : RunsBetween ((rewindWork Bool).extendTapes (tapeEmb (1 : Fin 2))) mid finish
      (word.length + 2) (2 * (word.length + 3)) := by
    apply RunsBetween.of_runFrom
    simp only [runFrom_tapeEmb, oneTapeCfg, Cfg.withState, extendTapes_q₀]
    have ht : mid.workTapes 1 = tapeOfList word := by
      funext z
      simp [mid, AppendWord.config, tapesCfg]
    have hp : mid.workTapePos 1 = (word.length : ℤ) := rfl
    rw [ht, hp]
    rw [runFrom_rewindWork_none _ _ _ rfl le_rfl, embed_tapeEmb]
    apply Cfg.ext <;> try rfl
    · funext i
      fin_cases i <;> simp [mid, finish, AppendWord.config, tapesCfg]
    · funext i
      fin_cases i <;> simp [mid, finish, AppendWord.config, tapesCfg]
  have h := (hcopy.seq hrewind).fromLeftBlank rfl rfl
  convert h using 1 <;> (first | rfl | omega)

end Turing.MultiTapeTM.CopyToOrigin
