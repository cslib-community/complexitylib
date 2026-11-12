/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Reverse
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
import Mathlib.Tactic.FinCases

/-!
# Preparing a persistent binary path for a leaf query

A path arrives on tape 1 with its head at the right blank. The native preparation machine rewinds
it and copies its reversal to blank tape 0, using blank tape 2 as a boundary marker. The source
is preserved, all three heads finish at zero, and the input head and ambient output are unchanged.
The certified clock is linear in path length. The reversed word is a little-endian representation of
the path's candidate index; it may have redundant high zeroes and is not claimed to be `encNat`.
-/

public section

namespace Turing.MultiTapeTM.PreparePath

/-- Rewind the persistent source path, then reverse-copy it to the query tape. -/
private noncomputable def core :=
  ((rewindWork Bool).extendTapes (tapeEmb (1 : Fin 3))).seq
    ((reverseInput Bool).onWords false)

/-- Initial storage: a persistent path at its right blank, with two blank private tapes. -/
private def coreInitial (input path : List Bool) (out : List Bool := []) : Cfg 3 Bool Unit input :=
  tapesCfg input ![[], path, []] 0 ![0, (path.length : ℤ), 0] out

/-- Final storage: little-endian candidate digits on tape 0, preserved path on tape 1. -/
private def coreFinal (input path : List Bool) (out : List Bool := []) : Cfg 3 Bool Unit input :=
  tapesCfg input ![path.reverse, path, []] 0 0 out

/-- Physical path preparation includes rewind, copy, output rewind, and marker cleanup. -/
private theorem runsBetween_core (input path out : List Bool) :
    RunsBetween core (coreInitial input path out) (coreFinal input path out)
      (4 * path.length + 10) (7 * path.length + 27) := by
  let ws : Fin 3 → List Bool := ![[], path, []]
  let middle : Cfg 3 Bool Unit input := tapesCfg input ws 0 0 out
  let rewind := (rewindWork Bool).extendTapes (tapeEmb (1 : Fin 3))
  have hr : RunsBetween rewind (coreInitial input path out) middle
      (path.length + 2) (3 * (path.length + 3)) := by
    apply RunsBetween.of_runFrom
    simp only [rewind, runFrom_tapeEmb, oneTapeCfg, coreInitial, tapesCfg, Cfg.withState,
      extendTapes_q₀, Pi.zero_apply, sub_zero]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [runFrom_rewindWork_none _ _ _ rfl le_rfl, embed_tapeEmb]
    apply Cfg.ext <;> try rfl
    all_goals
      funext j
      fin_cases j <;> simp [middle, ws, tapesCfg]
  have ht := (ReverseInput.computesTidily path).onWords false
  obtain ⟨ws', emitted, ⟨hws, hem⟩, hs⟩ :=
    RunsBetween.of_transformsTapes (input := input) ht
      (ws := ws) (by ext j; fin_cases j <;> simp [ws]) 0 out
  have hws' : ws' = ![path.reverse, path, []] := by
    rw [hws]
    ext j
    fin_cases j <;> simp [ws]
  rw [hws', hem] at hs
  have hs' : RunsBetween ((reverseInput Bool).onWords false) middle (coreFinal input path out)
      (3 * path.length + 8) (4 * path.length + 18) := by
    simp only [List.length_reverse, List.append_nil] at hs
    convert hs using 1 <;> (first | rfl | omega)
  convert hr.seq hs' using 1 <;> (first | rfl | omega)

private def inputStep (direction : SignType) : MultiTapeTM 3 Bool Unit :=
  ofTr () fun _ _ _ => ⟨direction, fun _ => (none, 0), none, none⟩

/-- Prepare a path at the stream's real-input left blank, restoring that input position. -/
noncomputable def machine := (inputStep 1).seq (core.seq (inputStep (-1)))

/-- Stream-facing initial storage, with the real input at its left blank. -/
def initial (input path : List Bool) (out : List Bool := []) : Cfg 3 Bool Unit input :=
  { tapesCfg input ![[], path, []] 0 ![0, (path.length : ℤ), 0] out with inputPos := 0 }

/-- Stream-facing final storage; the real input remains at its left blank. -/
def final (input path : List Bool) (out : List Bool := []) : Cfg 3 Bool Unit input :=
  { tapesCfg input ![path.reverse, path, []] 0 0 out with inputPos := 0 }

/-- Explicit initial configuration, for embedding this phase into another controller. -/
theorem initial_eq (input path out : List Bool) :
    initial input path out =
      { tapesCfg input ![[], path, []] 0 ![0, (path.length : ℤ), 0] out with inputPos := 0 } := by
  rw [initial]

/-- Explicit final configuration, for composing this phase with a subsequent reader. -/
theorem final_eq (input path out : List Bool) :
    final input path out =
      { tapesCfg input ![path.reverse, path, []] 0 0 out with inputPos := 0 } := by
  rw [final]

/-- The complete preparation includes both real-input positioning transitions. -/
theorem runsBetween (input path out : List Bool) :
    RunsBetween machine (initial input path out) (final input path out)
      (4 * path.length + 12) (7 * path.length + 39) := by
  have hstart : RunsBetween (inputStep 1) (initial input path out)
      (coreInitial input path out) 1 6 := by
    apply RunsBetween.of_runFrom
    simp [runFrom, step_of_state, inputStep, initial, coreInitial,
      tapesCfg, Cfg.withState, Action.apply, moveInputPos]
  have hfinish : RunsBetween (inputStep (-1)) (coreFinal input path out)
      (final input path out) 1 6 := by
    apply RunsBetween.of_runFrom
    simp [runFrom, step_of_state, inputStep, final, coreFinal,
      tapesCfg, Cfg.withState, Action.apply, moveInputPos]
    rfl
  convert hstart.seq ((runsBetween_core input path out).seq hfinish) using 1 <;>
    (first | rfl | omega)


end Turing.MultiTapeTM.PreparePath
