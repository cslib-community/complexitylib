/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween

/-!
# Running a word machine from the input's left blank

Word-machine contracts normally park the input head at position one. `fromLeftBlank` brackets
such a machine by two charged head movements, exposing the same work-tape contract at position zero.
-/

public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

private def inputStep (direction : SignType) : MultiTapeTM k Symbol Unit :=
  ofTr () fun _ _ _ => ⟨direction, fun _ => (none, 0), none, none⟩

/-- Position the input head from its left blank, run the supplied machine, and move it back. -/
noncomputable def fromLeftBlank (tm : MultiTapeTM k Symbol State) :=
  (inputStep 1).seq (tm.seq (inputStep (-1)))

/-- A machine returning the input head to position one can be used at position zero. The two
host-head movements cost two transitions and at most four visited work cells per tape. -/
theorem RunsBetween.fromLeftBlank {tm : MultiTapeTM k Symbol State}
    {c c' : Cfg k Symbol Unit input} {t s : ℕ} (h : RunsBetween tm c c' t s)
    (hc : c.inputPos = 1) (hc' : c'.inputPos = 1) :
    RunsBetween (input := input) tm.fromLeftBlank { c with inputPos := 0 } { c' with inputPos := 0 }
      (t + 2) (s + 4 * k) := by
  have hstart : RunsBetween (input := input) (inputStep 1)
      { c with inputPos := 0 } c 1 (k * 2) := by
    apply RunsBetween.of_runFrom
    apply Cfg.ext <;> simp [runFrom, step_of_state, inputStep, Cfg.withState,
      Action.apply, moveInputPos, hc]
  have hfinish : RunsBetween (input := input) (inputStep (-1))
      c' { c' with inputPos := 0 } 1 (k * 2) := by
    apply RunsBetween.of_runFrom
    apply Cfg.ext <;> simp [runFrom, step_of_state, inputStep, Cfg.withState,
      Action.apply, moveInputPos, hc']
  convert hstart.seq (h.seq hfinish) using 1 <;> (first | rfl | omega)

end Turing.MultiTapeTM
