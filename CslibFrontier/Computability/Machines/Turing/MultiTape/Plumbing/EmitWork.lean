/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween

/-!
# Emitting a work-tape word

A one-state native machine copies the suffix of a work-tape word to the append-only output.
It preserves the word, stops at its first following blank, and charges one transition per
emitted symbol plus one terminating transition. The input head does not move.
-/

public section

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-- Copy successive nonblank work-tape cells to the output, stopping at the first blank. -/
def emitWork (Symbol : Type*) : MultiTapeTM 1 Symbol Unit :=
  .ofTr () fun _ _ work => match work 0 with
    | none => ⟨0, fun _ => (none, 0), none, none⟩
    | some s => ⟨0, fun _ => (none, 1), some s, some ()⟩

private theorem runFrom_emitWork_suffix (pre rest out : List Symbol) :
    (emitWork Symbol).runFrom
      ((tapesCfg input (fun _ => pre ++ rest) 0 (fun _ => pre.length) out).withState (some ()))
      (rest.length + 1) =
      (tapesCfg input (fun _ => pre ++ rest) 0 (fun _ => (pre ++ rest).length)
        (out ++ rest)).withState none := by
  induction rest generalizing pre out with
  | nil =>
    rw [List.length_nil, Nat.zero_add, runFrom_one, step_of_state rfl]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
      simp [emitWork, tapesCfg, Action.apply, Cfg.withState, Cfg.workTapeSymbols]
  | cons a rest ih =>
    have hs : tapeOfList (pre ++ a :: rest) (pre.length : ℤ) = some a := by
      rw [tapeOfList_ofNat, List.getElem?_append_right le_rfl]
      simp
    have hstep : (emitWork Symbol).step
        ((tapesCfg input (fun _ => pre ++ a :: rest) 0 (fun _ => pre.length) out).withState
          (some ())) =
        (tapesCfg input (fun _ => (pre ++ [a]) ++ rest) 0
          (fun _ => (pre ++ [a]).length) (out ++ [a])).withState (some ()) := by
      rw [step_of_state rfl]
      refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
        simp [emitWork, tapesCfg, Action.apply, Cfg.withState, Cfg.workTapeSymbols, hs,
          List.append_assoc]
    rw [List.length_cons, Nat.add_comm (rest.length + 1) 1, runFrom_add, runFrom_one, hstep, ih]
    simp only [List.append_assoc, List.singleton_append]

/-- Emit a complete work word while preserving its cells; its head ends on the following blank.
The previous output is preserved as a prefix. -/
theorem runsBetween_emitWork (word out : List Symbol) :
    RunsBetween (emitWork Symbol) (tapesCfg input (fun _ => word) 0 0 out)
      (tapesCfg input (fun _ => word) 0 (fun _ => word.length) (out ++ word))
      (word.length + 1) (word.length + 2) := by
  have h := runFrom_emitWork_suffix (input := input) [] word out
  simp only [List.nil_append, List.length_nil, Nat.cast_zero] at h
  convert RunsBetween.of_runFrom h using 1
  simp

end Turing.MultiTapeTM
