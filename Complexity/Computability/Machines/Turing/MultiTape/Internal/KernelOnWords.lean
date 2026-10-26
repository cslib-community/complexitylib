/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: submitted #1111 @3441fa81

public import Mathlib.Basic.Finite.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs
import Cslib.Foundations.Data.Fin.Tuple

/-!
# Running a tidy computation on work tapes

`onWords tm mark` reads its input as a word on one work tape and writes the output of `tm` as a
word on another, leaving every other tape alone. It is `tm` with its output redirected to a new
work tape (`Turing.MultiTapeTM.outputToWord`) and its input read from another new work tape
(`Turing.MultiTapeTM.inputFromWord`).

Its `k + 1 + 2` work tapes are the `k` work tapes of `tm`, the *output work tape*
`(Fin.last k).castAdd 2`, the *input work tape* `Fin.natAdd (k + 1) 0`, and the flag tape of
`inputFromWord`.

## Main definitions

* `Turing.MultiTapeTM.onWords`: the composed machine.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.onWords_extendTapes`: run between two
  selected tapes with exact time and space overheads.

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.onWords`: if `tm` computes `output` from `input`
  tidily, then `onWords tm mark` takes `input` on its input work tape to `output` on its output
  work tape.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*}

/-- `tm`, with its output written to a new work tape and its input read from another, using `mark`
to flag the left end of the input. The output work tape is `(Fin.last k).castAdd 2`, the input
work tape `Fin.natAdd (k + 1) 0`. -/
noncomputable def onWords (tm : MultiTapeTM k Symbol State) (mark : Symbol) :
    MultiTapeTM (k + 1 + 2) Symbol (MarkWorkState ⊕ (State ⊕ RewindWorkState) ⊕ MarkWorkState) :=
  tm.outputToWord.inputFromWord mark

/-- The work tapes in which `onWords` halts, as seen by `inputFromWord`. -/
private lemma onWords_post (input output : List Symbol) :
    Fin.append (Function.update (fun _ : Fin (k + 1) => ([] : List Symbol)) (Fin.last k) output)
        ![input, []] =
      Function.update (Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) input)
        ((Fin.last k).castAdd 2) output := by
  rw [Fin.append_update_left, append_nil_eq_update]

/-- If `tm` computes `output` from `input` tidily, then `onWords tm mark`, started with `input` on
its input work tape and all other work tapes blank, halts with `output` on its output work tape,
every other work tape unchanged, and nothing emitted. -/
theorem ComputesTidilyInTimeAndSpace.onWords {tm : MultiTapeTM k Symbol State}
    {input output : List Symbol} {t s : ℕ} (mark : Symbol)
    (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    TransformsTapes (tm.onWords mark)
      (fun _ ws => ws = Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) input)
      (fun _ ws ws' emitted =>
        ws' = Function.update ws ((Fin.last k).castAdd 2) output ∧ emitted = [])
      (t + output.length + 6) (s + 2 * input.length + 2 * output.length + 3 * k + 18) := by
  -- the run of `outputToWord tm` on `input` with blank work tapes
  obtain ⟨ws', emitted, ⟨rfl, rfl⟩, hp⟩ :=
    transformsTapes_iff_nil_output.mp h.outputToWord input (fun _ => []) ⟨rfl, rfl⟩
  have key := transformsTapes_inputFromWord mark (M := tm.outputToWord)
    (w := input) (ws₀ := fun _ => [])
    (ws₁ := Function.update (fun _ => []) (Fin.last k) output) (e := []) hp
  refine key.imp (fun _ ws hws => ?_) (fun _ ws ws' em hws ⟨hws', hem⟩ => ⟨?_, hem⟩)
    (by omega) (by omega)
  · rw [hws, append_nil_eq_update]
  · rw [hws, hws', onWords_post]

-- upstream: candidate
-- vendored: generalize the selected-tape helper from `Encodings/MultiPass` to a single run,
-- retaining the exact space bound for streaming clients.
/-- Run a tidy computation between two selected tapes, preserving the input and emitting nothing.
The embedding ensures that the selected input and output tapes are distinct. -/
theorem ComputesTidilyInTimeAndSpace.onWords_extendTapes
    {tm : MultiTapeTM k Symbol State} (mark : Symbol) {input output : List Symbol} {t s K : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s)
    {e : Fin (k + 1 + 2) ↪ Fin K} {V O : Fin K} (hi : e (Fin.natAdd (k + 1) 0) = V)
    (ho : e ((Fin.last k).castAdd 2) = O) :
    TransformsTapes ((tm.onWords mark).extendTapes e)
      (fun _ ws => ws = Function.update (fun _ => []) V input)
      (fun _ ws ws' em => ws' = Function.update ws O output ∧ em = [])
      (t + output.length + 6)
      (s + 2 * input.length + 2 * output.length + 3 * k + 18 + (K - (k + 1 + 2))) := by
  have h' := ((h.onWords mark).imp
    (P' := fun _ ws => True ∧ ws = Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) input)
    (fun _ _ h => h.2) (fun _ _ _ _ _ h => h) le_rfl le_rfl).extendTapes_update e
  rw [hi, ho] at h'
  exact h'.imp (fun _ _ hws => ⟨trivial, hws⟩) (fun _ _ _ _ _ h => h) le_rfl le_rfl

end Turing.MultiTapeTM
