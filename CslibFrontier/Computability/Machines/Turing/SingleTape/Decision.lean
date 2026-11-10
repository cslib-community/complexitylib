/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
public import Mathlib.Computability.Language

/-!
# Single-tape deciders that answer under the head

A decision notion for cslib's deterministic single-tape machines `Cslib.Turing.SingleTapeTM`
in which the answer is the symbol under the head when the machine halts. The rest of the tape
is unconstrained. This is more permissive than cslib's `OutputsWithinTime`, which requires the
final tape to hold only the output with the head on its first cell.

## Main definitions

* `Cslib.Turing.SingleTapeTM.DecidesByHeadInTime tm ι L yes T`: on every word `w` over the input
  alphabet `α`, written on the tape through the letter map `ι : α → Symbol`, `tm` halts within
  `T |w|` steps, and the cell under its head then holds `yes` exactly when `w ∈ L`.
-/

public section

open Cslib Cslib.Turing Relation

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] {α : Type*}

/-- `tm` decides the language `L` over the input alphabet `α` within time `T`, answering under
the head. Each word `w` is written as `w.map ι`. From the initial configuration `tm` reaches,
within `T |w|` steps, a halted configuration whose scanned cell holds `yes` exactly when
`w ∈ L`. Any other scanned content, including a blank, means rejection. The rest of the final
tape is unconstrained.

This is more permissive than halting in cslib's canonical output form (`OutputsWithinTime`),
which requires the final tape to hold only the output with the head on its first cell. -/
@[expose] def DecidesByHeadInTime (tm : SingleTapeTM Symbol) (ι : α → Symbol) (L : Language α)
    (yes : Symbol) (T : ℕ → ℕ) : Prop :=
  ∀ w : List α, ∃ c : tm.Cfg, RelatesWithinSteps tm.TransitionRelation
    (tm.initCfg (w.map ι)) c (T w.length) ∧ c.state = none ∧ (c.BiTape.head = some yes ↔ w ∈ L)

end Cslib.Turing.SingleTapeTM
