/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation

/-! Plain signed products and uniform oracle-run resource certificates. -/

open Cslib Turing MultiTapeTM

example {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => left a * right a) input encIntBin := by
  fail_if_success (clear hleft; fun_prop)
  fail_if_success (clear hright; fun_prop)
  fun_prop

example : ComputableInPolyTime (fun p : ℤ × ℤ => p.1 * p.2)
    (encPair encIntBin encIntBin) encIntBin :=
  .intBin_mul' (.fst _ _) (.snd _ _)

example : (-7 : ℤ) * 3 = -21 ∧ (0 : ℤ) * (-3) = 0 := by decide

-- No chosen enumeration of the operation type, polynomial oracle-time bound, or fixed input
-- dimension is assumed. Time and charged workspace remain independent existential witnesses.
example {k : ℕ} {Control Operation α : Type} [Finite Control] [Finite Operation]
    [DecidableEq Operation] (machine : MultiTapePTM k Bool Control Operation)
    {input : α ↪ List Bool} {g : List Bool → Bool} {Tg Sg : List Bool → ℕ}
    (hg : ComputableInO g encBits encBool Tg Sg) (hSg : PolyBounded List.length Sg)
    (c d : ℕ) :
    ∃ T S, PolyBounded (fun a => (input a).length) S ∧
      ComputableInO (fun a => OracleComp.interpret (m := Id) (fun q => [g q.2])
        (machine.run (pure false) (fun op word => OracleComp.query (op, word))
          (c * ((input a).length + 1) ^ d) (input a))) input encBits T S :=
  machine.exists_computableInO_run hg hSg c d

-- The zero clock remains admissible; it is not replaced by a positivity premise.
example {k : ℕ} {Control Operation : Type} [Finite Control] [Finite Operation]
    [DecidableEq Operation] (machine : MultiTapePTM k Bool Control Operation)
    {g : List Bool → Bool} {Tg Sg : List Bool → ℕ}
    (hg : ComputableInO g encBits encBool Tg Sg) (hSg : PolyBounded List.length Sg) :
    ∃ T S, PolyBounded List.length S ∧
      ComputableInO (fun word => OracleComp.interpret (m := Id) (fun q => [g q.2])
        (machine.run (pure false) (fun op word => OracleComp.query (op, word))
          0 word)) encBits encBits T S := by
  simpa [encBits] using
    machine.exists_computableInO_run (input := encBits) hg hSg 0 0
