/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.OfTuring

/-!
# Turing machine ⇒ word-RAM simulation clients

A one-tape machine writes its input, with every bit flipped, leftward from the origin of its work
tape, so it crosses into the negative half-tape; at the end of the input it turns around and emits
the work tape back to the origin and one cell past it, so it crosses back. Its output is the input
flipped and reversed. The compiled simulator is run concretely, by kernel evaluation, and returns
that output read as a binary number within the instruction bound `simTime`. A two-tape machine
copies its input rightward on one tape and leftward on the other, then reads both tapes back
together, so each step dispatches on both work symbols. The headline
theorem applies to the machine on every input it finishes, and the polynomial-time form applies to
the identity on binary numbers.
-/

namespace ComplexityTests.WordRAMOfTuring

open Cslib Cslib.WordRAM Cslib.WordRAM.OfTuring Turing

/-! ## The output convention -/

example : BitString.lsbValue [true, false, true] = 5 := by decide
example : BitString.lsbValue [] = 0 := rfl
example (b : Bool) : BitString.lsbValue [b] = b.toNat := BitString.lsbValue_singleton b
example : BitString.lsbValue (Nat.bits 6) = 6 := BitString.lsbValue_bits 6

/-! ## A concrete machine -/

/-- In state `0`, write the flipped input bit, move the work head left and the input head right;
at the end of the input, turn the work head around and go to state `1`. In state `1`, emit the work
symbol and move right; halt at a blank. -/
def revFlip (q : Fin 2) (a : Option Bool) (s : Fin 1 → Option Bool) : Action 1 Bool (Fin 2) :=
  if q = 0 then
    match a with
    | some b => ⟨1, fun _ => (some (some !b), -1), none, some 0⟩
    | none => ⟨0, fun _ => (none, 1), none, some 1⟩
  else
    match s 0 with
    | some c => ⟨0, fun _ => (none, 1), some c, some 1⟩
    | none => ⟨0, fun _ => (none, 0), none, none⟩

/-- The machine with transition function `revFlip`, starting in state `0`. -/
noncomputable def revFlipTM : MultiTapeTM 1 Bool (Fin 2) := .ofTr 0 revFlip

/-- The simulator of `revFlip`, with the states numbered by themselves. -/
def revFlipProgram : Program .additive (regs 1) := simProgram revFlip 0 (Equiv.refl _)

/-- On `[true, false, false]` the machine outputs `[true, true, false]`, read as `3`; the run of
`8` machine steps takes `196` instructions. -/
theorem revFlipProgram_run :
    run 16 revFlipProgram 1000 (State.init [1, 0, 0]) = some (3, 196) := by
  decide +kernel

example : Executes 16 revFlipProgram (State.init ([true, false, false].map Bool.toNat)) 3 196 :=
  .of_run revFlipProgram_run

/-- The instruction count is within the bound for a run of `8` steps. -/
example : 196 ≤ simTime 1 2 8 := by decide

/-- On the empty input the machine halts after `2` steps with empty output. -/
example : run 16 revFlipProgram 1000 (State.init []) = some (0, 49) := by decide +kernel

/-- On `[false, true, true, false, true]` the output is `[false, true, false, false, true]`,
read as `18`. -/
example : run 16 revFlipProgram 1000 (State.init [0, 1, 1, 0, 1]) = some (18, 292) := by
  decide +kernel

/-! ## Two work tapes -/

/-- In state `0`, copy the input bit rightward on tape `0` and leftward on tape `1`; at the end of
the input, turn both heads around. In state `1`, emit the conjunction of the two work symbols, which
agree, and move the heads apart again; halt when either reads a blank. The output is the input
reversed. -/
def mirror (q : Fin 2) (a : Option Bool) (s : Fin 2 → Option Bool) : Action 2 Bool (Fin 2) :=
  if q = 0 then
    match a with
    | some b => ⟨1, ![(some (some b), 1), (some (some b), -1)], none, some 0⟩
    | none => ⟨0, ![(none, -1), (none, 1)], none, some 1⟩
  else
    match s 0, s 1 with
    | some x, some y => ⟨0, ![(none, -1), (none, 1)], some (x && y), some 1⟩
    | _, _ => ⟨0, ![(none, 0), (none, 0)], none, none⟩

/-- The simulator of `mirror`. -/
def mirrorProgram : Program .additive (regs 2) := simProgram mirror 0 (Equiv.refl _)

/-- On `[true, false, false]` the output is `[false, false, true]`, read as `4`, after `8` machine
steps. -/
example : run 32 mirrorProgram 2000 (State.init [1, 0, 0]) = some (4, 253) := by decide +kernel

example : 253 ≤ simTime 2 2 8 := by decide

/-- On `[true, true, false, true]` the output is `[true, false, true, true]`, read as `13`. -/
example : run 32 mirrorProgram 2000 (State.init [1, 1, 0, 1]) = some (13, 323) := by
  decide +kernel

/-! ## The headline theorems -/

/-- The simulation theorem for `revFlipTM` on every input it finishes. -/
example {inp : List Bool} {t w : ℕ}
    (ht : (revFlipTM.runFrom (revFlipTM.initCfg inp) t).state = none)
    (hw : simBound 1 2 inp.length t < 2 ^ w)
    (hout : (revFlipTM.runFrom (revFlipTM.initCfg inp) t).output.length < w) :
    ∃ n ≤ simTime 1 2 t, Executes w revFlipProgram (State.init (inp.map Bool.toNat))
      (BitString.lsbValue (revFlipTM.runFrom (revFlipTM.initCfg inp) t).output) n :=
  executes_simProgram (fun q a s => MultiTapeTM.tr_ofTr 0 revFlip q a s) (Equiv.refl _) ht hw hout

/-- The identity on binary numbers, computable in polynomial time by a machine, is computed by a
uniform word-RAM program from the bits of its input. -/
example : ∃ (r : ℕ) (p : Program .additive r) (T W : ℕ → ℕ), PolynomiallyBounded T ∧
    PolynomiallyBounded W ∧
      p.ComputesInTime (fun _ (v : ℕ) => (MultiTapeTM.encNat v).map Bool.toNat)
        (fun v _ => T (MultiTapeTM.encNat v).length)
        (fun v w => W (MultiTapeTM.encNat v).length ≤ w) id :=
  (MultiTapeTM.ComputableInPolyTime.id' (encIn := MultiTapeTM.encNat)).exists_wordRAM_nat

end ComplexityTests.WordRAMOfTuring
