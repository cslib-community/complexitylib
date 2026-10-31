/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Complexity.Classes.LogSpace.Savitch
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Savitch

/-!
# Tests: Savitch's theorem in space `log² n`

Words of a fixed width and the start word written as `(x + 2 ^ W).bits.dropLast`; the counting
phase of the query machine; the recursion deciding acceptance for a machine without work tapes
that accepts every input, so that the hypotheses of the machine-level theorem are satisfiable; and
the class inclusions `NL ⊆ DSPACE(log² n)` and `RL ⊆ DSPACE(log² n)` on concrete problems.
-/

namespace ComplexityTests.LogSpaceSavitch

open Cslib.Turing Turing Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeNTM.ConfigurationGraph Turing.MultiTapeNTM.LogSquareSavitch
open Cslib.BitString (lowBits)

/-! ### Words of a fixed width -/

example : lowBits 4 5 = [true, false, true, false] := by decide
example : (5 + 2 ^ 4).bits.dropLast = lowBits 4 5 := by decide
example : ofBits (lowBits 6 37) = 37 := by decide
example : (lowBits 3 0, lowBits 0 0) = ([false, false, false], []) := by decide

/-! ### A machine accepting every input -/

private def acceptAction : Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := some true, state := none }

private def acceptMachine : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ a := a = acceptAction

private theorem accepts_acceptMachine (w : List Bool) : acceptMachine.Accepts w := by
  have hstep : acceptMachine.Step (acceptMachine.initCfg w)
      (acceptAction.apply (acceptMachine.initCfg w)) := ⟨acceptAction, rfl, rfl⟩
  refine ⟨⟨(RelSeries.singleton _ _).cons (acceptMachine.initCfg w) hstep, rfl⟩, ?_, ?_⟩ <;>
    simp [acceptAction]

-- While counting, the query machine holds the number of input bits read, and at the end of the
-- input it starts the recursion.
example (D : ℕ) : (machine acceptMachine D).run [true, false, true] 2 = (2, false, idle) :=
  run_of_le _ (by decide)

example (D : ℕ) :
    (machine acceptMachine D).run [true, false] 3 = (2, true, initRound acceptMachine D 2) :=
  run_length_succ [true, false]

/-- The recursion on the graph on words decides acceptance, here of every input. -/
example (w : List Bool) :
    Cslib.Reachability.reach (inputEdge acceptMachine (radix (radixExponent Unit 0) w.length) w)
      (width 0 (radix (radixExponent Unit 0) w.length))
      (width 0 (radix (radixExponent Unit 0) w.length))
      (lowBits (width 0 (radix (radixExponent Unit 0) w.length))
        (startID acceptMachine (radix (radixExponent Unit 0) w.length)))
      (List.replicate (width 0 (radix (radixExponent Unit 0) w.length)) true) = true :=
  (reach_eq_true_iff (MultiTapeNTM.runsInSpace_zero_tapes _ _ _)).mpr (accepts_acceptMachine w)

/-- The machine-level theorem applies to a concrete recognizer. -/
example : ∃ t c', DecidableInTimeAndSpace (Set.univ : Set (List Bool)) encBits t
    fun w => c' * (Nat.log2 (encBits w).length + 1) ^ 2 :=
  MultiTapeNTM.exists_decidableInTimeAndSpace_log_sq (ntm := acceptMachine) (c := 0)
    fun w => ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, by simpa using accepts_acceptMachine w⟩

example : (Set.univ : Set (List Bool)) ∈ DSPACE encBits fun n => Nat.log2 n ^ 2 :=
  mem_DSPACE_log2_sq_of_recognizesInSpace (ntm := acceptMachine) (c := 0)
    fun w => ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, by simpa using accepts_acceptMachine w⟩

/-! ### The class inclusions -/

example {α : Type} (enc : α ↪ List Bool) : NL enc ⊆ DSPACE enc fun n => Nat.log2 n ^ 2 :=
  NL_subset_DSPACE_log2_sq

example {α : Type} (enc : α ↪ List Bool) : RL enc ⊆ DSPACE enc fun n => Nat.log2 n ^ 2 :=
  RL_subset_DSPACE_log2_sq

/-- Every problem in `L` is in `DSPACE(log² n)` through `RL`. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ L enc) :
    A ∈ DSPACE enc fun n => Nat.log2 n ^ 2 :=
  RL_subset_DSPACE_log2_sq (L_subset_RL h)

end ComplexityTests.LogSpaceSavitch
