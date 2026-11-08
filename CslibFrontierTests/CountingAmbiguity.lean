/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.UP.Machine
public import CslibFrontier.Computability.Complexity.Classes.FewP.Machine

/-!
Native ambiguity clients distinguish accepting from total branch counts, duplicate occurrences
from distinct endpoints, and first halting from clock padding. Every machine has fixed finite
control and a concrete nonblocking instance. Multiple accepting paths of one machine do not
claim that its language lies outside UP.
-/

@[expose] public section

namespace ComplexityTests.CountingAmbiguity

open Cslib Turing Turing.MultiTapeTM Turing.MultiTapeCTM

def halt (bit : Bool) : Turing.Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }

-- At a leading true bit, `copies` occurrences accept. Two other occurrences always reject.
def machine (copies : ℕ) : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ symbol _ _ :=
    ((List.replicate copies (symbol == some true)) ++ [false, false]).map
      (fun bit => MultiTapeMachine.Action.emptyOracleEquiv.symm (halt bit))

theorem nonblocking (copies : ℕ) : (machine copies).Nonblocking := by
  intro state symbol work
  simp [machine]

theorem runList_one (copies : ℕ) (input : List Bool) :
    (machine copies).runList 1 (Cfg.init () input) =
      ((List.replicate copies (input.head? == some true)) ++ [false, false]).map
        (fun bit => (halt bit).apply (Cfg.init () input)) := by
  rw [runList_succ _ _ 0 () rfl]
  cases input <;> simp [actions, machine, Cfg.inputSymbol, Cfg.init, List.flatMap_replicate]

theorem haltsWithin_one (copies : ℕ) (input : List Bool) :
    (machine copies).HaltsWithin 1 (Cfg.init () input) := by
  apply haltsWithin_of_halted _ (nonblocking copies).actions_ne_nil
  intro final hfinal
  rw [runList_one] at hfinal
  obtain ⟨bit, _, rfl⟩ := List.mem_map.mp hfinal
  rfl

theorem accepting_count (copies : ℕ) (input : List Bool) :
    (machine copies).acceptCount 1 (Cfg.init () input) =
      if input.head? = some true then copies else 0 := by
  rw [acceptCount, (haltsWithin_one copies input).branchCount_eq_countP, runList_one]
  simp [halt, Turing.Action.apply, List.countP_replicate]

theorem rejecting_count (copies : ℕ) (input : List Bool) :
    (machine copies).rejectCount 1 (Cfg.init () input) =
      (if input.head? = some true then 0 else copies) + 2 := by
  rw [rejectCount, (haltsWithin_one copies input).branchCount_eq_countP, runList_one]
  simp [halt, Turing.Action.apply, List.countP_replicate]

-- Two equal rejecting successors do not violate unambiguity of acceptance.
example : (machine 1).acceptCount 1 (Cfg.init () [true]) = 1 := by
  rw [accepting_count]
  rfl

example : (machine 1).rejectCount 1 (Cfg.init () [true]) = 2 := by
  rw [rejecting_count]
  rfl

-- No leading true bit means zero acceptance, including the empty input.
example : (machine 1).acceptCount 1 (Cfg.init () []) = 0 := by
  rw [accepting_count]
  rfl

-- Repeated equal accepting actions count separately; this machine is not unambiguous.
example : (machine 3).acceptCount 1 (Cfg.init () [true]) = 3 := by
  rw [accepting_count]
  rfl

example : ¬(machine 3).acceptCount 1 (Cfg.init () [true]) ≤ 1 := by
  rw [accepting_count]
  decide

-- Every branch halts after one instruction; a larger clock creates no additional choices.
example (copies padding : ℕ) (input : List Bool) :
    (machine copies).acceptCount (1 + padding) (Cfg.init () input) =
      if input.head? = some true then copies else 0 := by
  exact ((haltsWithin_one copies input).branchCount_eq (by lia) _).trans
    (accepting_count copies input)

example : {input : List Bool | input.head? = some true} ∈ Complexity.UP encBits := by
  apply Complexity.mem_UP_iff_exists_machine.mpr
  refine ⟨0, Unit, inferInstance, machine 1, 1, nonblocking 1, fun input => ?_⟩
  simp only [Polynomial.eval_one, encBits_apply]
  refine ⟨haltsWithin_one 1 input, ?_, ?_⟩
  · rw [accepting_count]
    split <;> lia
  · rw [accepting_count]
    simp

-- The same nonconstant language has a genuinely three-accepting native FewP witness.
example : {input : List Bool | input.head? = some true} ∈ Complexity.FewP encBits := by
  apply Complexity.mem_FewP_iff_exists_machine.mpr
  refine ⟨0, Unit, inferInstance, machine 3, 1, Polynomial.C 3, nonblocking 3,
    fun input => ?_⟩
  simp only [Polynomial.eval_one, Polynomial.eval_C, encBits_apply]
  refine ⟨haltsWithin_one 3 input, ?_, ?_⟩
  · rw [accepting_count]
    split <;> lia
  · rw [accepting_count]
    by_cases h : input.head? = some true <;> simp [h]

-- The ambiguity polynomial may be zero although two rejecting paths remain on every input.
example : (∅ : Set (List Bool)) ∈ Complexity.FewP encBits := by
  apply Complexity.mem_FewP_iff_exists_machine.mpr
  refine ⟨0, Unit, inferInstance, machine 0, 1, 0, nonblocking 0, fun input => ?_⟩
  simp only [Polynomial.eval_one, Polynomial.eval_zero, encBits_apply]
  refine ⟨haltsWithin_one 0 input, ?_, ?_⟩ <;> rw [accepting_count] <;> simp

end ComplexityTests.CountingAmbiguity
