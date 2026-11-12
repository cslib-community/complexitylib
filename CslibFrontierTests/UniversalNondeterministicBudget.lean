/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.NondeterministicBudget

/-! Tests for the nondeterministic universal recognizer within a space budget. A description with
one transition, which emits `1` and halts on the empty input, is accepted within a small budget,
so the universal recognizer accepts; it is not accepted within the budget `0`, where no
configuration fits; a description without transitions accepts nothing; and the recognizer
compiles to a native machine within logarithmic space. -/

namespace CslibFrontierTests.UniversalNondeterministicBudget

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- From the initial state `0`, on the blank after the empty input, emit `1` and halt. -/
private def emitOne : Desc :=
  ⟨0, 0, [(⟨0, none, []⟩, ⟨0, [], some (eBit true), none⟩)]⟩

/-- The step of `emitOne` on the empty input, within a budget that holds the halted
configuration. -/
private theorem bStep_emitOne {b : ℕ} (hb : (eCfg ⟨none, 1, []⟩).length ≤ b) :
    BStep emitOne [] b (init emitOne, []) (⟨none, 1, []⟩, [eBit true]) :=
  ⟨⟨0, rfl, _, List.mem_singleton_self _, rfl, rfl⟩, hb⟩

/-- `emitOne` accepts the empty input within the budget `100`. -/
example : BAccepts emitOne [] 100 :=
  ⟨_, rfl, .single (bStep_emitOne (by decide))⟩

/-- So the universal recognizer accepts the empty input. -/
example : (budgetedNUniversal.withInit (nuStart emitOne 100)).Accepts [] :=
  (budgetedNUniversal_accepts_iff _ _ _).mpr ⟨_, rfl, .single (bStep_emitOne (by decide))⟩

/-- No configuration is encoded within `0` bits, so nothing is accepted within the budget `0`. -/
example (x : List ℕ) : ¬ BAccepts emitOne x 0 := by
  rintro ⟨s, -, h⟩
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨_, -, -, hb⟩
  · simp at h
  · simp [eCfg_apply] at hb

/-- A description without transitions accepts nothing, within any budget. -/
example (x : List ℕ) (b : ℕ) : ¬ BAccepts ⟨0, 0, []⟩ x b := by
  rintro ⟨s, -, h⟩
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨_, -, ⟨_, -, _, he, -⟩, -⟩
  · simp at h
  · simp at he

/-- The inputs that `emitOne` accepts within the budget `100` are recognized by a native
nondeterministic machine within logarithmic space. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
    ntm.RecognizesInSpace encBits {x | BAccepts emitOne (x.map eBit) 100}
      (fun x => c * (Nat.log2 x.length + 1)) :=
  exists_recognizesInSpace_bAccepts encBits (fun _ => emitOne) (fun _ => 100)
    (fun x => Nat.log2 x.length + 1)
    ((ComputableInSpace.constZero _).mono_le fun _ => Nat.zero_le _)
    ((ComputableInSpace.constZero _).mono_le fun _ => Nat.zero_le _) fun _ => le_rfl

end CslibFrontierTests.UniversalNondeterministicBudget
