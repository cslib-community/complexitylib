/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.LogSpace
import Complexity.Computability.Complexity.Classes.LogSpace.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming

/-! Logarithmic space: a nontrivial problem in `L` decided in constant workspace, complements,
reductions and composition, a nondeterministic machine with a branch running forever, the
bounds at inputs of length zero and one, codes of views without their input, and breadth-first
search on small graphs. -/

namespace ComplexityTests.LogSpace

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### The logarithmic bound at short inputs -/

/-- Inputs of length zero and one are both granted `c` cells: each work tape costs a cell. -/
example (c : ℕ) :
    c * (Nat.log2 ([] : List Bool).length + 1) = c ∧
    c * (Nat.log2 [true].length + 1) = c := by
  simp

/-! ### A nontrivial problem in `L`: odd parity, in constant workspace -/

/-- Whether a word has an odd number of ones. -/
private def oddOnes (word : List Bool) : Bool := word.foldl (fun b x => b ^^ x) false

private theorem oddOnes_true : oddOnes [true, false, true, true] = true := by decide

private theorem oddOnes_false : oddOnes [true, true] = false := by decide

/-- The parity fold runs with constant workspace, hence in logarithmic space. -/
private theorem computableInLogSpace_oddOnes : ComputableInLogSpace oddOnes encBits encBool := by
  obtain ⟨c, h, -⟩ := ComputableTidilyInO.foldl_bits_finite encBool (fun b x => b ^^ x) false
  exact ⟨_, c, h.computableInTimeAndSpace.mono (fun _ => le_rfl) fun _ =>
    by simpa using Nat.le_mul_of_pos_right c (Nat.succ_pos _)⟩

/-- The words with an odd number of ones. -/
private def OddOnes : Set (List Bool) := {word | oddOnes word = true}

/-- `OddOnes` and its complement lie in `L`, hence in `NL`, `P`, and `PSPACE`. -/
example :
    OddOnes ∈ L encBits ∧
    OddOnesᶜ ∈ L encBits ∧
    OddOnes ∈ NL encBits ∧
    OddOnes ∈ P encBits ∧
    OddOnes ∈ PSPACE encBits :=
  let hL : OddOnes ∈ L encBits := ⟨oddOnes, computableInLogSpace_oddOnes, fun _ => Iff.rfl⟩
  ⟨hL, compl_mem_L hL, L_subset_NL hL, NL_subset_P (L_subset_NL hL), L_subset_PSPACE hL⟩

/-- The `DSPACE(log₂)` shape of cslib pull request #767. -/
example : ∃ c₁ c₂ t, DecidableInTimeAndSpace OddOnes encBits t
    fun w => c₁ * Nat.log2 (encBits w).length + c₂ :=
  mem_L_iff.mp ⟨oddOnes, computableInLogSpace_oddOnes, fun _ => Iff.rfl⟩

/-! ### Composition and reductions -/

/-- Composition with a function on a finite type and after the identity. -/
example :
    ComputableInLogSpace (fun w => !oddOnes w) encBits encBool ∧
    ComputableInLogSpace (oddOnes ∘ fun w : List Bool => w) encBits encBool :=
  ⟨(ComputableInLogSpace.of_finite (encIn := encBool) not).comp computableInLogSpace_oddOnes,
    computableInLogSpace_oddOnes.comp .id⟩

/-- Reversal is computable in zero workspace, so it reduces `OddOnes` (and its complement, in both
logarithmic space and polynomial time) to the words whose reversal has an odd number of ones. -/
private theorem logSpaceReducible_oddOnes_reverse :
    LogSpaceReducible encBits encBits OddOnes {w | oddOnes w.reverse = true} := by
  refine ⟨List.reverse, ⟨_, 0,
    ComputableTidilyInTimeAndSpace.reverse_bits.computableInTimeAndSpace.mono (fun _ => le_rfl)
      fun _ => Nat.zero_le _⟩, fun w => ?_⟩
  simp [OddOnes]

example :
    LogSpaceReducible encBits encBits OddOnesᶜ {w | oddOnes w.reverse = true}ᶜ ∧
    PolyTimeReducible encBits encBits OddOnesᶜ {w | oddOnes w.reverse = true}ᶜ :=
  ⟨logSpaceReducible_oddOnes_reverse.compl,
    logSpaceReducible_oddOnes_reverse.compl.polyTimeReducible⟩

/-! ### A nondeterministic machine with a branch running forever -/

/-- Halt with output `[true]`. -/
private def acceptAction : Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := some true, state := none }

/-- Stay in the initial state, emitting nothing. -/
private def loopAction : Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := none, state := some false }

/-- From its only running state, either accept or loop forever. -/
private def loopOrAccept : MultiTapeNTM 0 Bool Bool where
  q₀ := false
  Tr q _ _ action := q = false ∧ (action = acceptAction ∨ action = loopAction)

private theorem accepts_loopOrAccept (input : List Bool) : loopOrAccept.Accepts input := by
  have hstep : loopOrAccept.Step (loopOrAccept.initCfg input)
      (acceptAction.apply (loopOrAccept.initCfg input)) := ⟨acceptAction, ⟨rfl, .inl rfl⟩, rfl⟩
  refine ⟨⟨(RelSeries.singleton _ _).cons (loopOrAccept.initCfg input) hstep, rfl⟩, ?_, ?_⟩ <;>
    simp [acceptAction]

/-- A branch may run forever: the machine still recognizes every word in logarithmic space, with
any space constant. -/
private theorem recognizesInSpace_loopOrAccept :
    loopOrAccept.RecognizesInSpace encBits Set.univ
      fun a => 0 * (Nat.log2 (encBits a).length + 1) :=
  fun a => ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, by simpa using accepts_loopOrAccept a⟩

/-- Breadth-first search ignores the looping branch. -/
example : (Set.univ : Set (List Bool)) ∈ P encBits :=
  mem_P_of_recognizesInSpace recognizesInSpace_loopOrAccept

/-! ### Codes of views without their input -/

/-- The initial views on two inputs of length one have the same code without their input, so the
input hypothesis of `coreCode_injective` cannot be dropped. -/
example : MultiTapeNTM.coreCode (loopOrAccept.initView [true]) =
    MultiTapeNTM.coreCode (loopOrAccept.initView [false]) := rfl

example : loopOrAccept.initView [true] ≠ loopOrAccept.initView [false] := by
  intro h
  simpa [MultiTapeNTM.initView, FiniteCfg.init] using congrArg FiniteCfg.input h

/-! ### Breadth-first search on small graphs -/

/-- A path `0 → 1 → 2 → 3`. -/
private def pathSucc (n : ℕ) : List ℕ := if n < 3 then [n + 1] else []

/-- Each round of BFS finds the next vertex, saturating on paths, cycles, and isolated vertices. -/
example :
    Reachability.search pathSucc 2 0 = [0, 1, 2] ∧
    Reachability.search pathSucc 7 0 = [0, 1, 2, 3] ∧
    Reachability.search (fun n => [(n + 1) % 3]) 5 0 = [0, 1, 2] ∧
    Reachability.search (fun _ : ℕ => []) 4 7 = [7] :=
  ⟨by decide, by decide, by decide, by decide⟩

end ComplexityTests.LogSpace
