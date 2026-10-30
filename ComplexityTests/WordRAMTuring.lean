/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.ElementDistinctness

/-!
# Word-RAM ⇒ Turing-machine simulation clients

The finite initial memory stores the input convention of `State.init` and holds only words exactly
when the input fits. A two-instruction program returning the input length transfers to
Turing-machine polynomial time through the headline theorem and through an explicit width schedule,
and a two-branch decider of emptiness transfers to `P`. Element distinctness, decided by the
linear-time word-RAM table algorithm, is in `P` together with its complement.
-/

namespace ComplexityTests.WordRAMTuring

open Cslib.WordRAM Turing.MultiTapeTM

/-! ## Initialization -/

/-- The memory of `State.init [5, 7]`: the length at `0`, then the words. -/
example : Cslib.GenericRAM.SparseMemory.entries (initMemory [5, 7]) = [(0, 2), (1, 5), (2, 7)] :=
  rfl

/-- Reads agree with `Data.init`, including the default `0` past the input. -/
example : Cslib.GenericRAM.SparseMemory.read 0 2 (initMemory [5, 7]) = 7 ∧
    Cslib.GenericRAM.SparseMemory.read 0 9 (initMemory [5, 7]) = 0 := by
  simp [read_initMemory]

/-- A fitting input gives a word-bounded initial state; at width `2` the word `5` breaks the bound,
and indeed `[5]` does not fit there. -/
example : WordBounded 3 (initState .standard 1 [5, 7]) ∧
    ¬WordBounded 2 (initState .standard 1 [5]) ∧ ¬InputFits 2 [5] := by
  refine ⟨wordBounded_initState (by decide), fun h => ?_, by decide⟩
  have := (h.entries_lt (1, 5) (by simp [initState, Cslib.GenericRAM.FiniteState.initConst,
    Cslib.GenericRAM.FiniteState.init, entries_initMemory, initEntries])).2
  norm_num at this

/-- A word list fits its own encoded length, so the width `|encList encNat l|` is always safe. -/
example : InputFits (encList encNat [5, 7]).length [5, 7] :=
  inputFits_of_length_encList_le le_rfl

/-! ## A function: the input length -/

/-- Load the length from address `0` and return it. -/
def lengthProgram : Program .standard 1 := [.op (.load 0 0), .halt 0]

/-- The program returns the input length in two instructions at every width. -/
theorem lengthProgram_executes (w : ℕ) (l : List ℕ) :
    Executes w lengthProgram (.init l) l.length 2 := by
  refine Executes.head (t := ⟨1, (Data.init l).set 0 l.length⟩) ?_ (Executes.halt ?_)
  · simp [Next, Cslib.WordRAM.step, lengthProgram, State.init]
  · simp [Cslib.WordRAM.step, lengthProgram]

theorem lengthProgram_computesInTime :
    lengthProgram.ComputesInTime (fun _ l => l) (fun _ _ => 2) (fun _ _ => True) List.length :=
  fun l w _ _ => ⟨2, lengthProgram_executes w l, le_rfl⟩

/-- The input length is computable in polynomial time on framed binary lists, through the
headline theorem. -/
example : Turing.MultiTapeTM.ComputableInPolyTime List.length (encList encNat) encNat :=
  UniformComputableInPolyTime.turingComputableInPolyTime checkedOp_polyTime
    (UniformComputableInPolyTime.of_program lengthProgram (T := fun _ => 2) (.const 2) 1
      one_pos (lengthProgram_computesInTime.mono (fun _ _ => le_rfl) fun _ _ _ => trivial))
    (PolyBounded.self.mono fun l => length_le_length_encList encNat l) (.id' (encIn := _))

/-- The same function through an explicit width schedule: the encoded input length, computed by
reading the input. -/
example : Turing.MultiTapeTM.ComputableInPolyTime List.length (encList encNat) encNat :=
  lengthProgram_computesInTime.turingComputableInPolyTime_of_width checkedOp_polyTime
    (width := fun l => (encList encNat l).length)
    (Turing.MultiTapeTM.ComputableInPolyTime.encoding_length _) (fun _ => trivial)
    (fun _ => inputFits_of_length_encList_le le_rfl) (.id' (encIn := _)) (PolyBounded.const 2)

/-! ## A decision problem: emptiness -/

/-- Return `1` exactly when the input is empty, branching on its length. -/
def emptyProgram : Program .standard 2 :=
  [.op (.load 0 0), .branch (.eq 0 1) 3, .halt 1, .op (.const 1 1), .halt 1]

theorem emptyProgram_decidesInTime :
    emptyProgram.DecidesInTime (fun _ l => l) {l : List ℕ | l = []} (fun _ _ => 4)
      (fun _ w => 1 ≤ w) := by
  intro l w hw _
  rcases l with _ | ⟨x, l⟩
  · refine ⟨1, 4, ?_, le_rfl, le_rfl, by simp⟩
    refine .of_run (fuel := 4) ?_
    have h1 : Fits w 1 := (fits_iff.mpr (Nat.one_lt_two_pow (by omega)))
    simp [run, Cslib.WordRAM.step, WordSizeDependentProgram.const, emptyProgram, Op.eval,
      State.init, Data.put, h1]
  · refine ⟨0, 3, ?_, by norm_num, by norm_num, by simp⟩
    refine .of_run (fuel := 3) ?_
    simp [run, Cslib.WordRAM.step, WordSizeDependentProgram.const, emptyProgram, Op.eval,
      State.init]

/-- Emptiness is in `P` through the word-RAM decider, with width `1 + |encList encNat l|`. -/
example : {l : List ℕ | l = []} ∈ Cslib.Complexity.P (encList encNat) :=
  emptyProgram_decidesInTime.mem_P_of_width checkedOp_polyTime
    (width := fun l => 1 + (encList encNat l).length)
    (Turing.MultiTapeTM.ComputableInPolyTime.unary_add'
      (.const 1) (Turing.MultiTapeTM.ComputableInPolyTime.encoding_length _))
    (fun _ => Nat.le_add_right 1 _)
    (fun _ => inputFits_of_length_encList_le (Nat.le_add_left _ 1)) (.id' (encIn := _))
    (PolyBounded.const 4)

/-! ## The pilot: element distinctness -/

open Cslib.Algorithms.WordRAM.ElementDistinctness in
/-- Element distinctness and its complement are in `P`, both from the word-RAM table decider. -/
example : {l : Input | l.1.Nodup} ∈ Cslib.Complexity.P inputEncoding ∧
    {l : Input | l.1.Nodup}ᶜ ∈ Cslib.Complexity.P inputEncoding :=
  ⟨nodup_mem_P, Cslib.Complexity.compl_mem_P nodup_mem_P⟩

end ComplexityTests.WordRAMTuring
