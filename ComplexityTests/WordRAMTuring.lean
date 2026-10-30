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
and a two-branch decider of emptiness transfers to `P`. A binary number placed in one word, with
widths of at least twice its bit length admitted, can be squared without overflow; this is the
pattern for arithmetic on numeric inputs, and puts evenness in `P`. Element distinctness, decided
by the linear-time word-RAM table algorithm, is in `P` together with its complement.
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

/-! ## A binary number as one word, with a linear width schedule

A number `n` is given in binary and placed in a single word. Admitting only widths of at least
`2 · size n + 2` lets the program square it without overflow; the simulating machine computes such
a width from the length of the binary encoding. -/

/-- Register names for the evenness program. -/
abbrev one : Fin 4 := 0
/-- Register names for the evenness program. -/
abbrev x : Fin 4 := 1
/-- Register names for the evenness program. -/
abbrev two : Fin 4 := 2
/-- Register names for the evenness program. -/
abbrev ans : Fin 4 := 3

/-- Square the input word, reduce it modulo `2` and answer `1 - (n · n mod 2)`. -/
def evenSquare : Code .standard 4 :=
  ram[ one ← #1; x ← *one; x ← x * x; two ← #2; x ← x % two; ans ← one - x ]

theorem evenSquare_decidesInTime :
    (evenSquare.program ans).DecidesInTime (fun _ n => [n]) {n : ℕ | Even n} (fun _ _ => 7)
      (fun n w => 2 * Nat.size n + 2 ≤ w) := by
  refine evenSquare.decidesInTime_program (time := fun _ _ => 6) ans fun n w hw _ => ?_
  have h1 : Fits w 1 := fits_iff.mpr (Nat.one_lt_two_pow (by omega))
  have h2 : Fits w 2 := fits_iff.mpr (lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hsq : Fits w (n * n) := by
    have hn := Nat.lt_size_self n
    refine fits_iff.mpr (lt_of_lt_of_le (Nat.mul_lt_mul'' hn hn) ?_)
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmod : Fits w (n * n % 2) := h2.of_le (Nat.mod_lt _ (by norm_num)).le
  have hsub : Fits w (1 - n * n % 2) := h1.of_le (Nat.sub_le _ _)
  have hpar : n * n % 2 = n % 2 := by
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [Nat.mul_mod, h]
  have hmem : (Data.init [n] : Data 4).mem 1 = n := rfl
  refine ⟨?y, ⟨6, le_rfl, ?run⟩, ?out⟩
  case run => ram_eval [evenSquare, hmem, h1, h2, hsq, hmod, hsub]
  case out =>
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [hpar, h, Nat.even_iff]

/-- Evenness of binary naturals is in `P` through the word-RAM decider, at the width
`2 · |encNat n| + 2`. -/
example : {n : ℕ | Even n} ∈ Cslib.Complexity.P encNat :=
  evenSquare_decidesInTime.mem_P_of_width checkedOp_polyTime
    (width := fun n => 2 * (encNat n).length + 2)
    (by fun_prop) (fun n => by simp [encNat_apply, Nat.size_eq_bits_len])
    (fun n => inputFits_of_length_encList_le (by simp)) (by fun_prop)
    (PolyBounded.const 7)

/-! ## The pilot: element distinctness -/

open Cslib.Algorithms.WordRAM.ElementDistinctness in
/-- Element distinctness and its complement are in `P`, both from the word-RAM table decider. -/
example : {l : Input | l.1.Nodup} ∈ Cslib.Complexity.P inputEncoding ∧
    {l : Input | l.1.Nodup}ᶜ ∈ Cslib.Complexity.P inputEncoding :=
  ⟨nodup_mem_P, Cslib.Complexity.compl_mem_P nodup_mem_P⟩

end ComplexityTests.WordRAMTuring
