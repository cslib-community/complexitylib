/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.FunctionTime.WordRAM

/-!
# Explicit-overhead word-RAM simulation clients

The additive primitives are quadratic, and the counted initialization fold builds the memory of
`State.init`. A two-instruction additive program returning the input length, on the bits of the
input at logarithmic word size, puts the length function in an explicit `FTIME` class; a
two-branch additive decider puts emptiness in an explicit `DTIME` class. Both go through
`Program.ComputesInTime.computableInO_of_width_additive`, whose hypotheses these clients satisfy.
-/

namespace ComplexityTests.WordRAMTuringOverhead

open Cslib.WordRAM Turing.MultiTapeTM Cslib.Complexity

/-! ## Primitives and initialization -/

/-- The additive primitives are quadratic, so the simulator's exponent is `max 3 2 = 3`. -/
example : Basis.additive.quadraticPrimitives.HasDegree 2 :=
  Basis.additive.quadraticPrimitives_hasDegree

/-- The counted fold builds the stored cells of `State.init`. -/
example : initEntries [5, 7] = [(0, 2), (1, 5), (2, 7)] := by
  rw [initEntries_eq_foldl]
  rfl

/-- The fits test agrees with `v < 2 ^ w`: `5` fits three bits but not two. -/
example : Fits 3 5 ∧ ¬Fits 2 5 := by decide

/-! ## A constant clock -/

/-- A constant time bound is computable in linear time. -/
theorem const_mem_FTIME (v : ℕ) :
    (fun _ : List Bool => v) ∈ FTIME encBits encNat (fun n => n + 1) := by
  obtain ⟨c, hc, -⟩ := (ComputableInDegree.const (encIn := encBits) (encMid := encNat) v).inO
  exact ⟨c, c, fun n => c * ((n + 1) + 1),
    hc.mono (fun l => by simp [Nat.mul_add]) (fun l => by simp)⟩

/-! ## A function: the input length -/

/-- Load the length from address `0` and return it. -/
def lengthProgram : Program .additive 1 := [.op (.load 0 0), .halt 0]

theorem lengthProgram_executes (w : ℕ) (l : List ℕ) :
    Executes w lengthProgram (.init l) l.length 2 := by
  refine Executes.head (t := ⟨1, (Data.init l).set 0 l.length⟩) ?_ (Executes.halt ?_)
  · simp [Next, Cslib.WordRAM.step, lengthProgram, State.init]
  · simp [Cslib.WordRAM.step, lengthProgram]

theorem lengthProgram_computesInTime :
    lengthProgram.ComputesInTime (fun _ (l : List Bool) => l.map Bool.toNat) (fun _ _ => 2)
      (fun l w => logWidth 1 l.length ≤ w) List.length :=
  fun l w _ _ => ⟨2, by simpa only [List.length_map] using
    lengthProgram_executes w (l.map Bool.toNat), le_rfl⟩

/-- **The length of a bit list is in an explicit function-time class**, through the two-instruction
additive program at logarithmic word size. -/
example : List.length ∈ FTIME encBits encNat
    (fun n => (n + 1) + (n + 2 + 1) ^ 4 * (1 * (Nat.size n + 1) + 1) ^ 3) :=
  lengthProgram_computesInTime.mem_FTIME (encIn := encBits) (T := fun _ => 2) le_rfl
    (const_mem_FTIME 2)

/-! ## A decision problem: emptiness -/

/-- Return `1` exactly when the input is empty, branching on its length. -/
def emptyProgram : Program .additive 2 :=
  [.op (.load 0 0), .branch (.eq 0 1) 3, .halt 1, .op (.const 1 1), .halt 1]

theorem emptyProgram_decidesInTime :
    emptyProgram.DecidesInTime (fun _ (l : List Bool) => l.map Bool.toNat) {l | l = []}
      (fun _ _ => 4) (fun l w => logWidth 1 l.length ≤ w) := by
  intro l w hw _
  have hw1 : 1 ≤ w := le_trans (by simp [logWidth]) hw
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

/-- **Emptiness of a bit list is in an explicit `DTIME` class**, through the additive decider at
logarithmic word size. -/
example : {l : List Bool | l = []} ∈ DTIME encBits
    (fun n => (n + 1) + (n + 4 + 1) ^ 4 * (1 * (Nat.size n + 1) + 1) ^ 3) :=
  emptyProgram_decidesInTime.mem_DTIME (encIn := encBits) (T := fun _ => 4) le_rfl
    (const_mem_FTIME 4)

end ComplexityTests.WordRAMTuringOverhead
