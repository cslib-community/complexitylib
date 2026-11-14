/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of a candidate module)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Specialize

/-! Executable clients for encoded-description specialization and its concrete resource maps. -/

public section

namespace CslibFrontierTests.UniversalSpecialize

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- Move past the outer frame's first bit, then emit the next input bit and halt. This makes the
client depend on the first bit of the embedded `eDesc`, rather than merely carrying unused code. -/
def readFirstProgramBit : Desc :=
  ⟨0, 0,
    [(⟨0, some 1, []⟩, ⟨.pos, [], none, some 1⟩),
     (⟨1, some 0, []⟩, ⟨.zero, [], some 0, none⟩),
     (⟨1, some 1, []⟩, ⟨.zero, [], some 1, none⟩)]⟩

/-- Its `eDesc` begins with `false`, since the number of work tapes is zero. -/
def zeroTapeProgram : Desc := ⟨0, 0, []⟩

/-- Its `eDesc` begins with `true`, since the number of work tapes is one in unary. -/
def oneTapeProgram : Desc := ⟨1, 0, []⟩

/-- The same executable controller distinguishes the two embedded program descriptions. The
specialized clocks include every preparation step and the controller's two steps. -/
example :
    universal (specialize readFirstProgramBit zeroTapeProgram, [],
      specializePrepareSteps zeroTapeProgram [] + 2) = ([0], true) ∧
    universal (specialize readFirstProgramBit oneTapeProgram, [],
      specializePrepareSteps oneTapeProgram [] + 2) = ([1], true) := by
  constructor
  · calc
      _ = universal (readFirstProgramBit,
          (frame (eDesc zeroTapeProgram) ++ []).map eBit, 2) := by
        simpa using universal_specialize readFirstProgramBit zeroTapeProgram ([] : List Bool) 2
      _ = ([0], true) := by decide
  · calc
      _ = universal (readFirstProgramBit,
          (frame (eDesc oneTapeProgram) ++ []).map eBit, 2) := by
        simpa using universal_specialize readFirstProgramBit oneTapeProgram ([] : List Bool) 2
      _ = ([1], true) := by decide

/-- Generated code and interpreter requests charge program-description length explicitly; changing
the embedded description changes both the static size bound and the exact preparation clock. -/
example :
    descLen (specialize readFirstProgramBit zeroTapeProgram) ≤
        specializeSize readFirstProgramBit zeroTapeProgram ∧
    descLen (specialize readFirstProgramBit oneTapeProgram) ≤
        specializeSize readFirstProgramBit oneTapeProgram ∧
    descLen (specialize readFirstProgramBit zeroTapeProgram) <
        descLen (specialize readFirstProgramBit oneTapeProgram) ∧
    specializeSize readFirstProgramBit zeroTapeProgram <
        specializeSize readFirstProgramBit oneTapeProgram ∧
    specializePrepareSteps zeroTapeProgram [] <
        specializePrepareSteps oneTapeProgram [] := by
  have hlen : descLen zeroTapeProgram < descLen oneTapeProgram := by decide
  -- These closed generated descriptions contain thousands of encoded bits. The scoped depth is
  -- used only to reduce their exact lengths; it does not affect any library proof or algorithm.
  have hzero : descLen (specialize readFirstProgramBit zeroTapeProgram) = 4072 := by
    -- Reduce the complete 4,072-bit closed encoding for this regression check.
    set_option maxRecDepth 20000 in decide
  have hone : descLen (specialize readFirstProgramBit oneTapeProgram) = 7540 := by
    -- Reduce the complete 7,540-bit closed encoding for this regression check.
    set_option maxRecDepth 50000 in decide
  refine ⟨descLen_specialize_le _ _, descLen_specialize_le _ _, by omega, ?_, ?_⟩
  · unfold specializeSize
    exact Nat.mul_lt_mul_of_pos_left
      (Nat.pow_lt_pow_left (by omega) (by norm_num)) (by norm_num)
  · unfold specializePrepareSteps
    omega

/-- The concrete universal-interpreter bounds are usable directly at a generated program. -/
example :
    specializeUniversalTimeFormula readFirstProgramBit oneTapeProgram [] 2 ≤
        100025 * (specializeInterpreterInputBound readFirstProgramBit oneTapeProgram [] 2 + 1) ^ 6 ∧
    specializeUniversalSpaceFormula readFirstProgramBit oneTapeProgram [] 2 ≤
        205 * (specializeInterpreterInputBound readFirstProgramBit oneTapeProgram [] 2 + 1) ^ 3 :=
  universal_specialize_resource_bounds _ _ _ _

end CslibFrontierTests.UniversalSpecialize
