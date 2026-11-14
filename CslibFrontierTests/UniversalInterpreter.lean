/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.SpecializeInterpreter

/-! Checked clients for the encoded universal interpreter and its componentwise resources. -/

public section

namespace CslibFrontierTests.UniversalInterpreter

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- Move past the outer frame's first bit, then emit that bit and halt. -/
def readFirstProgramBit : Desc :=
  ⟨0, 0,
    [(⟨0, some 1, []⟩, ⟨.pos, [], none, some 1⟩),
     (⟨1, some 0, []⟩, ⟨.zero, [], some 0, none⟩),
     (⟨1, some 1, []⟩, ⟨.zero, [], some 1, none⟩)]⟩

/-- A two-bit description with no work tapes. -/
def zeroTapeProgram : Desc := ⟨0, 0, []⟩

/-- A four-bit description with one work tape. -/
def oneTapeProgram : Desc := ⟨1, 0, []⟩

/-- The selected interpreter has a separately charged static description and realizes
`Universal.universal` at its certified clock. -/
example (i : Desc × List ℕ × ℕ) :
    descLen encodedUniversalInterpreter ≤ encodedUniversalInterpreterSizeBound ∧
    universal (encodedUniversalInterpreter, (eIn i).map eBit,
        encodedUniversalInterpreterTime i) =
      ((eOut (universal i)).map eBit, true) :=
  ⟨descLen_encodedUniversalInterpreter_le,
    universal_encodedUniversalInterpreter i _ le_rfl⟩

/-- Even with zero controller steps, the generated program and unary request are nonconstant in
the embedded program; the selected native online bound therefore changes as well. -/
example :
    let zero := specializeInterpreterResources readFirstProgramBit zeroTapeProgram [] 0
    let one := specializeInterpreterResources readFirstProgramBit oneTapeProgram [] 0
    zero.programBits < one.programBits ∧ zero.requestBits < one.requestBits ∧
      zero.onlineSteps < one.onlineSteps := by
  have hprogram :
      specializeSize readFirstProgramBit zeroTapeProgram <
        specializeSize readFirstProgramBit oneTapeProgram := by
    have hlen : descLen zeroTapeProgram < descLen oneTapeProgram := by decide
    unfold specializeSize
    exact Nat.mul_lt_mul_of_pos_left
      (Nat.pow_lt_pow_left (by omega) (by norm_num)) (by norm_num)
  have hprepare :
      specializePrepareSteps zeroTapeProgram [] < specializePrepareSteps oneTapeProgram [] := by
    have hlen : descLen zeroTapeProgram < descLen oneTapeProgram := by decide
    unfold specializePrepareSteps
    omega
  have hrequest :
      specializeInterpreterInputBound readFirstProgramBit zeroTapeProgram [] 0 <
        specializeInterpreterInputBound readFirstProgramBit oneTapeProgram [] 0 := by
    unfold specializeInterpreterInputBound
    omega
  have hpower :
      100025 *
          (specializeInterpreterInputBound readFirstProgramBit zeroTapeProgram [] 0 + 1) ^ 6 + 1 <
        100025 *
          (specializeInterpreterInputBound readFirstProgramBit oneTapeProgram [] 0 + 1) ^ 6 + 1 :=
    by
      generalize specializeInterpreterInputBound readFirstProgramBit zeroTapeProgram [] 0 =
        zeroRequest at hrequest ⊢
      generalize specializeInterpreterInputBound readFirstProgramBit oneTapeProgram [] 0 =
        oneRequest at hrequest ⊢
      have hpow := Nat.pow_lt_pow_left (Nat.add_lt_add_right hrequest 1)
        (by norm_num : 6 ≠ 0)
      exact Nat.add_lt_add_right
        (Nat.mul_lt_mul_of_pos_left hpow (by norm_num : 0 < 100025)) 1
  simp only [specializeInterpreterResources]
  exact ⟨hprogram, hrequest,
    Nat.mul_lt_mul_of_pos_left hpower encodedUniversalInterpreterFactor_pos⟩

/-- The componentwise theorem applies at the zero-controller-clock edge without charging the
offline compiler to the run. -/
example :
    (specializeInterpreterResources readFirstProgramBit oneTapeProgram [] 0).Certifies
      readFirstProgramBit oneTapeProgram [] 0 :=
  specializeInterpreterResources_certifies _ _ _ _

/-- At zero controller steps the outer interpreter still performs the generated description's
online preparation, then returns the encoded zero-step controller result and halts. -/
example :
    universal (encodedUniversalInterpreter,
        (eIn (specializeInterpreterRequest readFirstProgramBit oneTapeProgram [] 0)).map eBit,
        (specializeInterpreterResources readFirstProgramBit oneTapeProgram [] 0).onlineSteps) =
      ([0, 0], true) := by
  calc
    _ = ((eOut (universal
        (readFirstProgramBit, (frame (eDesc oneTapeProgram)).map eBit, 0))).map eBit, true) := by
      simpa using universal_encodedUniversalInterpreter_specialize
        readFirstProgramBit oneTapeProgram [] 0
    _ = ([0, 0], true) := by decide

end CslibFrontierTests.UniversalInterpreter
