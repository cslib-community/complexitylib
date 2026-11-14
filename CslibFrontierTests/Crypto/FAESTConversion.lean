/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of a candidate module)

public import CslibFrontier.Crypto.Protocols.FAEST.Conversion

/-!
# FAEST v3 conversion-to-VOLE clients

These clients exercise two levels of Figure 5.6 with a nonzero hidden index, check the exact
prover and verifier columns, and instantiate the shared binary `VOLECorrelation.Valid` relation.
-/

public section

namespace CslibFrontierTests.Crypto.FAESTConversion

open Cslib Cslib.Crypto.FAEST Cslib.Crypto.Protocols.VOLE

/-- Four nonconstant expanded rows of length three. -/
def rows : Fin 4 → BitString 3 :=
  ![![true, false, false],
    ![false, true, false],
    ![false, false, true],
    ![true, true, false]]

/-- Hide leaf three, whose two little-endian challenge bits are both one. -/
def hidden : Fin 4 := ⟨3, by decide⟩

example : (BitString.equivFin 2).symm hidden = ![true, true] := by decide

-- Figure 5.6 returns `u = r₀ xor r₁ xor r₂ xor r₃`.
example : (convertExpandedRows 2 rows).u = ![false, false, true] := by decide

-- Column zero xors the odd input rows; column one xors the odd row after one pairing level.
example : (convertExpandedRows 2 rows).columns 0 = ![true, false, false] := by decide
example : (convertExpandedRows 2 rows).columns 1 = ![true, true, true] := by decide

-- With hidden index three, the verifier receives rows `[0, r₂, r₁, r₀]`.
example : verifierRows (d := 2) rows hidden =
    ![![false, false, false],
      ![false, false, true],
      ![false, true, false],
      ![true, false, false]] := by
  decide

-- Both verifier columns equal the prover column xor `u`, since both challenge bits are one.
example : (convertExpandedRows 2 (verifierRows (d := 2) rows hidden)).columns 0 =
    ![true, false, true] := by
  decide

example : (convertExpandedRows 2 (verifierRows (d := 2) rows hidden)).columns 1 =
    ![true, true, false] := by
  decide

example : (conversionCorrelation (d := 2) rows hidden 0).Valid :=
  conversionCorrelation_valid (d := 2) rows hidden 0

/-- Altering the receiver column destroys the shared VOLE invariant in this concrete instance. -/
def alteredCorrelation : VOLECorrelation Bool 3 :=
  { conversionCorrelation (d := 2) rows hidden 0 with w := fun _ => false }

example : ¬alteredCorrelation.Valid := by decide

end CslibFrontierTests.Crypto.FAESTConversion
