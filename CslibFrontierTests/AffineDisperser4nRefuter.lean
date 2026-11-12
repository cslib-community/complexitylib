/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterProofs
public meta import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterProofs

/-!
# Tests for the deterministic `4n - 10d` refuter
-/

set_option linter.hashCommand false

public section

namespace CslibFrontierTests.AffineDisperser4nRefuter

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.AffineDisperser4n
open Cslib.Circuits.Boolean.SemiCircuit

/-- A `0`-gate circuit on `100` bits. -/
def proj100Circuit : Circuit (fullSignature 2 Bool) 100 1 :=
  ⟨Program.empty, fun _ => Wire.input ⟨0, by decide⟩⟩

#guard (chooseStep? (initialState proj100Circuit)).isNone

/-- There exists a genuine `11`-affine disperser on `100` bits on which `refute` produces a
disagreeing input against `proj100Circuit`. -/
theorem exists_disperser_refute_disagrees :
    ∃ f : BitString 100 → Bool, IsAffineDisperser f 11 ∧
      proj100Circuit.eval fullInterpretation (@refute 100 11 proj100Circuit f) 0 ≠
        f (@refute 100 11 proj100Circuit f) := by
  obtain ⟨f, hf⟩ := exists_isAffineDisperser (n := 100) (d := 11) (by norm_num)
  exact ⟨f, hf, refute_correct proj100Circuit f hf (by decide)⟩

/-- A nonterminal circuit on `3` bits with one XOR gate. -/
def xor3Circuit : Circuit (fullSignature 2 Bool) 3 1 :=
  ⟨Program.gate Program.empty
    ⟨FullOp.fn fun xs => xs 0 ^^ xs 1,
      fun i => if h : i.val = 0 then Wire.input ⟨0, by decide⟩ else Wire.input ⟨1, by decide⟩⟩,
    fun _ => Wire.gate ⟨0, by decide⟩⟩

#guard (chooseStep? (initialState xor3Circuit)).isSome

end CslibFrontierTests.AffineDisperser4nRefuter
