/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterProofs

/-!
# Tests for the deterministic `4n - 10d` refuter
-/

public section

namespace CslibFrontierTests.AffineDisperser4nRefuter

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.AffineDisperser4n
open Cslib.Circuits.Boolean.SemiCircuit

/-- A `0`-gate circuit on `100` bits. -/
def proj100Circuit : Circuit (fullSignature 2 Bool) 100 1 :=
  ⟨Program.empty, fun _ => Wire.input ⟨0, by decide⟩⟩

/-- There exists a genuine `11`-affine disperser on `100` bits on which `refute` produces a
disagreeing input against `proj100Circuit`. -/
theorem exists_disperser_refute_disagrees :
    ∃ f : BitString 100 → Bool, IsAffineDisperser f 11 ∧
      proj100Circuit.eval fullInterpretation (@refute 100 11 proj100Circuit f) 0 ≠
        f (@refute 100 11 proj100Circuit f) := by
  obtain ⟨f, hf⟩ := exists_isAffineDisperser (n := 100) (d := 11) (by norm_num)
  exact ⟨f, hf, refute_correct proj100Circuit f hf (by decide)⟩

end CslibFrontierTests.AffineDisperser4nRefuter
