/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter

/-!
# Tests for deterministic poly(n, 2^d) refuter algorithm
-/

namespace CslibFrontierTests

open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.AffineDisperser4n
open Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Circuits Cslib.BitString

-- TODO: add concrete tests for refute

end CslibFrontierTests

private def proj4Circuit : Circuit (fullSignature 2 Bool) 4 1 :=
  ⟨Program.empty, fun _ => Wire.input ⟨0, by decide⟩⟩

private def dummyDisperser : BitString 4 → Bool :=
  fun _ => true

#eval refute proj4Circuit dummyDisperser
