/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Computational.MLDSA.Hint
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for ML-DSA hint generation and use

The standard modulus and both standardized `γ₂` families exercise positive and negative carries,
including wrap-around from the last high bucket to zero and from zero to the last bucket.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

open Cslib.Crypto.MLDSA

namespace MLDSAHintTests

private def corrections44 : Fin 4 → ZMod 8380417 := ![1, -2, 1, -1]

private def residues44 : Fin 4 → ZMod 8380417 := ![95232, 95233, 8285184, -95232]

-- The four positions are: positive carry, negative carry, positive wrap, and negative wrap.
example : makeHintVec 8380417 95232 corrections44 residues44 = fun _ => true := by
  decide +kernel

example : useHintVec 8380417 95232
    (makeHintVec 8380417 95232 corrections44 residues44) residues44 = ![1, 0, 0, 43] := by
  decide +kernel

example : useHintVec 8380417 95232
      (makeHintVec 8380417 95232 corrections44 residues44) residues44 =
    fun i => highBits 8380417 95232 (residues44 i + corrections44 i) :=
  useHintVec_makeHintVec (by decide) (by decide) (by decide) (by decide +kernel)

private def corrections65 : Fin 2 → ZMod 8380417 := ![1, -1]

private def residues65 : Fin 2 → ZMod 8380417 := ![261888, -261888]

-- The second standardized family has sixteen high buckets; the negative wrap lands at fifteen.
example : useHintVec 8380417 261888
    (makeHintVec 8380417 261888 corrections65 residues65) residues65 = ![1, 15] := by
  decide +kernel

example : useHintVec 8380417 261888
      (makeHintVec 8380417 261888 corrections65 residues65) residues65 =
    fun i => highBits 8380417 261888 (residues65 i + corrections65 i) :=
  useHintVec_makeHintVec (by decide) (by decide) (by decide) (by decide +kernel)

-- NIST's proposed correction records the strict upper bound used by `w1Encode`.
example (h : Bool) (r : ZMod 8380417) : useHint 8380417 95232 h r < 44 :=
  useHint_lt (by decide) (by decide) (by decide) h r

-- Distinct hint bits cannot produce the same adjusted high part.
example (r : ZMod 8380417) :
    Function.Injective fun h : Bool => useHint 8380417 95232 h r :=
  useHint_injective (by decide) (by decide) (by decide) r

end MLDSAHintTests
