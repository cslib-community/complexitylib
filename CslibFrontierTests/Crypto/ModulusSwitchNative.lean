/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.ModulusSwitch.Native

/-! Integer execution, binary magnitudes, variable row shapes and the existing ciphertext codec. -/

namespace ComplexityTests.Crypto.ModulusSwitchNative

open Cslib.Crypto Turing.MultiTapeTM
open scoped Matrix

/-- Negative ties use Euclidean division, matching nearest rounding towards positive infinity. -/
example : ZMod.modulusSwitchResidue 10 3 (-5) = 2 := by decide
example : ZMod.modulusSwitchResidue 10 3 (-25) = 2 := by decide
example : ZMod.modulusSwitchResidue 10 6 (-3) = 4 := by decide
example : ZMod.modulusSwitchResidue 1 6 (-123) = 0 := by decide
example : ZMod.modulusSwitchResidue 10 1 7 = 0 := by decide

/-- A 128-bit modulus and signed representative do not require enumerating their magnitudes. -/
example : ZMod.modulusSwitchResidue (2 ^ 128) (2 ^ 80) (-(2 ^ 127)) = 2 ^ 79 := by
  decide

/-- Total arithmetic behavior outside the positive-modulus semantic contract. -/
example : ZMod.modulusSwitchResidue 0 6 (-5) = 0 := by decide
example : ZMod.modulusSwitchResidue 10 0 (-5) = 0 := by decide

/-- Empty and ragged runtime rows use the same function and preserve their shapes. -/
example : modulusSwitchRows 10 6 [[], [1, 4, 7], [], [5]] = [[], [1, 2, 4], [], [3]] := by
  decide

example : modulusSwitchRows 10 6 [] = [] := by decide

private def ct : ModuleLWECiphertext 1 2 10 := (![![5, 7]], ![1, 4])

/-- The existing ciphertext extension puts `v` first, followed by the `u` rows. -/
example : (List.ofFn fun i => List.ofFn fun j => (extendCiphertext ct i j).val) =
    [[1, 4], [5, 7]] := by decide

/-- Concrete encoded output uses the existing `GeneralSIS.encodeMatrix`, with no new codec. -/
example : GeneralSIS.encodeMatrix (extendCiphertext (moduleLWEModulusSwitch 3 ct)) =
    encList (encList encNat) [[0, 1], [2, 2]] := by
  rw [← modulusSwitchRows_encodeMatrix_extendCiphertext (by decide) (by decide)]
  congr 1

/-- A pipeline of two runtime row conversions inherits a plain native certificate. Its numerical
result need not equal one direct conversion; this example asserts only the runtime guarantee. -/
example : ComputableInPolyTime
    (fun rows : List (List ℕ) => modulusSwitchRows 6 3 (modulusSwitchRows 10 6 rows))
    (encList (encList encNat)) (encList (encList encNat)) := by
  have hinput (q p : ℕ) : ComputableInPolyTime
      (fun rows : List (List ℕ) => ((q, p), rows))
      (encList (encList encNat))
      (encPair (encPair encNat encNat) (encList (encList encNat))) := by fun_prop
  have hfirst := computableInPolyTime_modulusSwitchRows.comp (hinput 10 6)
  have hsecond := computableInPolyTime_modulusSwitchRows.comp (hinput 6 3)
  have h := hsecond.comp hfirst
  simpa only [Function.comp_def] using h

end ComplexityTests.Crypto.ModulusSwitchNative
