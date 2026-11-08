/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.RSATrapdoor
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the RSA trapdoor permutation
-/

namespace ComplexityTests.Crypto.RSATrapdoor

open Cslib Cslib.Crypto

/-- Toy RSA instance `N = 3 * 11 = 33`, `e = 3`, `d = 7` (`3 * 7 ≡ 1 [MOD 20]`). -/
def rsa33 : RSADesc :=
  ⟨((3, 11), (3, 7)), ⟨by norm_num, by norm_num, by decide, by decide, by decide⟩⟩

example : rsaEval 33 3 2 = 8 := by decide

example : rsaInvert 33 7 8 = 2 := by decide

example : rsaInvert 33 7 (rsaEval 33 3 5) = 5 := by decide

/-- info: 'Cslib.Crypto.rsaEval_bijective_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.rsaEval_bijective_fin

/-- info: 'Cslib.Crypto.computableInPolyTime_rsaEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.computableInPolyTime_rsaEval

/-- info: 'Cslib.Crypto.computableInPolyTime_rsaInvert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.computableInPolyTime_rsaInvert

end ComplexityTests.Crypto.RSATrapdoor
