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

namespace CslibFrontierTests.Crypto.RSATrapdoor

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-- Toy RSA instance `N = 3 * 11 = 33`, `e = 3`, `d = 7` (`3 * 7 ≡ 1 [MOD 20]`). -/
def rsa33 : RSADesc :=
  { p := 3, q := 11, e := 3, d := 7, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

example : rsaEval 33 3 2 = 8 := by decide

example : rsaInvert 33 7 8 = 2 := by decide

example : rsaInvert 33 7 (rsaEval 33 3 5) = 5 := by decide

/-! ### Typed evaluation and encodings -/

example : NeZero rsa33.publicKey.N := inferInstance

example : (rsa33.publicKey.eval 5 : ℕ) = 26 := by decide

/-- The public key is framed `N` followed by `e`, both in binary. -/
example (pk : RSAPublicKey) : encRSAPublicKey pk = encPair encNat encNat (pk.N, pk.e) := rfl

/-- An inverter reads the unary security parameter, the public key and the challenge in binary:
the layout of the word-level inverters on keys with `0 < N` in `rsaOneWay_iff_encoded`. -/
example (x : RSAInput) : encRSAInput x = encPair encUnary (encPair
    ((Function.Embedding.subtype fun pk : RSAPublicKey => 0 < pk.N).trans encRSAPublicKey) encNat)
    (x.secParam, ⟨x.publicKey, x.challenge.pos⟩, (x.challenge : ℕ)) :=
  rfl

/-- info: 'Cslib.Crypto.rsaEval_bijective_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.rsaEval_bijective_fin

/-- info: 'Cslib.Crypto.computableInPolyTime_rsaEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.computableInPolyTime_rsaEval

/-- info: 'Cslib.Crypto.computableInPolyTime_rsaInvert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.computableInPolyTime_rsaInvert

/-- info: 'Cslib.Crypto.rsaOneWay_iff_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.rsaOneWay_iff_encoded

end CslibFrontierTests.Crypto.RSATrapdoor
