/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.IndexedSignature.Counter
import Complexity.Crypto.Computational.MerkleSignature.Security
import Complexity.Crypto.Computational.OneWayToSignature
import ComplexityTests.Crypto.MerkleSignature

/-!
# Tests for counter-stateful signatures

The counter signing oracle on the two-leaf Merkle scheme of
`ComplexityTests.Crypto.MerkleSignature`: the first request is signed at leaf `0` and advances the
counter, the second at leaf `1`, and the third is refused because the capacity `2` is exhausted.
The counter signature words of both leaves verify under `counterVerify`, the word of leaf `0` is
rejected on another message, and the word of leaf `0` re-indexed to leaf `1` is rejected. The
counter forger's handler forwards a request below the capacity as the indexed request at the
counter, and answers the empty word above it.
-/

namespace ComplexityTests.Crypto.CounterSignature

open Cslib Cslib.Crypto Cslib.Crypto.MerkleSignature Cslib.Crypto.IndexedSignatureScheme
  ComplexityTests.Crypto.MerkleSignature Turing.MultiTapeTM

/-- The counter signature word of leaf `u` with the secret words `sk`. -/
def counterSigAt (u : ℕ) (sk : List (List Bool)) : List Bool :=
  encPair encUnary encBits (u, sigAt u sk)

/-! ### The counter signing oracle -/

-- The first request is signed at leaf `0`, and the counter advances.
example : twoLeaves.counterSigningOracle 4 (secretKey key keys) ((), msg) (0, []) =
    (fun sig => (encPair encUnary encBits (0, sig), (1, [msg]))) <$>
      sign lamportId truncHash (secretKey key keys) 0 msg := by
  simp only [counterSigningOracle]
  simp [scheme]

-- The second request is signed at leaf `1`, whatever its message.
example : twoLeaves.counterSigningOracle 4 (secretKey key keys) ((), [false]) (1, [msg]) =
    (fun sig => (encPair encUnary encBits (1, sig), (2, [[false], msg]))) <$>
      sign lamportId truncHash (secretKey key keys) 1 [false] := by
  simp only [counterSigningOracle]
  simp [scheme]

-- The third request is refused: the reply is empty and the state is unchanged.
example : twoLeaves.counterSigningOracle 4 (secretKey key keys) ((), [true]) (2, [[false], msg]) =
    pure ([], (2, [[false], msg])) := by
  simp only [counterSigningOracle]
  simp [scheme]

/-! ### Counter verification -/

-- The honest counter signature words of both leaves verify.
example : twoLeaves.counterVerify (publicKey truncHash key keys) msg (counterSigAt 0 sk₀) =
    true := by
  decide +kernel

example : twoLeaves.counterVerify (publicKey truncHash key keys) msg (counterSigAt 1 sk₁) =
    true := by
  decide +kernel

-- A message with another digest is rejected.
example : twoLeaves.counterVerify (publicKey truncHash key keys) [false, false, true, true, false]
    (counterSigAt 0 sk₀) = false := by
  decide +kernel

-- The signature of leaf `0` re-indexed to leaf `1` is rejected.
example : twoLeaves.counterVerify (publicKey truncHash key keys) msg
    (encPair encUnary encBits (1, sigAt 0 sk₀)) = false := by
  decide +kernel

-- Completeness, as a theorem instance: the counter word of any supported signature at a leaf below
-- the capacity verifies.
example (keys' : List Bool × List Bool)
    (hkeys : keys' ∈ (ProbComp.eval (twoLeaves.keyGen 4)).support) (sig : List Bool)
    (hsig : sig ∈ (ProbComp.eval (twoLeaves.sign keys'.2 1 msg)).support) :
    twoLeaves.counterVerify keys'.1 msg (encPair encUnary encBits (1, sig)) = true :=
  counterVerify_sign 4 keys' hkeys (by decide) msg sig hsig

/-! ### The counter forger's handler -/

-- Below the capacity, the handler asks the indexed oracle to sign at the counter and advances.
example : twoLeaves.counterHandler 4 (fun _ L => L + 100) ((), msg) 1 =
    (fun sig => (encPair encUnary encBits (1, sig), 2)) <$>
      (List.take (msg.length + 100) <$>
        ProbOracleComp.query ((), encPair encUnary encBits (1, msg))) := by
  simp only [counterHandler]
  simp [scheme]

-- At the capacity, the handler answers the empty word without any query.
example : twoLeaves.counterHandler 4 (fun _ L => L + 100) ((), msg) 2 = pure ([], 2) := by
  simp only [counterHandler]
  simp [scheme]

/-! ### Security, as instances -/

-- Indexed security of any indexed scheme transfers to its counter-stateful use.
example (S : IndexedSignatureScheme) (h : S.IndexedEUFCMA) : S.CounterEUFCMA :=
  h.counterEUFCMA

-- Merkle signatures over a one-way function and a hash family are counter EUF-CMA secure.
example {f : List Bool → List Bool} (hf : OneWay f) {H : List Bool → List Bool → List Bool}
    (hH : HashFamily H) :
    ∃ S : IndexedSignatureScheme, (∀ n, S.capacity n = 2 ^ Nat.clog 2 (n + 1)) ∧
      S.CounterEUFCMA :=
  hf.exists_counterEUFCMA hH hcapClog

end ComplexityTests.Crypto.CounterSignature
