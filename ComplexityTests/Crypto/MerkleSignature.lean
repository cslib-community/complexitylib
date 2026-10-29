/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.MerkleSignature.Security
import Complexity.Crypto.Computational.OneWayToSignature
import Complexity.Tactic.PolyTime

/-!
# Tests for Merkle signatures

Merkle signatures over Lamport's one-time scheme on the identity function, with a toy truncating
hash and two leaves: an honest signature at each leaf verifies, and changing the message, the
leaf, or naming an index outside the tree is rejected. The indexed signing oracle signs at a fresh
leaf and refuses a repeated leaf or one outside the tree. The capacity hypothesis holds for constant
depth and for depth `Nat.clog 2 (n + 1)`, whose capacity grows linearly.
-/

namespace ComplexityTests.Crypto.MerkleSignature

open Cslib Cslib.Crypto Cslib.Crypto.MerkleSignature Turing.MultiTapeTM

/-- A toy keyed hash: the first `k.length` bits of the input, padded with `false`. -/
def truncHash (k x : List Bool) : List Bool :=
  (x ++ List.replicate k.length false).take k.length

theorem length_truncHash (k x : List Bool) : (truncHash k x).length = k.length := by
  simp [truncHash]

theorem computableInPolyTime_truncHash :
    ComputableInPolyTime (fun p : List Bool × List Bool => truncHash p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold truncHash
  polytime

/-- Lamport's scheme on the identity function, a concrete (insecure) one-time scheme. -/
noncomputable abbrev lamportId : SignatureScheme :=
  lamportScheme id ComputableInPolyTime.id'

/-- Two leaves. -/
theorem hcapOne : ComputableInPolyTime (fun _ : ℕ => 2 ^ 1) encUnary encUnary :=
  ComputableInPolyTime.const _

/-- Capacity `2 ^ Nat.clog 2 (n + 1)`, between `n + 1` and `2 * n + 1`. -/
theorem hcapClog : ComputableInPolyTime (fun n => 2 ^ Nat.clog 2 (n + 1)) encUnary encUnary :=
  .of_tidy (ComputableTidilyInPolyTime.unary_pow_clog_const (by polytime) 2 2)

example : (scheme lamportId truncHash (fun n => Nat.clog 2 (n + 1)) computableInPolyTime_truncHash
    length_truncHash hcapClog).capacity 5 = 8 := by
  decide

/-! ### A run with explicit keys at `n = 4` -/

def key : List Bool := [true, false, true, false]
/-- Lamport secret words for two leaves; the identity makes them the public words too. -/
def sk₀ : List (List Bool) := (List.range 8).map fun j => [j % 2 == 1, j % 3 == 1, false, true]
def sk₁ : List (List Bool) := (List.range 8).map fun j => [true, j % 2 == 0, true, false]
def keys : List (List Bool × List Bool) :=
  [(encList encBits sk₀, encList encBits sk₀), (encList encBits sk₁, encList encBits sk₁)]

def msg : List Bool := [true, false, true, true, false]

/-- The Lamport signature on the digest of `m` with the secret words `sk`. -/
def otsOn (sk : List (List Bool)) (m : List Bool) : List Bool :=
  encList encBits ((List.range 4).map fun i =>
    sk.getD (2 * i + ((truncHash key m).getD i false).toNat) [])

def sigAt (u : ℕ) (sk : List (List Bool)) : List Bool :=
  encodeSignature (keys.getD u ([], [])).1 (otsOn sk msg)
    (merklePath truncHash key (keys.map Prod.fst) u)

-- Honest signatures at both leaves verify.
example : verify lamportId truncHash (fun _ => 1) (publicKey truncHash key keys) 0 msg
    (sigAt 0 sk₀) = true := by
  decide +kernel

example : verify lamportId truncHash (fun _ => 1) (publicKey truncHash key keys) 1 msg
    (sigAt 1 sk₁) = true := by
  decide +kernel

-- A message with another digest is rejected.
example : verify lamportId truncHash (fun _ => 1) (publicKey truncHash key keys) 0
    [false, false, true, true, false] (sigAt 0 sk₀) = false := by
  decide +kernel

-- A message with the same digest under the toy hash verifies: a collision of `truncHash`, which
-- the reduction to collision finding would output.
example : verify lamportId truncHash (fun _ => 1) (publicKey truncHash key keys) 0
    [true, false, true, true, true] (sigAt 0 sk₀) = true := by
  decide +kernel

-- The signature of leaf `0` is rejected at leaf `1`.
example : verify lamportId truncHash (fun _ => 1) (publicKey truncHash key keys) 1 msg
    (sigAt 0 sk₀) = false := by
  decide +kernel

-- At the index `0 + 2` outside the tree the same opening recomputes the root, and only the range
-- check rejects it.
example : merkleRootOfPath truncHash key (keys.getD 0 ([], [])).1 2
    (merklePath truncHash key (keys.map Prod.fst) 0) =
      merkleRoot truncHash key (keys.map Prod.fst) := by
  decide +kernel

example : verify lamportId truncHash (fun _ => 1) (publicKey truncHash key keys) 2 msg
    (sigAt 0 sk₀) = false := by
  decide +kernel

-- The signer produces exactly this signature.
example : signWith lamportId truncHash key keys 0 msg = pure (sigAt 0 sk₀) := by
  simp only [signWith, lamportId, lamportScheme, lamportSign, sigAt, otsOn, keys,
    List.getD_cons_zero, frames_encList, List.length_map,
    List.length_range, length_truncHash, sk₀]
  rfl

/-! ### The indexed signing oracle -/

/-- Merkle signatures with two leaves. -/
noncomputable abbrev twoLeaves : IndexedSignatureScheme :=
  scheme lamportId truncHash (fun _ => 1) computableInPolyTime_truncHash length_truncHash hcapOne

/-- The request word for `msg` at leaf `u`. -/
def request (u : ℕ) : Unit × List Bool := ((), encPair encUnary encBits (u, msg))

-- A fresh leaf is signed, and the request is logged.
example : twoLeaves.indexedSigningOracle 4 (secretKey key keys) (request 1) [(0, msg)] =
    (fun sig => (sig, [(1, msg), (0, msg)])) <$> sign lamportId truncHash (secretKey key keys) 1
      msg := by
  simp only [IndexedSignatureScheme.indexedSigningOracle, request,
    IndexedSignatureScheme.requestDecoder.decode_enc]
  simp [scheme]

-- A repeated leaf is refused, even for a new message: the reply is empty and the log is unchanged.
example : twoLeaves.indexedSigningOracle 4 (secretKey key keys) (request 0) [(0, [false])] =
    pure ([], [(0, [false])]) := by
  simp only [IndexedSignatureScheme.indexedSigningOracle, request,
    IndexedSignatureScheme.requestDecoder.decode_enc]
  simp [scheme]

-- So is a leaf outside the tree.
example : twoLeaves.indexedSigningOracle 4 (secretKey key keys) (request 2) [] = pure ([], []) := by
  simp only [IndexedSignatureScheme.indexedSigningOracle, request,
    IndexedSignatureScheme.requestDecoder.decode_enc]
  simp [scheme]

end ComplexityTests.Crypto.MerkleSignature
