/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Kilian.Micali

/-!
# Tests for Micali's computationally sound proofs in the random oracle model

1. **Oracle-program Merkle tree.** On a two-leaf tree under the identity hash, `merkleRootProg`,
   `merklePathProg` and `merkleVerifyProg` agree with `merkleRoot`, `merklePath` and `merkleVerify`
   under `OracleComp.evalPure`, accept valid leaf openings
   (`evalPure_merkleVerifyProg_merklePathProg`, `merkleVerifyProg_merklePathProg`), and reject
   flipped leaf bits, wrong-length paths, and out-of-range indices.
2. **Micali prover and verifier.** On the one-bit, two-address toy PCP verifier of
   `CslibFrontierTests/Crypto/Kilian.lean`, `micaliProve` and `micaliVerify` accept the witness
   table
   `[true, true]` (and padded `[true, true, false]`) under deterministic evaluation and in the lazy
   random oracle experiment `micaliHonestGame` at every digest length `σ` and repetition count `m`
   (`micaliHonestGame_eq_pure_true`), while rejecting tampered roots, flipped opened bits,
   malformed paths, missing repetitions, and commitments to a rejected table `[true, false]`.
-/

namespace CslibFrontierTests.Crypto.Micali

open Cslib Cslib.Complexity Cslib.Crypto

/-- A deterministic Merkle hash that returns its message unchanged. -/
def idHash (x : List Bool) : List Bool := x

/-- Two one-bit leaves. -/
abbrev leaves : List (List Bool) := [[true], [false]]

-- Oracle-program Merkle root and paths agree with pure `merkleRoot` and `merklePath`.
example : OracleComp.evalPure idHash (merkleRootProg leaves) =
    merkleRoot (fun _ => idHash) [] leaves := rfl

example : OracleComp.evalPure idHash (merklePathProg leaves 0) = [[false]] := by decide
example : OracleComp.evalPure idHash (merklePathProg leaves 1) = [[true]] := by decide

-- Valid openings are accepted under both pure evaluation and the lazy random oracle.
example : OracleComp.evalPure idHash (do
    let root ← merkleRootProg leaves
    let path ← merklePathProg leaves 0
    merkleVerifyProg 1 root 0 [true] path) = true :=
  evalPure_merkleVerifyProg_merklePathProg idHash leaves (by decide)

example (dist : (q : List Bool) → PMF (MerkleHashSpec q)) :
    (OracleComp.runWith (RandomOracle.answer dist) (do
      let root ← merkleRootProg leaves
      let path ← merklePathProg leaves 1
      merkleVerifyProg 1 root 1 [false] path) (fun _ => none)).map Prod.fst = PMF.pure true :=
  merkleVerifyProg_merklePathProg dist leaves (by decide)

-- Flipping the leaf bit, giving a path of the wrong length, or using an out-of-range index is
-- rejected by `merkleVerifyProg`.
example : OracleComp.evalPure idHash (do
    let root ← merkleRootProg leaves
    let path ← merklePathProg leaves 0
    merkleVerifyProg 1 root 0 [false] path) = false := by decide

example : OracleComp.evalPure idHash (do
    let root ← merkleRootProg leaves
    merkleVerifyProg 1 root 0 [true] []) = false := by decide

example : OracleComp.evalPure idHash (do
    let root ← merkleRootProg leaves
    let path ← merklePathProg leaves 0
    merkleVerifyProg 1 root 2 [true] path) = false := by decide

/-- A toy PCP verifier: one random bit chooses the address `1000` or `5`, and the bit read must be
`true`. -/
def toyVerifier : PCPVerifier (List Bool) where
  coins _ := 1
  queries := fun (_, ρ) => [if ρ.headD false then 5 else 1000]
  verdict := fun (_, answers) => answers == [true]

/-- The statement. -/
abbrev x : List Bool := [true, false]

/-- Deterministic Fiat–Shamir oracle returning both one-bit challenges `[[false], [true]]`. -/
def fixedFS : List Bool × List Bool → List (List Bool) := fun _ => [[false], [true]]

/-- Deterministic combined oracle `(idHash, fixedFS)`. -/
abbrev toyOracle := micaliOracle idHash fixedFS

/-- Honest Micali proof on the witness table `[true, true]`. -/
abbrev honestProof : MicaliProof :=
  micaliProvePure idHash fixedFS toyVerifier x [true, true]

-- The `OracleComp` Micali prover and verifier agree with their pure counterparts.
example : OracleComp.evalPure toyOracle (micaliProve toyVerifier x [true, true]) =
    honestProof := rfl

example : OracleComp.evalPure toyOracle (micaliVerify toyVerifier x honestProof) = true := by
  decide

-- Completeness theorems apply to any accepted table, including `[true, true, false]`.
example : micaliVerifyPure idHash fixedFS toyVerifier x
    (micaliProvePure idHash fixedFS toyVerifier x [true, true, false]) = true :=
  micaliVerifyPure_micaliProvePure_eq_true (by decide) (by decide)

example : OracleComp.evalPure toyOracle (do
    let proof ← micaliProve toyVerifier x [true, true, false]
    micaliVerify toyVerifier x proof) = true :=
  micaliVerify_micaliProve_eq_true (by decide) (by decide)

-- Tampering with the root, flipping an opened bit, giving a wrong-length Merkle path, or dropping
-- a repetition causes `micaliVerify` to reject.
example : OracleComp.evalPure toyOracle
    (micaliVerify toyVerifier x ⟨[], honestProof.response⟩) = false := by decide

example : OracleComp.evalPure toyOracle
    (micaliVerify toyVerifier x
      ⟨honestProof.root,
        [honestProof.response.getD 0 [],
         [⟨false, ((honestProof.response.getD 1 []).getD 0 ⟨false, []⟩).path⟩]]⟩) = false := by
  decide

example : OracleComp.evalPure toyOracle
    (micaliVerify toyVerifier x
      ⟨honestProof.root, [honestProof.response.getD 0 [], [⟨true, []⟩]]⟩) = false := by
  decide

example : OracleComp.evalPure toyOracle
    (micaliVerify toyVerifier x
      ⟨honestProof.root, [honestProof.response.getD 0 []]⟩) = false := by
  decide

-- Committing honestly to a table `[true, false]` that the PCP verifier rejects is rejected when
-- the Fiat–Shamir oracle includes the challenge `[true]` that inspects the `false` entry.
example : OracleComp.evalPure toyOracle (do
    let proof ← micaliProve toyVerifier x [true, false]
    micaliVerify toyVerifier x proof) = false := by decide

-- Perfect completeness in the random oracle model at every digest length `σ` and repetition
-- count `m`.
example (σ m : ℕ) :
    micaliHonestGame toyVerifier x [true, true] σ m = PMF.pure true :=
  micaliHonestGame_eq_pure_true toyVerifier (by decide) σ m

end CslibFrontierTests.Crypto.Micali
