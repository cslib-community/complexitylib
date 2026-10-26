/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.GSW.DepthParameters.Scheme

/-!
GSW circuit evaluation is run on noiseless constants, on actual noisy encryptions under a key
with a nonzero error, on a depth-zero circuit and on malformed words. The scheme at the
logarithmic-depth family is then used as the base of Gentry's generic refresh, and its
native evaluator is composed with varying dimensions.
-/

namespace ComplexityTests.Crypto.GSWCircuitEvaluation

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.Homomorphic
open Cslib.Crypto.Homomorphic.GSW Cslib.Crypto.Homomorphic.GSW.DepthParameters
open Cslib.Probability Turing.MultiTapeTM

-- At `n = 1` and `w = 2` the constant one is the identity matrix `I_4`, row by row.
example : constSerialized 1 2 true =
    [true, false, false, false, false, true, false, false,
      false, false, true, false, false, false, false, true] ∧
    constSerialized 1 2 false = List.replicate 16 false := by decide +kernel

-- Noiseless constants decrypt correctly under every secret word of the declared width.
example : ∀ secret ∈ [[false, false], [true, false], [false, true], [true, true]],
    decryptSerialized 1 2 secret (constSerialized 1 2 true) = true ∧
      decryptSerialized 1 2 secret (constSerialized 1 2 false) = false := by decide +kernel

-- The compiled NAND circuit (an AND gate and a NOT gate, four NAND layers) maps noiseless
-- constants to the noiseless constant of their NAND, for all four input pairs.
example : ∀ a b : Bool, evaluateCircuit 1 2 ⟨2, nandCircuit⟩
    [constSerialized 1 2 a, constSerialized 1 2 b] = constSerialized 1 2 (!(a && b)) := by
  decide +kernel

/-- Key inputs with secret `5`, public rows `9` and `22`, and the nonzero error vector `(1, 0)`,
at `n = 1`, `m = 2`, `w = 6`. -/
private def keyInputs : SerializedKeyInputs := ([5], [[9], [22]], [1, 0])
private def publicWord : List Bool := publicMatrixSerialized 1 2 6 keyInputs
private def secretWord : List Bool := secretSerialized 1 6 keyInputs.1
private def coinsA : SerializedCoins := List.replicate 2 (List.replicate 6 [true, false])
private def coinsB : SerializedCoins := List.replicate 2 (List.replicate 6 [true, true])
private def fresh (μ : Bool) (coins : SerializedCoins) : List Bool :=
  encryptWithCoinsSerialized 1 2 6 publicWord μ coins

-- Actual encryptions carry visible error: their selected phases are `32 + 1` and `0 + 1`.
example : [fresh true coinsA, fresh false coinsA, fresh true coinsB, fresh false coinsB].map
    (decryptResidue 1 6 secretWord) = [33, 1, 33, 1] := by decide +kernel

-- One evaluated NAND layer grows the phase error to between `5` and `7`, still inside the
-- quarter-modulus margin `16`, as `BoundedError.nandSerialized` predicts (`1 + 12 * 1 = 13`).
example : [(true, true), (true, false), (false, true), (false, false)].map (fun p =>
    (evaluateLayers 1 6 [fresh p.1 coinsA, fresh p.2 coinsB] [[.nand 0 1]]).map
      (decryptResidue 1 6 secretWord)) = [[58], [27], [25], [26]] := by decide +kernel

example : ∀ a b : Bool,
    (evaluateLayers 1 6 [fresh a coinsA, fresh b coinsB] [[.nand 0 1]]).map
      (decryptSerialized 1 6 secretWord) = [!(a && b)] := by decide +kernel

-- A depth-zero circuit has no layers: its output wire is returned unchanged, even when the
-- input word is malformed.
example : evaluateCircuit 1 2 ⟨1, Circuit.wiring signature (fun _ => 0)⟩ [[true, false, true]] =
    [true, false, true] := by decide +kernel

-- Malformed or missing NAND inputs still produce a complete square word, and long copies are
-- cut to the ciphertext width.
example : (evaluateCircuit 1 2 ⟨2, nandCircuit⟩ [[true], []]).length = 16 ∧
    (evaluateLayers 1 2 [List.replicate 20 true] [[.copy 0]]).map List.length = [16] := by
  decide +kernel

-- The NAND circuit is permitted at security parameter zero, where the budget is `1024` layers.
example : scheme.permitted 0 ⟨2, nandCircuit⟩ ∧ depthBudget 0 = 1024 := by
  refine ⟨?_, by decide +kernel⟩
  change 2 * nandCircuit.depth ≤ depthBudget 0
  decide +kernel

/-- Gentry's NAND refresh, run with the actual GSW scheme and its raw-input decryption circuit,
computes NAND of the old plaintexts. The old ciphertexts need only the declared width; they may
be outputs of earlier evaluations. -/
example (security : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (scheme.keyGen security)).support)
    (secret first second : List Bool) (hsecret : secret.length = secretWidth security)
    (hfirst : first.length = ciphertextWidth security)
    (hsecond : second.length = ciphertextWidth security)
    (encryptedKey : List (List Bool))
    (hek : scheme.FreshInputs security keys.1 secret encryptedKey) (result : List Bool)
    (hresult : result ∈ (ProbComp.eval
      (Scheme.refreshNand decryptionCircuits security keys.1 encryptedKey first second)).support) :
    decryptSerialized (Parameters.dimension security) (width security) keys.2 result =
      !(decryptSerialized (Parameters.dimension security) (width security) secret first &&
        decryptSerialized (Parameters.dimension security) (width security) secret second) :=
  Scheme.decrypt_refreshNand decryptionCircuits correct bootstrappable security keys hkeys
    secret first second hsecret hfirst hsecond encryptedKey hek result hresult

-- The native evaluator composes with computed dimensions and a runtime list of ciphertexts.
example : ComputableInPolyTime (fun p : ℕ × List (List Bool) =>
    evaluateCircuit (p.1 + 1) (2 * p.1) ⟨2, nandCircuit⟩ p.2)
    (encPair encUnary (encList encBits)) encBits := by
  apply computableInPolyTime_evaluateCircuit <;> fun_prop

end ComplexityTests.Crypto.GSWCircuitEvaluation
