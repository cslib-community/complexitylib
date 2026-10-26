/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.CollisionResistant
import Complexity.Crypto.Computational.Encryption.CCA
import ComplexityTests.Crypto.Encryption
import Mathlib.Algebra.Field.ZMod

/-!
# Tests for public-key 1CCA (`INDCCA2`) and setup-parameterized collision resistance

Two-sided nonvacuity and regression tests for `Complexity.Crypto.Computational.Encryption.CCA` and
`Complexity.Crypto.Computational.CollisionResistant`:
1. **Satisfiable `INDCCA2` instance**: a constant-ciphertext scheme satisfies `INDCCA2`.
2. **Refutable `INDCCA2` instance**: the plaintext-leaking scheme from
   `ComplexityTests.Crypto.Encryption` violates `INDCCA2` via `INDCCA2.indcpa`.
3. **Concrete `cca2Phase2Oracle` and `CCA2Adversary.IsPPT` checks**: `cca2Phase2Oracle` returns
   `[]` on the challenge ciphertext and `encOption encBool (decrypt …)` otherwise, and
   `CCA2Adversary.isPPT_ofCPA` constructs a concrete strict oracle PPT 1CCA adversary.
4. **Live Phase-2 decryption-oracle test**: for a scheme whose decryption ignores trailing bits
   (`decrypt _ _ ct := ct.head?`), a Phase-2 adversary querying `ct ++ [true] ≠ ct` bypasses the
   challenge-ciphertext guard and recovers the challenge bit with probability `1`.
5. **Refutable `CollisionResistantFor` instance over `ZMod 11`**: a constant `ZMod 11`-valued hash
   family is refuted by `not_collisionResistantForOn_of_le_succProbability`.
-/

namespace ComplexityTests.Crypto.CCA

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Encryption Turing.MultiTapeTM
open scoped NNReal

/-! ### 1. Satisfiable `INDCCA2` instance -/

/-- Trivial constant-key generator. -/
def constKeyGen (_ : ℕ) : ProbComp (List Bool × List Bool) := pure ([], [])

/-- Trivial constant-ciphertext encryption. -/
def constEncrypt (_ : ℕ) (_ : List Bool) (_ : Bool) : ProbComp (List Bool) := pure []

/-- Trivial rejecting decryption. -/
def constDecrypt (_ : ℕ) (_ : List Bool) (_ : List Bool) : Option Bool := none

/-- The constant-ciphertext scheme satisfies `INDCCA2` because the `false` and `true` experiments
are identical. -/
theorem indcca2_const : INDCCA2 constKeyGen constEncrypt constDecrypt := by
  intro adversary _
  simpa only [cca2Game, cca2GameOn, constEncrypt, Game.advantage_self] using negligible_zero

/-- Length-only word encryption (`ct = List.replicate msg.length false`). -/
def lenEncrypt (_ : ℕ) (_ : List Bool) (msg : List Bool) : ProbComp (List Bool) :=
  pure (List.replicate msg.length false)

/-- Trivial rejecting word decryption. -/
def lenDecrypt (_ : ℕ) (_ : List Bool) (_ : List Bool) : Option (List Bool) := none

/-- Under `WordINDCCA2` (`valid := fun _ _ m₀ m₁ => m₀.length == m₁.length`), a scheme whose
ciphertexts depend only on message length is secure because unequal-length challenge pairs such as
`([], [false])` are rejected by `cca2GameOn` in both experiments. -/
theorem wordINDCCA2_lenEncrypt : WordINDCCA2 constKeyGen lenEncrypt lenDecrypt := by
  intro adversary _
  have heq (n : ℕ) :
      cca2GameOn (fun _ _ (m₀ m₁ : List Bool) => m₀.length == m₁.length) encBits
        constKeyGen lenEncrypt lenDecrypt adversary false n =
      cca2GameOn (fun _ _ (m₀ m₁ : List Bool) => m₀.length == m₁.length) encBits
        constKeyGen lenEncrypt lenDecrypt adversary true n := by
    simp only [cca2GameOn, lenEncrypt]
    congr 1; funext keys
    congr 1; funext choiceOut
    by_cases hlen : (choiceOut.1.1.1.length == choiceOut.1.1.2.length) = true
    · have hl : choiceOut.1.1.1.length = choiceOut.1.1.2.length := beq_iff_eq.mp hlen
      simp [hl]
    · simp [hlen]
  simpa only [heq, Game.advantage_self] using negligible_zero

/-! ### 2. Refutable `INDCCA2` instance via `INDCCA2.indcpa` -/

/-- The plaintext-leaking scheme from `ComplexityTests.Crypto.Encryption` violates `INDCCA2` for
every decryption function, by `INDCCA2.indcpa` and `not_indCPA`. -/
theorem not_indcca2_leaking (decrypt : ℕ → List Bool → List Bool → Option Bool) :
    ¬ INDCCA2 ComplexityTests.Crypto.Encryption.keyGen
        ComplexityTests.Crypto.Encryption.encrypt decrypt :=
  fun hCCA => ComplexityTests.Crypto.Encryption.not_indCPA hCCA.indcpa

/-- Concrete witness for `CCA2Adversary.IsPPT` via `CCA2Adversary.isPPT_ofCPA`. -/
example : (CCA2Adversary.ofCPA ComplexityTests.Crypto.Encryption.adversary).IsPPT :=
  CCA2Adversary.isPPT_ofCPA ComplexityTests.Crypto.Encryption.adversary_ppt

/-! ### 3. Concrete `cca2Phase2Oracle` behavior and live Phase-2 decryption-oracle test -/

/-- Decryption that reads the first bit and ignores any trailing bits. -/
def headDecrypt (_ : ℕ) (_ : List Bool) (ct : List Bool) : Option Bool := ct.head?

/-- `cca2Phase2Oracle` rejects the challenge ciphertext `[true]` with `[]` and decrypts `[false]`
to `encOption encBool (some false) = [true, false]`. -/
example :
    ProbComp.eval (cca2Phase2Oracle encBool headDecrypt 4 [] [true] ((), [true]) ()) =
      PMF.pure ([], ()) ∧
    ProbComp.eval (cca2Phase2Oracle encBool headDecrypt 4 [] [true] ((), [false]) ()) =
      PMF.pure ([true, false], ()) := by
  constructor <;> simp [cca2Phase2Oracle, headDecrypt, encOption, encBool_apply]

/-- Malleable encryption scheme: `encrypt` outputs `[b]`, while `headDecrypt` ignores trailing
bits so `ct ++ [true]` decrypts to `some b`. -/
def malleableEncrypt (_ : ℕ) (_ : List Bool) (b : Bool) : ProbComp (List Bool) := pure [b]

/-- A Phase-2 adversary that queries the decryption oracle on `ct ++ [true]` (which is distinct
from `ct = [b]`) and reads the decoded plaintext bit from the `encOption encBool` response
`[true, b]`. -/
def phase2Mallory : CCA2Adversary where
  choose _ _ := pure ((false, true), [])
  guess _ _ ct := do
    let resp ← ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
      ((), ct ++ [true])
    return List.getD resp 1 false

/-- `phase2Mallory` recovers the challenge bit with probability `1` via its Phase-2 decryption
query on `ct ++ [true] ≠ ct`. -/
theorem eval_cca2Game_phase2Mallory (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (cca2Game encBool constKeyGen malleableEncrypt headDecrypt phase2Mallory bit n) =
      PMF.pure bit := by
  cases bit <;>
    · simp [cca2Game, cca2GameOn, constKeyGen, malleableEncrypt, phase2Mallory,
        StateT.run_pure, StateT.run_map]
      simp [StateT.run, cca2Phase2Oracle, headDecrypt, encOption, encBool_apply]

/-! ### 4. Refutable `CollisionResistantFor` instance over `ZMod 11` -/

/-- Concrete check of `isCollisionFor` and `collisionGameFor_sampleList_eq`. -/
example :
    isCollisionFor (Param := Unit) (Digest := fun _ => ZMod 11)
      (fun _ _ => (0 : ZMod 11)) (fun _ _ _ => true)
      4 () [false] [true] = true := by
  decide

example (H : List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) (adversary : CollisionFinder) (n : ℕ) :
    collisionGameFor (Param := List Bool) (Digest := fun _ => List Bool)
      (fun m => ProbComp.eval (BitString.sampleList m)) H (fun m _ => valid m) adversary n =
      ProbComp.eval (collisionGame H valid adversary n) :=
  collisionGameFor_sampleList_eq H valid adversary n

/-- Constant `ZMod 11`-valued hash family indexed by `Unit`. -/
def constZModHash (_ : Unit) (_ : List Bool) : ZMod 11 := 0

/-- Constant collision finder outputting `([false], [true])`. -/
def constZModFinder : CollisionFinderFor Unit := fun _ _ => pure ([false], [true])

/-- `constZModFinder` is uniformly strict PPT. -/
theorem isPPTOn_constZModFinder :
    IsPPTOn (encPair encUnary (encFinite Unit)) (encPair encBits encBits)
      (fun p => constZModFinder p.1 p.2) :=
  (ComputableTidilyInPolyTime.const ([false], [true])).isPPTOn

/-- The constant `ZMod 11`-valued hash family is not collision-resistant. -/
theorem not_collisionResistantFor_constZModHash :
    ¬ CollisionResistantFor (Param := Unit) (Digest := fun _ => ZMod 11)
        (encFinite Unit) (fun _ => PMF.pure ()) constZModHash := by
  refine not_collisionResistantForOn_of_le_succProbability (c := 1) one_ne_zero
    constZModFinder isPPTOn_constZModFinder (fun n => ?_)
  have heval :
      collisionGameFor (Param := Unit) (Digest := fun _ => ZMod 11)
        (fun _ => PMF.pure ()) constZModHash (fun _ _ _ => true) constZModFinder n =
        PMF.pure true := by
    simp [collisionGameFor, constZModFinder, constZModHash, isCollisionFor]
    rfl
  simp [heval, Game.succProbability]

end ComplexityTests.Crypto.CCA
