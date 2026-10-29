/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Encryption.PolyTime
import Complexity.Crypto.Negligible.Basic
import Complexity.Tactic.PPT

/-!
# Tests for the bit-encryption security game

A plaintext-leaking encryption algorithm is rejected by an explicit uniform adversary. Its
challenge messages depend on the random public key, which it retains in the saved state. Thus
the regression exercises both stages and their state transfer, not merely a constant guess.
The native runtime test varies both the security parameter and the experiment selector.
-/

namespace ComplexityTests.Crypto.Encryption

open Cslib Cslib.Crypto Cslib.Crypto.Encryption Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- A random public bit, retained as the private key as well. -/
noncomputable def keyGen (_ : ℕ) : ProbComp (List Bool × List Bool) := do
  let key ← ProbComp.uniform Bool
  pure ([key], [key])

/-- Deliberately insecure encryption publishes the plaintext. -/
def encrypt (_ : ℕ) (_ : List Bool) (bit : Bool) : ProbComp (List Bool) := pure [bit]

/-- Choose opposite messages using the public key; recover the experiment selector using the
saved public key after reading the plaintext ciphertext. -/
def adversary : Adversary where
  choose _ pk := pure ((pk.headD false, !(pk.headD false)), pk)
  guess _ state ciphertext := pure (ciphertext.headD false ^^ state.headD false)

theorem keyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) keyGen := by
  unfold keyGen
  ppt

theorem encrypt_ppt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => encrypt p.1 p.2.1 p.2.2) := by
  unfold encrypt
  ppt

theorem adversary_ppt : adversary.IsPPT := by
  constructor <;> dsimp only [adversary] <;> ppt

-- Both stages, all saved state, and both possible experiment selectors are charged.
example : IsPPTOn (encPair encUnary encBool) encBool
    (fun p => game keyGen encrypt adversary p.2 p.1) :=
  isPPTOn_game keyGen_ppt encrypt_ppt adversary_ppt (by fun_prop) (by fun_prop)

/-- The stateful adversary recovers the selector with certainty for every security parameter. -/
theorem eval_game_adversary (bit : Bool) (n : ℕ) :
    ProbComp.eval (game keyGen encrypt adversary bit n) = PMF.pure bit := by
  cases bit <;>
    simp [eval_game, keyGen, encrypt, adversary, ProbComp.eval_map]

/-- An explicit admissible adversary has constant advantage one, so the leaking encryption
algorithm does not satisfy the new security predicate. -/
theorem not_indCPA : ¬ INDCPA keyGen encrypt := by
  intro hsecure
  have hnegligible := hsecure adversary adversary_ppt
  simp only [eval_game_adversary] at hnegligible
  have hone : Game.advantage (PMF.pure false) (PMF.pure true) = 1 := by
    simp [Game.advantage, Game.succProbability]
  rw [hone] at hnegligible
  exact not_negligible_const one_ne_zero hnegligible

end ComplexityTests.Crypto.Encryption
