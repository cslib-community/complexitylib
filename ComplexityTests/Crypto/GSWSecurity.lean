/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.GSW.Security
import Mathlib.Logic.Equiv.Bool

/-!
Regression clients for the actual GSW security reduction. A deliberately revealing test
encryption checks the hidden-bit orientation, preservation of saved public-key state and the
factor-two loss. The GSW clients use the actual growing parameter family and native algorithms;
their security theorem retains its precise decision-LWE hypothesis.
-/

namespace ComplexityTests.GSWSecurity

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Homomorphic.GSW
open Turing.MultiTapeTM
open scoped NNReal

private def revealingEncrypt (_ : ℕ) (_ : List Bool) (message : Bool) : ProbComp (List Bool) :=
  pure [message]

private def savedKeyAdversary : Encryption.Adversary where
  choose _ pk := pure ((false, true), pk)
  guess _ state ciphertext := pure (state.headD false ^^ ciphertext.headD false)

-- Losing the saved word or reversing the hidden-bit orientation changes this exact law.
private theorem saved_key_reduction (security : ℕ) (pk : List Bool) :
    ProbComp.eval (Encryption.keyDistinguisher revealingEncrypt savedKeyAdversary security pk) =
      PMF.pure (pk.headD false) := by
  simp [Encryption.keyDistinguisher, revealingEncrypt, savedKeyAdversary,
    PMF.map, Function.comp_def]

example :
    ProbComp.eval (Encryption.keyDistinguisher revealingEncrypt savedKeyAdversary 0 [true]) =
      PMF.pure true := saved_key_reduction 0 [true]

private noncomputable def idealTestKeys : PMF (List Bool) :=
  (PMF.uniformOfFintype Bool).map (fun bit => [bit])

private theorem test_distinguisher_real :
    distinguishingGame (PMF.pure [false])
      (Encryption.keyDistinguisher revealingEncrypt savedKeyAdversary 0) = PMF.pure false := by
  simp [distinguishingGame, saved_key_reduction]

private theorem test_distinguisher_ideal :
    distinguishingGame idealTestKeys
      (Encryption.keyDistinguisher revealingEncrypt savedKeyAdversary 0) =
        PMF.uniformOfFintype Bool := by
  simp [distinguishingGame, idealTestKeys, PMF.bind_map, saved_key_reduction, Function.comp_def]

private theorem test_public_game (bit : Bool) :
    Encryption.publicKeyGame (PMF.pure [false]) revealingEncrypt savedKeyAdversary bit 0 =
      PMF.pure bit := by
  cases bit <;> simp [Encryption.publicKeyGame, revealingEncrypt, savedKeyAdversary,
    ProbComp.eval_pure]

private theorem test_ideal_game (bit : Bool) :
    Encryption.publicKeyGame idealTestKeys revealingEncrypt savedKeyAdversary bit 0 =
      PMF.uniformOfFintype Bool := by
  cases bit
  · simp [Encryption.publicKeyGame, revealingEncrypt, savedKeyAdversary,
      idealTestKeys, ProbComp.eval_pure, PMF.map]
  · simpa [Encryption.publicKeyGame, revealingEncrypt, savedKeyAdversary,
      idealTestKeys, ProbComp.eval_pure, PMF.map, Equiv.boolNot, Function.comp_def] using
      PMF.uniformOfFintype_map_equiv Equiv.boolNot

-- The factor two is attained: a chosen-message gap of one corresponds to a key gap of one half,
-- while the replacement world's chosen-message gap is zero.
example :
    Game.advantage
      (Encryption.publicKeyGame (PMF.pure [false]) revealingEncrypt savedKeyAdversary false 0)
      (Encryption.publicKeyGame (PMF.pure [false]) revealingEncrypt savedKeyAdversary true 0) = 1 ∧
    Game.advantage
      (distinguishingGame (PMF.pure [false])
        (Encryption.keyDistinguisher revealingEncrypt savedKeyAdversary 0))
      (distinguishingGame idealTestKeys
        (Encryption.keyDistinguisher revealingEncrypt savedKeyAdversary 0)) = 1 / 2 ∧
    Game.advantage
      (Encryption.publicKeyGame idealTestKeys revealingEncrypt savedKeyAdversary false 0)
      (Encryption.publicKeyGame idealTestKeys revealingEncrypt savedKeyAdversary true 0) = 0 := by
  rw [test_public_game, test_public_game, test_distinguisher_real, test_distinguisher_ideal,
    test_ideal_game, test_ideal_game]
  norm_num [Game.advantage, Game.succProbability, NNReal.nndist_eq, ENNReal.toNNReal_ofNat]

-- This real client chooses messages as a function of the public key and retains its full word.
private def adaptiveAdversary : Encryption.Adversary where
  choose _ pk := pure ((pk.headD false, !pk.headD false), pk)
  guess _ state ciphertext := pure (state.headD false ^^ ciphertext.headD false)

private theorem adaptiveAdversary_isPPT : adaptiveAdversary.IsPPT := by
  constructor <;> simp only [adaptiveAdversary] <;> ppt

-- The reduction covers all input words, including malformed or oversized matrix encodings.
example : IsPPT encBool
    (lweDistinguisher Parameters.dimension Parameters.samples Parameters.width adaptiveAdversary) :=
  isPPT_lweDistinguisher Parameters.computableInPolyTime_dimension
    Parameters.computableInPolyTime_samples Parameters.computableInPolyTime_width
    adaptiveAdversary_isPPT

-- Both honest algorithms are strict PPT for the same growing, positive-noise parameter family.
example : IsPPTOn encUnary (encPair encBits encBits)
    (fun security => keyGenSerialized (Parameters.dimension security) (Parameters.samples security)
      (Parameters.width security) (Parameters.noise security)) :=
  isPPTOn_keyGenSerialized Parameters.computableInPolyTime_dimension
    Parameters.computableInPolyTime_samples Parameters.computableInPolyTime_width
    Parameters.computableInPolyTime_noise

example : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => encryptSerialized (Parameters.dimension p.1) (Parameters.samples p.1)
      (Parameters.width p.1) p.2.1 p.2.2) :=
  isPPTOn_encryptSerialized (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)

-- No separate encryption-efficiency, security-of-encryption, or zero-noise premise is supplied.
example
    (hLWE : DecisionLWE Parameters.dimension Parameters.samples Parameters.width
      (fun k => noiseLaw (Parameters.width k) (Parameters.noise k))) :
    Negligible (fun k =>
      Game.advantage
        (ProbComp.eval (Encryption.game
          (fun k => keyGenSerialized (Parameters.dimension k) (Parameters.samples k)
            (Parameters.width k) (Parameters.noise k))
          (fun k => encryptSerialized (Parameters.dimension k) (Parameters.samples k)
            (Parameters.width k))
          adaptiveAdversary false k))
        (ProbComp.eval (Encryption.game
          (fun k => keyGenSerialized (Parameters.dimension k) (Parameters.samples k)
            (Parameters.width k) (Parameters.noise k))
          (fun k => encryptSerialized (Parameters.dimension k) (Parameters.samples k)
            (Parameters.width k))
          adaptiveAdversary true k))) :=
  Parameters.indCPA hLWE adaptiveAdversary adaptiveAdversary_isPPT

end ComplexityTests.GSWSecurity
