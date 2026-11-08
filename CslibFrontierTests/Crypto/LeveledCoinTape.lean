/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.CoinTape
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Tactic.PPT

/-!
# Executing the encrypted-link reduction from coins

The fixture has a genuinely random one-bit key. Tests inspect the exact saved state and
challenge messages, exercise rejected coordinates and zero ranges, and enumerate the four
two-bit selector tapes for a three-link chain. No encryption-security assumption is used.
-/

namespace CslibFrontierTests.Crypto.LeveledCoinTape

open Cslib Cslib.Crypto.Homomorphic Cslib.Probability Turing.MultiTapeTM

private def evaluateKey (_ : ℕ) (tape : List Bool) : List Bool × List Bool :=
  (tape, tape)

private noncomputable def fixture : Scheme where
  keyGen n := evaluateKey n <$> BitString.sampleList 1
  encrypt _ _ bit := pure [bit]
  decrypt _ _ ciphertext := ciphertext.headD false
  evaluate _ _ _ _ := pure []
  permitted _ _ := False

private theorem key_law (n : ℕ) : ProbComp.eval (fixture.keyGen n) =
    (BitString.uniformList 1).map (evaluateKey n) := by
  simp [fixture, ProbComp.eval_map, BitString.eval_sampleList]

-- Before, predecessor, and after keys read distinct seed blocks.
example : Scheme.chooseLinkAtCoins evaluateKey 0 1 1 1 0 [true, false]
    [false, true, false] =
      ((true, false), Scheme.activeLinkState [([false], [false])] ([true], [true])
        [true, false] [([false], [false])] 0) := by decide

-- Changing the predecessor seed changes the selected challenge message.
example : (Scheme.chooseLinkAtCoins evaluateKey 0 1 1 1 0 [] [false, false, false]).1 =
    (false, false) := by decide

-- A bit index outside the generated secret rejects rather than reading a default bit.
example : Scheme.chooseLinkAtCoins evaluateKey 0 1 1 1 1 [] [false, true, false] =
    Scheme.rejectLinkChoice := by decide

-- The exact sampling law has three independent one-bit key seeds.
example : ProbComp.eval (fixture.chooseLinkAt 0 1 1 0 [true, false]) =
    (BitString.uniformList 3).map
      (Scheme.chooseLinkAtCoins evaluateKey 0 1 1 1 0 [true, false]) := by
  exact fixture.eval_chooseLinkAt_eq_map_coins evaluateKey 0 1 1 1 0 _ (key_law 0)

-- Two-bit selection modulo three retains its bias: indices 0 and 3 share the first link.
-- The saved context has respectively 2, 1, 0, 2 keys before its predecessor.
example : ([[false, false], [false, true], [true, false], [true, true]].map fun selector =>
    let choice := Scheme.chooseModLinkCoins evaluateKey 0 2 1 3 1 []
      (selector ++ [false, false] ++ [true, false, true])
    let (_, before, _, _, _, _) := Scheme.linkStateDecoder.decode choice.2
    before.length) = [2, 1, 0, 2] := by
  simp [Scheme.chooseModLinkCoins, Scheme.chooseLinkAtCoins, evaluateKey,
    BitString.binaryValue, BitString.listRows, BitString.listRow]

-- The exact original modular algorithm uses four selector bits and three key bits.
example : ProbComp.eval ((fixture.modLinkAdversary (fun _ => 2) (fun _ => 3) (fun _ => 1)
    (fun _ _ => pure true)).choose 0 []) =
      (BitString.uniformList 7).map (Scheme.chooseModLinkCoins evaluateKey 0 2 1 3 1 []) := by
  exact fixture.eval_modLinkAdversary_choose_eq_map_coins evaluateKey _ _ _ _ 0 1 [] (key_law 0)

example (tape : List Bool) : Scheme.chooseModLinkCoins evaluateKey 0 2 1 0 1 [] tape =
    Scheme.rejectLinkChoice := by simp [Scheme.chooseModLinkCoins]

example (tape : List Bool) : Scheme.chooseModLinkCoins evaluateKey 0 2 1 3 0 [] tape =
    Scheme.rejectLinkChoice := by simp [Scheme.chooseModLinkCoins]

-- The key generator inhabits the native efficiency premise, and its replay has a native
-- certificate jointly in the supplied parameter, public key, and tape.
private theorem fixture_keyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) fixture.keyGen := by
  unfold fixture evaluateKey
  ppt

example : ComputableInPolyTime (fun ((n, pk), tape) =>
    Scheme.chooseModLinkCoins evaluateKey n 2 1 (n + 1) 1 pk tape)
    (encPair (encPair encUnary encBits) encBits) (encPair (encPair encBool encBool) encBits) := by
  apply Scheme.computableInPolyTime_chooseModLinkCoins
  · unfold evaluateKey
    fun_prop
  all_goals fun_prop

end CslibFrontierTests.Crypto.LeveledCoinTape
