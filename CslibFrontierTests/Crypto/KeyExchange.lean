/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import CslibFrontier.Crypto.Computational.Encryption.PublicKeyCPA
import CslibFrontier.Crypto.Computational.KeyExchange
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Diffie–Hellman Key Exchange and Public-Key EAV-to-CPA

Concrete checks for `CslibFrontier/Crypto/Computational/KeyExchange.lean` (over the Schnorr
subgroup of order `11` in `(ZMod 23)ˣ` and on the 3-message XOR key-exchange protocol) and
`CslibFrontier/Crypto/Computational/Encryption/PublicKeyCPA.lean`.
-/

noncomputable section

namespace CslibFrontierTests.Crypto.KeyExchange

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM
open scoped NNReal

/-- Schnorr subgroup of order `11` in `(ZMod 23)ˣ` with generator `2`. -/
private def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

private def setup23 (_n : ℕ) : PMF schnorrGroups.Desc := PMF.pure d23

/-- Honest Diffie–Hellman executions over `d23` always agree on Alice's and Bob's keys. -/
example : (schnorrGroups.dhKeyExchange setup23).Correct :=
  schnorrGroups.dhKeyExchange_correct setup23

/-- Under DDH for `setup`, Diffie–Hellman key exchange is secure against eavesdroppers. -/
example {setup : ℕ → PMF schnorrGroups.Desc} (h : schnorrGroups.DDH setup) :
    (schnorrGroups.dhKeyExchange setup).EavSecure schnorrGroups.encDHTranscript encBits
      schnorrGroups.dhIdealKey :=
  PrimeOrderGroupFamily.DDH.dhKeyExchange_eavSecure h

/-- In the man-in-the-middle execution on `d23`, the adversary shares keys with both parties
while Alice's and Bob's marginal views match honest executions. -/
example (n : ℕ) :
    (∀ o ∈ (schnorrGroups.dhMitmExecution setup23 n).support,
      o.adversaryAliceKey = o.aliceKey ∧ o.adversaryBobKey = o.bobKey) ∧
    (schnorrGroups.dhMitmExecution setup23 n).map (fun o => (o.aliceView, o.aliceKey)) =
      ((schnorrGroups.dhKeyExchange setup23).execute n).map
        (fun o => (o.transcript, o.aliceKey)) :=
  ⟨schnorrGroups.dhMitmExecution_keys setup23 n,
    schnorrGroups.map_aliceView_dhMitmExecution setup23 n⟩

/-- The XOR key-exchange protocol is correct, yet `xorEavesdropper` achieves advantage `≥ 1/2`
at `n = 8`, refuting `EavSecureBits`. -/
example : KeyExchange.xorKeyExchange.Correct ∧
    (1 / 2 : ℝ≥0) ≤ Game.advantage
      (KeyExchange.xorKeyExchange.realGame KeyExchange.xorEavesdropper 8)
      (KeyExchange.xorKeyExchange.idealGame (fun n _ => BitString.uniformList n)
        KeyExchange.xorEavesdropper 8) ∧
    ¬ KeyExchange.xorKeyExchange.EavSecureBits KeyExchange.encXorTranscript :=
  ⟨KeyExchange.xorKeyExchange_correct,
    KeyExchange.half_le_advantage_xorEavesdropper (by norm_num),
    KeyExchange.not_eavSecureBits_xorKeyExchange⟩

/-- Public-key eavesdropping security (`WordINDCPA`) lifts to multi-query encryption-oracle CPA
security (`WordINDCPAOracle`) when honest encryption is uniform strict PPT. -/
example {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (henc : IsPPTOn Encryption.encEncryptInput encBits (fun p => encrypt p.1 p.2.1 p.2.2))
    (hcpa : Encryption.WordINDCPA keyGen encrypt) :
    Encryption.WordINDCPAOracle keyGen encrypt :=
  Encryption.WordINDCPA.wordINDCPAOracle henc hcpa

end CslibFrontierTests.Crypto.KeyExchange
