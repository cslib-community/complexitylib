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

/-! ### Word layouts -/

/-- A view is encoded as its framed transcript followed by the word of its key. -/
example {T : Type} {K : T → Type} (encT : T ↪ List Bool) (encK : (t : T) → K t ↪ List Bool)
    (view : KeyExchange.View T K) :
    KeyExchange.encView encT encK view =
      encPair encT encBits (view.transcript, encK view.transcript view.key) :=
  rfl

/-- For a constant key encoding, the eavesdropper input has the words of the untyped layout
`(1ⁿ, (transcript, key))`. -/
example {T K : Type} (encT : T ↪ List Bool) (encK : K ↪ List Bool) (n : ℕ)
    (view : KeyExchange.View T fun _ => K) :
    KeyExchange.encEavInput encT (fun _ => encK) (n, view) =
      encPair encUnary (encPair encT encK) (n, (view.transcript, view.key)) :=
  rfl

/-- A Diffie–Hellman transcript has the words of `(d, hA, hB)` with encoded shares. -/
example (F : PrimeOrderGroupFamily) (transcript : F.DHTranscript) :
    F.encDHTranscript transcript = encPair F.encDesc (encPair encBits encBits)
      (transcript.groupParameters, F.encode _ transcript.aliceShare,
        F.encode _ transcript.bobShare) :=
  rfl

/-! ### Diffie–Hellman -/

/-- Schnorr subgroup of order `11` in `(ZMod 23)ˣ` with generator `2`. -/
private def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

private def setup23 (_n : ℕ) : PMF schnorrGroups.Desc := PMF.pure d23

/-- Honest Diffie–Hellman executions over `d23` always agree on Alice's and Bob's keys. -/
example : (schnorrGroups.dhKeyExchange setup23).Correct :=
  schnorrGroups.dhKeyExchange_correct setup23

/-- Under DDH for `setup`, Diffie–Hellman key exchange is secure against eavesdroppers. -/
example {setup : ℕ → PMF schnorrGroups.Desc} (h : schnorrGroups.DDH setup) :
    (schnorrGroups.dhKeyExchange setup).EavSecure schnorrGroups.encDHTranscript
      schnorrGroups.encDHKey fun _ => schnorrGroups.dhIdealKey :=
  PrimeOrderGroupFamily.DDH.dhKeyExchange_eavSecure h

/-! The typed eavesdropper class contains every word-level eavesdropper that reads the encoded
transcript `(d, hA, hB)` and key, so the typed theorem gives the word-level statement. -/

section WordLevel

variable {F : PrimeOrderGroupFamily}

/-- A word-level eavesdropper as a typed one: encode the view, then run it. -/
private def ofWords
    (adversary : ℕ → (F.Desc × List Bool × List Bool) × List Bool → ProbComp Bool) :
    KeyExchange.Eavesdropper F.DHTranscript F.DHKey :=
  fun n view => adversary n
    ((view.transcript.groupParameters, F.encode _ view.transcript.aliceShare,
      F.encode _ view.transcript.bobShare), F.encode _ view.key)

open scoped KeyExchange PrimeOrderGroupFamily in
private theorem isPPT_ofWords
    {adversary : ℕ → (F.Desc × List Bool × List Bool) × List Bool → ProbComp Bool}
    (hA : IsPPTOn (encPair encUnary (encPair (encPair F.encDesc (encPair encBits encBits)) encBits))
      encBool fun input => adversary input.1 input.2) :
    (ofWords adversary).IsPPT F.encDHTranscript F.encDHKey := by
  have hkey : ComputableInPolyTime
      (fun input : ℕ × KeyExchange.View F.DHTranscript F.DHKey =>
        F.encode input.2.transcript.groupParameters input.2.key)
      (KeyExchange.encEavInput F.encDHTranscript F.encDHKey) encBits :=
    KeyExchange.encView_key_polyTime _ _ (.snd _ _)
  exact IsPPTOn.preprocess hA (prepare := fun input : ℕ × KeyExchange.View F.DHTranscript F.DHKey =>
    (input.1, ((input.2.transcript.groupParameters, F.encode _ input.2.transcript.aliceShare,
      F.encode _ input.2.transcript.bobShare), F.encode _ input.2.key))) (by fun_prop)

/-- The word-level real experiment: the encoded transcript with Alice's encoded key `x • hB`. -/
private def wordRealGame (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → (F.Desc × List Bool × List Bool) × List Bool → ProbComp Bool) (n : ℕ) :
    Game := do
  let d ← setup n
  let x ← PMF.uniformOfFintype (ZMod (F.order d))
  let y ← PMF.uniformOfFintype (ZMod (F.order d))
  ProbComp.eval (adversary n ((d, F.encode d (x • F.generator d), F.encode d (y • F.generator d)),
    F.encode d (x • y • F.generator d)))

/-- The word-level ideal experiment: the encoded transcript with an encoded uniform element. -/
private def wordIdealGame (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → (F.Desc × List Bool × List Bool) × List Bool → ProbComp Bool) (n : ℕ) :
    Game := do
  let d ← setup n
  let x ← PMF.uniformOfFintype (ZMod (F.order d))
  let y ← PMF.uniformOfFintype (ZMod (F.order d))
  let z ← PMF.uniformOfFintype (ZMod (F.order d))
  ProbComp.eval (adversary n ((d, F.encode d (x • F.generator d), F.encode d (y • F.generator d)),
    F.encode d (z • F.generator d)))

/-- Under DDH, every word-level PPT eavesdropper on the encoded transcript and key has negligible
advantage. -/
example {setup : ℕ → PMF F.Desc} (hDDH : F.DDH setup)
    {adversary : ℕ → (F.Desc × List Bool × List Bool) × List Bool → ProbComp Bool}
    (hA : IsPPTOn (encPair encUnary (encPair (encPair F.encDesc (encPair encBits encBits)) encBits))
      encBool fun input => adversary input.1 input.2) :
    Negligible fun n =>
      Game.advantage (wordRealGame setup adversary n) (wordIdealGame setup adversary n) := by
  have hreal : ∀ n, wordRealGame setup adversary n =
      (F.dhKeyExchange setup).realGame (ofWords adversary) n := fun n => by
    simp only [wordRealGame, KeyExchange.realGame, Game.withSetup, KeyExchange.realView,
      PrimeOrderGroupFamily.dhKeyExchange, PrimeOrderGroupFamily.dhExecution, ofWords,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  have hideal : ∀ n, wordIdealGame setup adversary n =
      (F.dhKeyExchange setup).idealGame (fun _ => F.dhIdealKey) (ofWords adversary) n :=
    fun n => by
      simp only [wordIdealGame, KeyExchange.idealGame, Game.withSetup, KeyExchange.idealView,
        PrimeOrderGroupFamily.dhKeyExchange, PrimeOrderGroupFamily.dhExecution,
        PrimeOrderGroupFamily.dhIdealKey, ofWords, PMF.monad_bind_eq_bind,
        PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, PMF.bind_map, Function.comp_def]
  simpa only [hreal, hideal] using
    PrimeOrderGroupFamily.DDH.dhKeyExchange_eavSecure hDDH (ofWords adversary) (isPPT_ofWords hA)

end WordLevel

/-- In the man-in-the-middle execution on `d23`, the adversary shares keys with both parties
while Alice's and Bob's views match the eavesdropper's view of honest executions. -/
example :
    (∀ o ∈ (schnorrGroups.dhMitmExecution d23).support,
      o.adversaryAliceKey = o.aliceView.key ∧ o.adversaryBobKey = o.bobView.key) ∧
    (schnorrGroups.dhMitmExecution d23).map PrimeOrderGroupFamily.DHMitmOutcome.aliceView =
      KeyExchange.realView (schnorrGroups.dhExecution d23) ∧
    (schnorrGroups.dhMitmExecution d23).map PrimeOrderGroupFamily.DHMitmOutcome.bobView =
      KeyExchange.realView (schnorrGroups.dhExecution d23) :=
  ⟨schnorrGroups.dhMitmExecution_keys d23, schnorrGroups.map_aliceView_dhMitmExecution d23,
    schnorrGroups.map_bobView_dhMitmExecution d23⟩

/-- Over a setup law the attack draws the group first, and Alice's view still has the law of the
eavesdropper's view of an honest execution. -/
example (setup : ℕ → PMF schnorrGroups.Desc) (n : ℕ) :
    ((setup n).bind schnorrGroups.dhMitmExecution).map
        PrimeOrderGroupFamily.DHMitmOutcome.aliceView =
      KeyExchange.realView ((schnorrGroups.dhKeyExchange setup).execute n) := by
  simp only [PMF.map_bind, PrimeOrderGroupFamily.map_aliceView_dhMitmExecution,
    PrimeOrderGroupFamily.dhKeyExchange, KeyExchange.realView, PMF.monad_bind_eq_bind,
    PMF.bind_bind]

/-! ### The XOR protocol -/

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

/-! ### Public-key EAV-to-CPA -/

/-- Public-key eavesdropping security (`WordINDCPA`) lifts to multi-query encryption-oracle CPA
security (`WordINDCPAOracle`) when honest encryption is uniform strict PPT. -/
example {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (henc : IsPPTOn Encryption.encEncryptInput encBits (fun p => encrypt p.1 p.2.1 p.2.2))
    (hcpa : Encryption.WordINDCPA keyGen encrypt) :
    Encryption.WordINDCPAOracle keyGen encrypt :=
  Encryption.WordINDCPA.wordINDCPAOracle henc hcpa

end CslibFrontierTests.Crypto.KeyExchange
