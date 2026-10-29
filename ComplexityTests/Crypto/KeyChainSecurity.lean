/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.KeyChain.Reduction.Game
import Complexity.Crypto.Computational.Homomorphic.KeyChain.Reduction.PolyTime
import Complexity.Tactic.PPT

/-!
# Tests for the acyclic encrypted-link reduction

The fixture samples independent two-bit secret keys. Ciphertexts expose their target public
key, plaintext and an independent random nonce. Two links include a repeated key value, and
every nonce combination has a concrete support witness. These are simulation and runtime
regressions; the fixture deliberately offers no encryption security.
-/

namespace ComplexityTests.Crypto.KeyChainSecurity

open Cslib Cslib.Crypto Cslib.Crypto.Homomorphic Cslib.Probability Turing.MultiTapeTM

/-- Two independent secret bits and a visible first bit; encryption retains a fresh nonce. -/
private noncomputable def fixture : Scheme where
  keyGen _ := do
    let first ← ProbComp.uniform Bool
    let second ← ProbComp.uniform Bool
    pure ([first], [first, second])
  encrypt _ pk bit := do
    let nonce ← ProbComp.uniform Bool
    pure [pk.headD false, bit, nonce]
  decrypt _ _ ciphertext := ciphertext.getD 1 false
  evaluate _ _ _ _ := pure []
  permitted _ _ := False

private theorem keys_supported (n : ℕ) (key : List Bool × List Bool) :
    key ∈ (ProbComp.eval (fixture.keyGen n)).support ↔
      ∃ first second : Bool, key = ([first], [first, second]) := by
  simp only [fixture, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, PMF.uniformOfFintype,
    PMF.mem_support_uniformOfFinset_iff, Finset.mem_univ, true_and]

private theorem secret_width (n : ℕ) (key : List Bool × List Bool)
    (hkey : key ∈ (ProbComp.eval (fixture.keyGen n)).support) : key.2.length = 2 := by
  obtain ⟨first, second, rfl⟩ := (keys_supported n key).1 hkey
  rfl

private def keys : List (List Bool × List Bool) :=
  [([false], [false, true]), ([true], [true, false]), ([false], [false, true])]

private def links (a b c d : Bool) : List (List (List Bool)) :=
  [[[true, false, a], [true, true, b]], [[false, true, c], [false, false, d]]]

-- Every combination of four encryption nonces is supported in this repeated-key chain.
private theorem chain_supported (a b c d : Bool) :
    (keys, links a b c d) ∈ (ProbComp.eval (fixture.generateKeyChain 0 2)).support := by
  rw [Scheme.mem_support_generateKeyChain_iff]
  refine ⟨rfl, ?_, ?_⟩
  · intro key hkey
    simp only [keys, List.mem_cons, List.not_mem_nil, or_false] at hkey
    rcases hkey with rfl | rfl | rfl
    all_goals exact (keys_supported 0 _).2 ⟨_, _, rfl⟩
  · simp [Scheme.ValidLinks, Scheme.FreshInputs, keys, links, fixture]

example (a b c d : Bool) : keys.length = 3 ∧ (links a b c d).length = 2 :=
  fixture.lengths_of_mem_support_generateKeyChain (chain_supported a b c d)

-- Projecting the retained encryption nonce recovers the original uniform distribution.
example (n : ℕ) (pk : List Bool) (bit : Bool) :
    (ProbComp.eval (fixture.encrypt n pk bit)).map (fun ct => ct.getD 2 false) =
      PMF.uniformOfFintype Bool := by
  simp [fixture, PMF.map, Function.comp_def]

/-- Observe the second secret bit of the first encrypted link. -/
private def observe (_ : ℕ)
    (artifact : List (List Bool) × List (List (List Bool))) : ProbComp Bool :=
  pure (((artifact.2.getD 0 []).getD 1 []).getD 1 false)

-- The active context has a nonempty outgoing zeroed suffix. The unknown secret differs from
-- its zero replacement, while the original challenge bit is true and the replacement false.
private theorem eval_active_bit (bit : Bool) :
    ProbComp.eval (do
      let challenge ← fixture.encrypt 0 [true] (if bit then false else true)
      fixture.guessLink observe 0
        (Scheme.activeLinkState [] ([false], [false, true]) [true]
          [([false], [false, true])] 1) challenge) = PMF.pure (!bit) := by
  have h := fixture.eval_guessLink_active observe 0 [] ([false], [false, true])
    ([true], [true, false]) [([false], [false, true])] 1 bit (by decide) rfl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  rw [h]
  cases bit <;>
    simp [Scheme.encryptKeyLinkHybrid, Scheme.encryptBitsHybrid, Scheme.encryptBits,
      Scheme.encryptKeyLinks, Scheme.encryptZeroKeyLinks, fixture, observe, List.mapM_cons,
      PMF.map, Function.comp_def]

-- The complete base game, including independently sampled keys, realizes each bit hybrid.
example (n : ℕ) (bit : Bool) :
    ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (fixture.linkAdversaryAt (fun _ => 0) (fun _ => 1) (fun _ => 1) observe) bit n) =
      ProbComp.eval (fixture.publicKeyLinkHybrid n 0 1 (1 + if bit then 1 else 0) >>=
        observe n) := by
  simpa using fixture.eval_linkAdversaryAt (fun _ => 0) (fun _ => 1) (fun _ => 1)
    observe n 2 bit (secret_width n)

-- A selected bit outside the supported secret word rejects in both worlds.
example (n : ℕ) (bit : Bool) :
    ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (fixture.linkAdversaryAt (fun _ => 0) (fun _ => 1) (fun _ => 2) observe) bit n) =
      PMF.pure false := by
  simpa using fixture.eval_linkAdversaryAt (fun _ => 0) (fun _ => 1) (fun _ => 2)
    observe n 2 bit (secret_width n)

-- Both sampling ranges have padding: only two links and two bits out of four are active.
example : dyadicSize 2 = 4 ∧ dyadicSize 3 = 4 := by decide

example (n : ℕ) (bit : Bool) :
    ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (fixture.linkAdversary (fun _ => 2) (fun _ => 3) observe) bit n) =
      fixture.keyChainHybridGame n 2 2 3 (observe n) bit :=
  fixture.eval_linkAdversary (fun _ => 2) (fun _ => 3) observe n 2 bit (secret_width n)

example (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (fixture.publicKeyChainHybrid n 2 2 >>= observe n)) : ℝ) -
      Game.succProbability (ProbComp.eval
        (fixture.publicKeyChainHybrid n 2 0 >>= observe n)) =
      16 * (Game.succProbability (ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
        (fixture.linkAdversary (fun _ => 2) (fun _ => 3) observe) false n)) -
        Game.succProbability (ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
          (fixture.linkAdversary (fun _ => 2) (fun _ => 3) observe) true n))) := by
  have h := fixture.publicKeyChainHybrid_gap_linkAdversary (fun _ => 2) (fun _ => 3)
    observe n 2 (secret_width n) (by decide)
  simpa only [show dyadicSize 2 = 4 from by decide, show dyadicSize 3 = 4 from by decide,
    Nat.cast_ofNat, show (4 : ℝ) * 4 = 16 by norm_num] using h

-- Zero links reject even though the base scheme still generates nonempty random secrets.
example (n : ℕ) (bit : Bool) :
    ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (fixture.linkAdversary (fun _ => 0) (fun _ => 3) observe) bit n) = PMF.pure false := by
  rw [fixture.eval_linkAdversary (fun _ => 0) (fun _ => 3) observe n 2 bit (secret_width n)]
  simp [Scheme.keyChainHybridGame]

private noncomputable def emptySecrets : Scheme :=
  { fixture with keyGen := fun _ => pure ([], []) }

private theorem empty_secret_width (n : ℕ) (key : List Bool × List Bool)
    (hkey : key ∈ (ProbComp.eval (emptySecrets.keyGen n)).support) : key.2.length = 0 := by
  simpa [emptySecrets] using congrArg (fun p : List Bool × List Bool => p.2.length)
    (PMF.mem_support_pure_iff _ _ |>.1 hkey)

-- Empty secrets retain the two link positions, each with an empty ciphertext list.
example (n : ℕ) : ProbComp.eval (emptySecrets.publicKeyChainHybrid n 2 2) =
    PMF.pure ([[], [], []], [[], []]) := by
  simp [Scheme.publicKeyChainHybrid, Scheme.generateKeys, OracleComp.replicate,
    Scheme.encryptKeyLinksHybrid, Scheme.encryptKeyLinks, Scheme.encryptZeroKeyLinks,
    Scheme.encryptBits, emptySecrets]

example (n : ℕ) (bit : Bool) :
    ProbComp.eval (Encryption.game emptySecrets.keyGen emptySecrets.encrypt
      (emptySecrets.linkAdversary (fun _ => 2) (fun _ => 0) observe) bit n) = PMF.pure false := by
  rw [emptySecrets.eval_linkAdversary (fun _ => 2) (fun _ => 0) observe n 0 bit
    (empty_secret_width n)]
  simp [Scheme.keyChainHybridGame]

private theorem keyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) fixture.keyGen := by
  dsimp only [fixture]
  ppt

private theorem encrypt_ppt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => fixture.encrypt p.1 p.2.1 p.2.2) := by
  dsimp only [fixture]
  ppt

private theorem observe_ppt : IsPPTOn
    (encPair encUnary (encPair (encList encBits) (encList (encList encBits)))) encBool
    (fun p => observe p.1 p.2) := by
  unfold observe
  apply ComputableInPolyTime.isPPTOn
  apply ComputableInPolyTime.bitsGetDWithInput
  · apply (ComputableInPolyTime.listGetD
      (encA := encBits) (encL := encList encBits) []).comp
      (g := fun p : ℕ × (List (List Bool) × List (List (List Bool))) =>
        (p.2.2.getD 0 [], 1))
    apply ComputableInPolyTime.prod
    · apply (ComputableInPolyTime.listGetD
        (encA := encList encBits) (encL := encList (encList encBits)) []).comp
        (g := fun p : ℕ × (List (List Bool) × List (List (List Bool))) => (p.2.2, 0))
      fun_prop
    · fun_prop
  · fun_prop

-- A nonconstant depth family is one uniform native adversary, not separately chosen advice.
example : (fixture.linkAdversary (fun n => n + 2) (fun _ => 3) observe).IsPPT :=
  fixture.isPPT_linkAdversary keyGen_ppt encrypt_ppt observe_ppt (by fun_prop) (by fun_prop)

-- Total decoding and guessing are charged on arbitrary complete saved words and ciphertexts.
example : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool
    (fun p => fixture.guessLink observe p.1 p.2.1 p.2.2) :=
  Scheme.isPPTOn_guessLink encrypt_ppt observe_ppt (by fun_prop) (by fun_prop) (by fun_prop)

end ComplexityTests.Crypto.KeyChainSecurity
