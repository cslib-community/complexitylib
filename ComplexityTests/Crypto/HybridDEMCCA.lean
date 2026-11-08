/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Encryption.Hybrid.DEMCCA
import Complexity.Crypto.Computational.Encryption.EncryptThenMAC
import ComplexityTests.Crypto.AuthenticatedEncryption
import Complexity.Tactic.PPT

/-!
# The actual-key DEM CCA leg

These clients use the existing PRF Encrypt-then-MAC cipher, expose the insecure echo cipher,
and check both phases, canonical word rejection, changed KEM components, and width zero.
-/

namespace ComplexityTests.Crypto.HybridDEMCCA

open Cslib Cslib.Crypto Cslib.Crypto.Encryption Cslib.Probability Turing.MultiTapeTM
open ComplexityTests.Crypto.AuthenticatedEncryption

def fixedKeyGen (_ : ℕ) : ProbComp (List Bool × List Bool) := pure ([], [])
def fixedEncaps (_ : ℕ) (_ : List Bool) : ProbComp (List Bool × List Bool) := pure ([], [])
def identityDecaps (_ : ℕ) (_ ct : List Bool) : Option (List Bool) := some ct

theorem fixedKeyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) fixedKeyGen := by
  unfold fixedKeyGen
  ppt

theorem fixedEncaps_ppt : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
    (fun p => fixedEncaps p.1 p.2) := by
  unfold fixedEncaps
  ppt

theorem identityDecaps_polyTime : ComputableInPolyTime
    (fun p : ℕ × List Bool × List Bool => identityDecaps p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encBits encBits)) (encOption encBits) := by
  unfold identityDecaps
  fun_prop

/-- Genuine conditional positive client: every premise of the DEM leg comes from the existing
PRF cipher and its actual encoded two-key sampler. No KEM security is claimed for this fixture. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    Game.Indistinguishable
      (fun A n => ProbComp.eval (hybridDEMGame
        (prfEncryptThenMAC family hprf.polyTime hprf.length_eq)
        fixedKeyGen fixedEncaps identityDecaps A false n))
      (fun A n => ProbComp.eval (hybridDEMGame
        (prfEncryptThenMAC family hprf.polyTime hprf.length_eq)
        fixedKeyGen fixedEncaps identityDecaps A true n)) WordCCA2Adversary.IsPPT :=
  hprf.indcca_prfEncryptThenMAC.oneTimeINDCCA.indistinguishable_hybridDEMGame
    fixedKeyGen_ppt fixedEncaps_ppt identityDecaps_polyTime

/-- The actual Encrypt-then-MAC key is a framed `n`-bit encryption key and a `2*n`-bit MAC key.
Its encoded length is `4*n+1`; it is not a uniform word of that length. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    (n : ℕ) (k : List Bool)
    (hk : k ∈ (ProbComp.eval
      ((prfEncryptThenMAC family hprf.polyTime hprf.length_eq).keyGen n)).support) :
    (unframe k).length = n ∧ (dropFrame k).length = 2 * n ∧ k.length = 4 * n + 1 := by
  change k ∈ (ProbComp.eval (do
    let ke ← BitString.sampleList n
    let km ← BitString.sampleList (2 * n)
    return encPair encBits encBits (ke, km))).support at hk
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hk
  obtain ⟨ke, hke, km, hkm, rfl⟩ := hk
  have he := BitString.length_of_mem_support_uniformList hke
  have hm := BitString.length_of_mem_support_uniformList hkm
  simp [encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append, he, hm]
  omega

def headAdversary : WordCCA2Adversary where
  choose n _ := pure ((List.replicate n false, List.replicate n true), [])
  guess _ _ ct := pure ((dropFrame ct).headD false)

theorem headAdversary_ppt : headAdversary.IsPPT := by
  constructor
  · exact ((by fun_prop : ComputableInPolyTime
      (fun p : ℕ × List Bool => ((List.replicate p.1 false, List.replicate p.1 true), []))
      (encPair encUnary encBits)
        (encPair (encPair encBits encBits) encBits)).isOraclePPTOn).isOraclePPT
  · exact (by polytime : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => (dropFrame p.2.2).headD false)
      (encPair encUnary (encPair encBits encBits)) encBool).isOraclePPTOn

/-- Native reduction and closed-game certificates apply even to this insecure cipher. -/
example : IsOraclePPT encBool (hybridToOneTimeCCAAdversary echoCipher fixedKeyGen fixedEncaps
    identityDecaps id (fun _ ct => ct.length + 1) headAdversary) :=
  isOraclePPT_hybridToOneTimeCCAAdversary echoCipher fixedKeyGen_ppt fixedEncaps_ppt
    identityDecaps_polyTime (by fun_prop) (by fun_prop) headAdversary_ppt

example (bit : Bool) : IsPPTOn encUnary encBool
    (hybridDEMGame echoCipher fixedKeyGen fixedEncaps identityDecaps headAdversary bit) :=
  isPPTOn_hybridDEMGame echoCipher fixedKeyGen_ppt fixedEncaps_ppt
    identityDecaps_polyTime headAdversary_ppt bit

theorem eval_headAdversary (bit : Bool) (n : ℕ) :
    ProbComp.eval (hybridDEMGame echoCipher fixedKeyGen fixedEncaps identityDecaps
      headAdversary bit (n + 1)) = PMF.pure bit := by
  cases bit <;> simp [hybridDEMGame, fixedKeyGen, fixedEncaps, echoCipher, cca2GameOn,
    headAdversary, ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.state, encPair_apply,
    encBits_apply, dropFrame_frame_append, List.replicate_succ]

/-- There is no unconditional security conclusion: the middle game of the echo cipher exposes
the challenge bit at every positive security parameter. -/
example (n : ℕ) : Game.advantage
    (ProbComp.eval (hybridDEMGame echoCipher fixedKeyGen fixedEncaps identityDecaps
      headAdversary false (n + 1)))
    (ProbComp.eval (hybridDEMGame echoCipher fixedKeyGen fixedEncaps identityDecaps
      headAdversary true (n + 1))) = 1 := by
  simp [eval_headAdversary, Game.advantage, Game.succProbability]

/-- A prechallenge query on the distinguished component, followed by the challenge itself
and a different KEM component carrying the same DEM word. -/
def phaseAdversary : WordCCA2Adversary where
  choose _ _ := do
    let reply ← List.take 1 <$> ProbOracleComp.query ((), encPair encBits encBits ([], []))
    return (([], []), reply)
  guess _ saved ct := do
    let rejected ← List.take 1 <$> ProbOracleComp.query ((), ct)
    let changed ← List.take 1 <$> ProbOracleComp.query
      ((), encPair encBits encBits ([true], dropFrame ct))
    return saved == [true] && rejected == [] && changed == [true]

theorem phaseAdversary_ppt : phaseAdversary.IsPPT := by
  constructor
  · have hq := IsOraclePPTOn.query_take' ()
      (ComputableInPolyTime.const (encPair encBits encBits ([], []))
        (encIn := encPair encUnary encBits))
      (ComputableInPolyTime.const 1)
    have hout : ComputableInPolyTime (fun reply : List Bool => (([], []), reply)) encBits
        (encPair (encPair encBits encBits) encBits) := by fun_prop
    simpa only [phaseAdversary, bind_pure_comp] using (hq.map' hout).isOraclePPT
  · let I := encPair encUnary (encPair encBits encBits)
    have hfirst := IsOraclePPTOn.query_take' ()
      (by fun_prop : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2) I encBits)
      (ComputableInPolyTime.const 1)
    have hrequest : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × List Bool =>
          encPair encBits encBits ([true], dropFrame p.1.2.2)) (encPair I encBits) encBits := by
      polytime
    have hsecond := IsOraclePPTOn.query_take' () hrequest (ComputableInPolyTime.const 1)
    have hout : ComputableInPolyTime
        (fun p : ((ℕ × List Bool × List Bool) × List Bool) × List Bool =>
          p.1.1.2.1 == [true] && p.1.2 == [] && p.2 == [true])
        (encPair (encPair I encBits) encBits) encBool := by polytime
    simpa only [phaseAdversary, bind_pure_comp] using hfirst.bind_with (hsecond.map_with' hout)

example : IsOraclePPT encBool (hybridToOneTimeCCAAdversary echoCipher fixedKeyGen fixedEncaps
    identityDecaps id (fun _ ct => ct.length + 1) phaseAdversary) :=
  isOraclePPT_hybridToOneTimeCCAAdversary echoCipher fixedKeyGen_ppt fixedEncaps_ppt
    identityDecaps_polyTime (by fun_prop) (by fun_prop) phaseAdversary_ppt

theorem eval_phaseAdversary_zero (bit : Bool) :
    ProbComp.eval (hybridDEMGame echoCipher fixedKeyGen fixedEncaps identityDecaps
      phaseAdversary bit 0) = PMF.pure true := by
  cases bit <;> rfl

/-- The actual symmetric experiment of the reduction has the same trace at width zero.
The encryption query returns `[]`, while accepted empty plaintext replies are `[true]`. -/
example (bit : Bool) : ProbComp.eval (echoCipher.ccaOneTimeGame
    (hybridToOneTimeCCAAdversary echoCipher fixedKeyGen fixedEncaps identityDecaps
      id (fun _ ct => ct.length + 1) phaseAdversary) bit 0) = PMF.pure true := by
  rw [← eval_hybridDEMGame echoCipher fixedKeyGen fixedEncaps identityDecaps id
    (fun _ ct => ct.length + 1) phaseAdversary bit 0]
  · exact eval_phaseAdversary_zero bit
  · intro k hk msg hmsg ct hct
    exact (echoCipher_ctLen 0 k hk msg hmsg ct hct).le
  · intro k _ ct
    simp [echoCipher, encOption_some, encBits_apply]

/-- Reject a noncanonical alias with a nonempty KEM projection before making an external call. -/
example : hybridDEMHandler echoCipher identityDecaps (fun _ ct => ct.length + 1)
    0 [] [true] ((), [true, true]) = pure [] := rfl

/-- A failure of local decapsulation remains rejection, not an accepted empty plaintext. -/
example : hybridDEMHandler echoCipher (fun _ _ _ => none) (fun _ ct => ct.length + 1)
    0 [] [] ((), encPair encBits encBits ([true], [])) = pure [] := rfl

/-- At width zero the real PRF Encrypt-then-MAC sampler returns the frame delimiter. A uniform
one-bit sampler also permits `[true]`, so replacing the real sampler would change the experiment. -/
theorem eval_prfKeyGen_zero {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) :
    ProbComp.eval ((prfEncryptThenMAC family hprf.polyTime hprf.length_eq).keyGen 0) =
      PMF.pure [false] := by
  change ProbComp.eval (do
    let ke ← BitString.sampleList 0
    let km ← BitString.sampleList 0
    return encPair encBits encBits (ke, km)) = _
  simp [BitString.sampleList, encPair_apply, encBits_apply, frame]

example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    [true] ∈ (ProbComp.eval (BitString.sampleList 1)).support ∧
      [true] ∉ (ProbComp.eval
        ((prfEncryptThenMAC family hprf.polyTime hprf.length_eq).keyGen 0)).support := by
  constructor
  · rw [BitString.eval_sampleList]
    exact BitString.mem_support_uniformList_iff.mpr rfl
  · rw [eval_prfKeyGen_zero hprf]
    simp

/-- Supported challenge encryption still recovers the message under the override, even if the
original decapsulator rejects the selected KEM component. -/
example (E : SymmetricCipher) (n : ℕ) (k ctK sk msg ct : List Bool)
    (hk : k ∈ (ProbComp.eval (E.keyGen n)).support) (hm : msg.length = n)
    (hc : ct ∈ (ProbComp.eval (E.encrypt n k msg)).support) :
    hybridDecrypt (fun _ _ q => if q == ctK then some k else none) E.decrypt n sk
      (encPair encBits encBits (ctK, ct)) = some msg := by
  rw [hybridDecrypt_encPair]
  simpa using E.decrypt_encrypt n k hk msg hm ct hc

end ComplexityTests.Crypto.HybridDEMCCA
