/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling

/-!
# Group parameters with an attached public key

A scheme over a prime-order group may also publish a key for another component. Cramer and Shoup
draw the key of their hash function at key generation and put it in the public key
([CramerShoup2003], Section 6.1, Figure 1). `F.withKey` is the group family `F` with a word `k`
attached to every group description: its parameters are pairs `(d, k)`, and the group, order,
generator and operations at `(d, k)` are those of `F` at `d`. A component keyed by `k`, such as a
hash function, can then take the pair `(d, k)` as its public system parameter, and its security
notion is stated for the setup `withKeySetup setup keyLen`, which draws `d ← setup n` and an
independent uniform `keyLen n`-bit key.

DDH ignores the key. `DDH.withKey` derives DDH for `F.withKey` under `withKeySetup setup keyLen`
from DDH for `F` under `setup`. The reduction `ddhSampleKey` draws the key itself, and
`isPPT_ddhSampleKey` certifies it.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.withKey`: the family with a public word attached to each
  group description.
* `Cslib.Crypto.PrimeOrderGroupFamily.withKeySetup`: a setup law followed by a uniform key.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhSampleKey`: the DDH reduction that samples the key.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhSampleKey`: the reduction is PPT.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRealGame_ddhSampleKey`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRandomGame_ddhSampleKey`: it plays the DDH games of
  `F.withKey` exactly.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.withKey`: DDH for `F` gives DDH for `F.withKey`.

## References

* [R. Cramer, V. Shoup, *Design and Analysis of Practical Public-Key Encryption Schemes Secure
  against Adaptive Chosen Ciphertext Attack*][CramerShoup2003], Section 6.1, Figure 1.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM

variable (F : PrimeOrderGroupFamily)

/-- The family `F` with a public word `k` attached to every group description. Its parameters
are pairs `(d, k)`; the group, its order, generator, encoding and operations at `(d, k)` are those
of `F` at `d`, and the parameters are encoded as `encPair F.encDesc encBits`. -/
abbrev withKey : PrimeOrderGroupFamily where
  Desc := F.Desc × List Bool
  encDesc := encPair F.encDesc encBits
  order p := F.order p.1
  prime_order p := F.prime_order p.1
  Carrier p := F.Carrier p.1
  addCommGroup p := F.addCommGroup p.1
  module p := F.module p.1
  generator p := F.generator p.1
  card_carrier p := F.card_carrier p.1
  generator_ne_zero p := F.generator_ne_zero p.1
  encode p := F.encode p.1
  encode_injective p := F.encode_injective p.1
  add := fun ((d, _), xy) => F.add (d, xy)
  add_encode p := F.add_encode p.1
  smul := fun ((d, _), ax) => F.smul (d, ax)
  smul_encode p := F.smul_encode p.1
  computableInPolyTime_order :=
    F.computableInPolyTime_order.comp (ComputableInPolyTime.fst F.encDesc encBits)
  computableInPolyTime_generator :=
    F.computableInPolyTime_generator.comp (ComputableInPolyTime.fst F.encDesc encBits)
  computableInPolyTime_add := by
    have hp := ComputableInPolyTime.id'
      (encIn := encPair (encPair F.encDesc encBits) (encPair encBits encBits))
    exact F.computableInPolyTime_add.comp (hp.fst'.fst'.prod hp.snd')
  computableInPolyTime_smul := by
    have hp := ComputableInPolyTime.id'
      (encIn := encPair (encPair F.encDesc encBits) (encPair encNat encBits))
    exact F.computableInPolyTime_smul.comp (hp.fst'.fst'.prod hp.snd')

/-- Draw group parameters `d ← setup n`, then an independent uniform `keyLen n`-bit key `k`, and
return `(d, k)`. -/
@[expose] noncomputable def withKeySetup (setup : ℕ → PMF F.Desc) (keyLen : ℕ → ℕ) (n : ℕ) :
    PMF F.withKey.Desc :=
  (setup n).bind fun d => (ProbComp.eval (BitString.sampleList (keyLen n))).map fun k => (d, k)

/-- A key in the support of `withKeySetup setup keyLen n` has length `keyLen n`, and its group
parameters are in the support of `setup n`. -/
theorem mem_support_withKeySetup {setup : ℕ → PMF F.Desc} {keyLen : ℕ → ℕ} {n : ℕ}
    {d : F.Desc} {k : List Bool} (h : (d, k) ∈ (F.withKeySetup setup keyLen n).support) :
    d ∈ (setup n).support ∧ k.length = keyLen n := by
  rw [withKeySetup, PMF.mem_support_bind_iff] at h
  obtain ⟨d', hd', hk⟩ := h
  rw [PMF.mem_support_map_iff, BitString.eval_sampleList] at hk
  obtain ⟨k', hk', heq⟩ := hk
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact ⟨hd', BitString.length_of_mem_support_uniformList hk'⟩

/-- **DDH reduction that samples the key**: given a DDH distinguisher for `F.withKey`, draw a
uniform `keyLen n`-bit key `k` and run it on the group parameters `(d, k)`. -/
noncomputable def ddhSampleKey (keyLen : ℕ → ℕ) (distinguisher : F.withKey.DDHDistinguisher) :
    F.DDHDistinguisher :=
  fun n d u v w => do
    let k ← BitString.sampleList (keyLen n)
    distinguisher n (d, k) u v w

variable {F} in
/-- `ddhSampleKey` is uniform strict PPT when the distinguisher is and `keyLen` is computable in
polynomial time on unary numbers. -/
theorem isPPT_ddhSampleKey {keyLen : ℕ → ℕ}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {distinguisher : F.withKey.DDHDistinguisher} (hD : distinguisher.IsPPT) :
    (F.ddhSampleKey keyLen distinguisher).IsPPT := by
  have hn : ComputableInPolyTime (fun x : F.DDHInput => x.secParam) F.encDDHInput encUnary := by
    fun_prop
  have hp := ComputableInPolyTime.id' (encIn := encPair F.encDDHInput encBits)
  have hsecond : IsPPTOn (encPair F.encDDHInput encBits) encBool
      (fun p : F.DDHInput × List Bool => distinguisher p.1.secParam (p.1.groupParameters, p.2)
        p.1.leftPublic p.1.rightPublic p.1.candidateShared) :=
    hD.comp (F := F.withKey) (hn.comp hp.fst')
      ((show ComputableInPolyTime (fun x : F.DDHInput => x.groupParameters) F.encDDHInput
        F.encDesc by fun_prop).comp hp.fst' |>.prod hp.snd')
      ((show ComputableInPolyTime (fun x : F.DDHInput => F.encode x.groupParameters x.leftPublic)
        F.encDDHInput encBits by fun_prop).comp hp.fst')
      ((show ComputableInPolyTime (fun x : F.DDHInput => F.encode x.groupParameters x.rightPublic)
        F.encDDHInput encBits by fun_prop).comp hp.fst')
      ((show ComputableInPolyTime
        (fun x : F.DDHInput => F.encode x.groupParameters x.candidateShared)
        F.encDDHInput encBits by fun_prop).comp hp.fst')
  exact (hkeyLen.comp hn).sampleList.bind_with hsecond

/-- In the real DDH game, `ddhSampleKey` plays the real DDH game of `F.withKey` under
`withKeySetup`. -/
theorem ddhRealGame_ddhSampleKey (setup : ℕ → PMF F.Desc) (keyLen : ℕ → ℕ)
    (distinguisher : F.withKey.DDHDistinguisher) (n : ℕ) :
    F.ddhRealGame setup (F.ddhSampleKey keyLen distinguisher) n =
      F.withKey.ddhRealGame (F.withKeySetup setup keyLen) distinguisher n := by
  simp only [ddhRealGame, withKeySetup, Game.withSetup, PMF.bind_bind, ddhRealExperiment,
    ddhSampleKey, ProbComp.eval_bind]
  refine congrArg _ (funext fun d => ?_)
  rw [PMF.bind_map]
  conv_lhs => arg 2; ext a; rw [PMF.bind_comm]
  rw [PMF.bind_comm]
  rfl

/-- In the random DDH game, `ddhSampleKey` plays the random DDH game of `F.withKey` under
`withKeySetup`. -/
theorem ddhRandomGame_ddhSampleKey (setup : ℕ → PMF F.Desc) (keyLen : ℕ → ℕ)
    (distinguisher : F.withKey.DDHDistinguisher) (n : ℕ) :
    F.ddhRandomGame setup (F.ddhSampleKey keyLen distinguisher) n =
      F.withKey.ddhRandomGame (F.withKeySetup setup keyLen) distinguisher n := by
  simp only [ddhRandomGame, withKeySetup, Game.withSetup, PMF.bind_bind, ddhRandomExperiment,
    ddhSampleKey, ProbComp.eval_bind]
  refine congrArg _ (funext fun d => ?_)
  rw [PMF.bind_map]
  conv_lhs => arg 2; ext a; arg 2; ext b; rw [PMF.bind_comm]
  conv_lhs => arg 2; ext a; rw [PMF.bind_comm]
  rw [PMF.bind_comm]
  rfl

/-- **DDH ignores an attached key**: DDH for `F` under `setup` gives DDH for `F.withKey` under
`withKeySetup setup keyLen`, through the explicit reduction `ddhSampleKey` and its certificate
`isPPT_ddhSampleKey`. -/
theorem DDH.withKey {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} {keyLen : ℕ → ℕ}
    (hDDH : F.DDH setup) (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    F.withKey.DDH (F.withKeySetup setup keyLen) := by
  intro distinguisher hD
  have h := hDDH _ (isPPT_ddhSampleKey hkeyLen hD)
  simpa only [ddhRealGame_ddhSampleKey, ddhRandomGame_ddhSampleKey] using h

end Cslib.Crypto.PrimeOrderGroupFamily
