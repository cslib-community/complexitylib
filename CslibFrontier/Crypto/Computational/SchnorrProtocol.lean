/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Computational.SchnorrIdentification
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Computational
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Linear
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PPT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Schnorr's Sigma protocol with an efficient extractor and simulator

Schnorr's Sigma protocol ([BonehShoup2023], Example 19.1) over a `PrimeOrderGroupFamily`, as a
family indexed by a unary security parameter `n` and a group description `d`, with challenges in
`ZMod q` for the group order `q`. Group elements are encoded by the family's encoding and scalars
in binary (`schnorrEncoding`).

* **Efficient special soundness** (`efficientSpecialSoundness_schnorr`, Example 19.2): the
  extractor `schnorrExtract` computes `(c - c')⁻¹ (z - z')` with `extractNat`, inverting by
  Fermat's little theorem, in polynomial time.
* **Efficient special HVZK** (`efficientSpecialHVZK_schnorr`, Example 19.3): Boneh and Shoup's
  simulator samples a uniform response `z` and outputs `(z • g - c • u, z)`. The typed simulator
  `schnorrSimulator` samples `z` with `sampleExp`, which is within statistical distance
  `1 / 2 ^ n` of uniform on `ZMod q`, so it realizes the simulator up to `1 / 2 ^ n`. Its strict
  PPT certificate is the word program `schnorrSimulateWord`, which computes it on encodings
  (`eval_schnorrSimulateWord`).
* **Computational special HVZK** (`computationalSpecialHVZK_schnorr`, Definition 20.6): because
  every output of `schnorrSimulator` satisfies `z • g = (z • g - c • u) + c • u` exactly
  (`accepts_schnorrSimulator`, acceptance error `0`), and `1 / 2 ^ n` is negligible along any
  group-description setup `(setup n).map (n, ·)`, `schnorrSimulator` satisfies Definition 20.6
  with zero acceptance error.

The protocol does not depend on the security parameter; only the simulator's sampling error does.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrFamily`: Schnorr's Sigma protocol at each index.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrBitSigma`: Schnorr's Sigma protocol in one group with
  `m`-bit challenges.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrEncoding`: its word encodings.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrExtract`: the extractor, computed with `extractNat`.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSimulator`: the simulator with `sampleExp`.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSimulateWord`: the simulator as a strict PPT program
  on words.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_schnorr`: efficient special
  soundness.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrSimulateWord`,
  `Cslib.Crypto.PrimeOrderGroupFamily.eval_schnorrSimulateWord`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_schnorrSimulator`,
  `Cslib.Crypto.PrimeOrderGroupFamily.simulatorRealizedBy_schnorrSimulator`: the word program is
  strict PPT and computes `schnorrSimulator` on encodings, so `schnorrSimulator` is strict PPT; it
  realizes Boneh and Shoup's simulator up to `1 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialHVZK_schnorr`: efficient special HVZK with
  statistical error `1 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.accepts_schnorrSimulator`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computationalSpecialHVZK_schnorr`: exact acceptance (`δ = 0`)
  and computational special HVZK (Definition 20.6).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Examples 19.1–19.3, Definitions 19.4–19.5, and Definition 20.6.
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991]
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Protocols.SigmaProtocol Interactive
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-- Group elements as words, through the family's injective encoding. -/
def encodeEmbedding (d : F.Desc) : F.Carrier d ↪ List Bool :=
  ⟨F.encode d, F.encode_injective d⟩

/-- Scalars modulo the group order as binary numbers, through their least nonnegative
representatives. -/
def encScalar (d : F.Desc) : ZMod (F.order d) ↪ List Bool :=
  ⟨fun a => encNat a.val, encNat.injective.comp (ZMod.val_injective _)⟩

/-- Schnorr's Sigma protocol ([BonehShoup2023], Example 19.1) in the group described by `i.2`,
with challenges in `ZMod q`. The security parameter `i.1` does not change the protocol. -/
noncomputable def schnorrFamily (i : ℕ × F.Desc) :
    SigmaProtocol (ZMod (F.order i.2)) (F.Carrier i.2) (F.Carrier i.2) (ZMod (F.order i.2))
      (ZMod (F.order i.2)) :=
  schnorr (Function.Embedding.refl _) (F.generator i.2)

/-- Schnorr's Sigma protocol in `F.Carrier d` with `m`-bit challenges `BitString m`, embedded as
scalars by `challengeEmbedding` when `2 ^ m ≤ F.order d`. -/
noncomputable def schnorrBitSigma (d : F.Desc) {m : ℕ} (hm : 2 ^ m ≤ F.order d) :
    SigmaProtocol (ZMod (F.order d)) (F.Carrier d) (F.Carrier d) (BitString m)
      (ZMod (F.order d)) :=
  schnorr (F.challengeEmbedding d hm) (F.generator d)

/-- The word encodings of `schnorrFamily`: the unary security parameter with the description,
group elements by the family's encoding, and challenges and responses in binary. -/
def schnorrEncoding :
    Encoding (ℕ × F.Desc) (fun i => F.Carrier i.2) (fun i => F.Carrier i.2)
      (fun i => ZMod (F.order i.2)) (fun i => ZMod (F.order i.2)) where
  index := encPair encUnary F.encDesc
  statement i := F.encodeEmbedding i.2
  commitment i := F.encodeEmbedding i.2
  challenge i := F.encScalar i.2
  response i := F.encScalar i.2

/-- Schnorr's extractor ([BonehShoup2023], Example 19.2), computed with `extractNat`: it is
`(c - c')⁻¹ (z - z')` whenever `c ≠ c'`. -/
def schnorrExtract (i : ℕ × F.Desc) (_ _ : F.Carrier i.2) (c z c' z' : ZMod (F.order i.2)) :
    ZMod (F.order i.2) :=
  extractNat (F.order i.2) c.val z.val c'.val z'.val

/-- Schnorr's simulator ([BonehShoup2023], Example 19.3) with fair coins: at index `(n, d)`, on a
statement `u` and a challenge `c`, sample `s` with `sampleExp n d`, read it as the response
`z = s mod q`, and return the commitment `z • g - c • u` with `z`. -/
noncomputable def schnorrSimulator :
    Simulator (ℕ × F.Desc) (fun i => F.Carrier i.2) (fun i => F.Carrier i.2)
      (fun i => ZMod (F.order i.2)) (fun i => ZMod (F.order i.2)) :=
  fun i u c => (fun z => (z • F.generator i.2 - c • u, z)) <$>
    ((Nat.cast : ℕ → ZMod (F.order i.2)) <$> F.sampleExp i.1 i.2)

/-- Schnorr's simulator on words ([BonehShoup2023], Example 19.3): on the index `(n, d)`, an
encoded statement `u` and a binary challenge `c`, sample `s` with `sampleExp n d` and return the
encodings of `s • g - c • u` and of `s mod q`. It is the strict PPT certificate of
`schnorrSimulator` (`eval_schnorrSimulateWord`); `SchnorrEavesdrop` also runs it on arbitrary
challenge words. -/
noncomputable def schnorrSimulateWord :
    (ℕ × F.Desc) × List Bool × List Bool → ProbComp (List Bool × List Bool)
  | ((n, d), u, c) => do
    let s ← F.sampleExp n d
    return (F.add (d, F.smul (d, s, F.encode d (F.generator d)),
        F.smul (d, F.order d - ofBits c % F.order d, u)),
      (s % F.order d).bits)

/-! ### Special soundness -/

/-- **Schnorr's protocol has efficient special soundness** ([BonehShoup2023], Example 19.2). -/
theorem efficientSpecialSoundness_schnorr :
    EfficientSpecialSoundness F.schnorrFamily (fun i α u => α • F.generator i.2 = u)
      F.schnorrEncoding (fun i => F.encScalar i.2) F.schnorrExtract where
  specialSoundness i u t c z c' z' hc hz hz' := by
    have hcast : ((c.val : ℕ) : ZMod (F.order i.2)) ≠ (c'.val : ℕ) := by
      simpa only [ZMod.natCast_zmod_val] using hc
    have h := schnorr_specialSoundness (ι := Function.Embedding.refl _) u t c z c' z' hc hz hz'
    simp only [linearExtract, Function.Embedding.refl_apply, smul_eq_mul] at h
    simp only [schnorrExtract, extractNat_cast hcast, ZMod.natCast_zmod_val]
    exact h
  polyTime := by
    let encIn := encPair (encPair encUnary F.encDesc) (encPair encBits (encPair encBits
      (encPair encBits (encPair encBits (encPair encBits encBits)))))
    refine ⟨fun p => (extractNat (F.order p.1.2) (ofBits p.2.2.2.1) (ofBits p.2.2.2.2.1)
      (ofBits p.2.2.2.2.2.1) (ofBits p.2.2.2.2.2.2)).bits, ?_, ?_⟩
    · have hd : ComputableInPolyTime
          (fun p : (ℕ × F.Desc) × List Bool × List Bool × List Bool × List Bool × List Bool ×
            List Bool => p.1.2) encIn F.encDesc := by fun_prop
      have hword {k : (ℕ × F.Desc) × List Bool × List Bool × List Bool × List Bool × List Bool ×
          List Bool → List Bool} (hk : ComputableInPolyTime k encIn encBits) :
          ComputableInPolyTime (fun p => ofBits (k p)) encIn encNat :=
        .of_tidy (ComputableTidilyInPolyTime.bitsToNat.comp hk.tidy)
      have hext := computableInPolyTime_extractNat hd
        (hword (k := fun p => p.2.2.2.1) (by fun_prop))
        (hword (k := fun p => p.2.2.2.2.1) (by fun_prop))
        (hword (k := fun p => p.2.2.2.2.2.1) (by fun_prop))
        (hword (k := fun p => p.2.2.2.2.2.2) (by fun_prop))
      exact .of_tidy (ComputableTidilyInPolyTime.natBits.comp hext.tidy)
    · intro i u t c z c' z'
      simp only [schnorrEncoding, encScalar, encodeEmbedding, Function.Embedding.coeFn_mk,
        encNat_apply, ofBits_bits, schnorrExtract, ZMod.val_natCast, extractNat,
        Nat.mod_mod]

/-! ### Special HVZK -/

open Classical in
/-- An exponent sampled by `sampleExp n d` is within statistical distance `1 / 2 ^ n` of
uniform on `ZMod q`. -/
theorem closeTo_uniform_sampleExp (n : ℕ) (d : F.Desc) :
    CloseTo (PMF.uniformOfFintype (ZMod (F.order d)))
      ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d)))
      (1 / 2 ^ n : ℝ≥0) := by
  refine Game.closeTo_of_advantage_decide_le fun E => ?_
  rw [Game.advantage_comm]
  have h := F.advantage_bind_sampleExp_le n d fun a => PMF.pure (decide (a ∈ E))
  rw [PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact h

/-- On an encoded statement and challenge, `schnorrSimulateWord` computes the encoded output of
`schnorrSimulator`. -/
theorem eval_schnorrSimulateWord (i : ℕ × F.Desc) (u : F.Carrier i.2) (c : ZMod (F.order i.2)) :
    ProbComp.eval (F.schnorrSimulateWord
        (i, F.schnorrEncoding.statement i u, F.schnorrEncoding.challenge i c)) =
      (ProbComp.eval (F.schnorrSimulator i u c)).map
        (Prod.map (F.schnorrEncoding.commitment i) (F.schnorrEncoding.response i)) := by
  obtain ⟨n, d⟩ := i
  have hneg : ((F.order d - c.val % F.order d : ℕ) : ZMod (F.order d)) = -c := by
    rw [Nat.mod_eq_of_lt (ZMod.val_lt c), Nat.cast_sub (ZMod.val_lt c).le, ZMod.natCast_self,
      ZMod.natCast_zmod_val, zero_sub]
  rw [show (F.schnorrEncoding.statement (n, d)) u = F.encode d u from rfl,
    show (F.schnorrEncoding.challenge (n, d)) c = encNat c.val from rfl,
    schnorrSimulateWord, ProbComp.eval_bind, schnorrSimulator, ProbComp.eval_map,
    ProbComp.eval_map, PMF.map_comp, PMF.map_comp]
  simp only [ProbComp.eval_pure, encNat_apply, ofBits_bits, F.smul_encode, F.add_encode, hneg,
    neg_smul, ← sub_eq_add_neg]
  rw [← PMF.bind_pure_comp]
  congr 1 with a : 1
  simp only [Function.comp_apply, Prod.map, schnorrEncoding, encodeEmbedding, encScalar,
    Function.Embedding.coeFn_mk, encNat_apply, ZMod.val_natCast]

/-- `schnorrSimulateWord` is uniform strict PPT in the security parameter, the description and the
encoded statement and challenge. -/
theorem isPPTOn_schnorrSimulateWord :
    IsPPTOn (encPair (encPair encUnary F.encDesc) (encPair encBits encBits))
      (encPair encBits encBits) F.schnorrSimulateWord := by
  let encIn := encPair (encPair encUnary F.encDesc) (encPair encBits encBits)
  have hn : ComputableInPolyTime (fun p : (ℕ × F.Desc) × List Bool × List Bool => p.1.1)
      encIn encUnary := by fun_prop
  have hd : ComputableInPolyTime (fun p : (ℕ × F.Desc) × List Bool × List Bool => p.1.2)
      encIn F.encDesc := by fun_prop
  change IsPPTOn encIn _ fun p => F.sampleExp p.1.1 p.1.2 >>= fun s =>
    pure (F.add (p.1.2, F.smul (p.1.2, s, F.encode p.1.2 (F.generator p.1.2)),
        F.smul (p.1.2, F.order p.1.2 - ofBits p.2.2 % F.order p.1.2, p.2.1)),
      (s % F.order p.1.2).bits)
  refine (F.isPPTOn_sampleExp hn hd).bind_with ?_
  let encMid := encPair encIn encNat
  have hd' : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
      p.1.1.2) encMid F.encDesc := by fun_prop
  have hs : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
      p.2) encMid encNat := by fun_prop
  have hu : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
      p.1.2.1) encMid encBits := by fun_prop
  have hc : ComputableInPolyTime (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
      p.1.2.2) encMid encBits := by fun_prop
  have hq := F.computableInPolyTime_order.comp hd'
  have hg := F.computableInPolyTime_generator.comp hd'
  have hsg := F.computableInPolyTime_smul.comp (hd'.prod (hs.prod hg))
  have hneg : ComputableInPolyTime
      (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
        F.order p.1.1.2 - ofBits p.1.2.2 % F.order p.1.1.2) encMid encNat :=
    .of_tidy (.binary_sub' hq.tidy (.binary_mod'
      (ComputableTidilyInPolyTime.bitsToNat.comp hc.tidy) hq.tidy))
  have hcu := F.computableInPolyTime_smul.comp (hd'.prod (hneg.prod hu))
  have ht := F.computableInPolyTime_add.comp (hd'.prod (hsg.prod hcu))
  have hz : ComputableInPolyTime
      (fun p : ((ℕ × F.Desc) × List Bool × List Bool) × ℕ =>
        (p.2 % F.order p.1.1.2).bits) encMid encBits :=
    .of_tidy (ComputableTidilyInPolyTime.natBits.comp (.binary_mod' hs.tidy hq.tidy))
  exact (ht.prod hz).isPPTOn

/-- `schnorrSimulator` is uniform strict PPT, certified by `schnorrSimulateWord`. -/
theorem isPPT_schnorrSimulator : Simulator.IsPPT F.schnorrEncoding F.schnorrSimulator :=
  .of_word F.isPPTOn_schnorrSimulateWord fun i u c => (F.eval_schnorrSimulateWord i u c).symm

/-- `schnorrSimulator` realizes Schnorr's perfect simulator `linearSimulate`
([BonehShoup2023], Example 19.3) up to statistical distance `1 / 2 ^ n` at security parameter
`n`. -/
theorem simulatorRealizedBy_schnorrSimulator :
    SimulatorRealizedBy
      (fun i : ℕ × F.Desc => linearSimulate (fun _ => LinearMap.toSpanSingleton
        (ZMod (F.order i.2)) (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _))
      F.schnorrSimulator (fun i => 1 / 2 ^ i.1) := by
  intro i u c
  have hδ : (((1 / 2 ^ i.1 : ℝ≥0)) : ℝ≥0∞) = 1 / 2 ^ i.1 := by
    rw [ENNReal.coe_div (pow_ne_zero _ two_ne_zero), ENNReal.coe_one, ENNReal.coe_pow,
      ENNReal.coe_ofNat]
  simp only [schnorrSimulator, ProbComp.eval_map]
  rw [← hδ]
  exact (F.closeTo_uniform_sampleExp i.1 i.2).map _

/-- **Schnorr's protocol has efficient special HVZK** ([BonehShoup2023], Example 19.3), with
statistical error `1 / 2 ^ n` at security parameter `n`: the perfect simulator `linearSimulate` is
realized by the strict PPT simulator `schnorrSimulator`. -/
theorem efficientSpecialHVZK_schnorr :
    EfficientSpecialHVZK F.schnorrFamily (fun i α u => α • F.generator i.2 = u) F.schnorrEncoding
      (fun i => linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2))
        (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _))
      (fun i => 1 / 2 ^ i.1) where
  specialHVZK _ := schnorr_specialHVZK
  realized := ⟨_, F.isPPT_schnorrSimulator, F.simulatorRealizedBy_schnorrSimulator⟩

/-- Every output of `schnorrSimulator` is an accepting conversation (acceptance error `0`): for
every sampled `z`, `(z • g - c • u) + c • u = z • g`. -/
theorem accepts_schnorrSimulator (i : ℕ × F.Desc) (u : F.Carrier i.2) (c : ZMod (F.order i.2)) :
    (ProbComp.eval (F.schnorrSimulator i u c)).toOuterMeasure
      {tz | (F.schnorrFamily i).Accepts u tz.1 c tz.2} = 1 := by
  simp only [schnorrSimulator, ProbComp.eval_map, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_apply_eq_one_iff]
  intro z _
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, schnorrFamily, schnorr_accepts_iff,
    Function.Embedding.refl_apply, sub_add_cancel]

/-- **Schnorr's protocol has computational special HVZK** ([BonehShoup2023], Definition 20.6) with
zero acceptance error (`δ = fun _ => 0`) over any group-description setup `setup : ℕ → PMF F.Desc`
paired with the security parameter. -/
theorem computationalSpecialHVZK_schnorr (setup : ℕ → PMF F.Desc) :
    ComputationalSpecialHVZK F.schnorrFamily (fun i α u => α • F.generator i.2 = u)
      F.schnorrEncoding (fun i => F.encScalar i.2) (fun n => (setup n).map (n, ·))
      F.schnorrSimulator (fun _ => 0) := by
  refine F.simulatorRealizedBy_schnorrSimulator.computationalSpecialHVZK_of_accepts
    (fun _ => schnorr_specialHVZK) F.isPPT_schnorrSimulator
    (fun i u c => by rw [F.accepts_schnorrSimulator i u c, tsub_zero])
    ⟨fun n => (1 / 2 : ℝ≥0) ^ n, negligible_geometric (by norm_num), fun n i hi => ?_⟩
  obtain ⟨d, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
  dsimp only
  rw [one_div_pow, ENNReal.coe_div (pow_ne_zero _ two_ne_zero), ENNReal.coe_one, ENNReal.coe_pow,
    ENNReal.coe_ofNat]

end Cslib.Crypto.PrimeOrderGroupFamily
