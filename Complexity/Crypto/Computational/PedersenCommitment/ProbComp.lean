/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.PedersenCommitment.PublicOperations
public import Complexity.Crypto.Computational.DiffieHellman
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Foundations.Data.Nat.Bits
import Complexity.Languages.Probabilistic.UniformNat.Support
import Complexity.Probability.PMF.Uniform

/-!
# Fair-coin realization of Pedersen commitments

`PrimeOrderGroupFamily.pedersenCommitProb` samples an exponent using the existing bounded
`sampleExp` program and evaluates the existing public commitment operations. Its native strict-PPT
certificate charges the unary accuracy parameter, exactly `pedersenScheme.encodeKey`, and the
message word. The sampler uses `n + |encNat q|` fair bits for `q = F.order d`, and every opening
has at most `|encNat q|` bits.

The output law is explicit. Against every randomized Boolean continuation, replacing it by the
existing ideal `pedersenScheme.commitDist` changes success probability by at most `1 / 2 ^ n`.
Supported outputs verify for valid messages. This approximates the ideal law; it does not replace
that law with a claim of exact fair-coin sampling, certify setup generation, or transfer the
scheme's security games to an executable implementation. The realization and certificate
packaging here are original.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.pedersenCommitProb`: bounded fair-coin commitment and opening.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_pedersenCommitProb`: uniform strict PPT from the
  advertised public key bytes and full input.
* `Cslib.Crypto.PrimeOrderGroupFamily.eval_pedersenCommitProb`: exact output law.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_pedersenCommitProb_le`: error at most
  `1 / 2 ^ n` against every randomized Boolean continuation.
* `Cslib.Crypto.PrimeOrderGroupFamily.pedersenVerify_of_mem_support_pedersenCommitProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.length_opening_pedersenCommitProb_le`: support correctness
  and opening-length bound.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-- Sample a bounded approximately uniform exponent, then evaluate Pedersen's public commitment
operations on its canonical bit representation. The accuracy parameter controls the sampling
error; the ideal law remains `pedersenScheme.commitDist`. -/
noncomputable def pedersenCommitProb (n : ℕ) (key : F.PedersenKey) (message : List Bool) :
    ProbComp (List Bool × List Bool) := do
  let r ← F.sampleExp n key.1
  return F.pedersenPublicOperations.commit key message r.bits

/-- Pedersen commitment sampling is uniformly strict PPT in the unary accuracy parameter, actual
public key encoding, and message word. -/
theorem isPPTOn_pedersenCommitProb :
    IsPPTOn (encPair encUnary (encPair F.pedersenScheme.encodeKey encBits))
      (encPair encBits encBits)
      (fun p : ℕ × F.PedersenKey × List Bool => F.pedersenCommitProb p.1 p.2.1 p.2.2) := by
  let E := encPair encUnary (encPair F.pedersenScheme.encodeKey encBits)
  have hn := ComputableInPolyTime.fst encUnary (encPair F.pedersenScheme.encodeKey encBits)
  have hrest := ComputableInPolyTime.snd encUnary (encPair F.pedersenScheme.encodeKey encBits)
  have hk := (ComputableInPolyTime.fst F.pedersenScheme.encodeKey encBits).comp hrest
  have hm := (ComputableInPolyTime.snd F.pedersenScheme.encodeKey encBits).comp hrest
  have hkey : ComputableInPolyTime
      (fun k : F.PedersenKey => (k.1, F.encode k.1 k.2))
      F.pedersenScheme.encodeKey (encPair F.encDesc encBits) := .of_eq fun _ => rfl
  have hd := (hkey.comp hk).fst'
  have hs := F.isPPTOn_sampleExp hn hd
  have hinput := ComputableInPolyTime.fst E encNat
  have hr : ComputableInPolyTime
      (fun p : (ℕ × F.PedersenKey × List Bool) × ℕ => p.2.bits)
      (encPair E encNat) encBits :=
    (ComputableInPolyTime.of_eq fun _ => rfl).comp (ComputableInPolyTime.snd E encNat)
  have heval := F.pedersenPublicOperations.computableInPolyTime_commit
    (hk.comp hinput) (hm.comp hinput) hr
  unfold pedersenCommitProb
  exact hs.bind_with heval.isPPTOn

/-- The sampled output is the existing Pedersen commitment-and-opening map applied to the
approximately uniform residue law. -/
theorem eval_pedersenCommitProb (n : ℕ) (key : F.PedersenKey) (message : List Bool) :
    ProbComp.eval (F.pedersenCommitProb n key message) =
      ((ProbComp.eval (F.sampleExp n key.1)).map
        (Nat.cast : ℕ → ZMod (F.order key.1))).map
        (fun r =>
          (F.encode key.1 (F.pedersenCommit key.1 key.2 (ofBits message) r), r.val.bits)) := by
  simp only [pedersenCommitProb, ProbComp.eval_bind, ProbComp.eval_pure]
  change (ProbComp.eval (F.sampleExp n key.1)).map
      (fun r => F.pedersenPublicOperations.commit key message r.bits) = _
  rw [PMF.map_comp]
  apply PMF.map_congr_on_support
  intro r hr
  have hlt := ProbComp.lt_of_mem_support_sampleModNat (F.prime_order key.1).pos hr
  have hval : (r : ZMod (F.order key.1)).val = r := ZMod.val_natCast_of_lt hlt
  simp only [pedersenPublicOperations, encodePedersenCommit_encode, ofBits,
    Nat.foldr_bit_bits, Function.comp_apply, hval]

/-- Every randomized Boolean continuation changes by at most `1 / 2 ^ n` when the sampled
commitment is replaced with the existing ideal commitment law. -/
theorem advantage_bind_pedersenCommitProb_le (n : ℕ) (key : F.PedersenKey)
    (message : List Bool) (continuation : (List Bool × List Bool) → Game) :
    Game.advantage ((ProbComp.eval (F.pedersenCommitProb n key message)).bind continuation)
      ((F.pedersenScheme.commitDist key message).bind continuation) ≤ 1 / 2 ^ n := by
  rw [F.eval_pedersenCommitProb]
  simpa only [pedersenScheme, pedersenCommitPairLaw, PMF.bind_map, Function.comp_def] using
    F.advantage_bind_sampleExp_le n key.1
      (fun r => continuation
        (F.encode key.1 (F.pedersenCommit key.1 key.2 (ofBits message) r), r.val.bits))

/-- A sampled commitment and opening verify whenever the message is valid. -/
theorem pedersenVerify_of_mem_support_pedersenCommitProb (n : ℕ) (key : F.PedersenKey)
    {message : List Bool} {co : List Bool × List Bool}
    (hm : F.pedersenScheme.ValidMessage key message)
    (hco : co ∈ (ProbComp.eval (F.pedersenCommitProb n key message)).support) :
    F.pedersenScheme.verify key message co.1 co.2 = true := by
  rw [F.eval_pedersenCommitProb, PMF.support_map] at hco
  obtain ⟨r, _, rfl⟩ := hco
  apply F.pedersenScheme.verify_of_mem_support key message _ hm
  simp only [pedersenScheme, pedersenCommitPairLaw, PMF.support_map]
  exact ⟨r, by simp, rfl⟩

/-- Every supported opening has at most the bit length of the public group order. -/
theorem length_opening_pedersenCommitProb_le (n : ℕ) (key : F.PedersenKey)
    {message : List Bool} {co : List Bool × List Bool}
    (hco : co ∈ (ProbComp.eval (F.pedersenCommitProb n key message)).support) :
    co.2.length ≤ (encNat (F.order key.1)).length := by
  rw [F.eval_pedersenCommitProb, PMF.support_map] at hco
  obtain ⟨r, _, rfl⟩ := hco
  simpa only [encNat_apply, ← Nat.size_eq_bits_len] using
    Nat.size_le_size (ZMod.val_lt r).le

end Cslib.Crypto.PrimeOrderGroupFamily
