/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
public import CslibFrontier.Crypto.Computational.PedersenCommitment.ProbComp
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.Negligible
import Mathlib.Tactic.NormNum.Prime

/-!
# Pedersen fair-coin sampling clients

The concrete order-11 Schnorr group modulo 23 checks an actual supported commitment, verification,
opening length and a nonuniform opening probability. A complete public-input client certifies
sampling followed by verification, with the accuracy parameter and public key charged as input.
-/

@[expose] public section

namespace CslibFrontierTests.Crypto.PedersenSampling

open Cslib Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- A concrete Schnorr group of order `11` modulo `23`. -/
def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- The public element `h = 8` in the concrete Schnorr group. -/
def key23 : schnorrGroups.PedersenKey :=
  ⟨d23, (3 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23⟩

/-- The bounded program can sample opening `5`, yielding commitment `3` to message `4`. -/
theorem supported_commitment :
    (Nat.bits 3, Nat.bits 5) ∈
      (ProbComp.eval (schnorrGroups.pedersenCommitProb 0 key23 (Nat.bits 4))).support := by
  simp only [pedersenCommitProb, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff]
  refine ⟨5, ?_, ?_⟩
  · rw [sampleExp, ProbComp.eval_sampleModNat, PMF.mem_support_map_iff]
    refine ⟨⟨5, by decide⟩, PMF.mem_support_uniformOfFintype _, ?_⟩
    rfl
  · decide

/-- Supported sampled commitments satisfy the existing verifier. -/
example : schnorrGroups.pedersenScheme.verify key23 (Nat.bits 4) (Nat.bits 3) (Nat.bits 5) =
    true := by
  apply schnorrGroups.pedersenVerify_of_mem_support_pedersenCommitProb 0 key23
    (co := (Nat.bits 3, Nat.bits 5)) ?_ supported_commitment
  change ofBits (Nat.bits 4) < 11 ∧ (ofBits (Nat.bits 4)).bits = Nat.bits 4
  decide

/-- The sampled opening has at most four bits, the encoded length of group order `11`. -/
example : (Nat.bits 5).length ≤ 4 :=
  schnorrGroups.length_opening_pedersenCommitProb_le 0 key23 supported_commitment

/-- Four fair bits reduced modulo eleven give opening five probability `1/16`, exhibiting the
actual bounded sampler rather than asserting exact uniform exponent sampling. -/
example : (((ProbComp.eval (schnorrGroups.pedersenCommitProb 0 key23 (Nat.bits 4))).map
    Prod.snd) (Nat.bits 5)).toReal = 1 / 16 := by
  simp only [pedersenCommitProb, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind,
    PMF.pure_map, pedersenPublicOperations]
  change (((ProbComp.eval (schnorrGroups.sampleExp 0 d23)).map Nat.bits) (Nat.bits 5)).toReal = _
  rw [sampleExp, ProbComp.eval_sampleModNat, PMF.map_comp]
  change (((PMF.uniformOfFintype (Fin 16)).map (fun i => (i.val % 11).bits))
    (Nat.bits 5)).toReal = _
  have hbits (a b : ℕ) : a.bits = b.bits ↔ a = b := encNat.injective.eq_iff
  simp only [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply, hbits]
  norm_num [Fin.sum_univ_succ, ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- At accuracy four, even a randomized continuation inspecting both commitment and opening has
at most `1/16` advantage against the existing ideal law. -/
example (continuation : (List Bool × List Bool) → Game) :
    Game.advantage
      ((ProbComp.eval (schnorrGroups.pedersenCommitProb 4 key23 (Nat.bits 4))).bind continuation)
      ((schnorrGroups.pedersenScheme.commitDist key23 (Nat.bits 4)).bind continuation) ≤
        1 / 16 := by
  have h := schnorrGroups.advantage_bind_pedersenCommitProb_le 4 key23 (Nat.bits 4) continuation
  norm_num at h ⊢
  exact h

/-- Two independent `sampleExp 4 d23` draws at accuracy four have at most `1/8` advantage against
two independent exact uniform draws on `ZMod 11`. -/
example (continuation : ZMod (schnorrGroups.order d23) → ZMod (schnorrGroups.order d23) → Game) :
    Game.advantage
      ((ProbComp.eval (schnorrGroups.sampleExp 4 d23)).bind fun a =>
        (ProbComp.eval (schnorrGroups.sampleExp 4 d23)).bind fun b =>
          continuation (a : ZMod (schnorrGroups.order d23)) (b : ZMod (schnorrGroups.order d23)))
      ((PMF.uniformOfFintype (ZMod (schnorrGroups.order d23))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (schnorrGroups.order d23))).bind fun β =>
          continuation α β) ≤
        1 / 8 := by
  have h := schnorrGroups.advantage_bind_sampleExp_pair_le 4 d23 continuation
  norm_num at h ⊢
  exact h

/-- A complete client samples and verifies, charging the unary accuracy, exact public-key bytes
and full message word throughout. -/
example : IsPPTOn
    (encPair encUnary (encPair schnorrGroups.pedersenScheme.encodeKey encBits)) encBool
    (fun p : ℕ × schnorrGroups.PedersenKey × List Bool => do
      let co ← schnorrGroups.pedersenCommitProb p.1 p.2.1 p.2.2
      return schnorrGroups.pedersenScheme.verify p.2.1 p.2.2 co.1 co.2) := by
  let E := encPair encUnary (encPair schnorrGroups.pedersenScheme.encodeKey encBits)
  have hp := ComputableInPolyTime.fst E (encPair encBits encBits)
  have hco := ComputableInPolyTime.snd E (encPair encBits encBits)
  have hrest := (ComputableInPolyTime.snd encUnary
    (encPair schnorrGroups.pedersenScheme.encodeKey encBits)).comp hp
  have hk := (ComputableInPolyTime.fst schnorrGroups.pedersenScheme.encodeKey encBits).comp hrest
  have hm := (ComputableInPolyTime.snd schnorrGroups.pedersenScheme.encodeKey encBits).comp hrest
  have hv := schnorrGroups.pedersenPublicOperations.computableInPolyTime_verify
    hk hm hco.fst' hco.snd'
  exact schnorrGroups.isPPTOn_pedersenCommitProb.bind_with hv.isPPTOn

/-- Native fair-coin Pedersen key generation is uniformly strict PPT in `(n, d)`. -/
example : IsPPTOn (encPair encUnary schnorrGroups.encDesc)
    schnorrGroups.pedersenScheme.encodeKey
    (fun p : ℕ × schnorrGroups.Desc => schnorrGroups.pedersenKeyGenProb p.1 p.2) :=
  schnorrGroups.isPPTOn_pedersenKeyGenProb

/-- At accuracy four, native Pedersen key generation on `d23` has at most `1/16` advantage against
exact uniform trapdoor-key generation. -/
example (continuation : schnorrGroups.PedersenKey → Game) :
    Game.advantage
      ((ProbComp.eval (schnorrGroups.pedersenKeyGenProb 4 d23)).bind continuation)
      ((PMF.uniformOfFintype (ZMod (schnorrGroups.order d23))).bind fun α =>
        continuation ⟨d23, α • schnorrGroups.generator d23⟩) ≤
        1 / 16 := by
  have h := schnorrGroups.advantage_bind_pedersenKeyGenProb_le 4 d23 continuation
  norm_num at h ⊢
  exact h

/-- At accuracy four on `key23` (where `h = 8 ≠ 1`), the native fair-coin Pedersen hiding game
for any stateful adversary has advantage at most `1/8`. -/
example (A : Encryption.WordAdversary) :
    Game.advantage
      (schnorrGroups.pedersenHidingProbForKey key23 A false 4)
      (schnorrGroups.pedersenHidingProbForKey key23 A true 4) ≤
        1 / 8 := by
  have hne : key23.2 ≠ 0 := by
    intro h0
    have h1 := congrArg (schnorrGroups.encode d23) h0
    revert h1
    decide
  have h := schnorrGroups.advantage_pedersenHidingProbForKey_le_of_ne_zero d23 hne A 4
  norm_num at h ⊢
  exact h

/-- Concrete hiding bound for `pedersenHidingProbGame` on the constant-`d23` setup (`m = 11`):
every stateful adversary has distinguishing advantage at most `1 / 11 + 4 / 2 ^ n`. -/
example (A : Encryption.WordAdversary) (n : ℕ) :
    Game.advantage
      (schnorrGroups.pedersenHidingProbGame (fun _ => PMF.pure d23) A false n)
      (schnorrGroups.pedersenHidingProbGame (fun _ => PMF.pure d23) A true n) ≤
      1 / 11 + 4 / 2 ^ n := by
  refine schnorrGroups.advantage_pedersenHidingProbGame_le (fun _ => PMF.pure d23) A n 11
    (by decide) ?_
  intro d hd
  obtain rfl : d = d23 := (PMF.mem_support_pure_iff _ _).mp hd
  decide

/-- Native fair-coin Pedersen hiding after `pedersenKeyGenProb` is unconditionally negligible for
every stateful adversary when `2 ^ n ≤ F.order d`, and the native hiding experiment is uniformly
strict PPT when `A` is strict PPT. -/
example (setup : ℕ → PMF schnorrGroups.Desc)
    (hm : ∀ n, ∀ d ∈ (setup n).support, 2 ^ n ≤ schnorrGroups.order d)
    (A : Encryption.WordAdversary) :
    Negligible (fun n =>
      Game.advantage
        (schnorrGroups.pedersenHidingProbGame setup A false n)
        (schnorrGroups.pedersenHidingProbGame setup A true n)) :=
  schnorrGroups.negligible_advantage_pedersenHidingProbGame setup A
    (fun n => Nat.two_pow_pos n) hm
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using negligible_one_div_two_pow)

example (A : Encryption.WordAdversary) (hA : A.IsPPT) (b : Bool) :
    IsPPTOn (encPair encUnary schnorrGroups.encDesc) encBool
      (fun p : ℕ × schnorrGroups.Desc =>
        schnorrGroups.pedersenHidingProbExperiment A b p.1 p.2) :=
  schnorrGroups.isPPTOn_pedersenHidingProbExperiment hA b

/-- Under the native fair-coin key distribution `pedersenKeyDistProb setup`, the Pedersen
commitment scheme remains statistically hiding and computationally binding under `DiscreteLog`. -/
example (setup : ℕ → PMF schnorrGroups.Desc)
    (hm : ∀ n, ∀ d ∈ (setup n).support, 2 ^ n ≤ schnorrGroups.order d)
    (hDL : schnorrGroups.DiscreteLog setup) :
    schnorrGroups.pedersenScheme.StatisticalHiding (schnorrGroups.pedersenKeyDistProb setup) ∧
      schnorrGroups.pedersenScheme.Binding (schnorrGroups.pedersenKeyDistProb setup) :=
  ⟨schnorrGroups.pedersenScheme_statisticalHiding_pedersenKeyDistProb setup
      (fun n => Nat.two_pow_pos n) hm
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using negligible_one_div_two_pow),
    hDL.pedersenScheme_binding_pedersenKeyDistProb⟩

end CslibFrontierTests.Crypto.PedersenSampling
