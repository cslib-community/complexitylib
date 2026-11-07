/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Crypto.Computational.DiscreteLog.SchnorrGroup
public import Complexity.Crypto.Computational.PedersenCommitment.ProbComp
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Probability.PMF.Uniform
import Mathlib.Tactic.NormNum.Prime

/-!
# Pedersen fair-coin sampling clients

The concrete order-11 Schnorr group modulo 23 checks an actual supported commitment, verification,
opening length and a nonuniform opening probability. A complete public-input client certifies
sampling followed by verification, with the accuracy parameter and public key charged as input.
-/

@[expose] public section

namespace ComplexityTests.Crypto.PedersenSampling

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

end ComplexityTests.Crypto.PedersenSampling
