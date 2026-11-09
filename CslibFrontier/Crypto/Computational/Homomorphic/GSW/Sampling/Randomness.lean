/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Sampling

/-!
# Exact finite randomness for GSW

One flat uniform tape realizes the complete joint law of key generation and encryption.
Its length is `n*w + m*n*w + 2*m*η + (n+1)*w*m`: the secret, public matrix, signed errors,
and binary encryption matrix consume disjoint blocks. No noise tails or rejection sampling
are involved. The law includes the secret key, so it preserves more than ciphertext marginals.

These are distribution identities. Native efficiency of the serialized random-input samplers
is proved separately; matrix computation and cryptographic security remain separate obligations.

## Main results

* `exists_uniform_seed_sampleKeyInputs`: one tape supplies all independent key inputs.
* `exists_uniform_seed_sampleCoins`: one tape supplies all encryption coins.
* `exists_uniform_seed_keyGen_encrypt`: exact joint key/ciphertext law from a tape of the stated
  length, including zero dimensions or zero noise width.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.1][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open ProbComp Probability

/-- A residue uses a uniform word of exactly its binary width. -/
theorem exists_uniform_seed_sampleResidue (w : ℕ) :
    ∃ evaluate : List Bool → ZMod (2 ^ w),
      ProbComp.eval (sampleResidue w) = (BitString.uniformList w).map evaluate := by
  refine ⟨fun bits => (BitString.binaryValue bits : ZMod (2 ^ w)), ?_⟩
  simp only [sampleResidue, sampleBinaryNat, ProbComp.eval_map, BitString.eval_sampleList,
    PMF.map_comp, Function.comp_def]

/-- Independent residues use disjoint width-sized blocks. -/
theorem exists_uniform_seed_sampleVector (count w : ℕ) :
    ∃ evaluate : List Bool → Fin count → ZMod (2 ^ w),
      ProbComp.eval (sampleVector count w) =
        (BitString.uniformList (count * w)).map evaluate := by
  obtain ⟨evaluate, hlaw⟩ := exists_uniform_seed_sampleResidue w
  exact ⟨_, ProbComp.eval_replicateFin_of_uniformList count w _ evaluate hlaw⟩

/-- Independent rows use disjoint row-sized blocks. -/
theorem exists_uniform_seed_sampleMatrix (rows cols w : ℕ) :
    ∃ evaluate : List Bool → Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w)),
      ProbComp.eval (sampleMatrix rows cols w) =
        (BitString.uniformList (rows * (cols * w))).map evaluate := by
  obtain ⟨evaluate, hlaw⟩ := exists_uniform_seed_sampleVector cols w
  exact ⟨_, ProbComp.eval_replicateFin_of_uniformList rows (cols * w) _ evaluate hlaw⟩

/-- The complete binary coin matrix uses one bit for each entry. -/
theorem exists_uniform_seed_sampleCoins (n m w : ℕ) :
    ∃ evaluate : List Bool → Matrix (Fin (n + 1) × Fin w) (Fin m) Bool,
      ProbComp.eval (sampleCoins n m w) =
        (BitString.uniformList ((n + 1) * (w * m))).map evaluate := by
  unfold Matrix
  have hbit : ProbComp.eval (ProbComp.uniform Bool) =
      (BitString.uniformList 1).map (fun bits => bits.headD false) := by
    simp [BitString.uniformList_succ, BitString.uniformList_zero, PMF.map_bind]
  have hrow := ProbComp.eval_replicateFin_of_uniformList m 1
    (ProbComp.uniform Bool) (fun bits => bits.headD false) hbit
  simp only [Nat.mul_one] at hrow
  have hblock := ProbComp.eval_replicateFin_of_uniformList w m _ _ hrow
  have hrows := ProbComp.eval_replicateFin_of_uniformList (n + 1) (w * m) _ _ hblock
  exact ⟨_, by
    simpa only [sampleCoins, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_comp,
      PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind] using
      congrArg (PMF.map Function.uncurry) hrows⟩

/-- All key-generation inputs are independent functions of disjoint parts of one finite tape. -/
theorem exists_uniform_seed_sampleKeyInputs (n m w η : ℕ) :
    ∃ evaluate : List Bool → KeyInputs n m w,
      ProbComp.eval (sampleKeyInputs n m w η) =
        (BitString.uniformList (n * w + m * (n * w) + m * (2 * η))).map evaluate := by
  obtain ⟨secret, hsecret⟩ := exists_uniform_seed_sampleVector n w
  obtain ⟨publicPart, hpublicPart⟩ := exists_uniform_seed_sampleMatrix m n w
  have herror := ProbComp.eval_replicateFin_of_uniformList m (2 * η)
    (sampleCenteredBinomial η) _ (eval_sampleCenteredBinomial_eq_map η)
  have hrest (t : Fin n → ZMod (2 ^ w)) :=
    ProbComp.eval_bind_of_uniformList (m * (n * w)) (m * (2 * η))
      (sampleMatrix m n w)
      (fun B => KeyInputs.mk t B <$> OracleComp.replicateFin m (sampleCenteredBinomial η))
      publicPart _ hpublicPart (fun B => by rw [ProbComp.eval_map, herror, PMF.map_comp])
  have hfull := ProbComp.eval_bind_of_uniformList (n * w) (m * (n * w) + m * (2 * η))
    (sampleVector n w) _ secret _ hsecret hrest
  exact ⟨_, by simpa only [sampleKeyInputs, bind_pure_comp, Nat.add_assoc] using hfull⟩

/-- A single flat tape realizes the joint key and ciphertext distribution of the actual programs.
The equality keeps the secret key as well as the public key and ciphertext. -/
theorem exists_uniform_seed_keyGen_encrypt (n m w η : ℕ) (μ : Bool) :
    ∃ evaluate : List Bool →
        ((Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)) × (Fin n → ZMod (2 ^ w))) ×
          Ciphertext n w),
      ProbComp.eval (do
        let keys ← keyGen n m w η
        let ciphertext ← encrypt keys.1 μ
        return (keys, ciphertext)) =
      (BitString.uniformList
        (n * w + m * n * w + 2 * m * η + (n + 1) * w * m)).map evaluate := by
  obtain ⟨inputs, hinputs⟩ := exists_uniform_seed_sampleKeyInputs n m w η
  obtain ⟨coins, hcoins⟩ := exists_uniform_seed_sampleCoins n m w
  let finish (x : KeyInputs n m w) (R : Matrix (Fin (n + 1) × Fin w) (Fin m) Bool) :=
    let keys := (publicMatrix x.publicPart x.secret x.error, x.secret)
    (keys, encryptWithCoins keys.1 μ R)
  have hfinish (x : KeyInputs n m w) :
      ProbComp.eval (finish x <$> sampleCoins n m w) =
        (BitString.uniformList ((n + 1) * (w * m))).map (finish x ∘ coins) := by
    rw [ProbComp.eval_map, hcoins, PMF.map_comp]
  have hfull := ProbComp.eval_bind_of_uniformList
    (n * w + m * (n * w) + m * (2 * η)) ((n + 1) * (w * m))
    (sampleKeyInputs n m w η) _ inputs _ hinputs hfinish
  exact ⟨_, by
    simpa only [keyGen, encrypt, bind_assoc, pure_bind, bind_pure_comp, bind_map_left, map_bind,
      Functor.map_map, finish, Nat.mul_assoc, Nat.mul_left_comm m 2] using hfull⟩

end Cslib.Crypto.Homomorphic.GSW
