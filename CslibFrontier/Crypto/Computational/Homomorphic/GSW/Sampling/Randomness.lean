/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Sampling
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# Exact finite randomness for GSW

One flat uniform tape realizes the complete joint law of key generation and encryption.
Its length is `n*w + m*n*w + 2*m*η + (n+1)*w*m`: the secret, public matrix, signed errors,
and binary encryption matrix consume disjoint blocks. No noise tails or rejection sampling
are involved. The law includes the secret key, so it preserves more than ciphertext marginals.

These are distribution identities. Native efficiency of the serialized random-input samplers
is proved separately; matrix computation and cryptographic security remain separate obligations.

## Main results

* `exists_uniform_seed_sampleCoins`: one tape supplies all encryption coins.
* `exists_uniform_seed_keyGen_encrypt`: exact joint key/ciphertext law from a tape of the stated
  length, including zero dimensions or zero noise width.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.1][GentrySahaiWaters2013]
-/

public section

namespace Cslib.Crypto.Homomorphic.GSW

open ProbComp Probability

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
    simpa only [pmf_norm, sampleCoins, PMF.map] using
      congrArg (PMF.map Function.uncurry) hrows⟩

/-- A single flat tape realizes the joint key and ciphertext distribution of the actual programs.
The equality keeps the secret key as well as the public key and ciphertext. -/
theorem exists_uniform_seed_keyGen_encrypt (n m w η : ℕ) (μ : Bool) :
    ∃ evaluate : List Bool →
        ((Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)) × (Fin n → ZMod (2 ^ w))) ×
          Ciphertext n w),
      ProbComp.eval (do
        let keys ← LWE.keyGen n m w η
        let ciphertext ← encrypt keys.1 μ
        return (keys, ciphertext)) =
      (BitString.uniformList
        (n * w + m * n * w + 2 * m * η + (n + 1) * w * m)).map evaluate := by
  obtain ⟨inputs, hinputs⟩ := LWE.exists_uniform_seed_sampleKeyInputs n m w η
  obtain ⟨coins, hcoins⟩ := exists_uniform_seed_sampleCoins n m w
  let finish (x : LWE.KeyInputs n m w) (R : Matrix (Fin (n + 1) × Fin w) (Fin m) Bool) :=
    let keys := (LWE.publicMatrixInt x.publicPart x.secret x.error, x.secret)
    (keys, encryptWithCoins keys.1 μ R)
  have hfinish (x : LWE.KeyInputs n m w) :
      ProbComp.eval (finish x <$> sampleCoins n m w) =
        (BitString.uniformList ((n + 1) * (w * m))).map (finish x ∘ coins) := by
    rw [ProbComp.eval_map, hcoins, PMF.map_comp]
  have hfull := ProbComp.eval_bind_of_uniformList
    (n * w + m * (n * w) + m * (2 * η)) ((n + 1) * (w * m))
    (LWE.sampleKeyInputs n m w η) _ inputs _ hinputs hfinish
  exact ⟨_, by
    simpa only [LWE.keyGen, encrypt, bind_assoc, pure_bind, bind_pure_comp, bind_map_left,
      map_bind, Functor.map_map, finish, Nat.mul_assoc, Nat.mul_left_comm m 2] using hfull⟩

end Cslib.Crypto.Homomorphic.GSW
