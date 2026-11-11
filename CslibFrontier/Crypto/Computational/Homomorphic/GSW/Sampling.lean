/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.SuppCases

/-!
# Finite sampling for the GSW construction

Binary encryption coin sampling and fresh/NAND correctness over supported draws of `LWE.keyGen`.
Key-input sampling (`LWE.sampleKeyInputs`, `LWE.keyGen`) is shared in
`Crypto.Computational.LWE.KeyGen`.

## Main definitions

* `sampleCoins`: independent binary encryption coin sampler.
* `encrypt`: fresh GSW encryption using uniform binary coins.

## Main results

* `eval_sampleCoins`: exact uniform coin law.
* `mem_support_encrypt_iff`: characterization of supported ciphertexts.
* `keyGen_encrypt_correct`, `keyGen_nand_correct`: correctness for all supported draws.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.1][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open ProbComp Probability

/-- Sample every entry of the binary encryption matrix independently. -/
noncomputable def sampleCoins (n m w : ℕ) :
    ProbComp (Matrix (Fin (n + 1) × Fin w) (Fin m) Bool) := do
  let rows ← OracleComp.replicateFin (n + 1)
    (OracleComp.replicateFin w (OracleComp.replicateFin m (ProbComp.uniform Bool)))
  return Function.uncurry rows

@[simp] theorem eval_sampleCoins (n m w : ℕ) :
    ProbComp.eval (sampleCoins n m w) =
      PMF.uniformOfFintype (Matrix (Fin (n + 1) × Fin w) (Fin m) Bool) := by
  unfold Matrix
  simp only [sampleCoins, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_replicateFin, ProbComp.eval_uniform, PMF.pi_uniformOfFintype]
  exact PMF.uniformOfFintype_map_equiv
    (Equiv.curry (Fin (n + 1)) (Fin w) (Fin m → Bool)).symm

/-- Encrypt a Boolean message using only the public matrix and independently sampled coins. -/
noncomputable def encrypt {n m w : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) (μ : Bool) : ProbComp (Ciphertext n w) := do
  let coins ← sampleCoins n m w
  return encryptWithCoins A μ coins

/-- A supported ciphertext is precisely an encryption with some binary coin matrix. -/
theorem mem_support_encrypt_iff {n m w : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) (μ : Bool) (C : Ciphertext n w) :
    C ∈ (ProbComp.eval (encrypt A μ)).support ↔
      ∃ coins, encryptWithCoins A μ coins = C := by
  simp only [encrypt, ProbComp.eval_bind, ProbComp.eval_pure, eval_sampleCoins,
    PMF.mem_support_bind_iff, PMF.mem_support_uniformOfFintype, true_and,
    PMF.mem_support_pure_iff, eq_comm]

/-- Every generated key and every supported fresh ciphertext are correct under the strict margin. -/
theorem keyGen_encrypt_correct {n m w η : ℕ} (hw : 0 < w)
    (hmargin : 4 * (m * η) < 2 ^ w)
    {keys : Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)) × (Fin n → ZMod (2 ^ w))}
    (hkeys : keys ∈ (ProbComp.eval (LWE.keyGen n m w η)).support)
    (μ : Bool) {C : Ciphertext n w} (hC : C ∈ (ProbComp.eval (encrypt keys.1 μ)).support) :
    decrypt keys.2 C = μ := by
  supp_cases hkeys [LWE.keyGen] with ⟨inputs, hinputs, rfl⟩
  obtain ⟨coins, rfl⟩ := (mem_support_encrypt_iff _ _ _).mp hC
  exact decrypt_encryptWithCoins inputs.publicPart inputs.secret inputs.error μ coins hw
    ((LWE.mem_support_sampleKeyInputs_iff _ _ _ _ _).mp hinputs) hmargin

/-- NAND of any two supported fresh ciphertexts is correct for every generated key. -/
theorem keyGen_nand_correct {n m w η : ℕ} (hw : 0 < w)
    (hmargin : 4 * ((1 + (n + 1) * w) * (m * η)) < 2 ^ w)
    {keys : Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)) × (Fin n → ZMod (2 ^ w))}
    (hkeys : keys ∈ (ProbComp.eval (LWE.keyGen n m w η)).support)
    (μ₁ μ₂ : Bool) {C₁ C₂ : Ciphertext n w}
    (hC₁ : C₁ ∈ (ProbComp.eval (encrypt keys.1 μ₁)).support)
    (hC₂ : C₂ ∈ (ProbComp.eval (encrypt keys.1 μ₂)).support) :
    decrypt keys.2 (nand C₁ C₂) = !(μ₁ && μ₂) := by
  supp_cases hkeys [LWE.keyGen] with ⟨inputs, hinputs, rfl⟩
  obtain ⟨R₁, rfl⟩ := (mem_support_encrypt_iff _ _ _).mp hC₁
  obtain ⟨R₂, rfl⟩ := (mem_support_encrypt_iff _ _ _).mp hC₂
  have herror := (LWE.mem_support_sampleKeyInputs_iff _ _ _ _ _).mp hinputs
  apply decrypt_nand inputs.secret _ _ μ₁ μ₂ _ _
    (encryptWithCoins_hasError inputs.publicPart inputs.secret inputs.error μ₁ R₁)
    (encryptWithCoins_hasError inputs.publicPart inputs.secret inputs.error μ₂ R₂) hw
    (encryptionError_natAbs_le R₁ inputs.error herror)
    (encryptionError_natAbs_le R₂ inputs.error herror)
  simpa only [Nat.add_mul, Nat.one_mul, Fintype.card_fin] using hmargin

end Cslib.Crypto.Homomorphic.GSW
