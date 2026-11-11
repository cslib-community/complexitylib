/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Basic
public import CslibFrontier.Languages.Probabilistic.CenteredBinomial
public import CslibFrontier.Languages.Probabilistic.UniformNat
public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Probability.PMF.Uniform

/-!
# Finite sampling for the GSW construction

Residues are sampled from exactly `w` fair bits. Each integer error is the difference of two
independent counts of `η` fair bits, so every supported error has magnitude at most `η`.
The actual key-generation and encryption programs feed these independent draws to the GSW
formulas. Their correctness holds for every supported draw under an explicit strict margin.

This exact noise distribution is a construction choice. No Gaussian equivalence, LWE hardness,
encryption security, complete native algorithm certificate or bootstrappability is asserted.

## Main definitions

* `sampleResidue`, `sampleVector`, `sampleMatrix`, `sampleCoins`: independent finite samplers.
* `KeyInputs`, `sampleKeyInputs`: the independent inputs to the public-key formula.
* `keyGen`, `encrypt`: the actual finite randomized key generation and encryption programs.

## Main results

* `eval_sampleResidue`, `eval_sampleVector`, `eval_sampleMatrix`, `eval_sampleCoins`:
  exact uniform laws.
* `mem_support_sampleKeyInputs_iff`: the exact support condition on the chosen integer errors.
* `keyGen_encrypt_correct`, `keyGen_nand_correct`: correctness for all supported draws.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.1][GentrySahaiWaters2013]
* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Algorithm 8][NISTFIPS203]
  for the scalar finite noise construction, without identifying the encryption schemes.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open ProbComp Probability

/-- Sample one residue from `w` independent fair bits. -/
noncomputable def sampleResidue (w : ℕ) : ProbComp (ZMod (2 ^ w)) :=
  (fun value : ℕ => (value : ZMod (2 ^ w))) <$> sampleBinaryNat w

/-- The fair-bit residue sampler is exactly uniform, including at width zero. -/
@[simp] theorem eval_sampleResidue (w : ℕ) :
    ProbComp.eval (sampleResidue w) = PMF.uniformOfFintype (ZMod (2 ^ w)) := by
  rw [sampleResidue, ProbComp.eval_map, eval_sampleBinaryNat, PMF.map_comp]
  let e : Fin (2 ^ w) ≃ ZMod (2 ^ w) :=
    { toFun := fun i => i.val
      invFun := fun z => ⟨z.val, ZMod.val_lt z⟩
      left_inv := fun i => Fin.ext (ZMod.val_cast_of_lt i.isLt)
      right_inv := fun z => ZMod.natCast_zmod_val z }
  exact PMF.uniformOfFintype_map_equiv e

/-- Sample independent residues into a length-indexed vector. -/
noncomputable def sampleVector (count w : ℕ) : ProbComp (Fin count → ZMod (2 ^ w)) :=
  OracleComp.replicateFin count (sampleResidue w)

@[simp] theorem eval_sampleVector (count w : ℕ) :
    ProbComp.eval (sampleVector count w) =
      PMF.uniformOfFintype (Fin count → ZMod (2 ^ w)) := by
  simp only [sampleVector, ProbComp.eval_replicateFin, eval_sampleResidue,
    PMF.pi_uniformOfFintype]

/-- Sample independent rows of independent residues. -/
noncomputable def sampleMatrix (rows cols w : ℕ) :
    ProbComp (Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w))) :=
  OracleComp.replicateFin rows (sampleVector cols w)

@[simp] theorem eval_sampleMatrix (rows cols w : ℕ) :
    ProbComp.eval (sampleMatrix rows cols w) =
      PMF.uniformOfFintype (Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w))) := by
  unfold Matrix
  simp only [sampleMatrix, ProbComp.eval_replicateFin, eval_sampleVector,
    PMF.pi_uniformOfFintype]
  congr 1

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

/-- The separately sampled secret, public-matrix part and integer errors. -/
structure KeyInputs (n m w : ℕ) where
  /-- Uniform secret entries. -/
  secret : Fin n → ZMod (2 ^ w)
  /-- Uniform public matrix entries. -/
  publicPart : Matrix (Fin m) (Fin n) (ZMod (2 ^ w))
  /-- Independent bounded integer errors. -/
  error : Fin m → ℤ

/-- Draw the three inputs independently, using the specified finite error distribution. -/
noncomputable def sampleKeyInputs (n m w η : ℕ) : ProbComp (KeyInputs n m w) := do
  let secret ← sampleVector n w
  let publicPart ← sampleMatrix m n w
  let error ← OracleComp.replicateFin m (sampleCenteredBinomial η)
  return ⟨secret, publicPart, error⟩

/-- The complete joint law retains the independence of the secret, public part and errors. -/
theorem eval_sampleKeyInputs (n m w η : ℕ) :
    ProbComp.eval (sampleKeyInputs n m w η) = (do
      let secret ← PMF.uniformOfFintype (Fin n → ZMod (2 ^ w))
      let publicPart ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
      let error ← ProbComp.eval (OracleComp.replicateFin m (sampleCenteredBinomial η))
      pure (KeyInputs.mk secret publicPart error)) := by
  simp only [sampleKeyInputs, ProbComp.eval_bind, ProbComp.eval_pure,
    eval_sampleVector, eval_sampleMatrix, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]

/-- Every secret and public part is possible; the exact error restriction is coordinatewise. -/
theorem mem_support_sampleKeyInputs_iff (n m w η : ℕ) (inputs : KeyInputs n m w) :
    inputs ∈ (ProbComp.eval (sampleKeyInputs n m w η)).support ↔
      ∀ i, (inputs.error i).natAbs ≤ η := by
  cases inputs
  simp only [sampleKeyInputs, ProbComp.eval_bind, ProbComp.eval_pure,
    eval_sampleVector, eval_sampleMatrix, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  simp only [PMF.mem_support_uniformOfFintype, true_and, KeyInputs.mk.injEq,
    ProbComp.mem_support_replicateFin_iff, mem_support_sampleCenteredBinomial_iff]
  constructor
  · rintro ⟨_, _, error, herror, rfl, rfl, rfl⟩
    exact herror
  · intro herror
    exact ⟨_, _, _, herror, rfl, rfl, rfl⟩

/-- Generate the actual public matrix and retain the sampled secret. -/
noncomputable def keyGen (n m w η : ℕ) :
    ProbComp (Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)) × (Fin n → ZMod (2 ^ w))) := do
  let inputs ← sampleKeyInputs n m w η
  return (publicMatrix inputs.publicPart inputs.secret inputs.error, inputs.secret)

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
    (hkeys : keys ∈ (ProbComp.eval (keyGen n m w η)).support)
    (μ : Bool) {C : Ciphertext n w} (hC : C ∈ (ProbComp.eval (encrypt keys.1 μ)).support) :
    decrypt keys.2 C = μ := by
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hkeys
  obtain ⟨inputs, hinputs, rfl⟩ := hkeys
  obtain ⟨coins, rfl⟩ := (mem_support_encrypt_iff _ _ _).mp hC
  exact decrypt_encryptWithCoins inputs.publicPart inputs.secret inputs.error μ coins hw
    ((mem_support_sampleKeyInputs_iff _ _ _ _ _).mp hinputs) hmargin

/-- NAND of any two supported fresh ciphertexts is correct for every generated key. -/
theorem keyGen_nand_correct {n m w η : ℕ} (hw : 0 < w)
    (hmargin : 4 * ((1 + (n + 1) * w) * (m * η)) < 2 ^ w)
    {keys : Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)) × (Fin n → ZMod (2 ^ w))}
    (hkeys : keys ∈ (ProbComp.eval (keyGen n m w η)).support)
    (μ₁ μ₂ : Bool) {C₁ C₂ : Ciphertext n w}
    (hC₁ : C₁ ∈ (ProbComp.eval (encrypt keys.1 μ₁)).support)
    (hC₂ : C₂ ∈ (ProbComp.eval (encrypt keys.1 μ₂)).support) :
    decrypt keys.2 (nand C₁ C₂) = !(μ₁ && μ₂) := by
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hkeys
  obtain ⟨inputs, hinputs, rfl⟩ := hkeys
  obtain ⟨R₁, rfl⟩ := (mem_support_encrypt_iff _ _ _).mp hC₁
  obtain ⟨R₂, rfl⟩ := (mem_support_encrypt_iff _ _ _).mp hC₂
  have herror := (mem_support_sampleKeyInputs_iff _ _ _ _ _).mp hinputs
  apply decrypt_nand inputs.secret _ _ μ₁ μ₂ _ _
    (encryptWithCoins_hasError inputs.publicPart inputs.secret inputs.error μ₁ R₁)
    (encryptWithCoins_hasError inputs.publicPart inputs.secret inputs.error μ₂ R₂) hw
    (encryptionError_natAbs_le R₁ inputs.error herror)
    (encryptionError_natAbs_le R₂ inputs.error herror)
  simpa only [Nat.add_mul, Nat.one_mul, Fintype.card_fin] using hmargin

end Cslib.Crypto.Homomorphic.GSW
