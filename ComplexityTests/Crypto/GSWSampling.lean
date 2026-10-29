/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.PMF.Uniform
import Complexity.Crypto.Computational.Homomorphic.GSW.Sampling.Randomness
import Complexity.Crypto.Computational.Homomorphic.GSW.Sampling.Serialized
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
Finite GSW sampling regressions. The noise fixture has positive width and supports both signed
endpoints. Its generated keys and both message bits meet the fresh and NAND correctness margins.
Exact joint sampling laws, empty dimensions, zero widths and the native scalar sampler interfaces
are checked separately. No security or complete matrix-algorithm efficiency claim is made.
-/

namespace ComplexityTests.GSWSampling

open Cslib Cslib.ProbComp Cslib.Probability Cslib.Crypto.Homomorphic.GSW
open Turing.MultiTapeTM

-- The smallest nontrivial noise law has masses 1/4, 1/2 and 1/4.
example : (ProbComp.eval (sampleCenteredBinomial 1)) (-1) = 1 / 4 ∧
    (ProbComp.eval (sampleCenteredBinomial 1)) 0 = 1 / 2 ∧
    (ProbComp.eval (sampleCenteredBinomial 1)) 1 = 1 / 4 := by
  simp only [sampleCenteredBinomial, OracleComp.countTrue, OracleComp.replicate_succ,
    OracleComp.replicate_zero, map_pure]
  norm_num [ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_apply, PMF.pure_apply,
    PMF.map_apply, tsum_fintype]
  have hquarter : (2 : ENNReal)⁻¹ * 2⁻¹ = 4⁻¹ := by
    rw [← ENNReal.mul_inv (by simp) (by simp)]
    norm_num
  exact ⟨hquarter, by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul], hquarter⟩

example : (-3 : ℤ) ∈ (ProbComp.eval (sampleCenteredBinomial 3)).support ∧
    (3 : ℤ) ∈ (ProbComp.eval (sampleCenteredBinomial 3)).support ∧
    (4 : ℤ) ∉ (ProbComp.eval (sampleCenteredBinomial 3)).support := by
  norm_num only [mem_support_sampleCenteredBinomial_iff, Int.natAbs_neg, Int.natAbs_natCast]
  decide

example : ProbComp.eval (sampleCenteredBinomial 0) = pure 0 := by simp

example : (3 : ℕ) ∈ (ProbComp.eval (sampleBinaryNat 2)).support ∧
    (4 : ℕ) ∉ (ProbComp.eval (sampleBinaryNat 2)).support := by
  norm_num only [mem_support_sampleBinaryNat_iff]
  decide

example : ProbComp.eval (sampleResidue 0) = pure 0 := by
  simp [sampleResidue]

private def keyInputs : KeyInputs 1 1 6 :=
  ⟨fun _ => 5, fun _ _ => 3, fun _ => 1⟩

private def keys : Matrix (Fin 1) (Fin 2) (ZMod (2 ^ 6)) × (Fin 1 → ZMod (2 ^ 6)) :=
  (publicMatrix keyInputs.publicPart keyInputs.secret keyInputs.error, keyInputs.secret)

private def coins : Matrix (Fin 2 × Fin 6) (Fin 1) Bool := fun _ _ => true

private def ciphertext (μ : Bool) : Ciphertext 1 6 := encryptWithCoins keys.1 μ coins

private theorem keyInputs_supported :
    keyInputs ∈ (ProbComp.eval (sampleKeyInputs 1 1 6 1)).support := by
  rw [mem_support_sampleKeyInputs_iff]
  decide +kernel

private theorem keys_supported : keys ∈ (ProbComp.eval (keyGen 1 1 6 1)).support := by
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  exact ⟨keyInputs, keyInputs_supported, rfl⟩

private theorem ciphertext_supported (μ : Bool) :
    ciphertext μ ∈ (ProbComp.eval (encrypt keys.1 μ)).support :=
  (mem_support_encrypt_iff _ _ _).mpr ⟨coins, rfl⟩

-- Both actual sampled messages decrypt correctly, with positive noise width and nonzero error.
example (μ : Bool) : decrypt keys.2 (ciphertext μ) = μ :=
  keyGen_encrypt_correct (by decide) (by decide) keys_supported μ (ciphertext_supported μ)

-- The same generated key satisfies the stronger NAND margin: 4*(1+12)*1 < 64.
example (μ₁ μ₂ : Bool) :
    decrypt keys.2 (nand (ciphertext μ₁) (ciphertext μ₂)) = !(μ₁ && μ₂) :=
  keyGen_nand_correct (by decide) (by decide) keys_supported μ₁ μ₂
    (ciphertext_supported μ₁) (ciphertext_supported μ₂)

-- The opposite signed endpoint is also an actual key-generation input.
example : (KeyInputs.mk (fun _ : Fin 1 => (5 : ZMod (2 ^ 6))) (fun _ _ => 3)
    (fun _ : Fin 1 => (-1 : ℤ))) ∈ (ProbComp.eval (sampleKeyInputs 1 1 6 1)).support := by
  rw [mem_support_sampleKeyInputs_iff]
  decide +kernel

example : (KeyInputs.mk (fun _ : Fin 1 => (5 : ZMod (2 ^ 6))) (fun _ _ => 3)
    (fun _ : Fin 1 => (2 : ℤ))) ∉ (ProbComp.eval (sampleKeyInputs 1 1 6 1)).support := by
  rw [mem_support_sampleKeyInputs_iff]
  decide +kernel

-- Empty vectors and zero-width matrices have their full, singleton typed support.
example (inputs : KeyInputs 0 0 0) :
    inputs ∈ (ProbComp.eval (sampleKeyInputs 0 0 0 0)).support := by
  simp only [mem_support_sampleKeyInputs_iff, Fin.forall_fin_zero]

example (R : Matrix (Fin 1 × Fin 0) (Fin 0) Bool) :
    R ∈ (ProbComp.eval (sampleCoins 0 0 0)).support := by
  rw [eval_sampleCoins]
  exact PMF.mem_support_uniformOfFintype R

-- The complete secret/public/ciphertext law is supplied by exactly 26 independent bits.
example (μ : Bool) :
    ∃ evaluate : List Bool →
        ((Matrix (Fin 1) (Fin 2) (ZMod (2 ^ 6)) × (Fin 1 → ZMod (2 ^ 6))) × Ciphertext 1 6),
      ProbComp.eval (do
        let keys ← keyGen 1 1 6 1
        let ciphertext ← encrypt keys.1 μ
        return (keys, ciphertext)) = (BitString.uniformList 26).map evaluate :=
  exists_uniform_seed_keyGen_encrypt 1 1 6 1 μ

-- These certificates grow with unary width and retain binary numeric outputs.
example : IsPPTOn encUnary (encPair encNat encIntBin)
    (fun width => do
      let a ← sampleBinaryNat width
      (a, ·) <$> sampleCenteredBinomial width) :=
  isPPTOn_sampleBinaryNat.bind_with
    ((isPPTOn_sampleCenteredBinomial.preprocess (by fun_prop)).map_with (by fun_prop))

example : serializeKeyInputs keyInputs = ([5], ([[3]], [1])) := by decide +kernel

example : decodeKeyInputs 1 1 6 (serializeKeyInputs keyInputs) = keyInputs :=
  decode_serializeKeyInputs keyInputs

example : decodeCoins 1 1 6 (serializeCoins coins) = coins := decode_serializeCoins coins

-- The total decoder reduces representatives, crops excess entries and pads missing entries.
example : ((decodeKeyInputs 1 1 6 ([69, 7], ([[67, 8], [9]], [1, 2]))).secret 0).val = 5 ∧
    ((decodeKeyInputs 1 1 6 ([69, 7], ([[67, 8], [9]], [1, 2]))).publicPart 0 0).val = 3 ∧
    (decodeKeyInputs 1 1 6 ([], ([], []))).error 0 = 0 := by
  decide +kernel

example : decodeCoins 1 1 6 [[[true]]] (0, 0) 0 = true ∧
    decodeCoins 1 1 6 [[[true]]] (0, 1) 0 = false ∧
    decodeCoins 1 1 6 [[[true]]] (1, 0) 0 = false := by
  decide +kernel

example : ProbComp.eval (decodeKeyInputs 1 1 6 <$> sampleKeyInputsSerialized 1 1 6 1) =
    ProbComp.eval (sampleKeyInputs 1 1 6 1) :=
  eval_decodeKeyInputs_sampleKeyInputsSerialized 1 1 6 1

example : ProbComp.eval (decodeCoins 1 1 6 <$> sampleCoinsSerialized 1 1 6) =
    ProbComp.eval (sampleCoins 1 1 6) := eval_decodeCoins_sampleCoinsSerialized 1 1 6

-- Every dimension grows with the input; the modulus itself is not encoded in unary.
example : IsPPTOn encUnary encSerializedKeyInputs
    (fun size => sampleKeyInputsSerialized size size size size) :=
  isPPTOn_sampleKeyInputsSerialized (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

example : IsPPTOn encUnary encSerializedCoins (fun size => sampleCoinsSerialized size size size) :=
  isPPTOn_sampleCoinsSerialized (by fun_prop) (by fun_prop) (by fun_prop)

end ComplexityTests.GSWSampling
