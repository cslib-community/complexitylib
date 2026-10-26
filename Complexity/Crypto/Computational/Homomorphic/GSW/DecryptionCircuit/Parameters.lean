/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.DecryptionCircuit
public import Complexity.Crypto.Computational.Homomorphic.GSW.DepthParameters
public import Complexity.Crypto.Computational.Homomorphic.Circuit
public import Complexity.Computability.Circuit.Boolean.Layered.Compile

/-!
# Concrete depth fit for GSW decryption

The complete raw-input decryptor and its two-copy NAND augmentation each compile to at most
`DepthParameters.depthBudget` layers, for every security parameter. This is an arithmetic budget
result; it does not assume or establish LWE hardness or circular security.

## Main results

* `Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit.layers_le_depthBudget`: the actual decryptor's
  layer count fits the existing GSW parameter family.
* `Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit.layers_augment_le_depthBudget`: the actual
  augmented circuit's layer count fits the same family.
-/

public section

namespace Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit

open Circuits Circuits.Boolean

private theorem clog_width_le (security : ℕ) :
    Nat.clog 2 (DepthParameters.width security + 1) ≤
      15 + 2 * DepthParameters.logSize security := by
  let t := DepthParameters.logSize security
  have ht : t ≤ 2 ^ t := Nat.le_of_lt Nat.lt_two_pow_self
  have hs : t ^ 2 ≤ (2 ^ t) ^ 2 := Nat.pow_le_pow_left ht 2
  apply Nat.clog_le_of_le_pow
  change 16384 * t ^ 2 + 1 ≤ 2 ^ (15 + 2 * t)
  have he : 2 ^ (15 + 2 * t) = 32768 * (2 ^ t) ^ 2 := by
    rw [pow_add, mul_comm 2 t, pow_mul]
    norm_num
  rw [he]
  have hp : 0 < (2 ^ t) ^ 2 := by positivity
  omega

private theorem clog_dimension_le (security : ℕ) :
    Nat.clog 2 (Parameters.dimension security) ≤ DepthParameters.logSize security := by
  have hm := Nat.clog_mono_right (b := 2) (show security + 1 ≤ security + 2 by omega)
  unfold Parameters.dimension DepthParameters.logSize
  omega

/-- Two microlevels per De Morgan level of the complete raw decryptor fit the budget. -/
theorem layers_le_depthBudget (security : ℕ) :
    (Layered.compile (inputWidth (Parameters.dimension security) (DepthParameters.width security))
      (circuit (Parameters.dimension security) (DepthParameters.width security)).code).1.length ≤
      DepthParameters.depthBudget security := by
  rw [Layered.length_compile]
  have hd := depth_circuit_le (Parameters.dimension security) (DepthParameters.width security)
  have hw := clog_width_le security
  have hn := clog_dimension_le security
  have ht := DepthParameters.two_le_logSize security
  unfold DepthParameters.depthBudget
  omega

/-- The NAND extension adds at most two De Morgan levels to the complete raw decryptor. -/
theorem depth_augment_le (n w : ℕ) :
    (augmentNand (circuit n w)).depth ≤
      30 + 18 * Nat.clog 2 (w + 1) + 12 * Nat.clog 2 n := by
  have hn : nandCircuit.depth ≤ 2 := by decide
  have hp : ((circuit n w).parallel (circuit n w)).depth ≤ (circuit n w).depth := by
    unfold Circuit.parallel
    apply (Circuit.depth_append_le _ _).trans
    apply max_le <;> exact (Circuit.depth_comp_le _ _).trans (by simp)
  have hc := Circuit.depth_comp_le nandCircuit ((circuit n w).parallel (circuit n w))
  have hd := depth_circuit_le n w
  change (augmentNand (circuit n w)).depth ≤ _ at hc
  omega

/-- Two microlevels per De Morgan level, including the actual NAND augmentation, fit the budget. -/
theorem layers_augment_le_depthBudget (security : ℕ) :
    (Layered.compile
      (inputWidth (Parameters.dimension security) (DepthParameters.width security) +
        inputWidth (Parameters.dimension security) (DepthParameters.width security))
      (augmentNand
      (circuit (Parameters.dimension security) (DepthParameters.width security))).code).1.length ≤
      DepthParameters.depthBudget security := by
  rw [Layered.length_compile]
  have hd := depth_augment_le (Parameters.dimension security) (DepthParameters.width security)
  have hw := clog_width_le security
  have hn := clog_dimension_le security
  have ht := DepthParameters.two_le_logSize security
  unfold DepthParameters.depthBudget
  omega

end Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit
