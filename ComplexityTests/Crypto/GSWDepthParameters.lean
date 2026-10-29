/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.GSW.DepthParameters.Security
import Complexity.Tactic.PPT

/-!
The new family's zero and growing parameters, full depth margin, positive supported noise,
honest native algorithms and exact-family security premise. The tests do not assert that an
augmented decryption circuit fits the budget or assume security of an insecure fixture.
-/

namespace ComplexityTests.GSWDepthParameters

open Cslib Cslib.Crypto Cslib.ProbComp Cslib.Probability Cslib.Crypto.Homomorphic.GSW
open Turing.MultiTapeTM

-- Zero is included; neither the dimensions, noise nor depth collapses to an empty case.
example : Parameters.dimension 0 = 1 ∧ Parameters.noise 0 = 1 ∧
    DepthParameters.logSize 0 = 2 ∧ DepthParameters.width 0 = 65536 ∧
    DepthParameters.rows 0 = 131072 ∧ DepthParameters.samples 0 = 131072 ∧
    DepthParameters.depthBudget 0 = 1024 := by decide +kernel

example : DepthParameters.logSize 1 = 3 ∧ DepthParameters.width 1 = 147456 ∧
    DepthParameters.samples 1 = 442370 ∧ DepthParameters.depthBudget 1 = 1536 ∧
    DepthParameters.logSize 6 = 4 ∧ DepthParameters.depthBudget 6 = 2048 := by decide +kernel

-- The earlier family retains its narrower modulus and original API.
example : Parameters.width 0 = 16 ∧ Parameters.width 1 = 24 := by decide +kernel

example (security : ℕ) : 0 < Parameters.dimension security ∧ 0 < Parameters.noise security ∧
    0 < DepthParameters.width security ∧ 0 < DepthParameters.rows security ∧
    0 < DepthParameters.samples security ∧ 0 < DepthParameters.depthBudget security := by
  have hw := DepthParameters.width_pos security
  have hdepth := DepthParameters.depthBudget_pos security
  refine ⟨by simp [Parameters.dimension], Parameters.noise_pos security, hw, ?_, ?_, hdepth⟩
  · unfold DepthParameters.rows
    positivity
  · unfold DepthParameters.samples DepthParameters.rows
    positivity

example : 4 * DepthParameters.samples 0 * Parameters.noise 0 *
    (DepthParameters.rows 0 + 1) ^ DepthParameters.depthBudget 0 <
      2 ^ DepthParameters.width 0 := DepthParameters.noise_margin 0

example :
    4 * DepthParameters.samples 0 * Parameters.noise 0 *
      (DepthParameters.rows 0 + 1) ^ 512 < 2 ^ DepthParameters.width 0 :=
  DepthParameters.noise_margin_of_le (security := 0) (by decide)

-- A nonzero error is actually supported at every parameter, including zero.
example (security : ℕ) :
    (1 : ℤ) ∈ (ProbComp.eval (sampleCenteredBinomial (Parameters.noise security))).support := by
  rw [mem_support_sampleCenteredBinomial_iff]
  simp [Parameters.noise]

-- Nonempty actual key and encryption supports realize the proved fresh and NAND margins.
-- State the finite-type client at arbitrary dimensions before specializing its large moduli.
private theorem supported_correct (n m w η : ℕ) (hw : 0 < w)
    (hfresh : 4 * (m * η) < 2 ^ w)
    (hnand : 4 * ((1 + (n + 1) * w) * (m * η)) < 2 ^ w) (left right : Bool) :
    ∃ keys ∈ (ProbComp.eval (keyGen n m w η)).support,
      ∃ c₁ ∈ (ProbComp.eval (encrypt keys.1 left)).support,
        ∃ c₂ ∈ (ProbComp.eval (encrypt keys.1 right)).support,
          decrypt keys.2 c₁ = left ∧ decrypt keys.2 (nand c₁ c₂) = !(left && right) := by
  obtain ⟨keys, hkeys⟩ := (ProbComp.eval (keyGen n m w η)).support_nonempty
  obtain ⟨c₁, hc₁⟩ := (ProbComp.eval (encrypt keys.1 left)).support_nonempty
  obtain ⟨c₂, hc₂⟩ := (ProbComp.eval (encrypt keys.1 right)).support_nonempty
  refine ⟨keys, hkeys, c₁, hc₁, c₂, hc₂, ?_, ?_⟩
  · exact keyGen_encrypt_correct hw hfresh hkeys left hc₁
  · exact keyGen_nand_correct hw hnand hkeys left right hc₁ hc₂

example (security : ℕ) (left right : Bool) :=
  supported_correct (Parameters.dimension security) (DepthParameters.samples security)
    (DepthParameters.width security) (Parameters.noise security)
    (DepthParameters.width_pos security)
    (by simpa only [Nat.mul_assoc, DepthParameters.modulus] using
      DepthParameters.fresh_margin security)
    (DepthParameters.nand_margin security) left right

-- Native routines return the full varying parameters, not a fixed finite-type code.
example : ComputableInPolyTime
    (fun security => (DepthParameters.width security,
      DepthParameters.samples security, DepthParameters.depthBudget security))
    encUnary (encPair encUnary (encPair encUnary encUnary)) := by fun_prop

-- The much larger modulus is returned in binary, not unary.
example : ComputableInPolyTime DepthParameters.modulus encUnary encNat := by fun_prop

example : PolynomiallyBounded (fun security => DepthParameters.rows security ^ 2) := by
  have := DepthParameters.polynomiallyBounded_parameters.2.2.2.1
  fun_prop

example : IsPPTOn encUnary (encPair encBits encBits)
    (fun security => keyGenSerialized (Parameters.dimension security)
      (DepthParameters.samples security) (DepthParameters.width security)
      (Parameters.noise security)) :=
  isPPTOn_keyGenSerialized Parameters.computableInPolyTime_dimension
    DepthParameters.computableInPolyTime_samples
    DepthParameters.computableInPolyTime_width Parameters.computableInPolyTime_noise

-- This certificate includes every raw public word and bit, including malformed input words.
example : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => encryptSerialized (Parameters.dimension p.1) (DepthParameters.samples p.1)
      (DepthParameters.width p.1) p.2.1 p.2.2) :=
  isPPTOn_encryptSerialized (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)

private def firstBitAdversary : Encryption.Adversary where
  choose _ _ := pure ((false, true), [])
  guess _ _ ciphertext := pure (ciphertext.headD false)

private theorem firstBitAdversary_isPPT : firstBitAdversary.IsPPT := by
  constructor <;> simp only [firstBitAdversary] <;> ppt

-- Only this exact family's LWE hypothesis is supplied: no old-family or encryption-security
-- assumption, efficient-width premise, or unproved decryption-circuit contract is added.
example
    (hLWE : DecisionLWE Parameters.dimension DepthParameters.samples DepthParameters.width
      (fun k => noiseLaw (DepthParameters.width k) (Parameters.noise k))) :
    Negligible (fun k =>
      Game.advantage
        (ProbComp.eval (Encryption.game
          (fun k => keyGenSerialized (Parameters.dimension k) (DepthParameters.samples k)
            (DepthParameters.width k) (Parameters.noise k))
          (fun k => encryptSerialized (Parameters.dimension k) (DepthParameters.samples k)
            (DepthParameters.width k))
          firstBitAdversary false k))
        (ProbComp.eval (Encryption.game
          (fun k => keyGenSerialized (Parameters.dimension k) (DepthParameters.samples k)
            (DepthParameters.width k) (Parameters.noise k))
          (fun k => encryptSerialized (Parameters.dimension k) (DepthParameters.samples k)
            (DepthParameters.width k))
          firstBitAdversary true k))) :=
  DepthParameters.indCPA hLWE firstBitAdversary firstBitAdversary_isPPT

end ComplexityTests.GSWDepthParameters
