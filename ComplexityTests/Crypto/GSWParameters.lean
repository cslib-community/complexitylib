/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.GSW.Parameters
import Complexity.Crypto.Computational.Homomorphic.GSW.Sampling
import Complexity.Crypto.Computational.Homomorphic.GSW.Hiding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
GSW parameter regressions connect the growing family to actual sampled keys, encryption and NAND,
and to the real-valued statistical bound. Positive signed errors occur at every parameter. These
checks supply no decision-LWE hardness or bootstrappability claim.
-/

namespace ComplexityTests.GSWParameters

open Cslib Cslib.Crypto Cslib.ProbComp Cslib.Probability Cslib.Crypto.Homomorphic.GSW
open Turing.MultiTapeTM
open scoped NNReal

-- Parameter zero remains nontrivial, and a ceiling-logarithm jump changes the actual dimensions.
example : Parameters.dimension 0 = 1 ∧ Parameters.noise 0 = 1 ∧ Parameters.width 0 = 16 ∧
    Parameters.rows 0 = 32 ∧ Parameters.samples 0 = 32 ∧ Parameters.modulus 0 = 65536 := by
  decide +kernel

example : Parameters.width 1 = 24 ∧ Parameters.samples 1 = 74 ∧
    Parameters.width 2 = 32 ∧ Parameters.samples 2 = 132 := by
  decide +kernel

-- Every unary-output native premise is instantiated by the same family, including the modulus.
example : ComputableInPolyTime
    (fun security => (Parameters.dimension security, Parameters.noise security,
      Parameters.width security, Parameters.rows security, Parameters.samples security,
      Parameters.modulus security)) encUnary
    (encPair encUnary (encPair encUnary (encPair encUnary
      (encPair encUnary (encPair encUnary encUnary))))) := by
  fun_prop

-- A finite exceptional parameter does not defeat the eventual-margin theorem. The output bit
-- count here is exponential; the theorem does not require a polynomial bound on that count.
example : Negligible (fun n => (((n + 1) ^ 2 : ℕ) : ℝ≥0) * NNReal.sqrt
    ((2 : ℝ≥0) ^ (2 ^ n) / 2 ^ (if n = 0 then 0 else 2 ^ n + 2 * n))) := by
  apply negligible_mul_sqrt_pow_two_div_pow_two (count := fun n => (n + 1) ^ 2) (by fun_prop)
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp only [ite_eq_right (by omega : n ≠ 0)]
  exact le_rfl

-- Without surplus entropy the error can be constantly one and hence non-negligible.
example : ¬ Negligible (fun n => NNReal.sqrt ((2 : ℝ≥0) ^ n / 2 ^ n)) := by
  simpa using not_negligible_const (by norm_num : (1 : ℝ≥0) ≠ 0)

private def keyInputs (security : ℕ) :
    KeyInputs (Parameters.dimension security) (Parameters.samples security)
      (Parameters.width security) :=
  ⟨fun _ => 5, fun _ _ => 3, fun _ => (Parameters.noise security : ℤ)⟩

private def keys (security : ℕ) :=
  (publicMatrix (keyInputs security).publicPart (keyInputs security).secret
    (keyInputs security).error, (keyInputs security).secret)

private def coins (security : ℕ) :
    Matrix (Fin (Parameters.dimension security + 1) × Fin (Parameters.width security))
      (Fin (Parameters.samples security)) Bool := fun _ _ => true

private def ciphertext (security : ℕ) (message : Bool) :=
  encryptWithCoins (keys security).1 message (coins security)

private theorem keyInputs_supported (security : ℕ) :
    keyInputs security ∈ (ProbComp.eval (sampleKeyInputs (Parameters.dimension security)
      (Parameters.samples security) (Parameters.width security)
        (Parameters.noise security))).support := by
  rw [mem_support_sampleKeyInputs_iff]
  simp [keyInputs]

-- Both nonzero signed endpoints occur in the actual error law at every security parameter.
example (security : ℕ) :
    (Parameters.noise security : ℤ) ∈
        (ProbComp.eval (sampleCenteredBinomial (Parameters.noise security))).support ∧
      -(Parameters.noise security : ℤ) ∈
        (ProbComp.eval (sampleCenteredBinomial (Parameters.noise security))).support ∧
      (Parameters.noise security : ℤ) ≠ 0 := by
  simp only [mem_support_sampleCenteredBinomial_iff, Int.natAbs_neg, Int.natAbs_natCast,
    le_refl, true_and]
  exact_mod_cast (Parameters.noise_pos security).ne'

private theorem keys_supported (security : ℕ) :
    keys security ∈ (ProbComp.eval (keyGen (Parameters.dimension security)
      (Parameters.samples security) (Parameters.width security)
        (Parameters.noise security))).support := by
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  exact ⟨keyInputs security, keyInputs_supported security, rfl⟩

private theorem ciphertext_supported (security : ℕ) (message : Bool) :
    ciphertext security message ∈ (ProbComp.eval (encrypt (keys security).1 message)).support :=
  (mem_support_encrypt_iff _ _ _).mpr ⟨coins security, rfl⟩

-- There are no uninstantiated width or noise-margin hypotheses in these growing-family clients.
example (security : ℕ) (message : Bool) :
    decrypt (keys security).2 (ciphertext security message) = message := by
  apply keyGen_encrypt_correct (η := Parameters.noise security) (Parameters.width_pos security)
    ?_ (keys_supported security) message (ciphertext_supported security message)
  simpa only [Parameters.modulus, Nat.mul_assoc] using Parameters.fresh_margin security

example (security : ℕ) (left right : Bool) :
    decrypt (keys security).2 (nand (ciphertext security left) (ciphertext security right)) =
      !(left && right) := by
  apply keyGen_nand_correct (η := Parameters.noise security) (Parameters.width_pos security)
    ?_ (keys_supported security) left right
    (ciphertext_supported security left) (ciphertext_supported security right)
  simpa only [Parameters.modulus, Parameters.rows, Nat.mul_assoc] using
    Parameters.nand_margin security

-- Match the real-valued bound used by the actual adaptive uniform-public-matrix game.
example : Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ))
    (fun n => ((Parameters.dimension n + 1) * Parameters.width n : ℕ) *
      Real.sqrt ((2 : ℝ) ^ (Parameters.width n * (Parameters.dimension n + 1)) /
        2 ^ Parameters.samples n)) := by
  simpa only [Parameters.rows, NNReal.coe_mul, NNReal.coe_natCast, Real.coe_sqrt,
    NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, Nat.mul_comm] using
      negligible_iff_coe.mp Parameters.negligible_statistical_error

-- The actual uniform-public-matrix chosen-message games have negligible advantage, including
-- adversaries with arbitrary parameter-dependent saved state and no efficiency restriction.
example {State : ℕ → Type}
    (choose : ∀ n, Matrix (Fin (Parameters.samples n)) (Fin (Parameters.dimension n + 1))
      (ZMod (2 ^ Parameters.width n)) → PMF ((Bool × Bool) × State n))
    (guess : ∀ n, State n → Ciphertext (Parameters.dimension n) (Parameters.width n) → PMF Bool) :
    Negligible (fun n => Game.advantage (uniformPublicGame (choose n) (guess n) false)
      (uniformPublicGame (choose n) (guess n) true)) := by
  apply negligible_of_le Parameters.negligible_statistical_error
  intro n
  apply NNReal.coe_le_coe.mp
  simpa only [Game.coe_advantage, Game.succProbability, ENNReal.coe_toNNReal_eq_toReal,
    NNReal.coe_mul, NNReal.coe_natCast, Real.coe_sqrt, NNReal.coe_div, NNReal.coe_pow,
    NNReal.coe_ofNat, Parameters.rows, Nat.mul_comm] using
      uniformPublicGame_advantage_le (choose n) (guess n)

end ComplexityTests.GSWParameters
