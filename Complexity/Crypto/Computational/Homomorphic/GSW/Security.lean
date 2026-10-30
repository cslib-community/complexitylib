/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Encryption.PublicKeyReplacement
public import Complexity.Crypto.Computational.Homomorphic.GSW.Hiding
public import Complexity.Crypto.Computational.Homomorphic.GSW.LWE
public import Complexity.Crypto.Computational.Homomorphic.GSW.Parameters
public import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized.PolyTime

/-!
# Generated-key GSW security from the exact decision-LWE assumption

The actual serialized key generator and encryption program satisfy chosen-message security
under decision LWE for their precise centered-binomial error law. A single uniform adversary
reduction has loss two; the remaining statistical error comes from the shared uniform public
matrix. Every runtime premise concerns the actual serialized program on its complete input.

## Main definitions

* `hidingError`: the explicit statistical term in the chosen-message advantage bound.
* `lweDistinguisher`: the uniform hidden-bit reduction using actual serialized encryption.

## Main results

* `advantage_game_le`: twice the decision-LWE advantage plus the explicit statistical term.
* `indCPA_of_decisionLWE`: negligible chosen-message advantage under an eventual entropy margin.
* `Parameters.indCPA`: the concrete positive-noise family instantiates all runtime and entropy
  requirements, leaving only its specified decision-LWE assumption.

This is ordinary single-challenge public-key security against uniform classical strict PPT
adversaries. It does not provide circular security, a quantum worst-case lattice reduction,
or a bootstrappability theorem.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*][GentrySahaiWaters2013],
  Sections 3.1–3.2.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- The shared-public-matrix statistical term, with `N = (n + 1) * w` ciphertext rows. -/
noncomputable def hidingError (n m w : ℕ) : ℝ≥0 :=
  ((n + 1) * w : ℕ) * NNReal.sqrt ((2 : ℝ≥0) ^ ((n + 1) * w) / 2 ^ m)

/-- The reduction uses the actual serialized encryption algorithm, including total decoding of
arbitrary challenge words. Its hidden fair bit is not supplied to either adversary stage. -/
noncomputable def lweDistinguisher (n m w : ℕ → ℕ)
    (adversary : Encryption.Adversary) : Distinguisher :=
  Encryption.keyDistinguisher
    (fun security => encryptSerialized (n security) (m security) (w security)) adversary

/-- Efficient parameter functions instantiate the actual reduction's uniform native certificate. -/
theorem isPPT_lweDistinguisher {n m w : ℕ → ℕ} {adversary : Encryption.Adversary}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hadversary : adversary.IsPPT) : IsPPT encBool (lweDistinguisher n m w adversary) := by
  apply Encryption.isPPT_keyDistinguisher ?_ hadversary
  exact isPPTOn_encryptSerialized (hn.comp (by fun_prop)) (hm.comp (by fun_prop))
    (hw.comp (by fun_prop)) (by fun_prop) (by fun_prop)

/-- In the uniform-matrix experiment, serialized message selection, encryption and guessing
agree with the typed adaptive hiding game, including the full saved word. -/
theorem publicKeyGame_uniformEnsemble (n m w : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (security : ℕ) :
    Encryption.publicKeyGame (LWE.uniformEnsemble n m w security)
      (fun k => encryptSerialized (n k) (m k) (w k)) adversary bit security =
        uniformPublicGame (n := n security) (m := m security) (w := w security)
          (fun A => ProbComp.eval (adversary.choose security (serializePublicMatrix A)))
          (fun state ciphertext =>
            ProbComp.eval (adversary.guess security state (serializeCiphertext ciphertext)))
          bit := by
  simp only [Encryption.publicKeyGame, LWE.uniformEnsemble, uniformPublicGame,
    PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, eval_encryptSerialized,
    Matrix.ofBinary_toBinary, encrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    eval_sampleCoins, PMF.bind_bind, PMF.pure_bind, serializePublicMatrix]

/-- The uniform public-key word gives the typed hiding theorem's full adaptive bound. -/
theorem advantage_uniformEnsemble_le (n m w : ℕ → ℕ)
    (adversary : Encryption.Adversary) (security : ℕ) :
    Game.advantage
      (Encryption.publicKeyGame (LWE.uniformEnsemble n m w security)
        (fun k => encryptSerialized (n k) (m k) (w k)) adversary false security)
      (Encryption.publicKeyGame (LWE.uniformEnsemble n m w security)
        (fun k => encryptSerialized (n k) (m k) (w k)) adversary true security) ≤
          hidingError (n security) (m security) (w security) := by
  apply NNReal.coe_le_coe.mp
  rw [Game.coe_advantage, publicKeyGame_uniformEnsemble, publicKeyGame_uniformEnsemble]
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, hidingError,
    NNReal.coe_mul, NNReal.coe_natCast, Real.coe_sqrt, NNReal.coe_div, NNReal.coe_pow,
    NNReal.coe_ofNat, Nat.mul_comm] using
      uniformPublicGame_advantage_le (n := n security) (m := m security) (w := w security)
        (fun A => ProbComp.eval (adversary.choose security (serializePublicMatrix A)))
        (fun state ciphertext =>
          ProbComp.eval (adversary.guess security state (serializeCiphertext ciphertext)))

/-- One uniform reduction bounds actual chosen-message advantage by twice its exact decision-LWE
advantage plus the shared-public-matrix statistical error. No efficiency is needed for this law. -/
theorem advantage_game_le (n m w η : ℕ → ℕ)
    (adversary : Encryption.Adversary) (security : ℕ) :
    Game.advantage
      (ProbComp.eval (Encryption.game
        (fun k => keyGenSerialized (n k) (m k) (w k) (η k))
        (fun k => encryptSerialized (n k) (m k) (w k)) adversary false security))
      (ProbComp.eval (Encryption.game
        (fun k => keyGenSerialized (n k) (m k) (w k) (η k))
        (fun k => encryptSerialized (n k) (m k) (w k)) adversary true security)) ≤
      2 * Game.advantage
        (distinguishingGame (LWE.realEnsemble n m w (fun k => noiseLaw (w k) (η k)) security)
          (lweDistinguisher n m w adversary security))
        (distinguishingGame (LWE.uniformEnsemble n m w security)
          (lweDistinguisher n m w adversary security)) +
            hidingError (n security) (m security) (w security) := by
  simp only [Encryption.eval_game_eq_publicKeyGame, eval_keyGenSerialized_publicWord]
  exact (Encryption.advantage_publicKeyGame_le _ (LWE.uniformEnsemble n m w security)
    _ adversary security).trans
      (add_le_add le_rfl (advantage_uniformEnsemble_le n m w adversary security))

open Filter in
/-- The actual encryption scheme is IND-CPA secure under its exact decision-LWE assumption,
provided efficient dimensions have an eventual entropy surplus of twice the security parameter. -/
theorem indCPA_of_decisionLWE {n m w η : ℕ → ℕ}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hmargin : ∀ᶠ security in atTop, (n security + 1) * w security + 2 * security ≤ m security)
    (hLWE : DecisionLWE n m w (fun k => noiseLaw (w k) (η k))) :
    Encryption.INDCPA (fun k => keyGenSerialized (n k) (m k) (w k) (η k))
      (fun k => encryptSerialized (n k) (m k) (w k)) := by
  intro adversary hadversary
  have hsource := hLWE (lweDistinguisher n m w adversary)
    (isPPT_lweDistinguisher hn hm hw hadversary)
  have hrows : PolynomiallyBounded (fun k => (n k + 1) * w k) := by
    have : PolynomiallyBounded n := hn.polynomiallyBounded
    have : PolynomiallyBounded w := hw.polynomiallyBounded
    fun_prop
  have herror := negligible_mul_sqrt_pow_two_div_pow_two hrows hmargin
  apply negligible_of_le
    ((hsource.polynomiallyBounded_mul (p := fun _ => 2) (by fun_prop)).add herror)
  exact advantage_game_le n m w η adversary

/-- The positive-noise parameter family supplies every dimension/runtime/entropy premise.
Only decision LWE for its precise centered-binomial law remains a security assumption. -/
theorem Parameters.indCPA
    (hLWE : DecisionLWE Parameters.dimension Parameters.samples Parameters.width
      (fun k => noiseLaw (Parameters.width k) (Parameters.noise k))) :
    Encryption.INDCPA
      (fun k => keyGenSerialized (Parameters.dimension k) (Parameters.samples k)
        (Parameters.width k) (Parameters.noise k))
      (fun k => encryptSerialized (Parameters.dimension k) (Parameters.samples k)
        (Parameters.width k)) :=
  indCPA_of_decisionLWE GSW.Parameters.computableInPolyTime_dimension
    GSW.Parameters.computableInPolyTime_samples GSW.Parameters.computableInPolyTime_width
    (Filter.Eventually.of_forall Parameters.entropy_margin) hLWE

end Cslib.Crypto.Homomorphic.GSW
