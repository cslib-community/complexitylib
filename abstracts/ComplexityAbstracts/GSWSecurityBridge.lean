/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.CryptographyBridge
import ComplexityAbstracts.Randomized
import ComplexityAbstracts.GSW
import Complexity.Crypto.Computational.Homomorphic.GSW.Security

/-! # Bridge for generated-key GSW security

The public abstract uses explicit PMF laws and the plain finite-coin-tape presentation of strict
PPT. This bridge identifies those laws with the complete serialized programs and reuses the
native generated-key security theorem. The bridge introduces no notation or elaboration rules.
-/

namespace ComplexityTests.Abstracts.GSWSecurityBridge

/-- The secret dimension and centered-binomial width are positive at every parameter. -/
def dimension (security : ℕ) : ℕ := security + 1

/-- Each residue uses `16 + 8 * ceil(log₂(security+1))` binary digits; the modulus is
`2 ^ digitWidth security`. The ceiling logarithm is `Nat.clog`. -/
def digitWidth (security : ℕ) : ℕ := 16 + 8 * Nat.clog 2 (security + 1)

/-- The public matrix has this many rows, giving `2 * security` surplus entropy bits. -/
def sampleCount (security : ℕ) : ℕ := (dimension security + 1) * digitWidth security + 2 * security

/-- Generate the actual public/secret pair. The secret, matrix rows, and signed errors are all
sampled independently, with `n = noiseWidth = security+1`. -/
noncomputable def keyGeneration (security : ℕ) : PMF (List Bool × List Bool) := do
  let secret ← GSW.independentList (dimension security) (GSW.residueLaw (digitWidth security))
  let matrix ← GSW.independentList (sampleCount security)
    (GSW.independentList (dimension security) (GSW.residueLaw (digitWidth security)))
  let errors ← GSW.independentList (sampleCount security) (GSW.errorLaw (dimension security))
  return (GSW.publicWord (dimension security) (sampleCount security) (digitWidth security)
    (secret, (matrix, errors)), GSW.secretWord (dimension security) (digitWidth security) secret)

/-- Encrypt using only the public word and independent fair matrix coins. This law is total
on every public word, including malformed lengths. -/
noncomputable def encryption (security : ℕ) (publicKey : List Bool) (message : Bool) :
    PMF (List Bool) := do
  let coins ← GSW.independentList (dimension security + 1)
    (GSW.independentList (digitWidth security) (GSW.independentList (sampleCount security)
      (Cslib.Probability.PMF.uniformOfFintype Bool)))
  return GSW.ciphertextWord (dimension security) (sampleCount security) (digitWidth security)
    publicKey message coins

/-- The decision-LWE comparison is an entirely uniform matrix of the same shape and modulus,
encoded in the same row-major, least-significant-first order. -/
noncomputable def uniformPublic (security : ℕ) : PMF (List Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype
    (Fin (sampleCount security) → Fin (dimension security + 1) →
      ZMod (2 ^ digitWidth security))).map
      (fun A => (List.ofFn fun i =>
        (List.ofFn fun j => GSW.lowBits (digitWidth security) (A i j).val).flatten).flatten)

/-- **Exact decision-LWE assumption.** The public sample `[B*t+e | B]`, with uniform secret,
uniform matrix and the independent signed noise above, is indistinguishable from the uniform
matrix. Neither the secret nor errors are exposed. This is an assumption against uniform
classical strict PPT tests; no lattice reduction or hardness theorem is asserted. -/
def DecisionLWE : Prop :=
  Randomized.Indistinguishable (fun security => (keyGeneration security).map Prod.fst) uniformPublic

/-- Generate keys, let the adversary choose two messages after seeing the public key, encrypt
the selected message, and pass its entire saved word unchanged to the guessing stage. -/
noncomputable def chosenMessageGame
    (choose : ℕ → List Bool → PMF ((Bool × Bool) × List Bool))
    (guess : ℕ → List Bool → List Bool → PMF Bool) (bit : Bool) (security : ℕ) : PMF Bool := do
  let keys ← keyGeneration security
  let choice ← choose security keys.1
  let ciphertext ← encryption security keys.1 (if bit then choice.1.2 else choice.1.1)
  guess security choice.2 ciphertext

/-- Single-challenge IND-CPA: every two-stage uniform strict PPT adversary has negligible
advantage. Both clocks charge the unary parameter and complete inputs; saved state can include
the public key. The adversary is fixed before the parameter, without nonuniform advice. -/
def ChosenMessageSecure : Prop :=
  ∀ (choose : ℕ → List Bool → PMF ((Bool × Bool) × List Bool))
    (guess : ℕ → List Bool → List Bool → PMF Bool),
    Randomized.StrictPPT (Encoding.encPair Encoding.encUnary Encoding.encBits)
      (Encoding.encPair (Encoding.encPair Encoding.encBool Encoding.encBool) Encoding.encBits)
      (fun p => choose p.1 p.2) →
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBits))
      Encoding.encBool (fun p => guess p.1 p.2.1 p.2.2) →
    Randomized.Negligible (fun security =>
      nndist (Randomized.probability (chosenMessageGame choose guess false security))
        (Randomized.probability (chosenMessageGame choose guess true security)))

open Cslib Cslib.ProbComp Cslib.Probability Turing.MultiTapeTM

private theorem independentList_eval {α : Type} (count : ℕ) (program : ProbComp α) :
    GSW.independentList count (ProbComp.eval program) =
      ProbComp.eval (OracleComp.replicate count program) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [GSW.independentList] at ih
    simp only [GSW.independentList, List.replicate_succ, List.mapM_cons,
      OracleComp.replicate_succ, ProbComp.eval_bind,
      ProbComp.eval_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map,
      Function.comp_def, ih]

private theorem keyGeneration_eq (security : ℕ) :
    keyGeneration security = ProbComp.eval
      (Crypto.Homomorphic.GSW.keyGenSerialized (dimension security) (sampleCount security)
        (digitWidth security) (dimension security)) := by
  simp only [keyGeneration, Crypto.Homomorphic.GSW.keyGenSerialized,
    Crypto.Homomorphic.GSW.sampleKeyInputsSerialized, ProbComp.eval_bind, ProbComp.eval_pure,
    ← independentList_eval, eval_sampleBinaryNat, eval_sampleCenteredBinomial,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
    GSW.errorLaw, Randomized.uniformBits]
  rfl

private theorem encryption_eq (security : ℕ) (publicKey : List Bool) (message : Bool) :
    encryption security publicKey message = ProbComp.eval
      (Crypto.Homomorphic.GSW.encryptSerialized (dimension security) (sampleCount security)
        (digitWidth security) publicKey message) := by
  simp only [encryption, Crypto.Homomorphic.GSW.encryptSerialized,
    Crypto.Homomorphic.GSW.sampleCoinsSerialized, ProbComp.eval_bind, ProbComp.eval_pure,
    ← independentList_eval, ProbComp.eval_uniform, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  rfl

private theorem uniformPublic_eq (security : ℕ) :
    uniformPublic security =
      Crypto.LWE.uniformEnsemble dimension sampleCount digitWidth security := by
  unfold uniformPublic Crypto.LWE.uniformEnsemble
  congr 1
  funext A
  simpa only [← BitString.lowBits_eq_ofFn, BitString.lowBits, GSW.lowBits] using
    (Matrix.toBinary_eq A).symm

private theorem decisionLWE_iff : DecisionLWE ↔
    Crypto.DecisionLWE Crypto.Homomorphic.GSW.Parameters.dimension
      Crypto.Homomorphic.GSW.Parameters.samples Crypto.Homomorphic.GSW.Parameters.width
      (fun security => Crypto.Homomorphic.GSW.noiseLaw
        (Crypto.Homomorphic.GSW.Parameters.width security)
        (Crypto.Homomorphic.GSW.Parameters.noise security)) := by
  change Randomized.Indistinguishable _ _ ↔ _
  rw [CryptographyBridge.indistinguishable_iff]
  change Crypto.ComputationallyIndistinguishable _ _ ↔
    Crypto.ComputationallyIndistinguishable _ _
  have hreal : (fun security => (keyGeneration security).map Prod.fst) =
      Crypto.LWE.realEnsemble dimension sampleCount digitWidth
        (fun security => Crypto.Homomorphic.GSW.noiseLaw
          (digitWidth security) (dimension security)) := by
    funext security
    rw [keyGeneration_eq, Crypto.Homomorphic.GSW.eval_keyGenSerialized_publicWord]
  rw [hreal, show uniformPublic = Crypto.LWE.uniformEnsemble dimension sampleCount digitWidth
    from funext uniformPublic_eq]
  rfl

/-- The complete honest algorithms have strict native polynomial clocks. -/
theorem native_algorithms :
    Randomized.StrictPPT Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBits)
      keyGeneration ∧
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBool))
      Encoding.encBits (fun p => encryption p.1 p.2.1 p.2.2) := by
  constructor
  · apply CryptographyBridge.strictPPT_iff.mpr
    refine ⟨fun security => Crypto.Homomorphic.GSW.keyGenSerialized (dimension security)
      (sampleCount security) (digitWidth security) (dimension security), ?_, ?_⟩
    · exact Crypto.Homomorphic.GSW.isPPTOn_keyGenSerialized
        Crypto.Homomorphic.GSW.Parameters.computableInPolyTime_dimension
        Crypto.Homomorphic.GSW.Parameters.computableInPolyTime_samples
        Crypto.Homomorphic.GSW.Parameters.computableInPolyTime_width
        Crypto.Homomorphic.GSW.Parameters.computableInPolyTime_noise
    · exact fun security => (keyGeneration_eq security).symm
  · apply CryptographyBridge.strictPPT_iff.mpr
    refine ⟨fun p => Crypto.Homomorphic.GSW.encryptSerialized (dimension p.1)
      (sampleCount p.1) (digitWidth p.1) p.2.1 p.2.2, ?_, ?_⟩
    · exact Crypto.Homomorphic.GSW.isPPTOn_encryptSerialized
        (.of_tidy (Crypto.Homomorphic.GSW.Parameters.computableInPolyTime_dimension.tidy.comp (by
          fun_prop)))
        (.of_tidy (Crypto.Homomorphic.GSW.Parameters.computableInPolyTime_samples.tidy.comp (by
          fun_prop)))
        (.of_tidy (Crypto.Homomorphic.GSW.Parameters.computableInPolyTime_width.tidy.comp (by
          fun_prop)))
        (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop))
    · exact fun p => (encryption_eq p.1 p.2.1 p.2.2).symm

/-- Transfer the actual generated-key theorem to the inspectable probability-law presentation. -/
theorem indCPA (hLWE : DecisionLWE) : ChosenMessageSecure := by
  intro choose guess hchoose hguess
  obtain ⟨chooseProgram, hchooseProgram, hchooseLaw⟩ :=
    CryptographyBridge.strictPPT_iff.mp hchoose
  obtain ⟨guessProgram, hguessProgram, hguessLaw⟩ :=
    CryptographyBridge.strictPPT_iff.mp hguess
  let adversary : Crypto.Encryption.Adversary :=
    ⟨fun security pk => chooseProgram (security, pk),
      fun security state ciphertext => guessProgram (security, state, ciphertext)⟩
  have h := Crypto.Homomorphic.GSW.Parameters.indCPA (decisionLWE_iff.mp hLWE)
    adversary ⟨hchooseProgram, hguessProgram⟩
  simpa only [Crypto.Encryption.game, Crypto.Encryption.gameOn, ↓reduceIte,
    adversary, ProbComp.eval_bind, keyGeneration_eq,
    encryption_eq, hchooseLaw, hguessLaw, chosenMessageGame, PMF.monad_bind_eq_bind,
    Randomized.Negligible, Crypto.Negligible, Asymptotics.SuperpolynomialDecay,
    Crypto.Game.advantage, Crypto.Game.succProbability, Randomized.probability,
    dimension, sampleCount, digitWidth, Crypto.Homomorphic.GSW.Parameters.dimension,
    Crypto.Homomorphic.GSW.Parameters.samples, Crypto.Homomorphic.GSW.Parameters.width,
    Crypto.Homomorphic.GSW.Parameters.noise, Crypto.Homomorphic.GSW.Parameters.rows] using h

end ComplexityTests.Abstracts.GSWSecurityBridge
