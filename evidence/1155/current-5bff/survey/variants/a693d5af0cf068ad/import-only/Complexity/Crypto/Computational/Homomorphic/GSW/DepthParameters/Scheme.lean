/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.CircuitEvaluation.PolyTime
public import Complexity.Crypto.Computational.Homomorphic.GSW.DecryptionCircuit.Parameters
public import Complexity.Crypto.Computational.Homomorphic.GSW.DecryptionCircuit.PolyTime
public import Complexity.Crypto.Computational.Homomorphic.GSW.DepthParameters.Security
public import Complexity.Crypto.Computational.Homomorphic.Refresh
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain


import Diag1155.Measure
/-!
# GSW evaluates its own augmented decryption circuit

The serialized GSW algorithms at the logarithmic-depth parameter family form a bit-encryption
`Scheme`. A circuit is permitted when its two NAND layers per De Morgan level fit
`depthBudget`. Fresh encryption and evaluation of every permitted circuit are perfectly correct,
with fixed key and ciphertext widths. The actual raw-input decryption circuit and its NAND
augmentation are permitted, so the scheme is bootstrappable in Gentry's sense
[Gentry2009, Definitions 4 and 5]. These are the premises of the generic constructions in
`Leveled` and `FixedKey` apart from security. All four algorithms and the decryption-circuit
generator have uniform native polynomial-time certificates.

IND-CPA security of the same algorithms assumes decision LWE for exactly this family.
Correctness, bootstrappability and the runtime certificates use no computational assumption,
and circular security is not asserted.

## Main definitions

* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.secretWidth`, `.ciphertextWidth`: word widths.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.scheme`: GSW as a homomorphic bit encryption.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.decryptionCircuits`: its actual decryptors.

## Main results

* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.correct`: perfect correctness of encryption and
  of evaluating every permitted circuit.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.fixedWidth`: fixed secret and ciphertext widths.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.bootstrappable`: the decryption circuit and its
  NAND augmentation are permitted.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.isPPTOn_keyGen`, `.isPPTOn_encrypt`,
  `.computableInPolyTime_decrypt`, `.isPPTOn_evaluate`: native algorithms.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.computableInPolyTime_decryptionCircuits`: a
  native generator of the decryption circuits.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.indCPA_scheme`: IND-CPA under this family's
  decision LWE.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*][Gentry2009]
* [C. Gentry, A. Sahai and B. Waters, Sections 3.3 and 3.4][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW.DepthParameters

open Circuits Circuits.Boolean Probability Turing.MultiTapeTM
open Parameters (dimension noise)

/-- Secret words hold `dimension` residues of `width` bits. -/
def secretWidth (security : ℕ) : ℕ := dimension security * width security

/-- Ciphertext words hold a square bit matrix with `rows` rows and columns. -/
def ciphertextWidth (security : ℕ) : ℕ := rows security * rows security

/-- GSW at the logarithmic-depth family. Evaluation is the deterministic layered evaluator and
reads no key. The permitted circuits are those of depth at most `depthBudget / 2`, the depth
whose compiled NAND schedule the noise margin covers. -/
noncomputable def scheme : Scheme where
  keyGen security := keyGenSerialized (dimension security) (samples security) (width security)
    (noise security)
  encrypt security := encryptSerialized (dimension security) (samples security) (width security)
  decrypt security := decryptSerialized (dimension security) (width security)
  evaluate security _ C inputs :=
    pure (evaluateCircuit (dimension security) (width security) C inputs)
  permitted security C := 2 * C.2.depth ≤ depthBudget security

/-- Encryption and evaluation of every permitted circuit are perfectly correct. -/
theorem correct : scheme.Correct where
  decrypt_encrypt security keys hkeys μ ciphertext hciphertext :=
    keyGenSerialized_encrypt_correct (width_pos security)
      (by simpa only [Nat.mul_assoc, modulus] using fresh_margin security) hkeys μ hciphertext
  decrypt_evaluate security keys hkeys C hC bits inputs hbits hinputs ciphertext hciphertext := by
    change ciphertext ∈ (ProbComp.eval (pure _ : ProbComp (List Bool))).support at hciphertext
    rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hciphertext
    subst hciphertext
    exact (evaluateCircuit_correct (width_pos security) hkeys C (noise_margin_of_le hC)
      hbits hinputs).2

/-- Secret keys, fresh ciphertexts and evaluation outputs have fixed widths. -/
theorem fixedWidth : scheme.FixedWidth secretWidth ciphertextWidth where
  secret_length security keys hkeys := by
    change keys ∈ (ProbComp.eval (keyGenSerialized _ _ _ _)).support at hkeys
    rw [eval_keyGenSerialized, PMF.mem_support_map_iff] at hkeys
    obtain ⟨typedKeys, _, rfl⟩ := hkeys
    exact length_serializeSecret _
  encrypt_length security keys hkeys μ ciphertext hciphertext :=
    (boundedError_encryptSerialized hkeys μ hciphertext).1.trans (pow_two _)
  evaluate_length security keys hkeys C _ bits inputs hbits hinputs ciphertext hciphertext := by
    change ciphertext ∈ (ProbComp.eval (pure _ : ProbComp (List Bool))).support at hciphertext
    rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hciphertext
    subst hciphertext
    exact (boundedError_evaluateCircuit C hbits
      (hinputs.imp fun μ c hc => boundedError_encryptSerialized hkeys μ hc)).1.trans (pow_two _)

/-- The actual raw-input GSW decryption circuits, secret bits first. -/
def decryptionCircuits : DecryptionCircuits scheme secretWidth ciphertextWidth where
  circuit security := DecryptionCircuit.circuit (dimension security) (width security)
  correct _ secret ciphertext hsecret hciphertext :=
    DecryptionCircuit.correct _ _ secret ciphertext hsecret hciphertext

/-- The decryption circuit and its NAND augmentation are permitted at every security parameter,
so GSW is bootstrappable for the identity and NAND gates [Gentry2009, Definition 5]. -/
theorem bootstrappable : Scheme.Bootstrappable decryptionCircuits where
  decrypt_mem security := by
    have h := DecryptionCircuit.layers_le_depthBudget security
    rwa [Layered.length_compile] at h
  nand_mem security := by
    have h := DecryptionCircuit.layers_augment_le_depthBudget security
    rwa [Layered.length_compile] at h

private theorem native_dimension : ComputableInPolyTime dimension encUnary encUnary :=
  Parameters.computableInPolyTime_dimension

private theorem native_width : ComputableInPolyTime width encUnary encUnary :=
  computableInPolyTime_width

/-- Key generation is strict PPT in the unary security parameter. -/
theorem isPPTOn_keyGen : IsPPTOn encUnary (encPair encBits encBits) scheme.keyGen :=
  isPPTOn_keyGenSerialized Parameters.computableInPolyTime_dimension
    computableInPolyTime_samples computableInPolyTime_width
    Parameters.computableInPolyTime_noise

/-- Encryption is strict PPT on every public word and message. -/
theorem isPPTOn_encrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => scheme.encrypt p.1 p.2.1 p.2.2) := by
  have hk := ComputableInPolyTime.fst encUnary (encPair encBits encBool)
  change IsPPTOn _ _ (fun p : ℕ × List Bool × Bool =>
    encryptSerialized (dimension p.1) (samples p.1) (width p.1) p.2.1 p.2.2)
  apply isPPTOn_encryptSerialized
  · exact Parameters.computableInPolyTime_dimension.comp hk
  · exact computableInPolyTime_samples.comp hk
  · exact computableInPolyTime_width.comp hk
  · fun_prop
  · fun_prop

/-- Decryption runs in native polynomial time on every raw secret and ciphertext word. -/
theorem computableInPolyTime_decrypt :
    ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => scheme.decrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool := by
  change ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
    decryptSerialized (dimension p.1) (width p.1) p.2.1 p.2.2) _ _
  apply computableInPolyTime_decryptSerialized
  · exact native_dimension.comp (.fst _ _)
  · exact native_width.comp (.fst _ _)
  · fun_prop
  · fun_prop

/-- Evaluation is strict PPT on every security parameter, public word, circuit and input list;
it samples no coins. -/
theorem isPPTOn_evaluate :
    IsPPTOn (encPair encUnary (encPair encBits (encPair (encCircuit 1) (encList encBits))))
      encBits (fun p => scheme.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  change IsPPTOn _ _ (fun p : ℕ × List Bool × (Σ k, Circuit signature k 1) × List (List Bool) =>
    pure (evaluateCircuit (dimension p.1) (width p.1) p.2.2.1 p.2.2.2))
  apply ComputableInPolyTime.isPPTOn
  apply computableInPolyTime_evaluateCircuit
  · exact native_dimension.comp (.fst _ _)
  · exact native_width.comp (.fst _ _)
  · fun_prop
  · fun_prop

/-- The decryption circuits, with their unary input arity, have a native generator. -/
theorem computableInPolyTime_decryptionCircuits :
    ComputableInPolyTime
      (fun security => (⟨_, decryptionCircuits.circuit security⟩ : Σ k, Circuit signature k 1))
      encUnary (encCircuit 1) := by
  change ComputableInPolyTime (fun security => (fun p : ℕ × ℕ =>
      (⟨DecryptionCircuit.inputWidth p.1 p.2, DecryptionCircuit.circuit p.1 p.2⟩ :
        Σ k, Circuit signature k 1)) (dimension security, width security)) _ _
  exact DecryptionCircuit.computableInPolyTime_circuit.comp (native_dimension.prod native_width)

/-- The scheme's key generation and encryption are IND-CPA under decision LWE for exactly this
family's dimensions, modulus and centered-binomial noise. -/
theorem indCPA_scheme
    (hLWE : DecisionLWE dimension samples width (fun k => noiseLaw (width k) (noise k))) :
    Encryption.INDCPA scheme.keyGen scheme.encrypt :=
  indCPA hLWE

end Cslib.Crypto.Homomorphic.GSW.DepthParameters
