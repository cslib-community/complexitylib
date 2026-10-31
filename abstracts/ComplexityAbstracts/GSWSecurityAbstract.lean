/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import ComplexityAbstracts.Randomized
import ComplexityAbstracts.GSW
import ComplexityAbstracts.GSWSecurityBridge

/-! # Generated-key GSW security from decision LWE

The explicit positive-noise GSW algorithms below are uniform strict polynomial time and satisfy
single-challenge IND-CPA under decision LWE for their exact centered-binomial error family.
The assumption concerns public matrices; the conclusion concerns adaptive message selection and
ciphertexts. The reduction uses one uniform distinguisher with loss two and a negligible
shared-public-matrix statistical error.

The definitions and theorem statements are self-contained over upstream mathematics, the displayed
shared foundations (`Encoding`, `Computation`, `Randomized`, and `GSW`), and plain machines. Lean
checks their connection to the implementation through `GSWSecurityBridge`; `#check_abstract`
permits no internal implementation dependencies in these public statements. This is classical
public-key security, not circular security, a worst-case lattice reduction, or an FHE or
bootstrappability theorem. Decryption and homomorphic correctness are separate results.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*][GentrySahaiWaters2013],
  Sections 2.1, 3.1–3.2.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 11.2.
* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*][NISTFIPS203], Algorithm 8,
  for the count-difference noise construction, without identifying this scheme with ML-KEM.
-/

namespace ComplexityTests.Abstracts.GSWSecurityAbstract

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

/-- **Native efficiency.** Both actual honest algorithms have one uniform strict polynomial
clock. This includes the complete public/secret output and every ciphertext bit, for arbitrary
public input words; no fixed-dimensional finite encoding supplies efficiency for free. -/
theorem native_algorithms :
    Randomized.StrictPPT Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBits)
      keyGeneration ∧
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBool))
      Encoding.encBits (fun p => encryption p.1 p.2.1 p.2.2) :=
  GSWSecurityBridge.native_algorithms

/-- **GSW generated-key IND-CPA from exact decision LWE.** For this explicit positive-noise
family, only the preceding LWE hypothesis is assumed. Security holds for every uniform classical
strict PPT message-selection and guessing pair, retaining arbitrary saved words. -/
theorem indCPA (hLWE : DecisionLWE) : ChosenMessageSecure :=
  GSWSecurityBridge.indCPA hLWE

end ComplexityTests.Abstracts.GSWSecurityAbstract

/--
info: abstract audit passed for `ComplexityTests.Abstracts.GSWSecurityAbstract`: 13 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.GSWSecurityAbstract allowing [
  ComplexityAbstracts.Encoding, ComplexityAbstracts.Computation, ComplexityAbstracts.Randomized,
  ComplexityAbstracts.GSW
]
