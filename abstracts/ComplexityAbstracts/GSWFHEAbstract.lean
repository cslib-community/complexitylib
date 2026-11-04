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
import ComplexityAbstracts.GSWFHEBridge

/-! # Fully homomorphic encryption from GSW and decision LWE

Gentry's bootstrapping turns an encryption scheme that can homomorphically evaluate its own
decryption circuit, also when two copies are joined by a NAND gate, into a scheme that evaluates
circuits of any prescribed depth. Applied to the Gentry–Sahai–Waters (GSW) scheme at an explicit
parameter family, it gives leveled fully homomorphic encryption assuming only decision LWE for
that family. Publishing an encryption of the secret key under its own public key gives fully
homomorphic encryption, under a second, separately stated assumption: this self-encryption is
indistinguishable from an encryption of zeros.

**The core is written out.** GSW key generation, encryption and decryption at the parameter
family are stated below as explicit algorithms, and both assumptions are stated on them. The
leveled scheme of `leveled` encrypts and decrypts exactly with these algorithms behind a one-bit
tag and a framed pair of secret keys, and the key pair for fresh ciphertexts, read from the first
framed words of its keys, has exactly the GSW key-generation law. The fully homomorphic scheme of
`fullyHomomorphic` encrypts and decrypts exactly with them, and its key generation is exactly
Gentry's self-loop key: a GSW key pair together with encryptions of its secret-key bits under its
own public key.

**Only the bootstrapping machinery is existential:** homomorphic evaluation, the rest of the leveled
scheme's keys and the polynomial-size decryption circuits. For `leveled` only the marginal law of
the fresh-ciphertext key pair is fixed; the later keys of the chain, the encrypted links and their
joint law with that pair are not. The theorems state that such machinery exists with elementary
properties: correctness for the allowed circuits, fixed key and ciphertext widths, one uniformly
generated decryption circuit family for all depths, native efficiency and IND-CPA security. These
properties exclude
trivial witnesses. Decryption is the fixed GSW decryption, and evaluated ciphertexts have the fixed
ciphertext width, so evaluation cannot leave the computation to decryption: it must output a word of
that width that GSW decryption maps to the circuit's output. Nor can evaluation work in the clear.
Evaluation is efficient and accepts the challenge ciphertext of the IND-CPA game, so if the public
key revealed the secret key that decrypts evaluated ciphertexts, an adversary could evaluate a
depth-zero circuit, whose output is its input, on the challenge and read the hidden bit.

**Provenance (not part of the checked statements).** The library's constructions witness both
theorems. In the namespace `Cslib.Crypto.Homomorphic`, write `D` for GSW's decryption circuits
`GSW.DepthParameters.decryptionCircuits`. Then `GSWFHEBridge.leveled_witness` exhibits the
depth-indexed family `fun d => Leveled.scheme D (fun _ => d)` and proves the properties of
`leveled` for `Leveled.scheme D budget`, and `GSWFHEBridge.fullyHomomorphic_witness` proves those
of `fullyHomomorphic` for `FixedKey.scheme D`. A reader need not inspect them: the statements
below do not depend on their definitions.

**What a reader inspects.** The definitions and statements in this file, the displayed shared
foundations, and the eight library modules that `#check_abstract` allows at the end of the file,
each a foundational model:
* `Crypto.Computational.Homomorphic.Basic`: the record `Cslib.Crypto.Homomorphic.Scheme` of four
  algorithms, with an unused fifth field, explained before `EncryptsAndDecrypts`.
* `Languages.Probabilistic.Basic`: randomized programs `Cslib.ProbComp`, whose only randomness is
  uniform choice from finite ranges, and their output law `Cslib.ProbComp.eval`.
* `Computability.Circuit.Boolean.Encoding`: the binary circuit code
  `Cslib.Circuits.Boolean.encCircuit`, the input format of native evaluation, explained before
  `Native`.
* Under `Computability.Machines.Turing.MultiTape`, the encodings from which that code is
  assembled: framing (`Encodings.Frame.Basic`), pairs (`Encodings.Pair`), lists
  (`Encodings.List`), binary numbers (`Encodings.Nat.Bits`), and unary numbers, `n` written as
  `n` ones (`Encodings.Unary`).
Lean checks every proof through `GSWFHEBridge`.

The claims are perfect correctness on supported fresh encryptions, fixed key and ciphertext
widths, uniformly generated polynomial-size decryption circuits, uniform native strict
polynomial-time algorithms and asymptotic IND-CPA security against uniform classical adversaries.
Uniform circuit generation means a single native machine that, on `1^security`, writes the
decryption circuit's binary code `Cslib.Circuits.Boolean.encCircuit 1`, including its input arity,
in time polynomial in `security`. The claims do not include lattice hardness or a worst-case
reduction, circuit privacy, evaluation of already evaluated ciphertexts, or the concrete loss of
Gentry's Theorem 4.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*][Gentry2009]: Section 1.1,
  pp. 169–170, with Definitions 1–3; Section 2, p. 171, with Definitions 4–5 and Theorems 3–4;
  and the self-loop construction at the end of Section 2, p. 172.
* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*][GentrySahaiWaters2013],
  Sections 3.1–3.4.
-/

namespace ComplexityTests.Abstracts.GSWFHEAbstract

/-! ## The parameter family

The security parameter is supplied in unary. With `t = 1 + ⌈log₂(security + 2)⌉`, every residue
has `w = 16384 t²` binary digits, so the modulus `2 ^ w` is quasi-polynomial. The secret
dimension and the noise width are `n = security + 1`. A ciphertext is an `N × N` bit matrix with
`N = (n + 1) w`, and the public matrix has `m = N + 2 · security` rows.
-/

/-- The logarithmic size `t = 1 + ⌈log₂(security + 2)⌉`; `Nat.clog 2` is the ceiling logarithm. -/
def logSize (security : ℕ) : ℕ := 1 + Nat.clog 2 (security + 2)

/-- Binary digits per residue, `w = 16384 t²`; the modulus is `2 ^ width security`. -/
def width (security : ℕ) : ℕ := 16384 * logSize security ^ 2

/-- The LWE secret dimension `n`. The centered-binomial noise has the same width. -/
def dimension (security : ℕ) : ℕ := security + 1

/-- Ciphertext rows and columns, `N = (n + 1) w`. -/
def rows (security : ℕ) : ℕ := (dimension security + 1) * width security

/-- Rows of the public matrix, `m = N + 2 · security`. -/
def samples (security : ℕ) : ℕ := rows security + 2 * security

/-- Bits of a GSW secret key: `n` residues of `w` bits each. -/
def secretWidth (security : ℕ) : ℕ := dimension security * width security

/-- Bits of a GSW ciphertext: an `N × N` bit matrix. -/
def ciphertextWidth (security : ℕ) : ℕ := rows security * rows security

/-! ## Representation details

Residues modulo `2 ^ w` are written with exactly `w` bits, least significant first. GSW writes each
coefficient with `ℓ` bits, one more than the floor of `log q` [GentrySahaiWaters2013, Section 3.1],
which is `w + 1` for `q = 2 ^ w`, so its `N` is `(n + 1)(w + 1)`. This file omits the top digit
position, whose power of two `2 ^ w` is zero modulo `q` and whose bit is zero in every canonical
residue; decryption reads the same row in both layouts, the one whose gadget coefficient
`2 ^ (w - 1)` lies in `(q / 4, q / 2]`. A public key is the matrix `[B t + e | B]` in row-major
order, its noisy column first; a secret key lists the residues of `t`; a ciphertext lists every
bit of `μ G + R A`, its rows indexed by `(i, k)` and its columns by `(j, l)`. These words are the
actual inputs and outputs of the native algorithms.

Keys of the bootstrapped schemes are framed words (`Encoding.frame` in the shared foundations).
`unframe` reads the first framed word and `dropFrame` returns what follows it; both are defined
on every word.
-/

/-- The first framed word: keep `b` from each leading pair `true, b`, and stop at the first
`false` or when fewer than two bits remain. Thus `unframe (Encoding.frame u ++ v) = u`. -/
def unframe : List Bool → List Bool
  | true :: b :: rest => b :: unframe rest
  | _ => []

/-- What follows the first framed word: skip the leading pairs `true, b` and one `false`. Thus
`dropFrame (Encoding.frame u ++ v) = v`; a word that ends inside its first frame leaves nothing. -/
def dropFrame : List Bool → List Bool
  | true :: _ :: rest => dropFrame rest
  | false :: rest => rest
  | _ => []

/-! ## GSW key generation, encryption and decryption

Key generation samples a uniform secret `t`, a uniform matrix `B` and independent signed errors
`e`, and publishes `[B t + e | B]`. Encryption of a bit `μ` samples a uniform 0/1 matrix `R` and
outputs the bits of `μ G + R A`. Decryption multiplies one row of a ciphertext by `(1, -t)`,
which for a fresh ciphertext gives `μ 2 ^ (w - 1)` plus the small error `⟨R_i, e⟩`, and rounds
[GentrySahaiWaters2013, Sections 3.1–3.2].
-/

/-- Generate the public and secret key words. The secret, the matrix rows and the signed errors
are sampled independently, with dimension and noise width both `security + 1`. -/
noncomputable def keyGeneration (security : ℕ) : PMF (List Bool × List Bool) := do
  let secret ← GSW.independentList (dimension security) (GSW.residueLaw (width security))
  let matrix ← GSW.independentList (samples security)
    (GSW.independentList (dimension security) (GSW.residueLaw (width security)))
  let errors ← GSW.independentList (samples security) (GSW.errorLaw (dimension security))
  return (GSW.publicWord (dimension security) (samples security) (width security)
    (secret, (matrix, errors)), GSW.secretWord (dimension security) (width security) secret)

/-- Encrypt a bit using only the public word and independent fair matrix coins. This law is
defined on every public word, including malformed ones. -/
noncomputable def encryption (security : ℕ) (publicKey : List Bool) (message : Bool) :
    PMF (List Bool) := do
  let coins ← GSW.independentList (dimension security + 1)
    (GSW.independentList (width security) (GSW.independentList (samples security)
      (Cslib.Probability.PMF.uniformOfFintype Bool)))
  return GSW.ciphertextWord (dimension security) (samples security) (width security)
    publicKey message coins

/-- **GSW decryption** [GentrySahaiWaters2013, Section 3.1]. Take row `(0, w - 1)` of the
ciphertext matrix, whose gadget entry is `2 ^ (w - 1)` in column `0`, and multiply it by
`(1, -t)` modulo `2 ^ w`. For a fresh encryption `μ G + R A` this gives
`value = μ 2 ^ (w - 1) + ⟨R_(0, w - 1), e⟩`. Decryption outputs `true` exactly when `value` lies
in the middle half `[2 ^ w / 4, 3 · 2 ^ w / 4)` of the residues: GSW's rounding of
`value / 2 ^ (w - 1)` to the nearest integer, read modulo 2, with halves rounded up. It reads
the first `n w` bits of the secret word and is defined on every pair of words. -/
def decryption (security : ℕ) (secret ciphertext : List Bool) : Bool :=
  let n := dimension security
  let w := width security
  let value := (((GSW.matrixEntry (n + 1) w ciphertext (w - 1) 0 : ℤ) -
    (((List.range n).map fun j =>
      GSW.matrixEntry (n + 1) w ciphertext (w - 1) (j + 1) *
        GSW.matrixEntry n w secret 0 j).sum : ℕ)) % (2 ^ w : ℤ)).toNat
  decide (2 ^ w ≤ 4 * value ∧ 4 * value < 3 * 2 ^ w)

/-- GSW decryption of one word that holds a secret key followed by a ciphertext, the input
order of a decryption circuit: the first `secretWidth` bits are the key and the rest is the
ciphertext. For a key of exactly `secretWidth` bits,
`decryptionWord security (secret ++ ciphertext) = decryption security secret ciphertext`. -/
def decryptionWord (security : ℕ) (word : List Bool) : Bool :=
  decryption security (word.take (secretWidth security)) (word.drop (secretWidth security))

/-! ## The two assumptions

Both are computational indistinguishability against uniform classical strict PPT tests, as
defined in the shared foundations. Neither is proved; each theorem below lists the assumptions
it uses.
-/

/-- A uniformly random `m × k` matrix of residues modulo `2 ^ w`, written row by row with `w`
bits per entry, least significant first. -/
noncomputable def uniformMatrixWord (m k w : ℕ) : PMF (List Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin m → Fin k → ZMod (2 ^ w))).map
    (fun A => (List.ofFn fun i => (List.ofFn fun j => GSW.lowBits w (A i j).val).flatten).flatten)

/-- The decision-LWE comparison: a uniform matrix of the same shape and modulus as the public
key, encoded in the same order. -/
noncomputable def uniformPublic (security : ℕ) : PMF (List Bool) :=
  uniformMatrixWord (samples security) (dimension security + 1) (width security)

/-- **Decision LWE for exactly this family.** The public matrix `[B t + e | B]`, with uniform
secret, uniform matrix and the independent centered-binomial errors above, is indistinguishable
from a uniform matrix. Neither the secret nor the errors are exposed. No lattice reduction or
hardness theorem is asserted. -/
def DecisionLWE : Prop :=
  Randomized.Indistinguishable (fun security => (keyGeneration security).map Prod.fst)
    uniformPublic

/-- Sample one key pair, then encrypt either every secret-key bit or equally many zero bits under
that public key. The public key and the complete vector of encryptions are published together,
encoded as a pair of the public word and the framed list of ciphertexts. -/
noncomputable def selfEncryption (real : Bool) (security : ℕ) : PMF (List Bool) := do
  let keys ← keyGeneration security
  let encrypted ← (if real then keys.2 else List.replicate keys.2.length false).mapM
    (encryption security keys.1)
  return Encoding.encPair Encoding.encBits (Encoding.encList Encoding.encBits) (keys.1, encrypted)

/-- **One-key circular security of GSW at this family.** Encryptions of the secret key under its
own public key are indistinguishable from encryptions of zeros. This is the one-key, bitwise
case of the key-dependent-message security that Gentry's self-loop construction assumes
[Gentry2009, Section 2, p. 172]. It is a separate assumption: it is not derived from decision
LWE or from IND-CPA. -/
def CircularSecure : Prop :=
  Randomized.Indistinguishable (selfEncryption true) (selfEncryption false)

/-! ## The algorithms fixed by the theorems

The leveled scheme adds a one-bit tag to GSW ciphertexts. Its secret key frames two GSW secret
keys: one for fresh ciphertexts (tag `false`) and one for evaluated ciphertexts (tag `true`).
The fully homomorphic scheme uses GSW ciphertexts and secret keys unchanged; its public key
frames a GSW public key followed by the framed list of encryptions of the secret-key bits.
-/

/-- **Leveled encryption.** A fresh ciphertext is the tag bit `false` followed by a GSW
encryption under `unframe (unframe publicKey)`, the first framed word inside the first framed
component of the public key. A public key that frames a list of GSW public keys, followed by any
further data, is thus used through the first key in the list. -/
noncomputable def leveledEncryption (security : ℕ) (publicKey : List Bool) (bit : Bool) :
    PMF (List Bool) :=
  (encryption security (unframe (unframe publicKey)) bit).map (List.cons false)

/-- **Leveled decryption.** A secret key `Encoding.frame first ++ last` holds two GSW secret
keys. The leading tag bit of the ciphertext selects `first` (`unframe secret`) when `false` and
`last` (`dropFrame secret`) when `true`; GSW decryption then reads the selected key followed by
the rest of the ciphertext. -/
def leveledDecryption (security : ℕ) (secret ciphertext : List Bool) : Bool :=
  decryptionWord security
    ((if ciphertext.headD false then dropFrame secret else unframe secret) ++ ciphertext.tail)

/-- **Gentry's self-loop key** [Gentry2009, Section 2, p. 172]. Sample one GSW key pair and
encrypt every secret-key bit under its own public key. The public key is the GSW public key
together with these encryptions, in the encoding of `selfEncryption true`; the secret key is the
GSW secret key. -/
noncomputable def selfLoopKeyGeneration (security : ℕ) : PMF (List Bool × List Bool) := do
  let keys ← keyGeneration security
  let encryptedKey ← keys.2.mapM (encryption security keys.1)
  return (Encoding.encPair Encoding.encBits (Encoding.encList Encoding.encBits)
    (keys.1, encryptedKey), keys.2)

/-- **Self-loop encryption.** GSW encryption under the first framed component of the public
key, which is the GSW public key in a key from `selfLoopKeyGeneration`. -/
noncomputable def selfLoopEncryption (security : ℕ) (publicKey : List Bool) (bit : Bool) :
    PMF (List Bool) :=
  encryption security (unframe publicKey) bit

/-- **Self-loop decryption.** GSW decryption of the secret key followed by the ciphertext; for a
secret key of `secretWidth` bits this is `decryption security secret ciphertext`. -/
def selfLoopDecryption (security : ℕ) (secret ciphertext : List Bool) : Bool :=
  decryptionWord security (secret ++ ciphertext)

/-! ## Homomorphic encryption

A `Cslib.Crypto.Homomorphic.Scheme` is a record of four algorithms on bit strings, each taking
the security parameter: `keyGen` samples a public and a secret key; `encrypt` encrypts one bit
under a public key; `decrypt` is deterministic; and `evaluate` receives a public key, a
single-output De Morgan circuit with its number of inputs, and a list of ciphertexts. A fifth
field, `permitted`, is not used by any claim below. Randomized algorithms are terminating
programs whose only randomness is uniform choice from finite ranges (`Cslib.ProbComp`), and
`Cslib.ProbComp.eval` is their output distribution.

Circuits are single-output De Morgan circuits (constants, negation, binary conjunction and
disjunction) given as a pair of their number of inputs `C.1` and the circuit `C.2`. The upstream
`depth` is the largest number of gates on a path to the output, where inputs have depth zero and
every gate, including a constant, adds one; `size` is the number of gates.
-/

/-- The scheme encrypts with the law `encrypt` and decrypts with the function `decrypt`, on every
security parameter, key and bit or ciphertext, including malformed keys and ciphertexts. -/
def EncryptsAndDecrypts (S : Cslib.Crypto.Homomorphic.Scheme)
    (encrypt : ℕ → List Bool → Bool → PMF (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Bool) : Prop :=
  (∀ security publicKey bit,
    Cslib.ProbComp.eval (S.encrypt security publicKey bit) = encrypt security publicKey bit) ∧
  ∀ security secret ciphertext, S.decrypt security secret ciphertext =
    decrypt security secret ciphertext

/-- **Correctness for a class of circuits** [Gentry2009, Section 1.1]. Under every supported key
pair, every supported fresh encryption decrypts to its bit; and every allowed circuit, evaluated
on supported fresh encryptions of its input bits, yields only ciphertexts that decrypt to the
circuit's output. Inputs may repeat a ciphertext or share randomness; `List.Forall₂` pairs each
bit with its ciphertext and fixes the number of ciphertexts. -/
def Homomorphic (S : Cslib.Crypto.Homomorphic.Scheme)
    (allowed : ℕ → (Σ k, Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature k 1) → Prop) :
    Prop :=
  ∀ security keys, keys ∈ (Cslib.ProbComp.eval (S.keyGen security)).support →
    (∀ bit ciphertext,
      ciphertext ∈ (Cslib.ProbComp.eval (S.encrypt security keys.1 bit)).support →
        S.decrypt security keys.2 ciphertext = bit) ∧
    ∀ C bits inputs, allowed security C → bits.length = C.1 →
      List.Forall₂ (fun bit ciphertext =>
        ciphertext ∈ (Cslib.ProbComp.eval (S.encrypt security keys.1 bit)).support) bits inputs →
      ∀ ciphertext ∈ (Cslib.ProbComp.eval (S.evaluate security keys.1 C inputs)).support,
        S.decrypt security keys.2 ciphertext =
          C.2.eval Cslib.Circuits.Boolean.interpretation (fun i => bits.getD i false) 0

/-- **Compactness by fixed widths** [Gentry2009, Section 1.1]. Supported secret keys have
`keyBits` bits, and supported fresh ciphertexts and every ciphertext evaluated from them by an
allowed circuit have `cipherBits` bits, independently of the circuit's size and depth. -/
def FixedWidths (S : Cslib.Crypto.Homomorphic.Scheme)
    (allowed : ℕ → (Σ k, Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature k 1) → Prop)
    (keyBits cipherBits : ℕ → ℕ) : Prop :=
  ∀ security keys, keys ∈ (Cslib.ProbComp.eval (S.keyGen security)).support →
    keys.2.length = keyBits security ∧
    (∀ bit ciphertext,
      ciphertext ∈ (Cslib.ProbComp.eval (S.encrypt security keys.1 bit)).support →
        ciphertext.length = cipherBits security) ∧
    ∀ C bits inputs, allowed security C → bits.length = C.1 →
      List.Forall₂ (fun bit ciphertext =>
        ciphertext ∈ (Cslib.ProbComp.eval (S.encrypt security keys.1 bit)).support) bits inputs →
      ∀ ciphertext ∈ (Cslib.ProbComp.eval (S.evaluate security keys.1 C inputs)).support,
        ciphertext.length = cipherBits security

/-- **Decryption by one circuit per parameter** [Gentry2009, Definition 1]. On every secret key
of `keyBits` bits and every ciphertext of `cipherBits` bits, the circuit computes decryption
from the key bits followed by the ciphertext bits. -/
def DecryptsWith (S : Cslib.Crypto.Homomorphic.Scheme) (keyBits cipherBits : ℕ → ℕ)
    (circuit : ∀ security, Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature
      (keyBits security + cipherBits security) 1) : Prop :=
  ∀ security (secret ciphertext : List Bool), secret.length = keyBits security →
    ciphertext.length = cipherBits security →
    (circuit security).eval Cslib.Circuits.Boolean.interpretation
      (fun i => (secret ++ ciphertext).getD i false) 0 = S.decrypt security secret ciphertext

/-- **Native efficiency.** Key generation, encryption and evaluation are uniform strict PPT, and
decryption is deterministic polynomial time; each is one machine for all parameters and runs on
all raw inputs, including malformed keys and ciphertexts. Time is measured in the length of the
encoded input: the unary parameter, the words and, for evaluation, the circuit in the binary
code `Cslib.Circuits.Boolean.encCircuit 1` (its input count in unary, then its gates and output
wires with wire numbers in binary) followed by the framed list of input ciphertexts. -/
def Native (S : Cslib.Crypto.Homomorphic.Scheme) : Prop :=
  Randomized.StrictPPT Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBits)
      (fun security => Cslib.ProbComp.eval (S.keyGen security)) ∧
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBool))
      Encoding.encBits (fun p => Cslib.ProbComp.eval (S.encrypt p.1 p.2.1 p.2.2)) ∧
    Computation.PolyTime (fun p : ℕ × List Bool × List Bool => S.decrypt p.1 p.2.1 p.2.2)
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBits))
      Encoding.encBool ∧
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits
        (Encoding.encPair (Cslib.Circuits.Boolean.encCircuit 1)
          (Encoding.encList Encoding.encBits))))
      Encoding.encBits (fun p => Cslib.ProbComp.eval (S.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))

/-- **Joint native efficiency in the parameter and the depth** [Gentry2009, Definition 3]. For a
depth-indexed family `E : ℕ → Cslib.Crypto.Homomorphic.Scheme`, key generation, encryption and
evaluation are uniform strict PPT in `(security, d)` jointly, and decryption is deterministic
polynomial time in `(security, d)` jointly; each is one machine for all pairs `(security, d)`,
taking `1^security` and `1^d` in unary together with the words (and, for evaluation, the circuit in
the binary code `Cslib.Circuits.Boolean.encCircuit 1` followed by the framed list of input
ciphertexts). One polynomial in the encoded input length bounds the runtime across all pairs
`(security, d)` simultaneously. -/
def NativeInDepth (E : ℕ → Cslib.Crypto.Homomorphic.Scheme) : Prop :=
  Randomized.StrictPPT (Encoding.encPair Encoding.encUnary Encoding.encUnary)
      (Encoding.encPair Encoding.encBits Encoding.encBits)
      (fun p : ℕ × ℕ => Cslib.ProbComp.eval ((E p.2).keyGen p.1)) ∧
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encUnary
        (Encoding.encPair Encoding.encBits Encoding.encBool)))
      Encoding.encBits (fun p => Cslib.ProbComp.eval ((E p.2.1).encrypt p.1 p.2.2.1 p.2.2.2)) ∧
    Computation.PolyTime
      (fun p : ℕ × ℕ × List Bool × List Bool => (E p.2.1).decrypt p.1 p.2.2.1 p.2.2.2)
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encUnary
        (Encoding.encPair Encoding.encBits Encoding.encBits)))
      Encoding.encBool ∧
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encUnary
        (Encoding.encPair Encoding.encBits
          (Encoding.encPair (Cslib.Circuits.Boolean.encCircuit 1)
            (Encoding.encList Encoding.encBits)))))
      Encoding.encBits
      (fun p => Cslib.ProbComp.eval ((E p.2.1).evaluate p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))

/-- Generate keys, let the adversary choose two messages after seeing the public key, encrypt
the selected message, and pass the saved word and the challenge ciphertext to the guessing
stage. The secret key is never given to the adversary. -/
noncomputable def chosenMessageGame (S : Cslib.Crypto.Homomorphic.Scheme)
    (choose : ℕ → List Bool → PMF ((Bool × Bool) × List Bool))
    (guess : ℕ → List Bool → List Bool → PMF Bool) (bit : Bool) (security : ℕ) :
    PMF Bool := do
  let keys ← Cslib.ProbComp.eval (S.keyGen security)
  let choice ← choose security keys.1
  let ciphertext ← Cslib.ProbComp.eval
    (S.encrypt security keys.1 (if bit then choice.1.2 else choice.1.1))
  guess security choice.2 ciphertext

/-- **IND-CPA**: every two-stage uniform strict PPT adversary has negligible advantage in
telling apart the two challenge bits. Both stages are charged for the unary parameter and their
complete inputs; the saved word may contain the public key. The adversary is fixed before the
parameter, without nonuniform advice. -/
def ChosenMessageSecure (S : Cslib.Crypto.Homomorphic.Scheme) : Prop :=
  ∀ (choose : ℕ → List Bool → PMF ((Bool × Bool) × List Bool))
    (guess : ℕ → List Bool → List Bool → PMF Bool),
    Randomized.StrictPPT (Encoding.encPair Encoding.encUnary Encoding.encBits)
      (Encoding.encPair (Encoding.encPair Encoding.encBool Encoding.encBool) Encoding.encBits)
      (fun p => choose p.1 p.2) →
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBits))
      Encoding.encBool (fun p => guess p.1 p.2.1 p.2.2) →
    Randomized.Negligible (fun security =>
      nndist (Randomized.probability (chosenMessageGame S choose guess false security))
        (Randomized.probability (chosenMessageGame S choose guess true security)))

/-! ## Main results

`Cslib.PolynomiallyBounded f` means that a fixed power bounds `f` eventually: some `d` has
`f security ≤ security ^ d` for all large `security`.

Gentry's Definition 3 asks for one decryption circuit shared by all depths, correctness for every
circuit up to the depth, and algorithms polynomial in the parameter and the depth [Gentry2009,
Definition 3]. In `leveled`, one uniformly generated polynomial-size circuit family `circuit` and
one depth-indexed scheme family `E : ℕ → Cslib.Crypto.Homomorphic.Scheme` are chosen first. The
family `E` satisfies
`NativeInDepth E`, so key generation, encryption, decryption and evaluation on
`(1^security, 1^d, …)` each run on a single uniform machine with one runtime polynomial in
`(security, d)` jointly, and at every fixed depth `d`, `E d` is correct for circuits of depth at
most `d`, has fixed polynomial widths, decrypts with `circuit`, and is IND-CPA secure. In addition,
for every depth budget `budget : ℕ → ℕ` computable in unary polynomial time, there is a scheme `S`
obtained by substituting `d = budget security` into `E` (`S.keyGen security =
(E (budget security)).keyGen security` and `S.evaluate security =
(E (budget security)).evaluate security`) that is correct for every circuit of depth at most
`budget security`, has fixed polynomial widths, native algorithms and IND-CPA security. Any
polynomially bounded depth `d(security) ≤ c (security + 1) ^ e` is covered by the budget
`c (security + 1) ^ e`.
-/

/-- **Leveled fully homomorphic encryption from decision LWE** [Gentry2009, Theorem 3]. One
uniformly generated polynomial-size decryption circuit family `circuit` and one depth-indexed
scheme family `E` satisfy
`NativeInDepth E` (one runtime polynomial in `(security, d)` jointly), and at every depth `d` and
every unary-polynomial depth budget `budget` (via `d = budget security`), the first framed word of
the first framed component of the public key and the first framed word of the secret key, the key
pair under which fresh bits are encrypted and decrypted, are jointly distributed as
`keyGeneration`. Only this marginal law is fixed; the rest of the key is not. Only the decision-LWE
assumption for this family is used; there is no circular-security assumption. IND-CPA is the
asymptotic consequence of [Gentry2009, Theorem 4], without its exact loss. -/
theorem leveled (hLWE : DecisionLWE) :
    ∃ (circuit : ∀ security, Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature
        ((3 * secretWidth security + 1) + (ciphertextWidth security + 1)) 1)
      (E : ℕ → Cslib.Crypto.Homomorphic.Scheme),
      Computation.PolyTime
        (fun security =>
          (⟨(3 * secretWidth security + 1) + (ciphertextWidth security + 1), circuit security⟩ :
            Σ k, Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature k 1))
        Encoding.encUnary (Cslib.Circuits.Boolean.encCircuit 1) ∧
      Cslib.PolynomiallyBounded (fun security => (circuit security).size) ∧
      Cslib.PolynomiallyBounded (fun security => 3 * secretWidth security + 1) ∧
      Cslib.PolynomiallyBounded (fun security => ciphertextWidth security + 1) ∧
      NativeInDepth E ∧
      (∀ d : ℕ,
        (∀ security, (Cslib.ProbComp.eval ((E d).keyGen security)).map
          (fun keys => (unframe (unframe keys.1), unframe keys.2)) = keyGeneration security) ∧
        EncryptsAndDecrypts (E d) leveledEncryption leveledDecryption ∧
        DecryptsWith (E d) (fun security => 3 * secretWidth security + 1)
          (fun security => ciphertextWidth security + 1) circuit ∧
        Homomorphic (E d) (fun _ C => C.2.depth ≤ d) ∧
        FixedWidths (E d) (fun _ C => C.2.depth ≤ d)
          (fun security => 3 * secretWidth security + 1)
          (fun security => ciphertextWidth security + 1) ∧
        Native (E d) ∧ ChosenMessageSecure (E d)) ∧
      ∀ budget : ℕ → ℕ, Computation.PolyTime budget Encoding.encUnary Encoding.encUnary →
        ∃ S : Cslib.Crypto.Homomorphic.Scheme,
          (∀ security, S.keyGen security = (E (budget security)).keyGen security ∧
            S.evaluate security = (E (budget security)).evaluate security) ∧
          (∀ security, (Cslib.ProbComp.eval (S.keyGen security)).map
            (fun keys => (unframe (unframe keys.1), unframe keys.2)) = keyGeneration security) ∧
          EncryptsAndDecrypts S leveledEncryption leveledDecryption ∧
          DecryptsWith S (fun security => 3 * secretWidth security + 1)
            (fun security => ciphertextWidth security + 1) circuit ∧
          Homomorphic S (fun security C => C.2.depth ≤ budget security) ∧
          FixedWidths S (fun security C => C.2.depth ≤ budget security)
            (fun security => 3 * secretWidth security + 1)
            (fun security => ciphertextWidth security + 1) ∧
          Native S ∧ ChosenMessageSecure S :=
  GSWFHEBridge.leveled
    (GSWFHEBridge.unframe_eq_of rfl rfl (fun _ => rfl) (fun _ _ => rfl))
    (GSWFHEBridge.dropFrame_eq_of rfl rfl (fun _ => rfl) (fun _ _ => rfl)) hLWE

/-- **Fully homomorphic encryption from decision LWE and circular security** [Gentry2009,
Definition 2 and Section 2]. There is a scheme whose key generation is the self-loop key and
which encrypts and decrypts with GSW that is correct for every circuit, keeps GSW's widths,
decrypts with uniformly generated polynomial-size circuits, has native algorithms and is IND-CPA,
assuming decision LWE for this family and, separately, one-key circular security of GSW. -/
theorem fullyHomomorphic (hLWE : DecisionLWE) (hcircular : CircularSecure) :
    ∃ circuit : ∀ security, Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature
        (secretWidth security + ciphertextWidth security) 1,
      Computation.PolyTime
        (fun security =>
          (⟨secretWidth security + ciphertextWidth security, circuit security⟩ :
            Σ k, Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature k 1))
        Encoding.encUnary (Cslib.Circuits.Boolean.encCircuit 1) ∧
      Cslib.PolynomiallyBounded (fun security => (circuit security).size) ∧
      Cslib.PolynomiallyBounded secretWidth ∧ Cslib.PolynomiallyBounded ciphertextWidth ∧
      ∃ S : Cslib.Crypto.Homomorphic.Scheme,
        (∀ security, Cslib.ProbComp.eval (S.keyGen security) = selfLoopKeyGeneration security) ∧
        EncryptsAndDecrypts S selfLoopEncryption selfLoopDecryption ∧
        DecryptsWith S secretWidth ciphertextWidth circuit ∧
        Homomorphic S (fun _ _ => True) ∧
        FixedWidths S (fun _ _ => True) secretWidth ciphertextWidth ∧
        Native S ∧ ChosenMessageSecure S :=
  GSWFHEBridge.fullyHomomorphic
    (GSWFHEBridge.unframe_eq_of rfl rfl (fun _ => rfl) (fun _ _ => rfl)) hLWE hcircular

end ComplexityTests.Abstracts.GSWFHEAbstract

/--
info: abstract audit passed for `ComplexityTests.Abstracts.GSWFHEAbstract`: 46 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.GSWFHEAbstract allowing [
  -- shared foundations
  ComplexityAbstracts.Encoding, ComplexityAbstracts.Computation, ComplexityAbstracts.Randomized,
  ComplexityAbstracts.GSW,
  -- the scheme record and randomized programs
  Complexity.Crypto.Computational.Homomorphic.Basic,
  Complexity.Languages.Probabilistic.Basic,
  -- the binary circuit code and the encodings it is assembled from
  Complexity.Computability.Circuit.Boolean.Encoding,
  Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic,
  Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair,
  Complexity.Computability.Machines.Turing.MultiTape.Encodings.List,
  Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits,
  Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
]
