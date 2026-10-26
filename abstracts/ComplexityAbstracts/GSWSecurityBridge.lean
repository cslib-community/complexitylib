/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.CryptographyBridge
import Complexity.Crypto.Computational.Homomorphic.GSW.Security

/-! # Bridge for generated-key GSW security

The public abstract uses explicit PMF laws and the plain finite-coin-tape presentation of strict
PPT. This bridge identifies those laws with the complete serialized programs and reuses the
native generated-key security theorem. The bridge introduces no notation or elaboration rules.
-/

namespace ComplexityTests.Abstracts.GSWSecurityBridge

/-- Self-delimiting framing: double each bit `b` to `[true,b]` and terminate with `[false]`. -/
def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

/-- Encode a pair by framing its first component and appending its second. -/
def encodePair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) (p : α × β) :
    List Bool := frame (a p.1) ++ b p.2

theorem encodePair_injective {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) :
    Function.Injective (encodePair a b) := CryptographyBridge.encodePair_injective a b

/-- The injective pair encoding. The arrow `↪` means an injective function. -/
def pairEncoding {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨encodePair a b, encodePair_injective a b⟩

/-- Bitstrings encode as themselves. -/
def bitsEncoding : List Bool ↪ List Bool := Function.Embedding.refl _

/-- The security parameter is supplied in unary: `n` consecutive true bits. -/
def unaryEncoding : ℕ ↪ List Bool := ⟨fun n => List.replicate n true,
  fun _ _ h => by simpa only [List.length_replicate] using congrArg List.length h⟩

/-- A Boolean output encodes as one bit. -/
def boolEncoding : Bool ↪ List Bool := ⟨fun b => [b], fun _ _ h => by injection h⟩

/-- One deterministic finite-state binary multitape Turing machine halts with the encoded
answer on every encoded input, within polynomially bounded time and space in its bit length.
`ComputableInTimeAndSpaceOfLength` is the upstream machine contract; both bounds are uniform. -/
def PolyTime {α β : Type} (f : α → β) (a : α ↪ List Bool) (b : β ↪ List Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f a b t s

/-- Exactly `n` independent fair bits, as a word of length `n`. -/
noncomputable def uniformBits (n : ℕ) : PMF (List Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin n → Bool)).map List.ofFn

/-- A uniformly strict polynomial-time probability law: one deterministic evaluator, supplied
with polynomially many independent fair bits, realizes every input's law exactly. Its time
includes reading the coin tape and writing the encoded output. Both evaluator and polynomial
are fixed before the input. This also bounds every execution, rather than its expectation. -/
def StrictPPT {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool)
    (law : α → PMF β) : Prop :=
  ∃ (c d : ℕ) (evaluate : α → List Bool → β),
    PolyTime (fun p : α × List Bool => evaluate p.1 p.2) (pairEncoding a bitsEncoding) b ∧
    ∀ x, law x = (uniformBits (c * ((a x).length + 1) ^ d)).map (evaluate x)

/-- A nonnegative error is negligible if multiplication by every fixed power of the security
parameter still tends to zero. The threshold and decay bound may depend on the whole adversary. -/
def Negligible (ε : ℕ → NNReal) : Prop :=
  ∀ k : ℕ, Filter.Tendsto (fun n : ℕ => (n : NNReal) ^ k * ε n)
    Filter.atTop (nhds 0)

/-- Probability that a Boolean experiment returns true. -/
noncomputable def probability (p : PMF Bool) : NNReal := (p true).toNNReal

/-- Every uniform strict PPT test has negligible distinguishing advantage.
The test receives the unary security parameter and a sample. `bind` samples the word and then runs
the test with independent coins; `nndist` is the absolute difference of success probabilities. -/
def Indistinguishable (X Y : ℕ → PMF (List Bool)) : Prop :=
  ∀ test : ℕ → List Bool → PMF Bool,
    StrictPPT (pairEncoding unaryEncoding bitsEncoding) boolEncoding
      (fun p => test p.1 p.2) →
    Negligible (fun n => nndist (probability ((X n).bind (test n)))
      (probability ((Y n).bind (test n))))

/-- The secret dimension and centered-binomial width are positive at every parameter. -/
def dimension (security : ℕ) : ℕ := security + 1

/-- Each residue uses `16 + 8 * ceil(log₂(security+1))` binary digits; the modulus is
`2 ^ digitWidth security`. The ceiling logarithm is `Nat.clog`. -/
def digitWidth (security : ℕ) : ℕ := 16 + 8 * Nat.clog 2 (security + 1)

/-- The public matrix has this many rows, giving `2 * security` surplus entropy bits. -/
def sampleCount (security : ℕ) : ℕ := (dimension security + 1) * digitWidth security + 2 * security

/-- Collect independent draws in their original order; the empty list requires no draw. -/
noncomputable def independentList {α : Type} (count : ℕ) (law : PMF α) : PMF (List α) :=
  (List.replicate count ()).mapM (fun _ => law)

/-- A canonical residue representative chosen uniformly from `0,...,2^w-1`. -/
noncomputable def residueLaw (w : ℕ) : PMF ℕ :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin (2 ^ w))).map Fin.val

/-- The exact signed noise is the difference of the counts in two independent words of length
`noiseWidth`. Its support is `[-noiseWidth,noiseWidth]`; this is not a discrete Gaussian. -/
noncomputable def errorLaw (noiseWidth : ℕ) : PMF ℤ := do
  let positive ← uniformBits noiseWidth
  let negative ← uniformBits noiseWidth
  return (positive.count true : ℤ) - negative.count true

/-- Write exactly `w` digits, least significant first, including leading zeros. -/
def lowBits (w value : ℕ) : List Bool := (List.range w).map value.testBit

/-- The leading entry of `[B*t+e | B]`, reduced by signed Euclidean remainder. -/
def rowHead (n w : ℕ) (inputs : List ℕ × (List (List ℕ) × List ℤ)) (i : ℕ) : ℕ :=
  (((((List.range n).map fun j =>
    (inputs.2.1.getD i []).getD j 0 * inputs.1.getD j 0).sum : ℕ) +
      inputs.2.2.getD i 0 : ℤ) % (2 ^ w : ℤ)).toNat

/-- Row-major serialization of the public matrix, with its noisy column first. -/
def publicWord (n m w : ℕ) (inputs : List ℕ × (List (List ℕ) × List ℤ)) : List Bool :=
  (List.range m).flatMap fun i =>
    lowBits w (rowHead n w inputs i) ++
      (List.range n).flatMap fun j => lowBits w ((inputs.2.1.getD i []).getD j 0 % 2 ^ w)

/-- Serialize the secret residues; these bits are not given to the adversary. -/
def secretWord (n w : ℕ) (secret : List ℕ) : List Bool :=
  (List.range n).flatMap fun j => lowBits w (secret.getD j 0 % 2 ^ w)

/-- Generate the actual public/secret pair. The secret, matrix rows, and signed errors are all
sampled independently, with `n = noiseWidth = security+1`. -/
noncomputable def keyGeneration (security : ℕ) : PMF (List Bool × List Bool) := do
  let secret ← independentList (dimension security) (residueLaw (digitWidth security))
  let matrix ← independentList (sampleCount security)
    (independentList (dimension security) (residueLaw (digitWidth security)))
  let errors ← independentList (sampleCount security) (errorLaw (dimension security))
  return (publicWord (dimension security) (sampleCount security) (digitWidth security)
    (secret, (matrix, errors)), secretWord (dimension security) (digitWidth security) secret)

/-- Read a fixed-width matrix entry. Missing bits are zero, and excess bits are ignored. -/
def matrixEntry (cols w : ℕ) (word : List Bool) (i j : ℕ) : ℕ :=
  ((word.drop ((i * cols + j) * w) ++ List.replicate w false).take w).foldr Nat.bit 0

/-- An entry of `message*G + R*A`, before binary decomposition. -/
def ciphertextEntry (n m w : ℕ) (publicKey : List Bool) (message : Bool)
    (coins : List (List (List Bool))) (i k j : ℕ) : ℕ :=
  ((if i = j then message.toNat * 2 ^ k else 0) +
    ((List.range m).map fun r =>
      if ((coins.getD i []).getD k []).getD r false then
        matrixEntry (n + 1) w publicKey r j else 0).sum) % 2 ^ w

/-- Write every bit of the square ciphertext. Its row order is `(i,k)` and column order `(j,l)`;
this is the bit decomposition of `message*G + R*A`, equivalent to the GSW flattening formula. -/
def ciphertextWord (n m w : ℕ) (publicKey : List Bool) (message : Bool)
    (coins : List (List (List Bool))) : List Bool :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range w).flatMap fun k =>
      (List.range (n + 1)).flatMap fun j =>
        lowBits w (ciphertextEntry n m w publicKey message coins i k j)

/-- Encrypt using only the public word and independent fair matrix coins. This law is total
on every public word, including malformed lengths. -/
noncomputable def encryption (security : ℕ) (publicKey : List Bool) (message : Bool) :
    PMF (List Bool) := do
  let coins ← independentList (dimension security + 1)
    (independentList (digitWidth security) (independentList (sampleCount security)
      (Cslib.Probability.PMF.uniformOfFintype Bool)))
  return ciphertextWord (dimension security) (sampleCount security) (digitWidth security)
    publicKey message coins

/-- The decision-LWE comparison is an entirely uniform matrix of the same shape and modulus,
encoded in the same row-major, least-significant-first order. -/
noncomputable def uniformPublic (security : ℕ) : PMF (List Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype
    (Fin (sampleCount security) → Fin (dimension security + 1) →
      ZMod (2 ^ digitWidth security))).map
      (fun A => (List.ofFn fun i =>
        (List.ofFn fun j => lowBits (digitWidth security) (A i j).val).flatten).flatten)

/-- **Exact decision-LWE assumption.** The public sample `[B*t+e | B]`, with uniform secret,
uniform matrix and the independent signed noise above, is indistinguishable from the uniform
matrix. Neither the secret nor errors are exposed. This is an assumption against uniform
classical strict PPT tests; no lattice reduction or hardness theorem is asserted. -/
def DecisionLWE : Prop :=
  Indistinguishable (fun security => (keyGeneration security).map Prod.fst) uniformPublic

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
    StrictPPT (pairEncoding unaryEncoding bitsEncoding)
      (pairEncoding (pairEncoding boolEncoding boolEncoding) bitsEncoding)
      (fun p => choose p.1 p.2) →
    StrictPPT (pairEncoding unaryEncoding (pairEncoding bitsEncoding bitsEncoding)) boolEncoding
      (fun p => guess p.1 p.2.1 p.2.2) →
    Negligible (fun security =>
      nndist (probability (chosenMessageGame choose guess false security))
        (probability (chosenMessageGame choose guess true security)))

open Cslib Cslib.ProbComp Cslib.Probability Turing.MultiTapeTM

private theorem independentList_eval {α : Type} (count : ℕ) (program : ProbComp α) :
    independentList count (ProbComp.eval program) =
      ProbComp.eval (OracleComp.replicate count program) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [independentList] at ih
    simp only [independentList, List.replicate_succ, List.mapM_cons,
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
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
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
  simpa only [← BitString.lowBits_eq_ofFn, BitString.lowBits, lowBits] using
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
    StrictPPT unaryEncoding (pairEncoding bitsEncoding bitsEncoding) keyGeneration ∧
    StrictPPT (pairEncoding unaryEncoding (pairEncoding bitsEncoding boolEncoding)) bitsEncoding
      (fun p => encryption p.1 p.2.1 p.2.2) := by
  constructor
  · change Randomized.StrictPPT _ _ _
    apply CryptographyBridge.strictPPT_iff.mpr
    refine ⟨fun security => Crypto.Homomorphic.GSW.keyGenSerialized (dimension security)
      (sampleCount security) (digitWidth security) (dimension security), ?_, ?_⟩
    · exact Crypto.Homomorphic.GSW.isPPTOn_keyGenSerialized
        Crypto.Homomorphic.GSW.Parameters.computableInPolyTime_dimension
        Crypto.Homomorphic.GSW.Parameters.computableInPolyTime_samples
        Crypto.Homomorphic.GSW.Parameters.computableInPolyTime_width
        Crypto.Homomorphic.GSW.Parameters.computableInPolyTime_noise
    · exact fun security => (keyGeneration_eq security).symm
  · change Randomized.StrictPPT _ _ _
    apply CryptographyBridge.strictPPT_iff.mpr
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
    Negligible, Crypto.Negligible, Asymptotics.SuperpolynomialDecay,
    Crypto.Game.advantage, Crypto.Game.succProbability, probability,
    dimension, sampleCount, digitWidth, Crypto.Homomorphic.GSW.Parameters.dimension,
    Crypto.Homomorphic.GSW.Parameters.samples, Crypto.Homomorphic.GSW.Parameters.width,
    Crypto.Homomorphic.GSW.Parameters.noise, Crypto.Homomorphic.GSW.Parameters.rows] using h

end ComplexityTests.Abstracts.GSWSecurityBridge
