/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.CryptographyBridge
import ComplexityAbstracts.Randomized
import ComplexityAbstracts.GSW
import Complexity.Crypto.Computational.Homomorphic.GSW.FullyHomomorphic

/-! # Bridge for fully homomorphic encryption from GSW

The public abstract states the GSW algorithms, both assumptions and every claimed property in
elementary terms, and asserts that suitable bootstrapping machinery exists. This bridge proves
that the library's constructions are such machinery: `leveled_witness` for
`Leveled.scheme GSW.DepthParameters.decryptionCircuits budget` and `fullyHomomorphic_witness` for
`FixedKey.scheme GSW.DepthParameters.decryptionCircuits`. It identifies their encryption,
decryption and fixed-key generation, and the law of the leveled chain's first key pair, with the
explicit GSW algorithms, identifies the assumptions with the library's decision-LWE and
circular-security experiments, and derives the elementary properties from `Scheme.Correct`,
`Scheme.FixedWidth`, the native certificates and `Encryption.INDCPA`. The leveled endpoint is
assembled for every efficiently computable budget from the generic bootstrapping lemmas. The
bridge introduces no notation or elaboration rules.
-/

namespace ComplexityTests.Abstracts.GSWFHEBridge

open Cslib Cslib.ProbComp Cslib.Probability Turing.MultiTapeTM
open Cslib.Crypto Cslib.Crypto.Homomorphic
open ComplexityTests.Abstracts.GSW

def logSize (security : ℕ) : ℕ := 1 + Nat.clog 2 (security + 2)

def width (security : ℕ) : ℕ := 16384 * logSize security ^ 2

def dimension (security : ℕ) : ℕ := security + 1

def rows (security : ℕ) : ℕ := (dimension security + 1) * width security

def samples (security : ℕ) : ℕ := rows security + 2 * security

def secretWidth (security : ℕ) : ℕ := dimension security * width security

def ciphertextWidth (security : ℕ) : ℕ := rows security * rows security

noncomputable def keyGeneration (security : ℕ) : PMF (List Bool × List Bool) := do
  let secret ← independentList (dimension security) (residueLaw (width security))
  let matrix ← independentList (samples security)
    (independentList (dimension security) (residueLaw (width security)))
  let errors ← independentList (samples security) (errorLaw (dimension security))
  return (publicWord (dimension security) (samples security) (width security)
    (secret, (matrix, errors)), secretWord (dimension security) (width security) secret)

noncomputable def encryption (security : ℕ) (publicKey : List Bool) (message : Bool) :
    PMF (List Bool) := do
  let coins ← independentList (dimension security + 1)
    (independentList (width security) (independentList (samples security)
      (Cslib.Probability.PMF.uniformOfFintype Bool)))
  return ciphertextWord (dimension security) (samples security) (width security)
    publicKey message coins

def decryption (security : ℕ) (secret ciphertext : List Bool) : Bool :=
  let n := dimension security
  let w := width security
  let value := (((matrixEntry (n + 1) w ciphertext (w - 1) 0 : ℤ) -
    (((List.range n).map fun j =>
      matrixEntry (n + 1) w ciphertext (w - 1) (j + 1) * matrixEntry n w secret 0 j).sum : ℕ)) %
        (2 ^ w : ℤ)).toNat
  decide (2 ^ w ≤ 4 * value ∧ 4 * value < 3 * 2 ^ w)

def decryptionWord (security : ℕ) (word : List Bool) : Bool :=
  decryption security (word.take (secretWidth security)) (word.drop (secretWidth security))

noncomputable def uniformMatrixWord (m k w : ℕ) : PMF (List Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin m → Fin k → ZMod (2 ^ w))).map
    (fun A => (List.ofFn fun i => (List.ofFn fun j => lowBits w (A i j).val).flatten).flatten)

noncomputable def uniformPublic (security : ℕ) : PMF (List Bool) :=
  uniformMatrixWord (samples security) (dimension security + 1) (width security)

def DecisionLWE : Prop :=
  Randomized.Indistinguishable (fun security => (keyGeneration security).map Prod.fst)
    uniformPublic

noncomputable def selfEncryption (real : Bool) (security : ℕ) : PMF (List Bool) := do
  let keys ← keyGeneration security
  let encrypted ← (if real then keys.2 else List.replicate keys.2.length false).mapM
    (encryption security keys.1)
  return Encoding.encPair Encoding.encBits (Encoding.encList Encoding.encBits) (keys.1, encrypted)

def CircularSecure : Prop :=
  Randomized.Indistinguishable (selfEncryption true) (selfEncryption false)

noncomputable def selfLoopKeyGeneration (security : ℕ) : PMF (List Bool × List Bool) := do
  let keys ← keyGeneration security
  let encryptedKey ← keys.2.mapM (encryption security keys.1)
  return (Encoding.encPair Encoding.encBits (Encoding.encList Encoding.encBits)
    (keys.1, encryptedKey), keys.2)

/-! The abstract defines its framing decoders by recursion. Recursive definitions in two files
are not definitionally equal, so the definitions that read framed keys take the decoders as
parameters, and the theorems assume only that they agree with the library's decoders. -/

section Decoders

variable (unframe dropFrame : List Bool → List Bool)

noncomputable def leveledEncryption (security : ℕ) (publicKey : List Bool) (bit : Bool) :
    PMF (List Bool) :=
  (encryption security (unframe (unframe publicKey)) bit).map (List.cons false)

def leveledDecryption (security : ℕ) (secret ciphertext : List Bool) : Bool :=
  decryptionWord security
    ((if ciphertext.headD false then dropFrame secret else unframe secret) ++ ciphertext.tail)

noncomputable def selfLoopEncryption (security : ℕ) (publicKey : List Bool) (bit : Bool) :
    PMF (List Bool) :=
  encryption security (unframe publicKey) bit

end Decoders

def selfLoopDecryption (security : ℕ) (secret ciphertext : List Bool) : Bool :=
  decryptionWord security (secret ++ ciphertext)

def EncryptsAndDecrypts (S : Homomorphic.Scheme)
    (encrypt : ℕ → List Bool → Bool → PMF (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Bool) : Prop :=
  (∀ security publicKey bit,
    ProbComp.eval (S.encrypt security publicKey bit) = encrypt security publicKey bit) ∧
  ∀ security secret ciphertext, S.decrypt security secret ciphertext =
    decrypt security secret ciphertext

def Homomorphic (S : Homomorphic.Scheme)
    (allowed : ℕ → (Σ k, Circuits.Circuit Circuits.Boolean.signature k 1) → Prop) : Prop :=
  ∀ security keys, keys ∈ (ProbComp.eval (S.keyGen security)).support →
    (∀ bit ciphertext,
      ciphertext ∈ (ProbComp.eval (S.encrypt security keys.1 bit)).support →
        S.decrypt security keys.2 ciphertext = bit) ∧
    ∀ C bits inputs, allowed security C → bits.length = C.1 →
      List.Forall₂ (fun bit ciphertext =>
        ciphertext ∈ (ProbComp.eval (S.encrypt security keys.1 bit)).support) bits inputs →
      ∀ ciphertext ∈ (ProbComp.eval (S.evaluate security keys.1 C inputs)).support,
        S.decrypt security keys.2 ciphertext =
          C.2.eval Circuits.Boolean.interpretation (fun i => bits.getD i false) 0

def FixedWidths (S : Homomorphic.Scheme)
    (allowed : ℕ → (Σ k, Circuits.Circuit Circuits.Boolean.signature k 1) → Prop)
    (keyBits cipherBits : ℕ → ℕ) : Prop :=
  ∀ security keys, keys ∈ (ProbComp.eval (S.keyGen security)).support →
    keys.2.length = keyBits security ∧
    (∀ bit ciphertext,
      ciphertext ∈ (ProbComp.eval (S.encrypt security keys.1 bit)).support →
        ciphertext.length = cipherBits security) ∧
    ∀ C bits inputs, allowed security C → bits.length = C.1 →
      List.Forall₂ (fun bit ciphertext =>
        ciphertext ∈ (ProbComp.eval (S.encrypt security keys.1 bit)).support) bits inputs →
      ∀ ciphertext ∈ (ProbComp.eval (S.evaluate security keys.1 C inputs)).support,
        ciphertext.length = cipherBits security

def DecryptsWith (S : Homomorphic.Scheme) (keyBits cipherBits : ℕ → ℕ)
    (circuit : ∀ security, Circuits.Circuit Circuits.Boolean.signature
      (keyBits security + cipherBits security) 1) : Prop :=
  ∀ security (secret ciphertext : List Bool), secret.length = keyBits security →
    ciphertext.length = cipherBits security →
    (circuit security).eval Circuits.Boolean.interpretation
      (fun i => (secret ++ ciphertext).getD i false) 0 = S.decrypt security secret ciphertext

def Native (S : Homomorphic.Scheme) : Prop :=
  Randomized.StrictPPT Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBits)
      (fun security => ProbComp.eval (S.keyGen security)) ∧
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBool))
      Encoding.encBits (fun p => ProbComp.eval (S.encrypt p.1 p.2.1 p.2.2)) ∧
    Computation.PolyTime (fun p : ℕ × List Bool × List Bool => S.decrypt p.1 p.2.1 p.2.2)
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBits))
      Encoding.encBool ∧
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits
        (Encoding.encPair (Circuits.Boolean.encCircuit 1)
          (Encoding.encList Encoding.encBits))))
      Encoding.encBits (fun p => ProbComp.eval (S.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))

def NativeInDepth (E : ℕ → Homomorphic.Scheme) : Prop :=
  Randomized.StrictPPT (Encoding.encPair Encoding.encUnary Encoding.encUnary)
      (Encoding.encPair Encoding.encBits Encoding.encBits)
      (fun p : ℕ × ℕ => ProbComp.eval ((E p.2).keyGen p.1)) ∧
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encUnary
        (Encoding.encPair Encoding.encBits Encoding.encBool)))
      Encoding.encBits (fun p => ProbComp.eval ((E p.2.1).encrypt p.1 p.2.2.1 p.2.2.2)) ∧
    Computation.PolyTime
      (fun p : ℕ × ℕ × List Bool × List Bool => (E p.2.1).decrypt p.1 p.2.2.1 p.2.2.2)
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encUnary
        (Encoding.encPair Encoding.encBits Encoding.encBits)))
      Encoding.encBool ∧
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encUnary
        (Encoding.encPair Encoding.encBits
          (Encoding.encPair (Circuits.Boolean.encCircuit 1)
            (Encoding.encList Encoding.encBits)))))
      Encoding.encBits
      (fun p => ProbComp.eval ((E p.2.1).evaluate p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))

noncomputable def chosenMessageGame (S : Homomorphic.Scheme)
    (choose : ℕ → List Bool → PMF ((Bool × Bool) × List Bool))
    (guess : ℕ → List Bool → List Bool → PMF Bool) (bit : Bool) (security : ℕ) :
    PMF Bool := do
  let keys ← ProbComp.eval (S.keyGen security)
  let choice ← choose security keys.1
  let ciphertext ← ProbComp.eval
    (S.encrypt security keys.1 (if bit then choice.1.2 else choice.1.1))
  guess security choice.2 ciphertext

def ChosenMessageSecure (S : Homomorphic.Scheme) : Prop :=
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

/-! ### The framing decoders -/

/-- A function with the defining equations of the abstract's `unframe` is the library's
`unframe`. -/
theorem unframe_eq_of {unframe : List Bool → List Bool} (hnil : unframe [] = [])
    (hone : unframe [true] = []) (hfalse : ∀ rest, unframe (false :: rest) = [])
    (hpair : ∀ b rest, unframe (true :: b :: rest) = b :: unframe rest) :
    ∀ word, unframe word = Turing.MultiTapeTM.unframe word
  | [] => hnil
  | [true] => hone
  | false :: rest => hfalse rest
  | true :: b :: rest => by
    rw [hpair, unframe_eq_of hnil hone hfalse hpair rest]
    rfl

/-- A function with the defining equations of the abstract's `dropFrame` is the library's
`dropFrame`. -/
theorem dropFrame_eq_of {dropFrame : List Bool → List Bool} (hnil : dropFrame [] = [])
    (hone : dropFrame [true] = []) (hfalse : ∀ rest, dropFrame (false :: rest) = rest)
    (hpair : ∀ b rest, dropFrame (true :: b :: rest) = dropFrame rest) :
    ∀ word, dropFrame word = Turing.MultiTapeTM.dropFrame word
  | [] => hnil
  | [true] => hone
  | false :: rest => hfalse rest
  | true :: b :: rest => by
    rw [hpair, dropFrame_eq_of hnil hone hfalse hpair rest]
    rfl

/-- The first framed word of a list of framed words, or the empty word if there is none. -/
private theorem getD_frames (word : List Bool) :
    ((frames word).map Decoder.bits.decode).getD 0 [] = Turing.MultiTapeTM.unframe word := by
  by_cases h : word = []
  · subst h
    rw [frames_nil]
    rfl
  · rw [frames_of_ne_nil h]
    rfl

/-! ### The GSW laws are the library's serialized programs -/

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
      (GSW.keyGenSerialized (dimension security) (samples security) (width security)
        (dimension security)) := by
  simp only [keyGeneration, GSW.keyGenSerialized, GSW.sampleKeyInputsSerialized,
    ProbComp.eval_bind, ProbComp.eval_pure, ← independentList_eval, eval_sampleBinaryNat,
    eval_sampleCenteredBinomial, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind, errorLaw, Randomized.uniformBits]
  rfl

private theorem encryption_eq (security : ℕ) (publicKey : List Bool) (message : Bool) :
    encryption security publicKey message = ProbComp.eval
      (GSW.encryptSerialized (dimension security) (samples security) (width security)
        publicKey message) := by
  simp only [encryption, GSW.encryptSerialized, GSW.sampleCoinsSerialized, ProbComp.eval_bind,
    ProbComp.eval_pure, ← independentList_eval, ProbComp.eval_uniform, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  rfl

/-- The library's GSW key generation and encryption have exactly the explicit laws. -/
theorem base_scheme (security : ℕ) :
    ProbComp.eval (GSW.DepthParameters.scheme.keyGen security) = keyGeneration security ∧
      ∀ publicKey message,
        ProbComp.eval (GSW.DepthParameters.scheme.encrypt security publicKey message) =
          encryption security publicKey message :=
  ⟨(keyGeneration_eq security).symm, fun publicKey message =>
    (encryption_eq security publicKey message).symm⟩

/-- Serialized decryption reads only the first `n w` secret bits and the first `N²` ciphertext
bits, with missing bits read as `false`. -/
private theorem decryptSerialized_congr {n w : ℕ}
    {secret secret' ciphertext ciphertext' : List Bool}
    (hsecret : ∀ i < n * w, secret.getD i false = secret'.getD i false)
    (hciphertext : ∀ i < (n + 1) * w * ((n + 1) * w),
      ciphertext.getD i false = ciphertext'.getD i false) :
    GSW.decryptSerialized n w secret ciphertext =
      GSW.decryptSerialized n w secret' ciphertext' := by
  have hs : Cslib.Matrix.ofBinary 1 n w secret = Cslib.Matrix.ofBinary 1 n w secret' := by
    have h : BitString.ofList (1 * (n * w)) secret = BitString.ofList (1 * (n * w)) secret' := by
      funext i
      exact hsecret i (by have := i.2; omega)
    unfold Cslib.Matrix.ofBinary
    rw [h]
  have hc : GSW.decodeCiphertext n w ciphertext = GSW.decodeCiphertext n w ciphertext' := by
    have h : BitString.ofList ((n + 1) * (w * ((n + 1) * w))) ciphertext =
        BitString.ofList ((n + 1) * (w * ((n + 1) * w))) ciphertext' := by
      funext i
      exact hciphertext i (by have := i.2; rwa [Nat.mul_assoc])
    unfold GSW.decodeCiphertext
    rw [h]
  rw [GSW.decryptSerialized_eq, GSW.decryptSerialized_eq, GSW.decodeSecret, GSW.decodeSecret,
    hs, hc]

/-- **The decryption circuit computes `decryptionWord` on every word.** The circuit reads the
word padded with `false` or truncated to its input width, and GSW decryption ignores the bits
beyond its widths. -/
theorem eval_decryptionCircuit (security : ℕ) (word : List Bool) :
    (GSW.DepthParameters.decryptionCircuits.circuit security).eval Circuits.Boolean.interpretation
      (BitString.ofList (GSW.DepthParameters.secretWidth security +
        GSW.DepthParameters.ciphertextWidth security) word) 0 =
      decryptionWord security word := by
  have hsw : GSW.DepthParameters.secretWidth security = secretWidth security := rfl
  have hcw : GSW.DepthParameters.ciphertextWidth security =
      (dimension security + 1) * width security * ((dimension security + 1) * width security) :=
    rfl
  obtain ⟨full, hfull⟩ : ∃ full, full = List.ofFn (BitString.ofList
      (GSW.DepthParameters.secretWidth security + GSW.DepthParameters.ciphertextWidth security)
        word) := ⟨_, rfl⟩
  have hlength : full.length =
      GSW.DepthParameters.secretWidth security + GSW.DepthParameters.ciphertextWidth security := by
    rw [hfull, List.length_ofFn]
  have hget : ∀ i < GSW.DepthParameters.secretWidth security +
      GSW.DepthParameters.ciphertextWidth security, full[i]? = word[i]?.getD false := by
    intro i hi
    rw [List.getElem?_eq_getElem (by rw [hlength]; exact hi)]
    simp only [hfull, List.getElem_ofFn, BitString.ofList, List.getD_eq_getElem?_getD]
  have hsplit : BitString.ofList
      (GSW.DepthParameters.secretWidth security + GSW.DepthParameters.ciphertextWidth security)
        word = BitString.ofList
      (GSW.DepthParameters.secretWidth security + GSW.DepthParameters.ciphertextWidth security)
        (full.take (GSW.DepthParameters.secretWidth security) ++
          full.drop (GSW.DepthParameters.secretWidth security)) := by
    rw [List.take_append_drop, hfull, BitString.ofList_ofFn]
  rw [hsplit, GSW.DepthParameters.decryptionCircuits.correct security _ _
    (by rw [List.length_take, hlength]; omega) (by rw [List.length_drop, hlength]; omega)]
  change GSW.decryptSerialized (dimension security) (width security) _ _ =
    decryption security (word.take (secretWidth security)) (word.drop (secretWidth security))
  rw [decryptSerialized_congr (secret' := word.take (secretWidth security))
    (ciphertext' := word.drop (secretWidth security))]
  · have hw : width security ≠ 0 := (GSW.DepthParameters.width_pos security).ne'
    unfold GSW.decryptSerialized
    simp only [hw, ite_false]
    rfl
  · intro i hi
    have hi' : i < secretWidth security := hi
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (show i < GSW.DepthParameters.secretWidth security from hi'),
      List.getElem?_take_of_lt hi', hget i (by rw [hsw]; omega), Option.getD_some]
  · intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [hget _ (by rw [hsw, hcw]; omega), Option.getD_some]
    rfl

/-! ### The two assumptions -/

private theorem uniformMatrixWord_eq (m k w : ℕ) :
    uniformMatrixWord m (k + 1) w =
      LWE.uniformEnsemble (fun _ => k) (fun _ => m) (fun _ => w) 0 := by
  unfold uniformMatrixWord LWE.uniformEnsemble
  congr 1
  funext A
  simpa only [← BitString.lowBits_eq_ofFn, BitString.lowBits, lowBits] using
    (Matrix.toBinary_eq A).symm

private theorem uniformPublic_eq (security : ℕ) :
    uniformPublic security = LWE.uniformEnsemble dimension samples width security :=
  uniformMatrixWord_eq _ _ _

/-- The elementary decision-LWE assumption is the library's, for this family. -/
theorem decisionLWE_iff : DecisionLWE ↔
    Crypto.DecisionLWE GSW.Parameters.dimension GSW.DepthParameters.samples
      GSW.DepthParameters.width
      (fun security => GSW.noiseLaw (GSW.DepthParameters.width security)
        (GSW.Parameters.noise security)) := by
  change Randomized.Indistinguishable _ _ ↔ _
  rw [CryptographyBridge.indistinguishable_iff]
  change ComputationallyIndistinguishable _ _ ↔ ComputationallyIndistinguishable _ _
  have hreal : (fun security => (keyGeneration security).map Prod.fst) =
      LWE.realEnsemble dimension samples width
        (fun security => GSW.noiseLaw (width security) (dimension security)) := by
    funext security
    rw [keyGeneration_eq, GSW.eval_keyGenSerialized_publicWord]
  rw [hreal, show uniformPublic = LWE.uniformEnsemble dimension samples width
    from funext uniformPublic_eq]
  rfl

private theorem mapM_eval {α β : Type} (program : α → ProbComp β) (inputs : List α) :
    inputs.mapM (fun a => ProbComp.eval (program a)) = ProbComp.eval (inputs.mapM program) := by
  induction inputs with
  | nil => simp only [List.mapM_nil, ProbComp.eval_pure, PMF.monad_pure_eq_pure]
  | cons a inputs ih =>
    simp only [List.mapM_cons, ProbComp.eval_bind, ProbComp.eval_pure, ih,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]

private theorem encryption_fun_eq (security : ℕ) : encryption security =
    fun publicKey message =>
      ProbComp.eval (GSW.DepthParameters.scheme.encrypt security publicKey message) := by
  funext publicKey message
  exact encryption_eq security publicKey message

private theorem selfEncryption_eq (real : Bool) (security : ℕ) :
    selfEncryption real security =
      (ProbComp.eval (Encryption.circularPublicKey GSW.DepthParameters.scheme.keyGen
        GSW.DepthParameters.scheme.encrypt real security)).map
        Encryption.encCircularPublicKey := by
  simp only [selfEncryption, Encryption.circularPublicKey, encryption_fun_eq, mapM_eval,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map, (base_scheme security).1]
  rfl

/-- The elementary circular-security assumption is the library's, for GSW at this family. -/
theorem circularSecure_iff : CircularSecure ↔
    Encryption.CircularSecure GSW.DepthParameters.scheme.keyGen
      GSW.DepthParameters.scheme.encrypt := by
  change Randomized.Indistinguishable _ _ ↔ _
  rw [CryptographyBridge.indistinguishable_iff]
  have h (real : Bool) : selfEncryption real = fun security =>
      (ProbComp.eval (Encryption.circularPublicKey GSW.DepthParameters.scheme.keyGen
        GSW.DepthParameters.scheme.encrypt real security)).map
        Encryption.encCircularPublicKey :=
    funext (selfEncryption_eq real)
  rw [h true, h false]
  rfl

/-! ### The library's bootstrapped schemes use the explicit algorithms -/

/-- The library's leveled scheme, for every budget, encrypts with a tag and GSW encryption under
the chain's first public key, and decrypts with the tag-selected endpoint secret. -/
theorem leveled_encryptsAndDecrypts (budget : ℕ → ℕ) :
    EncryptsAndDecrypts (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget)
      (leveledEncryption Turing.MultiTapeTM.unframe)
      (leveledDecryption Turing.MultiTapeTM.unframe Turing.MultiTapeTM.dropFrame) := by
  refine ⟨fun security publicKey bit => ?_, fun security secret ciphertext => ?_⟩
  · have hkey : (Leveled.publicKeyDecoder.decode publicKey).1.getD 0 [] =
        Turing.MultiTapeTM.unframe (Turing.MultiTapeTM.unframe publicKey) :=
      getD_frames _
    change ProbComp.eval (List.cons false <$> GSW.DepthParameters.scheme.encrypt security
      ((Leveled.publicKeyDecoder.decode publicKey).1.getD 0 []) bit) = _
    rw [ProbComp.eval_map, (base_scheme security).2, hkey]
    rfl
  · have hkey : Leveled.secretKeyDecoder.decode secret =
        (Turing.MultiTapeTM.unframe secret, Turing.MultiTapeTM.dropFrame secret) := rfl
    simp only [Leveled.scheme, Leveled.decrypt, hkey, eval_decryptionCircuit]
    rfl

/-- The library's leveled key generation, for every budget, publishes the chain's first public key
and keeps its secret as the first endpoint; that key pair has GSW's key-generation law. The rest
of the chain is sampled after it and is projected away. -/
theorem leveled_keyGen (budget : ℕ → ℕ) (security : ℕ) :
    (ProbComp.eval ((Leveled.scheme GSW.DepthParameters.decryptionCircuits budget).keyGen
        security)).map (fun keys => (Turing.MultiTapeTM.unframe
          (Turing.MultiTapeTM.unframe keys.1), Turing.MultiTapeTM.unframe keys.2)) =
      keyGeneration security := by
  have hproj (first : List Bool × List Bool) (rest : List (List Bool × List Bool))
      (links : List (List (List Bool))) :
      (Turing.MultiTapeTM.unframe (Turing.MultiTapeTM.unframe
          (Leveled.keyPair (2 * budget security) (first :: rest) links).1),
        Turing.MultiTapeTM.unframe
          (Leveled.keyPair (2 * budget security) (first :: rest) links).2) = first := by
    simp only [Leveled.keyPair, Leveled.encPublicKey, Leveled.encSecretKey, encPair, encList,
      encBits, Function.Embedding.coeFn_mk, Function.Embedding.refl_apply, List.map_cons,
      List.flatMap_cons, Function.comp_apply, unframe_frame_append, List.getD_cons_zero]
  change (ProbComp.eval ((fun chain => Leveled.keyPair (2 * budget security) chain.1 chain.2) <$>
    GSW.DepthParameters.scheme.generateKeyChain security (2 * budget security))).map _ = _
  simp only [Scheme.generateKeyChain, Scheme.generateKeys, OracleComp.replicate_succ,
    ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.bind_bind,
    PMF.pure_map, PMF.bind_map, Function.comp_apply, hproj, PMF.bind_const, PMF.bind_pure,
    (base_scheme security).1]

/-- The library's fixed-key key generation is the self-loop key generation. -/
theorem fixedKey_keyGen (security : ℕ) :
    ProbComp.eval ((FixedKey.scheme GSW.DepthParameters.decryptionCircuits).keyGen security) =
      selfLoopKeyGeneration security := by
  simp only [FixedKey.scheme, FixedKey.keyGen, Scheme.encryptBits, selfLoopKeyGeneration,
    encryption_fun_eq, mapM_eval, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, (base_scheme security).1]
  rfl

/-- The library's fixed-key scheme encrypts with GSW under the first framed component of its
public key and decrypts with GSW on the concatenated key and ciphertext. -/
theorem fixedKey_encryptsAndDecrypts :
    EncryptsAndDecrypts (FixedKey.scheme GSW.DepthParameters.decryptionCircuits)
      (selfLoopEncryption Turing.MultiTapeTM.unframe) selfLoopDecryption := by
  refine ⟨fun security publicKey bit => ?_, fun security secret ciphertext => ?_⟩
  · change ProbComp.eval (GSW.DepthParameters.scheme.encrypt security
      (FixedKey.publicKeyDecoder.decode publicKey).1 bit) = _
    rw [(base_scheme security).2]
    rfl
  · simp only [FixedKey.scheme, FixedKey.decrypt, selfLoopDecryption, eval_decryptionCircuit]

/-! ### The claimed properties from the library's notions

Each lemma proves the direction the conclusions need: the library's notion implies the
elementary one. -/

theorem homomorphic_of_correct {S : Homomorphic.Scheme} (hS : S.Correct)
    {allowed : ℕ → (Σ k, Circuits.Circuit Circuits.Boolean.signature k 1) → Prop}
    (hallowed : ∀ security C, allowed security C → S.permitted security C) :
    Homomorphic S allowed := fun security keys hkeys =>
  ⟨hS.decrypt_encrypt security keys hkeys, fun C bits inputs hC hbits hinputs =>
    hS.decrypt_evaluate security keys hkeys C (hallowed security C hC) bits inputs hbits
      hinputs⟩

theorem fixedWidths_of_fixedWidth {S : Homomorphic.Scheme} {keyBits cipherBits : ℕ → ℕ}
    (hS : S.FixedWidth keyBits cipherBits)
    {allowed : ℕ → (Σ k, Circuits.Circuit Circuits.Boolean.signature k 1) → Prop}
    (hallowed : ∀ security C, allowed security C → S.permitted security C) :
    FixedWidths S allowed keyBits cipherBits := fun security keys hkeys =>
  ⟨hS.secret_length security keys hkeys, hS.encrypt_length security keys hkeys,
    fun C bits inputs hC hbits hinputs =>
      hS.evaluate_length security keys hkeys C (hallowed security C hC) bits inputs hbits
        hinputs⟩

theorem native_of {S : Homomorphic.Scheme}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) S.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => S.encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => S.decrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool)
    (hevaluate : IsPPTOn
      (encPair encUnary (encPair encBits (encPair (Circuits.Boolean.encCircuit 1)
        (encList encBits))))
      encBits (fun p => S.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Native S :=
  ⟨CryptographyBridge.strictPPT_iff.mpr ⟨S.keyGen, hkeyGen, fun _ => rfl⟩,
    CryptographyBridge.strictPPT_iff.mpr ⟨_, hencrypt, fun _ => rfl⟩, hdecrypt,
    CryptographyBridge.strictPPT_iff.mpr ⟨_, hevaluate, fun _ => rfl⟩⟩

theorem nativeInDepth_of {E : ℕ → Homomorphic.Scheme}
    (hkeyGen : IsPPTOn (encPair encUnary encUnary) (encPair encBits encBits)
      (fun p : ℕ × ℕ => (E p.2).keyGen p.1))
    (hencrypt : IsPPTOn
      (encPair encUnary (encPair encUnary (encPair encBits encBool))) encBits
      (fun p => (E p.2.1).encrypt p.1 p.2.2.1 p.2.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × ℕ × List Bool × List Bool => (E p.2.1).decrypt p.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encUnary (encPair encBits encBits))) encBool)
    (hevaluate : IsPPTOn
      (encPair encUnary (encPair encUnary
        (encPair encBits (encPair (Circuits.Boolean.encCircuit 1)
          (encList encBits)))))
      encBits (fun p => (E p.2.1).evaluate p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    NativeInDepth E :=
  ⟨CryptographyBridge.strictPPT_iff.mpr ⟨_, hkeyGen, fun _ => rfl⟩,
    CryptographyBridge.strictPPT_iff.mpr ⟨_, hencrypt, fun _ => rfl⟩, hdecrypt,
    CryptographyBridge.strictPPT_iff.mpr ⟨_, hevaluate, fun _ => rfl⟩⟩

theorem chosenMessageSecure_of_indCPA {S : Homomorphic.Scheme}
    (hS : Encryption.INDCPA S.keyGen S.encrypt) : ChosenMessageSecure S := by
  intro choose guess hchoose hguess
  obtain ⟨chooseProgram, hchooseProgram, hchooseLaw⟩ :=
    CryptographyBridge.strictPPT_iff.mp hchoose
  obtain ⟨guessProgram, hguessProgram, hguessLaw⟩ :=
    CryptographyBridge.strictPPT_iff.mp hguess
  let adversary : Encryption.Adversary :=
    ⟨fun security pk => chooseProgram (security, pk),
      fun security state ciphertext => guessProgram (security, state, ciphertext)⟩
  have h := hS adversary ⟨hchooseProgram, hguessProgram⟩
  simpa only [Encryption.game, Encryption.gameOn, ↓reduceIte,
    adversary, ProbComp.eval_bind, hchooseLaw, hguessLaw,
    chosenMessageGame, PMF.monad_bind_eq_bind, Randomized.Negligible, Crypto.Negligible,
    Asymptotics.SuperpolynomialDecay, Crypto.Game.advantage, Crypto.Game.succProbability,
    Randomized.probability] using h

/-! ### Provenance: the library's schemes are the witnesses -/

/-- **The library's leveled scheme witnesses `leveled`.** The depth-indexed family
`fun d => Leveled.scheme GSW.DepthParameters.decryptionCircuits (fun _ => d)` satisfies
`NativeInDepth` (one joint polynomial in `(security, d)`), and for every budget computable in
unary polynomial time, `Leveled.scheme GSW.DepthParameters.decryptionCircuits budget` substitutes
`d = budget security` into that family and has every property that the abstract's `leveled`
asserts, with one decryption circuit family chosen before the depth and budget. -/
theorem leveled_witness (hLWE : DecisionLWE) :
    ∃ circuit : ∀ security, Circuits.Circuit Circuits.Boolean.signature
        ((3 * secretWidth security + 1) + (ciphertextWidth security + 1)) 1,
      Computation.PolyTime
        (fun security =>
          (⟨(3 * secretWidth security + 1) + (ciphertextWidth security + 1), circuit security⟩ :
            Σ k, Circuits.Circuit Circuits.Boolean.signature k 1))
        Encoding.encUnary (Circuits.Boolean.encCircuit 1) ∧
      PolynomiallyBounded (fun security => (circuit security).size) ∧
      PolynomiallyBounded (fun security => 3 * secretWidth security + 1) ∧
      PolynomiallyBounded (fun security => ciphertextWidth security + 1) ∧
      NativeInDepth
        (fun d => Leveled.scheme GSW.DepthParameters.decryptionCircuits (fun _ => d)) ∧
      (∀ d : ℕ,
        (∀ security, (ProbComp.eval
          ((Leveled.scheme GSW.DepthParameters.decryptionCircuits (fun _ => d)).keyGen
            security)).map
            (fun keys => (Turing.MultiTapeTM.unframe (Turing.MultiTapeTM.unframe keys.1),
              Turing.MultiTapeTM.unframe keys.2)) = keyGeneration security) ∧
        EncryptsAndDecrypts
          (Leveled.scheme GSW.DepthParameters.decryptionCircuits (fun _ => d))
          (leveledEncryption Turing.MultiTapeTM.unframe)
          (leveledDecryption Turing.MultiTapeTM.unframe Turing.MultiTapeTM.dropFrame) ∧
        DecryptsWith
          (Leveled.scheme GSW.DepthParameters.decryptionCircuits (fun _ => d))
          (fun security => 3 * secretWidth security + 1)
          (fun security => ciphertextWidth security + 1) circuit ∧
        Homomorphic
          (Leveled.scheme GSW.DepthParameters.decryptionCircuits (fun _ => d))
          (fun _ C => C.2.depth ≤ d) ∧
        FixedWidths
          (Leveled.scheme GSW.DepthParameters.decryptionCircuits (fun _ => d))
          (fun _ C => C.2.depth ≤ d)
          (fun security => 3 * secretWidth security + 1)
          (fun security => ciphertextWidth security + 1) ∧
        Native (Leveled.scheme GSW.DepthParameters.decryptionCircuits (fun _ => d)) ∧
        ChosenMessageSecure
          (Leveled.scheme GSW.DepthParameters.decryptionCircuits (fun _ => d))) ∧
      ∀ budget : ℕ → ℕ, Computation.PolyTime budget Encoding.encUnary Encoding.encUnary →
        (∀ security,
          (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget).keyGen security =
            (Leveled.scheme GSW.DepthParameters.decryptionCircuits
              (fun _ => budget security)).keyGen security ∧
          (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget).evaluate security =
            (Leveled.scheme GSW.DepthParameters.decryptionCircuits
              (fun _ => budget security)).evaluate security) ∧
        (∀ security, (ProbComp.eval
          ((Leveled.scheme GSW.DepthParameters.decryptionCircuits budget).keyGen security)).map
            (fun keys => (Turing.MultiTapeTM.unframe (Turing.MultiTapeTM.unframe keys.1),
              Turing.MultiTapeTM.unframe keys.2)) = keyGeneration security) ∧
        EncryptsAndDecrypts (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget)
          (leveledEncryption Turing.MultiTapeTM.unframe)
          (leveledDecryption Turing.MultiTapeTM.unframe Turing.MultiTapeTM.dropFrame) ∧
        DecryptsWith (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget)
          (fun security => 3 * secretWidth security + 1)
          (fun security => ciphertextWidth security + 1) circuit ∧
        Homomorphic (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget)
          (fun security C => C.2.depth ≤ budget security) ∧
        FixedWidths (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget)
          (fun security C => C.2.depth ≤ budget security)
          (fun security => 3 * secretWidth security + 1)
          (fun security => ciphertextWidth security + 1) ∧
        Native (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget) ∧
        ChosenMessageSecure (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget) := by
  let D := GSW.DepthParameters.decryptionCircuits
  have hD := GSW.DepthParameters.computableInPolyTime_decryptionCircuits
  have hkeyGen := GSW.DepthParameters.isPPTOn_keyGen
  have hencrypt := GSW.DepthParameters.isPPTOn_encrypt
  have hevaluate := GSW.DepthParameters.isPPTOn_evaluate
  obtain ⟨circuits, hgen, hsize, hcircuits⟩ := GSW.DepthParameters.exists_leveled_decrypt_circuits
  obtain ⟨hsecret, hciphertext, hkgJoint, hencJoint, hdecJoint, hevalJoint⟩ :=
    Leveled.schemeFamily_spec D hkeyGen hencrypt hevaluate
      GSW.DepthParameters.computableInPolyTime_decryptionCircuits
  have hforBudget (budget : ℕ → ℕ) (hb : ComputableInPolyTime budget encUnary encUnary) :
      (∀ security, (ProbComp.eval
        ((Leveled.scheme D budget).keyGen security)).map
          (fun keys => (Turing.MultiTapeTM.unframe (Turing.MultiTapeTM.unframe keys.1),
            Turing.MultiTapeTM.unframe keys.2)) = keyGeneration security) ∧
      EncryptsAndDecrypts (Leveled.scheme D budget)
        (leveledEncryption Turing.MultiTapeTM.unframe)
        (leveledDecryption Turing.MultiTapeTM.unframe Turing.MultiTapeTM.dropFrame) ∧
      DecryptsWith (Leveled.scheme D budget)
        (fun security => 3 * secretWidth security + 1)
        (fun security => ciphertextWidth security + 1) circuits ∧
      Homomorphic (Leveled.scheme D budget)
        (fun security C => C.2.depth ≤ budget security) ∧
      FixedWidths (Leveled.scheme D budget)
        (fun security C => C.2.depth ≤ budget security)
        (fun security => 3 * secretWidth security + 1)
        (fun security => ciphertextWidth security + 1) ∧
      Native (Leveled.scheme D budget) ∧
      ChosenMessageSecure (Leveled.scheme D budget) := by
    obtain ⟨hcorrect, hwidth, -, -, hsecure⟩ :=
      Leveled.correct_fixedWidth_indCPA D GSW.DepthParameters.correct
        GSW.DepthParameters.fixedWidth GSW.DepthParameters.bootstrappable
        (GSW.DepthParameters.indCPA_scheme (decisionLWE_iff.mp hLWE)) hkeyGen hencrypt hD hb
    exact ⟨leveled_keyGen budget, leveled_encryptsAndDecrypts budget,
      fun security => hcircuits budget security,
      homomorphic_of_correct hcorrect fun _ _ h => h,
      fixedWidths_of_fixedWidth hwidth fun _ _ h => h,
      native_of (Leveled.isPPTOn_scheme_keyGen hkeyGen hencrypt D budget hb)
        (Leveled.isPPTOn_scheme_encrypt hencrypt D budget)
        (Leveled.computableInPolyTime_scheme_decrypt D hD budget)
        (Leveled.isPPTOn_scheme_evaluate hencrypt D hD hevaluate budget hb),
      chosenMessageSecure_of_indCPA hsecure⟩
  refine ⟨circuits, CryptographyBridge.polyTime_iff.mpr hgen.tidy, hsize, hsecret, hciphertext,
    nativeInDepth_of hkgJoint hencJoint hdecJoint hevalJoint,
    fun d => hforBudget (fun _ => d) (by fun_prop),
    fun budget hbudget =>
      ⟨fun _ => ⟨rfl, rfl⟩,
        hforBudget budget (.of_tidy (CryptographyBridge.polyTime_iff.mp hbudget))⟩⟩

/-- **The library's fixed-key scheme witnesses `fullyHomomorphic`**, with GSW's own decryption
circuits `GSW.DepthParameters.decryptionCircuits.circuit`. -/
theorem fullyHomomorphic_witness (hLWE : DecisionLWE) (hcircular : CircularSecure) :
    Computation.PolyTime
        (fun security =>
          (⟨secretWidth security + ciphertextWidth security,
              GSW.DepthParameters.decryptionCircuits.circuit security⟩ :
            Σ k, Circuits.Circuit Circuits.Boolean.signature k 1))
        Encoding.encUnary (Circuits.Boolean.encCircuit 1) ∧
      PolynomiallyBounded
        (fun security => (GSW.DepthParameters.decryptionCircuits.circuit security).size) ∧
      PolynomiallyBounded secretWidth ∧ PolynomiallyBounded ciphertextWidth ∧
      (∀ security, ProbComp.eval
        ((FixedKey.scheme GSW.DepthParameters.decryptionCircuits).keyGen security) =
          selfLoopKeyGeneration security) ∧
      EncryptsAndDecrypts (FixedKey.scheme GSW.DepthParameters.decryptionCircuits)
        (selfLoopEncryption Turing.MultiTapeTM.unframe) selfLoopDecryption ∧
      DecryptsWith (FixedKey.scheme GSW.DepthParameters.decryptionCircuits) secretWidth
        ciphertextWidth GSW.DepthParameters.decryptionCircuits.circuit ∧
      Homomorphic (FixedKey.scheme GSW.DepthParameters.decryptionCircuits) (fun _ _ => True) ∧
      FixedWidths (FixedKey.scheme GSW.DepthParameters.decryptionCircuits) (fun _ _ => True)
        secretWidth ciphertextWidth ∧
      Native (FixedKey.scheme GSW.DepthParameters.decryptionCircuits) ∧
      ChosenMessageSecure (FixedKey.scheme GSW.DepthParameters.decryptionCircuits) := by
  obtain ⟨hcorrect, hpermitted, hwidth, hsecret, hciphertext, hsize, hkeyGen, hencrypt,
      hdecrypt, hevaluate, hsecure⟩ :=
    GSW.DepthParameters.fullyHomomorphic_of_decisionLWE_of_circularSecure
      (decisionLWE_iff.mp hLWE) (circularSecure_iff.mp hcircular)
  exact ⟨CryptographyBridge.polyTime_iff.mpr
      GSW.DepthParameters.computableInPolyTime_decryptionCircuits.tidy,
    hsize, hsecret, hciphertext, fixedKey_keyGen, fixedKey_encryptsAndDecrypts,
    (FixedKey.decryptionCircuits GSW.DepthParameters.decryptionCircuits).correct,
    homomorphic_of_correct hcorrect fun security C _ => hpermitted security C,
    fixedWidths_of_fixedWidth hwidth fun security C _ => hpermitted security C,
    native_of hkeyGen hencrypt hdecrypt hevaluate, chosenMessageSecure_of_indCPA hsecure⟩

/-! ### The headline theorems

The decoders are those of the abstract; they agree with the library's on every word. -/

theorem leveled {unframe dropFrame : List Bool → List Bool}
    (hunframe : ∀ word, unframe word = Turing.MultiTapeTM.unframe word)
    (hdropFrame : ∀ word, dropFrame word = Turing.MultiTapeTM.dropFrame word)
    (hLWE : DecisionLWE) :
    ∃ (circuit : ∀ security, Circuits.Circuit Circuits.Boolean.signature
        ((3 * secretWidth security + 1) + (ciphertextWidth security + 1)) 1)
      (E : ℕ → Homomorphic.Scheme),
      Computation.PolyTime
        (fun security =>
          (⟨(3 * secretWidth security + 1) + (ciphertextWidth security + 1), circuit security⟩ :
            Σ k, Circuits.Circuit Circuits.Boolean.signature k 1))
        Encoding.encUnary (Circuits.Boolean.encCircuit 1) ∧
      PolynomiallyBounded (fun security => (circuit security).size) ∧
      PolynomiallyBounded (fun security => 3 * secretWidth security + 1) ∧
      PolynomiallyBounded (fun security => ciphertextWidth security + 1) ∧
      NativeInDepth E ∧
      (∀ d : ℕ,
        (∀ security, (ProbComp.eval ((E d).keyGen security)).map
          (fun keys => (unframe (unframe keys.1), unframe keys.2)) = keyGeneration security) ∧
        EncryptsAndDecrypts (E d) (leveledEncryption unframe)
          (leveledDecryption unframe dropFrame) ∧
        DecryptsWith (E d) (fun security => 3 * secretWidth security + 1)
          (fun security => ciphertextWidth security + 1) circuit ∧
        Homomorphic (E d) (fun _ C => C.2.depth ≤ d) ∧
        FixedWidths (E d) (fun _ C => C.2.depth ≤ d)
          (fun security => 3 * secretWidth security + 1)
          (fun security => ciphertextWidth security + 1) ∧
        Native (E d) ∧ ChosenMessageSecure (E d)) ∧
      ∀ budget : ℕ → ℕ, Computation.PolyTime budget Encoding.encUnary Encoding.encUnary →
        ∃ S : Homomorphic.Scheme,
          (∀ security, S.keyGen security = (E (budget security)).keyGen security ∧
            S.evaluate security = (E (budget security)).evaluate security) ∧
          (∀ security, (ProbComp.eval (S.keyGen security)).map
            (fun keys => (unframe (unframe keys.1), unframe keys.2)) = keyGeneration security) ∧
          EncryptsAndDecrypts S (leveledEncryption unframe)
            (leveledDecryption unframe dropFrame) ∧
          DecryptsWith S (fun security => 3 * secretWidth security + 1)
            (fun security => ciphertextWidth security + 1) circuit ∧
          Homomorphic S (fun security C => C.2.depth ≤ budget security) ∧
          FixedWidths S (fun security C => C.2.depth ≤ budget security)
            (fun security => 3 * secretWidth security + 1)
            (fun security => ciphertextWidth security + 1) ∧
          Native S ∧ ChosenMessageSecure S := by
  obtain rfl : unframe = Turing.MultiTapeTM.unframe := funext hunframe
  obtain rfl : dropFrame = Turing.MultiTapeTM.dropFrame := funext hdropFrame
  obtain ⟨circuit, hgen, hsize, hsecret, hciphertext, hjoint, hd, hbudget⟩ := leveled_witness hLWE
  exact ⟨circuit, _, hgen, hsize, hsecret, hciphertext, hjoint, hd, fun budget hb =>
    ⟨_, hbudget budget hb⟩⟩

theorem fullyHomomorphic {unframe : List Bool → List Bool}
    (hunframe : ∀ word, unframe word = Turing.MultiTapeTM.unframe word)
    (hLWE : DecisionLWE) (hcircular : CircularSecure) :
    ∃ circuit : ∀ security, Circuits.Circuit Circuits.Boolean.signature
        (secretWidth security + ciphertextWidth security) 1,
      Computation.PolyTime
        (fun security =>
          (⟨secretWidth security + ciphertextWidth security, circuit security⟩ :
            Σ k, Circuits.Circuit Circuits.Boolean.signature k 1))
        Encoding.encUnary (Circuits.Boolean.encCircuit 1) ∧
      PolynomiallyBounded (fun security => (circuit security).size) ∧
      PolynomiallyBounded secretWidth ∧ PolynomiallyBounded ciphertextWidth ∧
      ∃ S : Homomorphic.Scheme,
        (∀ security, ProbComp.eval (S.keyGen security) = selfLoopKeyGeneration security) ∧
        EncryptsAndDecrypts S (selfLoopEncryption unframe) selfLoopDecryption ∧
        DecryptsWith S secretWidth ciphertextWidth circuit ∧
        Homomorphic S (fun _ _ => True) ∧
        FixedWidths S (fun _ _ => True) secretWidth ciphertextWidth ∧
        Native S ∧ ChosenMessageSecure S := by
  obtain rfl : unframe = Turing.MultiTapeTM.unframe := funext hunframe
  obtain ⟨hgen, hsize, hsecret, hciphertext, h⟩ := fullyHomomorphic_witness hLWE hcircular
  exact ⟨_, hgen, hsize, hsecret, hciphertext, _, h⟩

end ComplexityTests.Abstracts.GSWFHEBridge
