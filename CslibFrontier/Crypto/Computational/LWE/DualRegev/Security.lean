/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.PublicKeyReplacement
public import CslibFrontier.Crypto.Computational.LWE.DualRegev
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import Cslib.Probability.StatisticalDistance
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PPT

/-!
# Generated-key dual-Regev IND-CPA security from decision LWE

Serializes `DualRegev` public keys `(A, u)` as the `(m + 1) × n` row-major matrix `[u; A]` and
ciphertexts `(b, c₀)` as the `(m + 1)`-entry row vector `(c₀, b)` modulo `2 ^ w`. This embeds
an `(m + 1)`-sample `DecisionLWE` matrix `M = [B * s + e | B]` directly into a challenge pair
`(pk, c)`: columns `1..n` of `M` supply `(u; A)` and column `0` shifted at coordinate `0` by
`μ * 2 ^ (w - 1)` supplies `(c₀, b)`.

Under `DecisionLWE` with `m + 1` samples and error distribution `LWE.noiseLaw w η`, replacing
the generated public key `(A, eᵀ A)` by a uniform `(A, u)` via `DualRegev.dist_keyGen_uniform_le`
costs at most `sqrt(2 ^ (w * n) / 2 ^ m)` and replacing `(c₀, b)` by uniform costs at most
twice the `DecisionLWE` distinguishing advantage (`DualRegev.advantage_game_le`,
`DualRegev.indCPA_of_decisionLWE`).

## Main definitions

* `DualRegev.serializePublicKey`, `DualRegev.decodePublicKey`: row-major public-key bit codecs.
* `DualRegev.serializeCiphertext`, `DualRegev.decodeCiphertext`: fixed-width ciphertext codecs.
* `DualRegev.SerializedKeyInputs`, `DualRegev.encSerializedKeyInputs`,
  `DualRegev.SerializedEncCoins`, `DualRegev.encSerializedEncCoins`: serialized key-input and
  encryption-coin structures with `enc_structure` encodings.
* `DualRegev.keyGenSerialized`, `DualRegev.encryptSerialized`: strict-PPT bit-word algorithms.
* `DualRegev.lweDistinguisher`: uniform hidden-bit `DecisionLWE` reduction with `m + 1` samples.
* `DualRegev.hidingError`: leftover-hash term `sqrt(2 ^ (w * n) / 2 ^ m)`.

## Main results

* `DualRegev.decodePublicKey_serializePublicKey`, `DualRegev.decodeCiphertext_serializeCiphertext`:
  exact roundtrips for all dimensions and widths.
* `DualRegev.eval_keyGenSerialized_fst`, `DualRegev.eval_encryptSerialized`,
  `DualRegev.eval_encryptSerialized_serializePublicKey`: exact distributional bridges.
* `DualRegev.isPPTOn_keyGenSerialized`, `DualRegev.isPPTOn_encryptSerialized`,
  `DualRegev.isPPT_lweDistinguisher`: uniform strict PPT certificates.
* `DualRegev.advantage_game_le`, `DualRegev.indCPA_of_decisionLWE`: concrete bound and IND-CPA
  security under `DecisionLWE` with `m + 1` samples and entropy margin `w * n + 2 * k ≤ m`.

## References

* [C. Gentry, C. Peikert and V. Vaikuntanathan, *Trapdoors for Hard Lattices and New Cryptographic
  Constructions*, Section 7.1][GentryPeikertVaikuntanathan2008]
* [C. Peikert, *A Decade of Lattice Cryptography*, Section 5.2.2][Peikert2016]
-/

@[expose] public section

namespace Cslib.Crypto.DualRegev

open ProbComp Probability BitString Turing.MultiTapeTM
open scoped BigOperators _root_.Matrix NNReal Cslib.Probability.PMF

/-! ### Serialization and total decoding -/

/-- Canonical public keys stack the syndrome row `u` ahead of the `m` rows of `A`, encoded as an
`(m + 1) × n` binary matrix modulo `2 ^ w`. -/
def serializePublicKey {n m w : ℕ} (pk : PublicKey n m w) : List Bool :=
  Cslib.Matrix.toBinary
    (_root_.Matrix.of (Fin.cons (α := fun _ => Fin n → ZMod (2 ^ w)) pk.2 (fun r => pk.1 r)))

/-- Total public-key decoder reading the first `n` entries as `u` and the next `m × n` entries as
`A`, padding absent bits with zero. -/
def decodePublicKey (n m w : ℕ) (word : List Bool) : PublicKey n m w :=
  let M := Cslib.Matrix.ofBinary (m + 1) n w word
  (_root_.Matrix.of (fun i j => M i.succ j), fun j => M 0 j)

/-- Canonical public-key words roundtrip through `decodePublicKey`. -/
@[simp] theorem decodePublicKey_serializePublicKey {n m w : ℕ} (pk : PublicKey n m w) :
    decodePublicKey n m w (serializePublicKey pk) = pk := by
  unfold decodePublicKey serializePublicKey
  dsimp only
  rw [Cslib.Matrix.ofBinary_toBinary]
  ext i j <;> simp

/-- A serialized public key has exact bit length `(m + 1) * n * w`. -/
@[simp] theorem length_serializePublicKey {n m w : ℕ} (pk : PublicKey n m w) :
    (serializePublicKey pk).length = (m + 1) * n * w :=
  Cslib.Matrix.length_toBinary _

/-- Canonical ciphertexts write `c₀` followed by the `m` entries of `b` modulo `2 ^ w`. -/
def serializeCiphertext {m w : ℕ} (c : Ciphertext m w) : List Bool :=
  Cslib.Matrix.toBinary (_root_.Matrix.of fun _ : Fin 1 => Fin.cons c.2 c.1)

/-- Total ciphertext decoder reading `c₀` from index `0` and `b` from indices `1..m`. -/
def decodeCiphertext (m w : ℕ) (word : List Bool) : Ciphertext m w :=
  let row := Cslib.Matrix.ofBinary 1 (m + 1) w word 0
  (fun i => row i.succ, row 0)

/-- Canonical ciphertext words roundtrip through `decodeCiphertext`. -/
@[simp] theorem decodeCiphertext_serializeCiphertext {m w : ℕ} (c : Ciphertext m w) :
    decodeCiphertext m w (serializeCiphertext c) = c := by
  ext i
  · simp [decodeCiphertext, serializeCiphertext, Cslib.Matrix.ofBinary_toBinary]
  · simp [decodeCiphertext, serializeCiphertext, Cslib.Matrix.ofBinary_toBinary]

/-- A serialized ciphertext has exact bit length `(m + 1) * w`. -/
@[simp] theorem length_serializeCiphertext {m w : ℕ} (c : Ciphertext m w) :
    (serializeCiphertext c).length = (m + 1) * w := by
  dsimp only [serializeCiphertext]
  rw [Cslib.Matrix.length_toBinary, Nat.one_mul]

/-! ### Serialized key generation -/

/-- Random inputs for serialized dual-Regev key generation: `m` rows of `n` residues and `m`
secret bits. -/
@[ext]
structure SerializedKeyInputs where
  /-- List of public-matrix rows (`m` rows of `n` residue representatives). -/
  publicPart : List (List ℕ)
  /-- List of binary secret bits. -/
  bits : List Bool
  deriving DecidableEq, Repr

/-- Framing encoding for serialized key-generation inputs. -/
enc_structure encSerializedKeyInputs : SerializedKeyInputs where
  publicPart : (encList (encList encNat)), bits : encBits

attribute [fun_prop] encSerializedKeyInputs_publicPart_polyTime
  encSerializedKeyInputs_bits_polyTime encSerializedKeyInputs_mk_polyTime

/-- Independently sample the `m × n` matrix entries and `m` binary secret bits. -/
noncomputable def sampleKeyInputsSerialized (n m w : ℕ) : ProbComp SerializedKeyInputs := do
  let publicPart ← OracleComp.replicate m (OracleComp.replicate n (sampleBinaryNat w))
  let bits ← OracleComp.replicate m (ProbComp.uniform Bool)
  return { publicPart, bits }

/-- Coordinate `j` of the syndrome `eᵀ A` modulo `2 ^ w`. -/
def syndromeEntry (m w : ℕ) (inputs : SerializedKeyInputs) (j : ℕ) : ℕ :=
  ((List.range m).map fun i =>
    if inputs.bits.getD i false then (inputs.publicPart.getD i []).getD j 0 else 0).sum % 2 ^ w

/-- Construct the canonical public-key word `[u; A]` from serialized key inputs. -/
def publicKeySerialized (n m w : ℕ) (inputs : SerializedKeyInputs) : List Bool :=
  (List.range n).flatMap (fun j => lowBits w (syndromeEntry m w inputs j)) ++
    (List.range m).flatMap fun i =>
      (List.range n).flatMap fun j =>
        lowBits w ((inputs.publicPart.getD i []).getD j 0 % 2 ^ w)

/-- Normalize the binary secret list to length `m`. -/
def secretSerialized (m : ℕ) (bits : List Bool) : List Bool :=
  (List.range m).map fun i => bits.getD i false

/-- Executable serialized dual-Regev key generation. -/
noncomputable def keyGenSerialized (n m w : ℕ) : ProbComp (List Bool × List Bool) := do
  let inputs ← sampleKeyInputsSerialized n m w
  return (publicKeySerialized n m w inputs, secretSerialized m inputs.bits)

private def decodeKeyInputs (n m w : ℕ) (inputs : SerializedKeyInputs) :
    _root_.Matrix (Fin m) (Fin n) (ZMod (2 ^ w)) × (Fin m → Bool) :=
  (fun i j => ((inputs.publicPart.getD i.val []).getD j.val 0 : ZMod (2 ^ w)),
    fun i => inputs.bits.getD i.val false)

private theorem syndromeEntry_eq {n m w : ℕ} (inputs : SerializedKeyInputs) (j : Fin n) :
    syndromeEntry m w inputs j.val =
      ((castVector w (fun i => ((decodeKeyInputs n m w inputs).2 i).toNat) ᵥ*
        (decodeKeyInputs n m w inputs).1) j).val := by
  unfold syndromeEntry decodeKeyInputs
  rw [List.map_range_eq_ofFn, List.sum_ofFn, ← ZMod.val_natCast]
  congr 1
  simp only [Nat.cast_sum, _root_.Matrix.vecMul, dotProduct, castVector]
  apply Finset.sum_congr rfl
  intro i _
  cases inputs.bits.getD i.val false <;> simp

private theorem publicKeySerialized_eq (n m w : ℕ) (inputs : SerializedKeyInputs) :
    publicKeySerialized n m w inputs = serializePublicKey
      (publicKeyOf (decodeKeyInputs n m w inputs).1
        (fun i => ((decodeKeyInputs n m w inputs).2 i).toNat)) := by
  unfold publicKeySerialized serializePublicKey publicKeyOf
  rw [Cslib.Matrix.toBinary_eq]
  simp only [List.ofFn_succ, List.flatten_cons, _root_.Matrix.of_apply, Fin.cons_zero,
    Fin.cons_succ]
  congr 1
  · simp only [List.flatMap_def, List.map_range_eq_ofFn, lowBits_eq_ofFn, syndromeEntry_eq]
  · simp only [List.flatMap_def, List.map_range_eq_ofFn, lowBits_eq_ofFn, decodeKeyInputs,
      ZMod.val_natCast]

/-- The public-key marginal of serialized key generation matches typed `DualRegev.keyGen`. -/
theorem eval_keyGenSerialized_fst (n m w : ℕ) :
    (ProbComp.eval (keyGenSerialized n m w)).map Prod.fst =
      (ProbComp.eval (keyGen n m w)).map (fun keys => serializePublicKey keys.1) := by
  have hrow := ProbComp.eval_replicateFin_map (LWE.eval_sampleBinaryNat_eq_map_val w) n
  have hmat := ProbComp.eval_replicateFin_map hrow m
  have hbits := ProbComp.eval_replicateFin_map
    (PMF.map_id (ProbComp.eval (ProbComp.uniform Bool))).symm m
  change _ = (ProbComp.eval (LWE.sampleMatrix m n w)).map _ at hmat
  rw [LWE.eval_sampleMatrix] at hmat
  have hlhs : (ProbComp.eval (keyGenSerialized n m w)).map Prod.fst =
      (PMF.uniformOfFintype (_root_.Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))).bind fun A =>
        (PMF.uniformOfFintype (Fin m → Bool)).bind fun bits =>
          PMF.pure (serializePublicKey (publicKeyOf A fun i => (bits i).toNat)) := by
    unfold keyGenSerialized sampleKeyInputsSerialized
    simp only [pmf_norm, hmat, hbits, ProbComp.eval_replicateFin, ProbComp.eval_uniform,
      PMF.pi_uniformOfFintype, _root_.Matrix, publicKeySerialized_eq]
    congr 1 with A : 1
    congr 1 with bits : 1
    refine congrArg PMF.pure (congrArg serializePublicKey ?_)
    congr 1
    · ext i j
      simp [decodeKeyInputs]
    · funext i
      simp [decodeKeyInputs]
  have hrhs : (ProbComp.eval (keyGen n m w)).map (fun keys => serializePublicKey keys.1) =
      (PMF.uniformOfFintype (_root_.Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))).bind fun A =>
        (PMF.uniformOfFintype (Fin m → Bool)).bind fun bits =>
          PMF.pure (serializePublicKey (publicKeyOf A fun i => (bits i).toNat)) := by
    unfold keyGen
    simp only [pmf_norm, LWE.eval_sampleMatrix, ProbComp.eval_replicateFin, ProbComp.eval_uniform,
      PMF.pi_uniformOfFintype]
  exact hlhs.trans hrhs.symm

/-! ### Serialized encryption -/

/-- Coins `(secret, error, scalarError)` for serialized dual-Regev encryption. -/
@[ext]
structure SerializedEncCoins where
  /-- List of binary secret vector representatives `s`. -/
  secret : List ℕ
  /-- List of signed integer vector errors `x`. -/
  error : List ℤ
  /-- Signed integer scalar error `x₀`. -/
  scalarError : ℤ
  deriving DecidableEq, Repr

/-- Framing encoding for serialized encryption coins. -/
enc_structure encSerializedEncCoins : SerializedEncCoins where
  secret : (encList encNat), error : (encList encIntBin), scalarError : encIntBin

attribute [fun_prop] encSerializedEncCoins_secret_polyTime
  encSerializedEncCoins_error_polyTime encSerializedEncCoins_scalarError_polyTime
  encSerializedEncCoins_mk_polyTime

/-- Independently sample the uniform secret `s`, error vector `x`, and scalar error `x₀`. -/
noncomputable def sampleEncCoinsSerialized (n m w η : ℕ) : ProbComp SerializedEncCoins := do
  let secret ← OracleComp.replicate n (sampleBinaryNat w)
  let error ← OracleComp.replicate m (sampleCenteredBinomial η)
  let scalarError ← sampleCenteredBinomial η
  return { secret, error, scalarError }

/-- Coordinate `idx` (`0` for `c₀`, `i + 1` for `b i`) of the ciphertext modulo `2 ^ w`. -/
def encryptEntry (n w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : SerializedEncCoins) (idx : ℕ) : ℕ :=
  (((((List.range n).map fun j =>
      Cslib.Matrix.binaryEntry n w publicWord idx j * coins.secret.getD j 0).sum : ℕ) +
    if idx = 0 then coins.scalarError + ((message.toNat : ℤ) * 2 ^ (w - 1))
    else coins.error.getD (idx - 1) 0 : ℤ) % (2 ^ w : ℤ)).toNat

/-- Compute all ciphertext bits from an arbitrary public word, message, and coins. -/
def encryptWithCoinsSerialized (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : SerializedEncCoins) : List Bool :=
  (List.range (m + 1)).flatMap fun idx => lowBits w (encryptEntry n w publicWord message coins idx)

/-- Executable serialized dual-Regev encryption. -/
noncomputable def encryptSerialized (n m w η : ℕ) (publicWord : List Bool) (message : Bool) :
    ProbComp (List Bool) := do
  let coins ← sampleEncCoinsSerialized n m w η
  return encryptWithCoinsSerialized n m w publicWord message coins

private def decodeEncCoins (n m w : ℕ) (coins : SerializedEncCoins) :
    (Fin n → ZMod (2 ^ w)) × (Fin m → ℤ) × ℤ :=
  (fun j => (coins.secret.getD j.val 0 : ZMod (2 ^ w)),
    fun i => coins.error.getD i.val 0, coins.scalarError)

private theorem encryptEntry_eq (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : SerializedEncCoins) (idx : Fin (m + 1)) :
    encryptEntry n w publicWord message coins idx.val =
      (Fin.cons (α := fun _ => ZMod (2 ^ w))
        (encryptWithCoins (decodePublicKey n m w publicWord) message
          (decodeEncCoins n m w coins).1 (decodeEncCoins n m w coins).2.1
          (decodeEncCoins n m w coins).2.2).2
        (encryptWithCoins (decodePublicKey n m w publicWord) message
          (decodeEncCoins n m w coins).1 (decodeEncCoins n m w coins).2.1
          (decodeEncCoins n m w coins).2.2).1 idx).val := by
  rcases coins with ⟨s, x, x₀⟩
  unfold encryptEntry decodeEncCoins encryptWithCoins decodePublicKey
  dsimp only
  rw [List.map_range_eq_ofFn, List.sum_ofFn]
  have hsum : ((∑ j : Fin n,
      Cslib.Matrix.binaryEntry n w publicWord idx.val j.val * s.getD j.val 0 : ℕ) :
        ZMod (2 ^ w)) =
      ∑ j : Fin n, (Cslib.Matrix.ofBinary (m + 1) n w publicWord idx j) *
        (s.getD j.val 0 : ZMod (2 ^ w)) := by
    simp only [Nat.cast_sum, Nat.cast_mul, Cslib.Matrix.ofBinary_apply]
  have hcast := congrArg Int.toNat (ZMod.val_intCast (n := 2 ^ w)
    (((∑ j : Fin n, Cslib.Matrix.binaryEntry n w publicWord idx.val j.val *
        s.getD j.val 0 : ℕ) : ℤ) +
      if idx.val = 0 then x₀ + (message.toNat : ℤ) * 2 ^ (w - 1)
      else x.getD (idx.val - 1) 0))
  rw [Int.toNat_natCast, Nat.cast_pow, Nat.cast_ofNat] at hcast
  rw [← hcast]
  congr 1
  simp only [Int.cast_add, Int.cast_natCast, hsum]
  refine Fin.cases ?_ ?_ idx
  · simp [dotProduct, LWE.encodeBit, add_assoc]
  · intro i
    simp [Matrix.mulVec, dotProduct, castVector]

private theorem encryptWithCoinsSerialized_eq (n m w : ℕ) (publicWord : List Bool)
    (message : Bool) (coins : SerializedEncCoins) :
    encryptWithCoinsSerialized n m w publicWord message coins = serializeCiphertext
      (encryptWithCoins (decodePublicKey n m w publicWord) message
        (decodeEncCoins n m w coins).1 (decodeEncCoins n m w coins).2.1
        (decodeEncCoins n m w coins).2.2) := by
  unfold encryptWithCoinsSerialized serializeCiphertext
  rw [Cslib.Matrix.toBinary_eq]
  simp only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.flatMap_def, List.map_range_eq_ofFn, encryptEntry_eq,
    lowBits_eq_ofFn, _root_.Matrix.of_apply]

/-- Serialized encryption has the typed encryption distribution of the decoded public key. -/
theorem eval_encryptSerialized (n m w η : ℕ) (publicWord : List Bool) (message : Bool) :
    ProbComp.eval (encryptSerialized n m w η publicWord message) =
      (ProbComp.eval (encrypt η (decodePublicKey n m w publicWord) message)).map
        serializeCiphertext := by
  have hs := ProbComp.eval_replicateFin_map (LWE.eval_sampleBinaryNat_eq_map_val w) n
  have hx := ProbComp.eval_replicateFin_map
    (PMF.map_id (ProbComp.eval (sampleCenteredBinomial η))).symm m
  change _ = (ProbComp.eval (LWE.sampleVector n w)).map _ at hs
  rw [LWE.eval_sampleVector] at hs
  simp only [pmf_norm, encryptSerialized, sampleEncCoinsSerialized, hs, hx, encrypt,
    LWE.eval_sampleVector, Function.comp_def, encryptWithCoinsSerialized_eq]
  congr 1 with s : 1
  congr 1 with x : 1
  congr 1 with x₀ : 1
  refine congrArg (PMF.pure ∘ serializeCiphertext) ?_
  congr 1 <;> ext k <;> simp [decodeEncCoins]

/-- On canonical public-key words, serialized encryption matches typed `DualRegev.encrypt`. -/
theorem eval_encryptSerialized_serializePublicKey {n m w η : ℕ} (pk : PublicKey n m w)
    (message : Bool) :
    ProbComp.eval (encryptSerialized n m w η (serializePublicKey pk) message) =
      (ProbComp.eval (encrypt η pk message)).map serializeCiphertext := by
  rw [eval_encryptSerialized, decodePublicKey_serializePublicKey]

/-! ### Uniform polynomial-time certificates for honest algorithms -/

section PolyTime

open Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool} {n m w η j idx : α → ℕ}

/-- Uniform strict PPT generation of serialized dual-Regev key inputs. -/
@[fun_prop]
theorem isPPTOn_sampleKeyInputsSerialized
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary) :
    IsPPTOn input encSerializedKeyInputs
      (fun a => sampleKeyInputsSerialized (n a) (m a) (w a)) := by
  have hrow := hw.sampleBinaryNat.replicate hn
  have hmat := hrow.replicate hm
  have hbits := (isPPTOn_uniform_bool input).replicate_bool hm
  unfold sampleKeyInputsSerialized
  ppt

/-- Compute one coordinate of the binary syndrome `eᵀ A` modulo `2 ^ w` in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_syndromeEntry {inputs : α → SerializedKeyInputs}
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hinputs : ComputableInPolyTime inputs input encSerializedKeyInputs)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a => syndromeEntry (m a) (w a) (inputs a) (j a)) input encNat := by
  unfold syndromeEntry
  have hterm : ComputableInPolyTime
      (fun p : α × ℕ =>
        if (inputs p.1).bits.getD p.2 false then
          ((inputs p.1).publicPart.getD p.2 []).getD (j p.1) 0
        else 0)
      (encPair input encUnary) encNat := by
    have hbit := (bitsGetD false).comp
      (((encSerializedKeyInputs_bits_polyTime hinputs).comp
        (fst input encUnary)).prod (snd input encUnary))
    apply hbit.ite'
    · have hrow := (listGetD (encA := encList encNat) []).comp
        (((encSerializedKeyInputs_publicPart_polyTime hinputs).comp
          (fst input encUnary)).prod (snd input encUnary))
      exact (listGetD (encA := encNat) 0).comp
        (hrow.prod (hj.comp (fst input encUnary)))
    · exact const 0
  have hsum := (show ComputableInPolyTime List.sum (encList encNat) encNat by fun_prop).comp
    (mapWithInput (f := fun a i =>
      if (inputs a).bits.getD i false then
        ((inputs a).publicPart.getD i []).getD (j a) 0
      else 0)
      (range.comp hm) hterm)
  exact binary_mod.comp (hsum.prod (binary_pow' (const 2) hw))

/-- Construct the serialized dual-Regev public-key word `[u; A]` in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_publicKeySerialized {inputs : α → SerializedKeyInputs}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hinputs : ComputableInPolyTime inputs input encSerializedKeyInputs) :
    ComputableInPolyTime (fun a => publicKeySerialized (n a) (m a) (w a) (inputs a))
      input encBits := by
  unfold publicKeySerialized
  apply bitsAppend
  · apply flatMapToBitsWithInput (range.comp hn)
    apply bitsLow (hw.comp (fst input encUnary))
    exact computableInPolyTime_syndromeEntry (hm.comp (fst input encUnary))
      (hw.comp (fst input encUnary)) (hinputs.comp (fst input encUnary)) (snd input encUnary)
  · apply flatMapToBitsWithInput (range.comp hm)
    apply flatMapToBitsWithInput (range.comp (hn.comp (fst input encUnary)))
    apply bitsLow (hw.comp ((fst input encUnary).comp (fst (encPair input encUnary) encUnary)))
    have hrow := (listGetD (encA := encList encNat) []).comp
      (((encSerializedKeyInputs_publicPart_polyTime hinputs).comp
        (fst input encUnary)).prod (snd input encUnary))
    have hentry := (listGetD (encA := encNat) 0).comp
      ((hrow.comp (fst (encPair input encUnary) encUnary)).prod
        (snd (encPair input encUnary) encUnary))
    exact binary_mod.comp (hentry.prod (binary_pow' (const 2) (by fun_prop)))

/-- Normalize the binary secret list to length `m` in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_secretSerialized {bits : α → List Bool}
    (hm : ComputableInPolyTime m input encUnary)
    (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => secretSerialized (m a) (bits a)) input encBits := by
  unfold secretSerialized
  exact mapToBitsWithInput (enc := encUnary) (range.comp hm)
    ((bitsGetD false).comp ((hbits.comp (fst input encUnary)).prod (snd input encUnary)))

/-- Serialized dual-Regev key generation is uniform strict PPT. -/
@[fun_prop]
theorem isPPTOn_keyGenSerialized
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary) :
    IsPPTOn input (encPair encBits encBits)
      (fun a => keyGenSerialized (n a) (m a) (w a)) := by
  have hsample := isPPTOn_sampleKeyInputsSerialized hn hm hw
  unfold keyGenSerialized
  ppt

/-- Uniform strict PPT generation of serialized dual-Regev encryption coins. -/
@[fun_prop]
theorem isPPTOn_sampleEncCoinsSerialized
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hη : ComputableInPolyTime η input encUnary) :
    IsPPTOn input encSerializedEncCoins
      (fun a => sampleEncCoinsSerialized (n a) (m a) (w a) (η a)) := by
  have hs := hw.sampleBinaryNat.replicate hn
  have hx := (isPPTOn_sampleCenteredBinomial.preprocess hη).replicate hm
  have hx₀ := isPPTOn_sampleCenteredBinomial.preprocess hη
  unfold sampleEncCoinsSerialized
  ppt

/-- Compute one coordinate of the serialized dual-Regev ciphertext in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_encryptEntry
    {publicWord : α → List Bool} {message : α → Bool} {coins : α → SerializedEncCoins}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hpublicWord : ComputableInPolyTime publicWord input encBits)
    (hmessage : ComputableInPolyTime message input encBool)
    (hcoins : ComputableInPolyTime coins input encSerializedEncCoins)
    (hidx : ComputableInPolyTime idx input encUnary) :
    ComputableInPolyTime
      (fun a => encryptEntry (n a) (w a) (publicWord a) (message a) (coins a) (idx a))
      input encNat := by
  unfold encryptEntry
  have hterm : ComputableInPolyTime
      (fun p : α × ℕ =>
        Cslib.Matrix.binaryEntry (n p.1) (w p.1) (publicWord p.1) (idx p.1) p.2 *
          (coins p.1).secret.getD p.2 0) (encPair input encUnary) encNat := by
    apply binary_mul'
    · exact matrixBinaryEntry (by fun_prop) (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop)
    · exact (listGetD (encA := encNat) 0).comp
        (((encSerializedEncCoins_secret_polyTime hcoins).comp
          (fst input encUnary)).prod (snd input encUnary))
  have hsum := (show ComputableInPolyTime List.sum (encList encNat) encNat by fun_prop).comp
    (mapWithInput
      (f := fun a j => Cslib.Matrix.binaryEntry (n a) (w a) (publicWord a) (idx a) j *
        (coins a).secret.getD j 0)
      (range.comp hn) hterm)
  have hboolUnary : ComputableInPolyTime Bool.toNat encBool encUnary := of_finite Bool.toNat
  have hpad : ComputableInPolyTime
      (fun a => ((message a).toNat : ℤ) * 2 ^ (w a - 1)) input encIntBin :=
    (show ComputableInPolyTime (fun p : ℤ × ℤ => p.1 * p.2)
      (encPair encIntBin encIntBin) encIntBin by fun_prop).comp
        ((intBin_natCast.comp (unary_to_binary.comp (hboolUnary.comp hmessage))).prod
          (intBin_natCast.comp (binary_pow' (const 2) (by fun_prop))))
  have hzero : ComputableInPolyTime
      (fun a => (coins a).scalarError + ((message a).toNat : ℤ) * 2 ^ (w a - 1)) input
        encIntBin :=
    (show ComputableInPolyTime (fun p : ℤ × ℤ => p.1 + p.2)
      (encPair encIntBin encIntBin) encIntBin by fun_prop).comp
        ((encSerializedEncCoins_scalarError_polyTime hcoins).prod hpad)
  have htail : ComputableInPolyTime
      (fun a => (coins a).error.getD (idx a - 1) 0) input encIntBin :=
    (listGetD (encA := encIntBin) 0).comp
      ((encSerializedEncCoins_error_polyTime hcoins).prod (by fun_prop))
  have herr : ComputableInPolyTime
      (fun a => if idx a = 0 then (coins a).scalarError + ((message a).toNat : ℤ) * 2 ^ (w a - 1)
        else (coins a).error.getD (idx a - 1) 0) input encIntBin := by
    simpa only [Function.comp_apply, beq_iff_eq] using (beq hidx (const 0)).ite' hzero htail
  have hadd := (show ComputableInPolyTime (fun p : ℤ × ℤ => p.1 + p.2)
    (encPair encIntBin encIntBin) encIntBin by fun_prop).comp
      ((intBin_natCast.comp hsum).prod herr)
  simpa only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat] using
    intBin_emodNat' hadd (binary_pow' (const 2) hw)

/-- Assemble all serialized dual-Regev ciphertext bits deterministically in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_encryptWithCoinsSerialized
    {publicWord : α → List Bool} {message : α → Bool} {coins : α → SerializedEncCoins}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hpublicWord : ComputableInPolyTime publicWord input encBits)
    (hmessage : ComputableInPolyTime message input encBool)
    (hcoins : ComputableInPolyTime coins input encSerializedEncCoins) :
    ComputableInPolyTime
      (fun a => encryptWithCoinsSerialized (n a) (m a) (w a) (publicWord a) (message a) (coins a))
      input encBits := by
  unfold encryptWithCoinsSerialized
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  apply bitsLow (by fun_prop)
  fun_prop

/-- Serialized dual-Regev encryption is uniform strict PPT on arbitrary public-key words. -/
@[fun_prop]
theorem isPPTOn_encryptSerialized
    {publicWord : α → List Bool} {message : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hη : ComputableInPolyTime η input encUnary)
    (hpublicWord : ComputableInPolyTime publicWord input encBits)
    (hmessage : ComputableInPolyTime message input encBool) :
    IsPPTOn input encBits
      (fun a => encryptSerialized (n a) (m a) (w a) (η a) (publicWord a) (message a)) := by
  have hsample := isPPTOn_sampleEncCoinsSerialized hn hm hw hη
  unfold encryptSerialized
  ppt

end PolyTime

/-! ### Reduction from `(m + 1)`-sample Decision LWE -/

/-- Extract the `(m + 1) × n` public key `[u; A]` from columns `1..n` of an `(m + 1)`-sample
decision-LWE word. -/
def lweExtractPublicKey (n m w : ℕ) (lweWord : List Bool) : List Bool :=
  (List.range (m + 1)).flatMap fun i =>
    (List.range n).flatMap fun j =>
      lowBits w (Cslib.Matrix.binaryEntry (n + 1) w lweWord i (j + 1))

/-- Extract the challenge ciphertext `(b, c₀)` from column `0` of an `(m + 1)`-sample decision-LWE
word, adding `message * 2 ^ (w - 1)` to row `0`. -/
def lweExtractChallenge (m n w : ℕ) (lweWord : List Bool) (message : Bool) : List Bool :=
  lowBits w ((Cslib.Matrix.binaryEntry (n + 1) w lweWord 0 0 +
      message.toNat * 2 ^ (w - 1)) % 2 ^ w) ++
    (List.range m).flatMap fun i =>
      lowBits w (Cslib.Matrix.binaryEntry (n + 1) w lweWord (i + 1) 0)

private theorem lowBits_mod_two_pow (w x : ℕ) :
    lowBits w (x % 2 ^ w) = lowBits w x := by
  simp only [lowBits]
  refine List.map_congr_left fun k hk => ?_
  simp [Nat.testBit_mod_two_pow, List.mem_range.mp hk]

private theorem lowBits_zmod (w x : ℕ) :
    lowBits w x = lowBits w (x : ZMod (2 ^ w)).val := by
  rw [ZMod.val_natCast, lowBits_mod_two_pow]

private theorem binaryEntry_zmod {m n w : ℕ}
    (M : _root_.Matrix (Fin m) (Fin n) (ZMod (2 ^ w))) (i : Fin m) (j : Fin n) :
    (Cslib.Matrix.binaryEntry n w (Cslib.Matrix.toBinary M) i.val j.val : ZMod (2 ^ w)) =
      M i j := by
  rw [← Cslib.Matrix.ofBinary_apply m n w, Cslib.Matrix.ofBinary_toBinary]

private theorem lweExtractPublicKey_toBinary {n m w : ℕ}
    (M : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) (ZMod (2 ^ w))) :
    lweExtractPublicKey n m w (Cslib.Matrix.toBinary M) =
      serializePublicKey (fun i j => M i.succ j.succ, fun j => M 0 j.succ) := by
  unfold lweExtractPublicKey
  conv_rhs => unfold serializePublicKey; rw [Cslib.Matrix.toBinary_eq]
  simp only [List.flatMap_def, List.map_range_eq_ofFn, _root_.Matrix.of_apply]
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 1
  apply congrArg List.ofFn
  funext j
  rw [lowBits_zmod, ← Fin.val_succ j, binaryEntry_zmod M i j.succ, lowBits_eq_ofFn]
  refine Fin.cases rfl (fun _ => rfl) i

private theorem lweExtractChallenge_toBinary {n m w : ℕ}
    (M : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) (ZMod (2 ^ w))) (message : Bool) :
    lweExtractChallenge m n w (Cslib.Matrix.toBinary M) message =
      serializeCiphertext (fun i => M i.succ 0, M 0 0 + LWE.encodeBit w message) := by
  unfold lweExtractChallenge
  conv_rhs => unfold serializeCiphertext; rw [Cslib.Matrix.toBinary_eq]
  simp only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.flatMap_def, List.map_range_eq_ofFn, _root_.Matrix.of_apply,
    Fin.cons_zero, Fin.cons_succ]
  congr 1
  · have h0 := binaryEntry_zmod M 0 0
    simp only [Fin.val_zero] at h0
    rw [lowBits_mod_two_pow, lowBits_zmod, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, h0, lowBits_eq_ofFn]
    cases message <;> simp [LWE.encodeBit]
  · congr 1
    apply congrArg List.ofFn
    funext i
    have hi := binaryEntry_zmod M i.succ 0
    simp only [Fin.val_zero] at hi
    rw [lowBits_zmod, ← Fin.val_succ i, hi, lowBits_eq_ofFn]

/-- Uniform hidden-bit reduction turning an `(m + 1)`-sample `DecisionLWE` challenge matrix word
into a dual-Regev IND-CPA challenge. -/
noncomputable def lweDistinguisher (n m w : ℕ → ℕ)
    (adversary : Encryption.Adversary) : Distinguisher := fun security lweWord => do
  let pkWord := lweExtractPublicKey (n security) (m security) (w security) lweWord
  let choice ← adversary.choose security pkWord
  let bit ← ProbComp.uniform Bool
  let msg := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
  let ctWord := lweExtractChallenge (m security) (n security) (w security) lweWord msg
  let guess ← adversary.guess security (Encryption.ChoiceOut.state choice) ctWord
  return guess ^^ bit

section DistinguisherPolyTime

open Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool} {n m w : α → ℕ}

/-- Extract the serialized dual-Regev public key `[u; A]` from a Decision-LWE word in
polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_lweExtractPublicKey {lweWord : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hlweWord : ComputableInPolyTime lweWord input encBits) :
    ComputableInPolyTime (fun a => lweExtractPublicKey (n a) (m a) (w a) (lweWord a))
      input encBits := by
  unfold lweExtractPublicKey
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  apply flatMapToBitsWithInput (range.comp (hn.comp (fst input encUnary)))
  apply bitsLow (hw.comp ((fst input encUnary).comp (fst (encPair input encUnary) encUnary)))
  exact matrixBinaryEntry (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

/-- Extract the serialized dual-Regev challenge ciphertext from column `0` in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_lweExtractChallenge {lweWord : α → List Bool} {message : α → Bool}
    (hm : ComputableInPolyTime m input encUnary)
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hlweWord : ComputableInPolyTime lweWord input encBits)
    (hmessage : ComputableInPolyTime message input encBool) :
    ComputableInPolyTime (fun a => lweExtractChallenge (m a) (n a) (w a) (lweWord a) (message a))
      input encBits := by
  unfold lweExtractChallenge
  apply bitsAppend
  · apply bitsLow hw
    have hhead := matrixBinaryEntry (by fun_prop) hw hlweWord (const 0) (const 0)
      (cols := fun a => n a + 1)
    have hboolUnary : ComputableInPolyTime Bool.toNat encBool encUnary := of_finite Bool.toNat
    have hhalf : ComputableInPolyTime (fun a => w a - 1) input encUnary := by fun_prop
    have hpad := binary_mul' (unary_to_binary.comp (hboolUnary.comp hmessage))
      (binary_pow' (const 2) hhalf)
    exact binary_mod.comp ((binary_add.comp (hhead.prod hpad)).prod (binary_pow' (const 2) hw))
  · apply flatMapToBitsWithInput (range.comp hm)
    apply bitsLow (hw.comp (fst input encUnary))
    exact matrixBinaryEntry (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (const 0)

end DistinguisherPolyTime

/-- Efficient parameter schedules make `lweDistinguisher` one uniform strict PPT distinguisher. -/
theorem isPPT_lweDistinguisher {n m w : ℕ → ℕ} {adversary : Encryption.Adversary}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hadversary : adversary.IsPPT) : IsPPT encBool (lweDistinguisher n m w adversary) := by
  open Turing.MultiTapeTM.ComputableInPolyTime in
  let baseEnc := encPair encUnary encBits
  let choiceEnc := encPair (encPair encBool encBool) encBits
  let coinEnc := encPair (encPair baseEnc choiceEnc) encBool
  have hpk : ComputableInPolyTime
      (fun p : ℕ × List Bool => (p.1, lweExtractPublicKey (n p.1) (m p.1) (w p.1) p.2))
      baseEnc baseEnc := by
    change ComputableInPolyTime
      (fun p : ℕ × List Bool => (p.1, lweExtractPublicKey (n p.1) (m p.1) (w p.1) p.2))
      (encPair encUnary encBits) (encPair encUnary encBits)
    fun_prop
  have hchoose := hadversary.choose.on.preprocess hpk
  have hcoin := isPPTOn_uniform_bool (encPair baseEnc choiceEnc)
  have hct : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ((Bool × Bool) × List Bool)) × Bool =>
        (p.1.1.1, p.1.2.2, lweExtractChallenge (m p.1.1.1) (n p.1.1.1) (w p.1.1.1) p.1.1.2
          (if p.2 then p.1.2.1.2 else p.1.2.1.1)))
      coinEnc (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [coinEnc, baseEnc, choiceEnc]
    fun_prop
  have hguess := hadversary.guess.preprocess hct
  have hxor : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × ((Bool × Bool) × List Bool)) × Bool) × Bool => p.2 ^^ p.1.2)
      (encPair coinEnc encBool) encBool := by
    have hx := of_finite (encIn := encPair encBool encBool) (encOut := encBool)
      fun p : Bool × Bool => p.1 ^^ p.2
    have harg : ComputableInPolyTime
        (fun p : (((ℕ × List Bool) × ((Bool × Bool) × List Bool)) × Bool) × Bool =>
          (p.2, p.1.2)) (encPair coinEnc encBool) (encPair encBool encBool) := by
      dsimp only [coinEnc, baseEnc, choiceEnc]
      fun_prop
    simpa only [Function.comp_def] using hx.comp harg
  have htail := hguess.map_with (f := fun p guess => guess ^^ p.2) hxor
  have hbits := hcoin.bind_with
    (second := fun p bit =>
      let ct := lweExtractChallenge (m p.1.1) (n p.1.1) (w p.1.1) p.1.2
        (if bit then p.2.1.2 else p.2.1.1)
      (fun guess => guess ^^ bit) <$> adversary.guess p.1.1 p.2.2 ct) htail
  simpa only [IsPPT, lweDistinguisher, baseEnc, choiceEnc, coinEnc, Function.comp_def,
    bind_pure_comp, Encryption.ChoiceOut.msg₀, Encryption.ChoiceOut.msg₁,
    Encryption.ChoiceOut.state] using
    hchoose.bind_with (second := fun p choice => do
      let bit ← ProbComp.uniform Bool
      let msg := if bit then choice.1.2 else choice.1.1
      let ct := lweExtractChallenge (m p.1) (n p.1) (w p.1) p.2 msg
      (fun guess => guess ^^ bit) <$> adversary.guess p.1 choice.2 ct) hbits

/-! ### Exact game identities and hybrid security proof -/

private noncomputable def uniformPublicKeyWord (n m w : ℕ) : PMF (List Bool) :=
  (PMF.uniformOfFintype (PublicKey n m w)).map serializePublicKey

private noncomputable def idealCipherGame (n m w : ℕ) (adversary : Encryption.Adversary)
    (security : ℕ) : Game := do
  let pk ← PMF.uniformOfFintype (PublicKey n m w)
  let choice ← ProbComp.eval (adversary.choose security (serializePublicKey pk))
  let c ← PMF.uniformOfFintype (Ciphertext m w)
  ProbComp.eval (adversary.guess security (Encryption.ChoiceOut.state choice)
    (serializeCiphertext c))

private theorem uniform_split_publicKey {m n w : ℕ} :
    (PMF.uniformOfFintype (_root_.Matrix (Fin (m + 1)) (Fin n) (ZMod (2 ^ w)))).map
      (fun B => (((fun i j => B i.succ j, fun j => B 0 j) : PublicKey n m w))) =
        PMF.uniformOfFintype (PublicKey n m w) := by
  let e : _root_.Matrix (Fin (m + 1)) (Fin n) (ZMod (2 ^ w)) ≃ PublicKey n m w :=
    { toFun := fun B => ((fun i j => B i.succ j, fun j => B 0 j) : PublicKey n m w)
      invFun := fun pk =>
        _root_.Matrix.of (Fin.cons (α := fun _ => Fin n → ZMod (2 ^ w)) pk.2 (fun r => pk.1 r))
      left_inv := fun B => by ext i j; refine Fin.cases rfl (fun _ => rfl) i
      right_inv := fun pk => by refine Prod.ext (by ext i j; simp) (by ext j; simp) }
  exact PMF.uniformOfFintype_map_equiv e

private theorem uniform_split_lweMatrix {m n w : ℕ} :
    (PMF.uniformOfFintype (_root_.Matrix (Fin (m + 1)) (Fin (n + 1)) (ZMod (2 ^ w)))).map
      (fun M => (((fun i j => M i.succ j.succ, fun j => M 0 j.succ) : PublicKey n m w),
        ((fun i => M i.succ 0, M 0 0) : Ciphertext m w))) =
      (PMF.uniformOfFintype (PublicKey n m w)).bind fun pk =>
        (PMF.uniformOfFintype (Ciphertext m w)).map fun c => (pk, c) := by
  let e : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) (ZMod (2 ^ w)) ≃
      PublicKey n m w × Ciphertext m w :=
    { toFun := fun M =>
        (((fun i j => M i.succ j.succ, fun j => M 0 j.succ) : PublicKey n m w),
          ((fun i => M i.succ 0, M 0 0) : Ciphertext m w))
      invFun := fun p => _root_.Matrix.of
        (Fin.cons (α := fun _ => Fin (n + 1) → ZMod (2 ^ w))
          (Fin.cons (α := fun _ => ZMod (2 ^ w)) p.2.2 p.1.2)
          (fun i => Fin.cons (α := fun _ => ZMod (2 ^ w)) (p.2.1 i) (fun j => p.1.1 i j)))
      left_inv := fun M => by
        ext i j
        refine Fin.cases ?_ (fun _ => ?_) i <;> refine Fin.cases rfl (fun _ => rfl) j
      right_inv := fun p => by
        refine Prod.ext (Prod.ext (by ext i j; simp) (by ext j; simp))
          (Prod.ext (by ext i; simp) (by simp)) }
  calc
    _ = PMF.uniformOfFintype (PublicKey n m w × Ciphertext m w) :=
      PMF.uniformOfFintype_map_equiv e
    _ = _ := by
      rw [← PMF.uniformOfFintype_prod]

private theorem distinguishingGame_realEnsemble (n m w η : ℕ → ℕ)
    (adversary : Encryption.Adversary) (security : ℕ) :
    distinguishingGame
      (LWE.realEnsemble n (fun k => m k + 1) w (fun k => LWE.noiseLaw (w k) (η k)) security)
      (lweDistinguisher n m w adversary security) =
      ((PMF.uniformOfFintype Bool).bind fun bit =>
        (Encryption.publicKeyGame
          (uniformPublicKeyWord (n security) (m security) (w security))
          (fun k => encryptSerialized (n k) (m k) (w k) (η k))
          adversary bit security).map fun guess => guess ^^ bit) := by
  simp only [distinguishingGame_eq_bind, lweDistinguisher, LWE.realEnsemble, LWE.publicMatrixLaw,
    LWE.publicMatrix, Encryption.publicKeyGame, Encryption.publicKeyGameOn, ↓reduceIte,
    uniformPublicKeyWord, pmf_norm,
    lweExtractPublicKey_toBinary, lweExtractChallenge_toBinary,
    eval_encryptSerialized_serializePublicKey, encrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    LWE.eval_sampleVector, ProbComp.eval_uniform]
  rw [PMF.pi_fin_succ (m security) (LWE.noiseLaw (w security) (η security)),
    ← LWE.eval_errorVector_mod (m security) (w security) (η security)]
  simp only [LWE.noiseLaw, PMF.bind_map, PMF.bind_bind, Function.comp_def,
    Fin.cons_zero, Fin.cons_succ]
  rw [← uniform_split_publicKey (m := m security) (n := n security) (w := w security)]
  simp only [PMF.bind_map, Function.comp_def]
  pmf_swap

private theorem distinguishingGame_uniformEnsemble (n m w : ℕ → ℕ)
    (adversary : Encryption.Adversary) (security : ℕ) :
    distinguishingGame (LWE.uniformEnsemble n (fun k => m k + 1) w security)
      (lweDistinguisher n m w adversary security) =
      ((PMF.uniformOfFintype Bool).bind fun bit =>
        (idealCipherGame (n security) (m security) (w security) adversary security).map
          fun guess => guess ^^ bit) := by
  simp only [distinguishingGame_eq_bind, lweDistinguisher, LWE.uniformEnsemble, idealCipherGame,
    pmf_norm, lweExtractPublicKey_toBinary, lweExtractChallenge_toBinary, ProbComp.eval_uniform]
  have hsplit := congrArg
    (fun law : PMF (PublicKey (n security) (m security) (w security) ×
        Ciphertext (m security) (w security)) =>
      law.bind fun p =>
        (ProbComp.eval (adversary.choose security (serializePublicKey p.1))).bind fun choice =>
          (PMF.uniformOfFintype Bool).bind fun bit =>
            (ProbComp.eval (adversary.guess security (Encryption.ChoiceOut.state choice)
              (serializeCiphertext (p.2.1, p.2.2 + LWE.encodeBit (w security)
                (if bit then Encryption.ChoiceOut.msg₁ choice
                  else Encryption.ChoiceOut.msg₀ choice))))).bind fun guess =>
              PMF.pure (guess ^^ bit))
    (uniform_split_lweMatrix (m := m security) (n := n security) (w := w security))
  calc
    _ = ((PMF.uniformOfFintype (PublicKey (n security) (m security) (w security))).bind fun pk =>
          (PMF.uniformOfFintype (Ciphertext (m security) (w security))).map fun c => (pk, c)).bind
        (fun p =>
          (ProbComp.eval (adversary.choose security (serializePublicKey p.1))).bind fun choice =>
            (PMF.uniformOfFintype Bool).bind fun bit =>
              (ProbComp.eval (adversary.guess security (Encryption.ChoiceOut.state choice)
                (serializeCiphertext (p.2.1, p.2.2 + LWE.encodeBit (w security)
                  (if bit then Encryption.ChoiceOut.msg₁ choice
                    else Encryption.ChoiceOut.msg₀ choice))))).bind fun guess =>
                PMF.pure (guess ^^ bit)) := by
      simpa only [PMF.bind_map, PMF.bind_bind, Function.comp_def] using hsplit
    _ = _ := by
      simp only [PMF.bind_map, PMF.bind_bind, Function.comp_def]
      pmf_swap with bit pk choice
      let msg := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
      let shift : Ciphertext (m security) (w security) :=
        (0, LWE.encodeBit (w security) msg)
      have hshift := congrArg
        (fun law : PMF (Ciphertext (m security) (w security)) =>
          law.bind fun c =>
            (ProbComp.eval (adversary.guess security (Encryption.ChoiceOut.state choice)
              (serializeCiphertext c))).bind fun guess => PMF.pure (guess ^^ bit))
        (PMF.uniformOfFintype_map_equiv (Equiv.addRight shift))
      simp only [shift, msg, PMF.bind_map, Function.comp_def, Equiv.coe_addRight, Prod.add_def,
        add_zero] at hshift
      dsimp only [PMF.map]
      exact hshift

/-- The statistical hiding error `sqrt(2 ^ (w * n) / 2 ^ m)` from replacing `(A, eᵀ A)` by uniform
`(A, u)`. -/
noncomputable def hidingError (n m w : ℕ) : ℝ≥0 :=
  NNReal.sqrt ((2 : ℝ≥0) ^ (w * n) / 2 ^ m)

/-- Concrete chosen-message bound for dual-Regev in terms of one uniform hidden-bit `(m + 1)`-sample
decision-LWE distinguisher plus the statistical public-key hiding term. -/
theorem advantage_game_le (n m w η : ℕ → ℕ) (adversary : Encryption.Adversary) (security : ℕ) :
    Encryption.advantage
      (Encryption.game (fun k => keyGenSerialized (n k) (m k) (w k))
        (fun k => encryptSerialized (n k) (m k) (w k) (η k)) adversary) security ≤
      2 * Game.advantage
        (distinguishingGame
          (LWE.realEnsemble n (fun k => m k + 1) w (fun k => LWE.noiseLaw (w k) (η k)) security)
          (lweDistinguisher n m w adversary security))
        (distinguishingGame (LWE.uniformEnsemble n (fun k => m k + 1) w security)
          (lweDistinguisher n m w adversary security)) +
        hidingError (n security) (m security) (w security) := by
  have hpk : (ProbComp.eval (keyGenSerialized (n security) (m security) (w security))).map
      Prod.fst =
      (ProbComp.eval (keyGen (n security) (m security) (w security))).map
        (fun keys => serializePublicKey keys.1) :=
    eval_keyGenSerialized_fst (n security) (m security) (w security)
  let enc := fun k => encryptSerialized (n k) (m k) (w k) (η k)
  let realPK := (ProbComp.eval (keyGen (n security) (m security) (w security))).map
    (fun keys => serializePublicKey keys.1)
  let unifPK := uniformPublicKeyWord (n security) (m security) (w security)
  have hhop1 :
      Encryption.advantage
        (Encryption.game (fun k => keyGenSerialized (n k) (m k) (w k)) enc adversary) security ≤
      2 * Game.advantage
        (distinguishingGame realPK (Encryption.keyDistinguisher enc adversary security))
        (distinguishingGame unifPK (Encryption.keyDistinguisher enc adversary security)) +
        Game.advantage
          (Encryption.publicKeyGame unifPK enc adversary false security)
          (Encryption.publicKeyGame unifPK enc adversary true security) := by
    simp only [Encryption.advantage, Encryption.eval_game_eq_publicKeyGame, hpk]
    exact Encryption.advantage_publicKeyGame_le realPK unifPK enc adversary security
  have hdistPK :
      (2 : ℝ) * Game.advantage
        (distinguishingGame realPK (Encryption.keyDistinguisher enc adversary security))
        (distinguishingGame unifPK (Encryption.keyDistinguisher enc adversary security)) ≤
        (hidingError (n security) (m security) (w security) : ℝ) := by
    rw [Game.advantage_eq_nndist, coe_nndist]
    have hd :
        dist (distinguishingGame realPK (Encryption.keyDistinguisher enc adversary security))
          (distinguishingGame unifPK (Encryption.keyDistinguisher enc adversary security)) ≤
          dist ((ProbComp.eval (keyGen (n security) (m security) (w security))).map Prod.fst)
            (do
              let A ← PMF.uniformOfFintype
                (_root_.Matrix (Fin (m security)) (Fin (n security)) (ZMod (2 ^ w security)))
              let u ← PMF.uniformOfFintype (Fin (n security) → ZMod (2 ^ w security))
              return (A, u)) := by
      have hLHS : distinguishingGame realPK
          (Encryption.keyDistinguisher enc adversary security) =
          ((ProbComp.eval (keyGen (n security) (m security) (w security))).map Prod.fst).bind
            fun pk => ProbComp.eval
              (Encryption.keyDistinguisher enc adversary security (serializePublicKey pk)) := by
        simp only [distinguishingGame_eq_bind, realPK, pmf_norm]
      have hRHS : distinguishingGame unifPK
          (Encryption.keyDistinguisher enc adversary security) =
          (do
            let A ← PMF.uniformOfFintype
              (_root_.Matrix (Fin (m security)) (Fin (n security)) (ZMod (2 ^ w security)))
            let u ← PMF.uniformOfFintype (Fin (n security) → ZMod (2 ^ w security))
            return (A, u)).bind fun pk => ProbComp.eval
              (Encryption.keyDistinguisher enc adversary security (serializePublicKey pk)) := by
        unfold unifPK uniformPublicKeyWord
        simp only [distinguishingGame_eq_bind]
        rw [← PMF.uniformOfFintype_prod]
        simp only [pmf_norm]
      rw [hLHS, hRHS]
      exact Probability.PMF.dist_bind_le _ _ _
    have hbound := hd.trans (dist_keyGen_uniform_le (n security) (m security) (w security))
    have hcoe : (hidingError (n security) (m security) (w security) : ℝ) =
        Real.sqrt ((2 : ℝ) ^ (w security * n security) / (2 : ℝ) ^ m security) := by
      simp [hidingError]
    linarith
  have hhop2 :
      Game.advantage
        (Encryption.publicKeyGame unifPK enc adversary false security)
        (Encryption.publicKeyGame unifPK enc adversary true security) ≤
      2 * Game.advantage
        (distinguishingGame
          (LWE.realEnsemble n (fun k => m k + 1) w (fun k => LWE.noiseLaw (w k) (η k)) security)
          (lweDistinguisher n m w adversary security))
        (distinguishingGame (LWE.uniformEnsemble n (fun k => m k + 1) w security)
          (lweDistinguisher n m w adversary security)) := by
    rw [distinguishingGame_realEnsemble, distinguishingGame_uniformEnsemble]
    have h := Game.advantage_le_two_mul_uniform_bool_xor
      (fun bit => Encryption.publicKeyGame unifPK enc adversary bit security)
      (fun _ => idealCipherGame (n security) (m security) (w security) adversary security)
    simpa only [Game.advantage_self, add_zero] using h
  have hreal :
      (Encryption.advantage
        (Encryption.game (fun k => keyGenSerialized (n k) (m k) (w k)) enc adversary)
        security : ℝ) ≤
        (2 * Game.advantage
          (distinguishingGame
            (LWE.realEnsemble n (fun k => m k + 1) w (fun k => LWE.noiseLaw (w k) (η k)) security)
            (lweDistinguisher n m w adversary security))
          (distinguishingGame (LWE.uniformEnsemble n (fun k => m k + 1) w security)
            (lweDistinguisher n m w adversary security)) +
          hidingError (n security) (m security) (w security) : ℝ) := by
    have h1 := NNReal.coe_le_coe.mpr hhop1
    have h2 := NNReal.coe_le_coe.mpr hhop2
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat] at h1 h2 ⊢
    linarith
  exact NNReal.coe_le_coe.mp hreal

open Filter in
/-- Dual-Regev encryption is IND-CPA secure under decision LWE with `m + 1` samples for
centered-binomial errors `LWE.noiseLaw w η`, whenever `n`, `m`, `w` are uniform polynomial-time
computable and eventually satisfy `w * n + 2 * security ≤ m`. -/
theorem indCPA_of_decisionLWE {n m w η : ℕ → ℕ}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hmargin : ∀ᶠ security in atTop, w security * n security + 2 * security ≤ m security)
    (hLWE : DecisionLWE n (fun k => m k + 1) w (fun k => LWE.noiseLaw (w k) (η k))) :
    Encryption.INDCPA (fun k => keyGenSerialized (n k) (m k) (w k))
      (fun k => encryptSerialized (n k) (m k) (w k) (η k)) := by
  intro adversary hadversary
  have hsource := hLWE.encoded (lweDistinguisher n m w adversary)
    (isPPT_lweDistinguisher hn hm hw hadversary)
  have herror := negligible_mul_sqrt_pow_two_div_pow_two
    (count := fun _ => 1) (outputBits := fun k => w k * n k) (by fun_prop) hmargin
  apply negligible_of_le
    ((hsource.polynomiallyBounded_mul (p := fun _ => 2) (by fun_prop)).add herror)
  intro security
  refine (advantage_game_le n m w η adversary security).trans (le_of_eq ?_)
  simp [hidingError]

end Cslib.Crypto.DualRegev
