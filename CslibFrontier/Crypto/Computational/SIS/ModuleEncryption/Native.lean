/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption
public import CslibFrontier.Computability.PolyTime.Int.DotProduct
public import CslibFrontier.Computability.PolyTime.Int.Negacyclic
import CslibFrontier.Crypto.Computational.SIS.Native
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.ZMod.DotProduct
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Native realization of existing Module-LWE key generation and decryption

One total word implementation realizes `moduleLWEKeyGen` in the existing
`ModuleLWE.encodeSample` codec, and one total word implementation realizes
`moduleLWEDecrypt` over existing ciphertext matrices and secret integer lists.
Both dimensions are unary runtime inputs; the modulus and coefficients are binary.
Runtime charges all input words, including discarded data. Canonical interpretation
requires a positive modulus.

## Main results

* `exists_computableInPolyTime_moduleLWEKeyGen`: a single native implementation for all
  dimensions, positive moduli, structured matrices and signed integer secret/error lifts.
* `exists_computableInPolyTime_moduleLWEDecrypt`: a single native implementation for all
  dimensions, positive moduli, signed integer secrets and structured ciphertexts.

This is original implementation algebra. It supplies neither native matrix sampling nor a
malformed-input rejection policy, encryption implementation or security theorem.
-/

public section

open scoped Matrix

namespace Cslib.Crypto

open Turing.MultiTapeTM Mathlib.Tactic.Matrix

private abbrev KeyGenInput := ((ℕ × ℕ) × ℕ) × List Bool × List Bool × List Bool

private def keyGenInputEncoding : KeyGenInput ↪ List Bool :=
  encPair (encPair (encPair encUnary encUnary) encNat)
    (encPair encBits (encPair encBits encBits))

private def keyGenCoefficients (d q : ℕ) (rows : List (List ℕ)) (s e : List ℤ) : List ℕ :=
  (List.range d).map fun i =>
    ((ListMatrix.dotProduct d ((rows.getD i []).map (fun x : ℕ => (x : ℤ))) s +
      e.getD i 0) % (q : ℤ)).toNat

private theorem keyGenCoefficients_polyTime :
    ComputableInPolyTime
      (fun a : (ℕ × ℕ) × List (List ℕ) × List ℤ × List ℤ =>
        keyGenCoefficients a.1.1 a.1.2 a.2.1 a.2.2.1 a.2.2.2)
      (encPair (encPair encUnary encNat)
        (encPair (encList (encList encNat)) (encPair (encList encIntBin) (encList encIntBin))))
      (encList encNat) := by
  unfold keyGenCoefficients
  have hcast := ComputableInPolyTime.intBin_natCast
  apply ComputableInPolyTime.mapWithInput (encA := encUnary)
  · fun_prop
  · apply ComputableInPolyTime.intBin_emodNat'
    · fun_prop
    · fun_prop

private def keyGenWords (a : KeyGenInput) : List Bool :=
  encPair encBits (encList encNat) (a.2.1,
    keyGenCoefficients (a.1.1.1 * a.1.1.2) a.1.2
      ((Decoder.list (Decoder.list Decoder.nat)).decode a.2.1)
      ((Decoder.list Decoder.intBin).decode a.2.2.1)
      ((Decoder.list Decoder.intBin).decode a.2.2.2))

private theorem keyGenWords_polyTime :
    ComputableInPolyTime keyGenWords keyGenInputEncoding encBits := by
  have hrows := (Decoder.list (Decoder.list Decoder.nat)).computableInPolyTime
  have hdecode := (Decoder.list Decoder.intBin).computableInPolyTime
  have hcoeff := keyGenCoefficients_polyTime
  have hinput : ComputableInPolyTime
      (fun a : KeyGenInput => (((a.1.1.1 * a.1.1.2), a.1.2),
        ((Decoder.list (Decoder.list Decoder.nat)).decode a.2.1,
          (Decoder.list Decoder.intBin).decode a.2.2.1,
          (Decoder.list Decoder.intBin).decode a.2.2.2)))
      keyGenInputEncoding
      (encPair (encPair encUnary encNat)
        (encPair (encList (encList encNat))
          (encPair (encList encIntBin) (encList encIntBin)))) := by
    unfold keyGenInputEncoding
    apply ComputableInPolyTime.prod
    · fun_prop
    · exact (hrows.comp (by fun_prop)).prod
        ((hdecode.comp (by fun_prop)).prod (hdecode.comp (by fun_prop)))
  have h := (show ComputableInPolyTime (fun a : KeyGenInput => a.2.1)
      keyGenInputEncoding encBits by unfold keyGenInputEncoding; fun_prop).prod
    (hcoeff.comp hinput)
  exact h.of_enc_eq fun _ => rfl

private theorem keyGenCoefficients_ofFn {d q : ℕ} (hq : 0 < q)
    (A : _root_.Matrix (Fin d) (Fin d) (ZMod q)) (s e : Fin d → ℤ) :
    keyGenCoefficients d q (List.ofFn fun i => List.ofFn fun j => (A i j).val)
      (List.ofFn s) (List.ofFn e) =
    List.ofFn (fun i => ((A *ᵥ (Int.cast ∘ s)) i + (e i : ZMod q)).val) := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [keyGenCoefficients, List.map_range_eq_ofFn]
  congr 1 with i : 1
  simp only [List.getD_ofFn, List.map_ofFn, Function.comp_def]
  have h := ListMatrix.intCast_dotProduct_matrix_ofFn A s i
  simp only [List.getD_ofFn, ZMod.cast_eq_val, Function.comp_def] at h
  rw [← h, ← Int.cast_add]
  have hv := congrArg Int.toNat (ZMod.val_intCast (n := q)
    (ListMatrix.dotProduct d (List.ofFn fun j => ((A i j).val : ℤ)) (List.ofFn s) + e i))
  simpa only [Int.toNat_natCast] using hv.symm

private theorem keyGenWords_encode {k n q : ℕ} (hq : 0 < q)
    (A : _root_.Matrix (Fin k) (Fin k) (Fin n → ZMod q))
    (s e : Fin k → Fin n → ℤ) :
    keyGenWords (((k, n), q), (ModuleSIS.encodeMatrix A,
      (ModuleSIS.encodeVec s, ModuleSIS.encodeVec e))) =
      ModuleLWE.encodeSample
        (moduleLWEKeyGen A (fun j i => (s j i : ZMod q)) (fun j i => (e j i : ZMod q))) := by
  simp only [keyGenWords, ModuleSIS.encodeMatrix, ModuleSIS.encodeVec,
    GeneralSIS.encodeMatrix, GeneralSIS.encodeVec, Decoder.decode_enc]
  rw [keyGenCoefficients_ofFn hq]
  simp only [ModuleLWE.encodeSample, moduleLWEKeyGen_eq_sample,
    ModuleLWE.flattenPolyVec_sample, ← intCast_comp_flattenPolyVec]
  rfl

/-- A single total native function realizes existing deterministic Module-LWE key generation
in its existing expanded-matrix/public-sample codec. Dimensions are unary; the modulus and
all coefficient words are binary. The certificate charges the full raw input. No sampling
or canonicality test is included; semantic equality holds for canonical inputs and `q > 0`. -/
theorem exists_computableInPolyTime_moduleLWEKeyGen :
    ∃ run : (((ℕ × ℕ) × ℕ) × List Bool × List Bool × List Bool) → List Bool,
      ComputableInPolyTime run
        (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair encBits (encPair encBits encBits))) encBits ∧
      ∀ (k n q : ℕ) (_hq : 0 < q)
        (A : _root_.Matrix (Fin k) (Fin k) (Fin n → ZMod q))
        (s e : Fin k → Fin n → ℤ),
        run (((k, n), q), (ModuleSIS.encodeMatrix A,
          (ModuleSIS.encodeVec s, ModuleSIS.encodeVec e))) =
          ModuleLWE.encodeSample
            (moduleLWEKeyGen A (fun j i => (s j i : ZMod q))
              (fun j i => (e j i : ZMod q))) :=
  ⟨keyGenWords, keyGenWords_polyTime, fun _ _ _ hq A s e => keyGenWords_encode hq A s e⟩

private abbrev DecryptInput := ((ℕ × ℕ) × ℕ) × List Bool × List Bool

private def decryptInputEncoding : DecryptInput ↪ List Bool :=
  encPair (encPair (encPair encUnary encUnary) encNat)
    (encPair encBits encBits)

private def decryptSecretCoeffs (n q : ℕ) (s_ints : List ℤ) (j : ℕ) : List ℕ :=
  (List.range n).map fun l => ((s_ints.getD (j * n + l) 0) % (q : ℤ)).toNat

private theorem decryptSecretCoeffs_polyTime :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List ℤ) × ℕ =>
        decryptSecretCoeffs p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary)
      (encList encNat) := by
  unfold decryptSecretCoeffs
  apply ComputableInPolyTime.mapWithInput (encA := encUnary)
  · exact ComputableInPolyTime.range.comp (by fun_prop)
  · have hs : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × List ℤ) × ℕ) × ℕ => p.1.1.2)
        (encPair (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary)
          encUnary)
        (encList encIntBin) := by fun_prop
    have hj : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × List ℤ) × ℕ) × ℕ => p.1.2)
        (encPair (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary)
          encUnary)
        encUnary := by fun_prop
    have hn : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × List ℤ) × ℕ) × ℕ => p.1.1.1.1)
        (encPair (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary)
          encUnary)
        encUnary := by fun_prop
    have hl : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × List ℤ) × ℕ) × ℕ => p.2)
        (encPair (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary)
          encUnary)
        encUnary := by fun_prop
    have hmul : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × List ℤ) × ℕ) × ℕ => p.1.2 * p.1.1.1.1)
        (encPair (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary)
          encUnary)
        encUnary :=
      ComputableInPolyTime.unary_mul.comp (hj.prod hn)
    have hidx : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × List ℤ) × ℕ) × ℕ => p.1.2 * p.1.1.1.1 + p.2)
        (encPair (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary)
          encUnary)
        encUnary :=
      ComputableInPolyTime.unary_add.comp (hmul.prod hl)
    have hget : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × List ℤ) × ℕ) × ℕ => p.1.1.2.getD (p.1.2 * p.1.1.1.1 + p.2) 0)
        (encPair (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary)
          encUnary)
        encIntBin :=
      (ComputableInPolyTime.listGetD (encA := encIntBin) 0).comp (hs.prod hidx)
    have hq : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × List ℤ) × ℕ) × ℕ => p.1.1.1.2)
        (encPair (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary)
          encUnary)
        encNat := by fun_prop
    exact ComputableInPolyTime.intBin_emodNat' hget hq

private def decryptProducts (k n q : ℕ) (ct_rows : List (List ℕ)) (s_ints : List ℤ) :
    List (List ℕ) :=
  (List.range k).map fun j =>
    negacyclicMulResidues n q (ct_rows.getD (j + 1) []) (decryptSecretCoeffs n q s_ints j)

private theorem decryptProducts_polyTime :
    ComputableInPolyTime
      (fun a : ((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ =>
        decryptProducts a.1.1.1 a.1.1.2 a.1.2 a.2.1 a.2.2)
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair (encList (encList encNat)) (encList encIntBin)))
      (encList (encList encNat)) := by
  unfold decryptProducts
  apply ComputableInPolyTime.mapWithInput (encA := encUnary)
  · exact ComputableInPolyTime.range.comp (by fun_prop)
  · have hmul := computableInPolyTime_negacyclicMulResidues
    have hsec := decryptSecretCoeffs_polyTime
    have hn : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) × ℕ => p.1.1.1.2)
        (encPair (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair (encList (encList encNat)) (encList encIntBin))) encUnary)
        encUnary := by fun_prop
    have hq : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) × ℕ => p.1.1.2)
        (encPair (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair (encList (encList encNat)) (encList encIntBin))) encUnary)
        encNat := by fun_prop
    have hj : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) × ℕ => p.2)
        (encPair (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair (encList (encList encNat)) (encList encIntBin))) encUnary)
        encUnary := by fun_prop
    have hj1 : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) × ℕ => p.2 + 1)
        (encPair (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair (encList (encList encNat)) (encList encIntBin))) encUnary)
        encUnary :=
      ComputableInPolyTime.unary_add.comp (hj.prod (ComputableInPolyTime.const 1))
    have hrows : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) × ℕ => p.1.2.1)
        (encPair (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair (encList (encList encNat)) (encList encIntBin))) encUnary)
        (encList (encList encNat)) := by fun_prop
    have hu : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) × ℕ =>
          p.1.2.1.getD (p.2 + 1) [])
        (encPair (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair (encList (encList encNat)) (encList encIntBin))) encUnary)
        (encList encNat) :=
      (ComputableInPolyTime.listGetD (encA := encList encNat) []).comp (hrows.prod hj1)
    have hs_ints : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) × ℕ => p.1.2.2)
        (encPair (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair (encList (encList encNat)) (encList encIntBin))) encUnary)
        (encList encIntBin) := by fun_prop
    have hsec_in : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) × ℕ =>
          (((p.1.1.1.2, p.1.1.2), p.1.2.2), p.2))
        (encPair (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair (encList (encList encNat)) (encList encIntBin))) encUnary)
        (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary) :=
      ((hn.prod hq).prod hs_ints).prod hj
    have hs : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) × ℕ =>
          decryptSecretCoeffs p.1.1.1.2 p.1.1.2 p.1.2.2 p.2)
        (encPair (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair (encList (encList encNat)) (encList encIntBin))) encUnary)
        (encList encNat) :=
      hsec.comp hsec_in
    have hmul_in : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) × ℕ =>
          ((p.1.1.1.2, p.1.1.2),
            (p.1.2.1.getD (p.2 + 1) [], decryptSecretCoeffs p.1.1.1.2 p.1.1.2 p.1.2.2 p.2)))
        (encPair (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair (encList (encList encNat)) (encList encIntBin))) encUnary)
        (encPair (encPair encUnary encNat) (encPair (encList encNat) (encList encNat))) :=
      (hn.prod hq).prod (hu.prod hs)
    have hres := hmul.comp hmul_in
    simpa only [Function.comp_def] using hres

private def columnSum (prods : List (List ℕ)) (i : ℕ) : ℕ :=
  (prods.map fun row => row.getD i 0).sum

private theorem columnSum_polyTime :
    ComputableInPolyTime (fun p : List (List ℕ) × ℕ => columnSum p.1 p.2)
      (encPair (encList (encList encNat)) encUnary) encNat := by
  unfold columnSum
  have hsum : ComputableInPolyTime List.sum (encList encNat) encNat :=
    .of_tidy Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_sum
  apply hsum.comp
  have hlist : ComputableInPolyTime (fun p : List (List ℕ) × ℕ => p.1)
      (encPair (encList (encList encNat)) encUnary) (encList (encList encNat)) := by fun_prop
  apply ComputableInPolyTime.mapWithInput hlist
  have hrow : ComputableInPolyTime (fun p : (List (List ℕ) × ℕ) × List ℕ => p.2)
      (encPair (encPair (encList (encList encNat)) encUnary) (encList encNat))
      (encList encNat) := by fun_prop
  have hi : ComputableInPolyTime (fun p : (List (List ℕ) × ℕ) × List ℕ => p.1.2)
      (encPair (encPair (encList (encList encNat)) encUnary) (encList encNat))
      encUnary := by fun_prop
  exact (ComputableInPolyTime.listGetD (encA := encNat) 0).comp (hrow.prod hi)

private def decryptedBit (q v_i sum_i : ℕ) : Bool :=
  let diff := (((v_i : ℤ) - (sum_i : ℤ)) % (q : ℤ)).toNat
  decide (q / 4 < if diff ≤ q / 2 then diff else q - diff)

private theorem decryptedBit_polyTime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => decryptedBit p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) encNat) encBool := by
  unfold decryptedBit
  have hdiff : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => (((p.1.2 : ℤ) - (p.2 : ℤ)) % (p.1.1 : ℤ)).toNat)
      (encPair (encPair encNat encNat) encNat) encNat := by
    have hcast := ComputableInPolyTime.intBin_natCast
    have hv : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => (p.1.2 : ℤ))
        (encPair (encPair encNat encNat) encNat) encIntBin :=
      hcast.comp (by fun_prop)
    have hsum : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => (p.2 : ℤ))
        (encPair (encPair encNat encNat) encNat) encIntBin :=
      hcast.comp (by fun_prop)
    have hsub : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => (p.1.2 : ℤ) - (p.2 : ℤ))
        (encPair (encPair encNat encNat) encNat) encIntBin :=
      ComputableInPolyTime.intBin_sub.comp (hv.prod hsum)
    have hq : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.1)
        (encPair (encPair encNat encNat) encNat) encNat := by fun_prop
    exact ComputableInPolyTime.intBin_emodNat' hsub hq
  have hq : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.1)
      (encPair (encPair encNat encNat) encNat) encNat := by fun_prop
  have hdiv : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 / p.2)
      (encPair encNat encNat) encNat :=
    .of_tidy Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_div
  have hq4 : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.1 / 4)
      (encPair (encPair encNat encNat) encNat) encNat :=
    hdiv.comp (hq.prod (ComputableInPolyTime.const 4))
  have hq2 : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.1 / 2)
      (encPair (encPair encNat encNat) encNat) encNat :=
    hdiv.comp (hq.prod (ComputableInPolyTime.const 2))
  have hle : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ =>
        decide ((((p.1.2 : ℤ) - (p.2 : ℤ)) % (p.1.1 : ℤ)).toNat ≤ p.1.1 / 2))
      (encPair (encPair encNat encNat) encNat) encBool :=
    ComputableInPolyTime.binary_le.comp (hdiff.prod hq2)
  have hsub_nat : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 - p.2)
      (encPair encNat encNat) encNat :=
    .of_tidy Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_sub
  have hqsub : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => p.1.1 - (((p.1.2 : ℤ) - (p.2 : ℤ)) % (p.1.1 : ℤ)).toNat)
      (encPair (encPair encNat encNat) encNat) encNat :=
    hsub_nat.comp (hq.prod hdiff)
  have hbound : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ =>
        let diff := (((p.1.2 : ℤ) - (p.2 : ℤ)) % (p.1.1 : ℤ)).toNat
        if diff ≤ p.1.1 / 2 then diff else p.1.1 - diff)
      (encPair (encPair encNat encNat) encNat) encNat :=
    ComputableInPolyTime.ite_decide hle hdiff hqsub
  exact ComputableInPolyTime.binary_lt.comp (hq4.prod hbound)

private abbrev DecryptEnv := ((ℕ × ℕ) × List ℕ) × List (List ℕ)

private def decryptEnvEncoding : DecryptEnv ↪ List Bool :=
  encPair (encPair (encPair encUnary encNat) (encList encNat)) (encList (encList encNat))

private def makeDecryptEnv (a : ((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) : DecryptEnv :=
  (((a.1.1.2, a.1.2), a.2.1.getD 0 []), decryptProducts a.1.1.1 a.1.1.2 a.1.2 a.2.1 a.2.2)

private theorem makeDecryptEnv_polyTime :
    ComputableInPolyTime makeDecryptEnv
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair (encList (encList encNat)) (encList encIntBin)))
      decryptEnvEncoding := by
  unfold makeDecryptEnv decryptEnvEncoding
  have hn : ComputableInPolyTime
      (fun a : ((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ => a.1.1.2)
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair (encList (encList encNat)) (encList encIntBin)))
      encUnary := by fun_prop
  have hq : ComputableInPolyTime
      (fun a : ((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ => a.1.2)
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair (encList (encList encNat)) (encList encIntBin)))
      encNat := by fun_prop
  have hrows : ComputableInPolyTime
      (fun a : ((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ => a.2.1)
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair (encList (encList encNat)) (encList encIntBin)))
      (encList (encList encNat)) := by fun_prop
  have hv : ComputableInPolyTime
      (fun a : ((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ => a.2.1.getD 0 [])
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair (encList (encList encNat)) (encList encIntBin)))
      (encList encNat) :=
    (ComputableInPolyTime.listGetD (encA := encList encNat) []).comp
      (hrows.prod (ComputableInPolyTime.const 0))
  have hprods := decryptProducts_polyTime
  exact ((hn.prod hq).prod hv).prod hprods

private def decryptBitsFromEnv (e : DecryptEnv) : List Bool :=
  (List.range e.1.1.1).map fun i =>
    decryptedBit e.1.1.2 (e.1.2.getD i 0) (columnSum e.2 i)

private theorem decryptBitsFromEnv_polyTime :
    ComputableInPolyTime decryptBitsFromEnv decryptEnvEncoding encBits := by
  unfold decryptBitsFromEnv
  apply ComputableInPolyTime.mapToBitsWithInput (enc := encUnary)
  · have hn : ComputableInPolyTime (fun e : DecryptEnv => e.1.1.1)
        decryptEnvEncoding encUnary := by
      unfold decryptEnvEncoding; fun_prop
    exact ComputableInPolyTime.range.comp hn
  · have hbit := decryptedBit_polyTime
    have hcol := columnSum_polyTime
    have hq : ComputableInPolyTime (fun p : DecryptEnv × ℕ => p.1.1.1.2)
        (encPair decryptEnvEncoding encUnary) encNat := by
      unfold decryptEnvEncoding; fun_prop
    have hv : ComputableInPolyTime (fun p : DecryptEnv × ℕ => p.1.1.2)
        (encPair decryptEnvEncoding encUnary) (encList encNat) := by
      unfold decryptEnvEncoding; fun_prop
    have hi : ComputableInPolyTime (fun p : DecryptEnv × ℕ => p.2)
        (encPair decryptEnvEncoding encUnary) encUnary := by fun_prop
    have hvi : ComputableInPolyTime (fun p : DecryptEnv × ℕ => p.1.1.2.getD p.2 0)
        (encPair decryptEnvEncoding encUnary) encNat :=
      (ComputableInPolyTime.listGetD (encA := encNat) 0).comp (hv.prod hi)
    have hprods : ComputableInPolyTime (fun p : DecryptEnv × ℕ => p.1.2)
        (encPair decryptEnvEncoding encUnary) (encList (encList encNat)) := by
      unfold decryptEnvEncoding; fun_prop
    have hsum : ComputableInPolyTime (fun p : DecryptEnv × ℕ => columnSum p.1.2 p.2)
        (encPair decryptEnvEncoding encUnary) encNat :=
      hcol.comp (hprods.prod hi)
    have hbit_in : ComputableInPolyTime (fun p : DecryptEnv × ℕ =>
        ((p.1.1.1.2, p.1.1.2.getD p.2 0), columnSum p.1.2 p.2))
        (encPair decryptEnvEncoding encUnary)
        (encPair (encPair encNat encNat) encNat) :=
      (hq.prod hvi).prod hsum
    have hres := hbit.comp hbit_in
    simpa only [Function.comp_def] using hres

private def decryptBits (k n q : ℕ) (ct_rows : List (List ℕ)) (s_ints : List ℤ) : List Bool :=
  decryptBitsFromEnv (makeDecryptEnv (((k, n), q), ct_rows, s_ints))

private theorem decryptBits_def (k n q : ℕ) (ct_rows : List (List ℕ)) (s_ints : List ℤ) :
    decryptBits k n q ct_rows s_ints =
      (List.range n).map fun i =>
        decryptedBit q ((ct_rows.getD 0 []).getD i 0)
          (columnSum (decryptProducts k n q ct_rows s_ints) i) :=
  rfl

private theorem decryptBits_polyTime :
    ComputableInPolyTime
      (fun a : ((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ =>
        decryptBits a.1.1.1 a.1.1.2 a.1.2 a.2.1 a.2.2)
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair (encList (encList encNat)) (encList encIntBin)))
      encBits := by
  have h := decryptBitsFromEnv_polyTime.comp makeDecryptEnv_polyTime
  simpa only [Function.comp_def, decryptBits] using h

private def decryptWords (a : DecryptInput) : List Bool :=
  decryptBits a.1.1.1 a.1.1.2 a.1.2
    ((Decoder.list (Decoder.list Decoder.nat)).decode a.2.2)
    ((Decoder.list Decoder.intBin).decode a.2.1)

private theorem decryptWords_polyTime :
    ComputableInPolyTime decryptWords decryptInputEncoding encBits := by
  unfold decryptWords
  have hct := (Decoder.list (Decoder.list Decoder.nat)).computableInPolyTime
  have hs := (Decoder.list Decoder.intBin).computableInPolyTime
  have hinput : ComputableInPolyTime
      (fun a : DecryptInput =>
        (a.1, ((Decoder.list (Decoder.list Decoder.nat)).decode a.2.2,
          (Decoder.list Decoder.intBin).decode a.2.1)))
      decryptInputEncoding
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair (encList (encList encNat)) (encList encIntBin))) := by
    unfold decryptInputEncoding
    apply ComputableInPolyTime.prod
    · fun_prop
    · exact (hct.comp (by fun_prop)).prod (hs.comp (by fun_prop))
  have h := decryptBits_polyTime.comp hinput
  exact h

private theorem valMinAbs_natAbs {q : ℕ} (hq : 0 < q) (x : ZMod q) :
    x.valMinAbs.natAbs = if x.val ≤ q / 2 then x.val else q - x.val := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [ZMod.valMinAbs_def_pos]
  split_ifs with h
  · exact Int.natAbs_natCast x.val
  · have heq : ((x.val : ℤ) - q) = - ((q - x.val : ℕ) : ℤ) := by
      have hlt := ZMod.val_lt x
      omega
    rw [heq, Int.natAbs_neg, Int.natAbs_natCast]

private theorem zmod_val_intCast {q : ℕ} (hq : 0 < q) (z : ℤ) :
    (z : ZMod q).val = (z % (q : ℤ)).toNat := by
  let : NeZero q := ⟨hq.ne'⟩
  have hv := congrArg Int.toNat (ZMod.val_intCast (n := q) z)
  simpa only [Int.toNat_natCast] using hv

private theorem decryptSecretCoeffs_ofFn {k n q : ℕ} (hq : 0 < q)
    (s : Fin k → Fin n → ℤ) (j : Fin k) :
    decryptSecretCoeffs n q (List.ofFn (flattenPolyVec s)) j.val =
      List.ofFn fun l : Fin n => (s j l : ZMod q).val := by
  unfold decryptSecretCoeffs
  rw [List.map_range_eq_ofFn]
  congr 1 with l : 1
  have hidx : (finProdFinEquiv (j, l)).val = j.val * n + l.val := by
    simp [finProdFinEquiv, mul_comm, add_comm]
  have hlen : j.val * n + l.val < k * n := by
    rw [← hidx]
    exact (finProdFinEquiv (j, l)).isLt
  have hget : (List.ofFn (flattenPolyVec s)).getD (j.val * n + l.val) 0 = s j l := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [hlen, dite_true]
    have hfin : (⟨j.val * n + l.val, hlen⟩ : Fin (k * n)) = finProdFinEquiv (j, l) := by
      ext
      exact hidx.symm
    rw [hfin, flattenPolyVec_apply]
    rfl
  rw [hget, zmod_val_intCast hq]

private theorem decryptProducts_ofFn {k n q : ℕ} (hq : 0 < q)
    (s : Fin k → Fin n → ℤ) (ct : ModuleLWECiphertext k n q) :
    decryptProducts k n q
      (List.ofFn fun i : Fin (k + 1) => List.ofFn fun j : Fin n => (extendCiphertext ct i j).val)
      (List.ofFn (flattenPolyVec s)) =
      List.ofFn fun j : Fin k => List.ofFn fun l : Fin n =>
        (negacyclicMul (ct.1 j) (fun l => (s j l : ZMod q)) l).val := by
  unfold decryptProducts
  rw [List.map_range_eq_ofFn]
  congr 1 with j : 1
  have hu : (List.ofFn fun i : Fin (k + 1) => List.ofFn fun j : Fin n =>
      (extendCiphertext ct i j).val).getD (j.val + 1) [] =
      List.ofFn fun l : Fin n => (ct.1 j l).val := by
    have hlt : j.val + 1 < k + 1 := Nat.add_lt_add_right j.isLt 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [hlt, dite_true]
    have hsucc : (⟨j.val + 1, hlt⟩ : Fin (k + 1)) = j.succ := by
      ext; rfl
    rw [hsucc]
    rfl
  rw [hu, decryptSecretCoeffs_ofFn hq s j]
  exact negacyclicMulResidues_ofFn hq (ct.1 j) (fun l => (s j l : ZMod q))

private theorem columnSum_decryptProducts_ofFn {k n q : ℕ} (hq : 0 < q)
    (s : Fin k → Fin n → ℤ) (ct : ModuleLWECiphertext k n q) (i : Fin n) :
    ((columnSum (decryptProducts k n q
      (List.ofFn fun i : Fin (k + 1) => List.ofFn fun j : Fin n => (extendCiphertext ct i j).val)
      (List.ofFn (flattenPolyVec s))) i.val : ZMod q)) =
      (innerPoly ct.1 (fun j l => (s j l : ZMod q))) i := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [decryptProducts_ofFn hq s ct]
  unfold columnSum
  simp only [List.map_ofFn, Function.comp_def, List.getD_ofFn]
  rw [List.sum_ofFn]
  push_cast
  simp only [ZMod.natCast_zmod_val]
  unfold innerPoly
  rw [Finset.sum_apply]

private theorem decryptBits_ofFn {k n q : ℕ} (hq : 0 < q)
    (s : Fin k → Fin n → ℤ) (ct : ModuleLWECiphertext k n q) :
    decryptBits k n q
      (List.ofFn fun i : Fin (k + 1) => List.ofFn fun j : Fin n => (extendCiphertext ct i j).val)
      (List.ofFn (flattenPolyVec s)) =
      List.ofFn (moduleLWEDecrypt (fun j i => (s j i : ZMod q)) ct) := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [decryptBits_def]
  rw [List.map_range_eq_ofFn]
  congr 1 with i : 1
  have hv : (List.ofFn fun i : Fin (k + 1) => List.ofFn fun j : Fin n =>
      (extendCiphertext ct i j).val).getD 0 [] =
      List.ofFn fun l : Fin n => (ct.2 l).val := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [Nat.zero_lt_succ, dite_true]
    rfl
  simp only [hv, List.getD_ofFn]
  unfold decryptedBit
  set sum_i := columnSum (decryptProducts k n q
    (List.ofFn fun i : Fin (k + 1) => List.ofFn fun j : Fin n => (extendCiphertext ct i j).val)
    (List.ofFn (flattenPolyVec s))) i.val
  set w := ct.2 - innerPoly ct.1 (fun j l => (s j l : ZMod q))
  have hdiff_cast : ((((ct.2 i).val : ℤ) - (sum_i : ℤ) : ZMod q)) = w i := by
    push_cast
    rw [ZMod.natCast_zmod_val, columnSum_decryptProducts_ofFn hq s ct i]
    rfl
  have hdiff_nat : ((((ct.2 i).val : ℤ) - (sum_i : ℤ)) % (q : ℤ)).toNat = (w i).val := by
    rw [← zmod_val_intCast hq, Int.cast_sub, hdiff_cast]
  dsimp only
  rw [hdiff_nat]
  rw [← valMinAbs_natAbs hq (w i)]
  rfl

private theorem decryptWords_encode {k n q : ℕ} (hq : 0 < q)
    (s : Fin k → Fin n → ℤ) (ct : ModuleLWECiphertext k n q) :
    decryptWords (((k, n), q), (ModuleSIS.encodeVec s,
      GeneralSIS.encodeMatrix (extendCiphertext ct))) =
      List.ofFn (moduleLWEDecrypt (fun j i => (s j i : ZMod q)) ct) := by
  simp only [decryptWords, ModuleSIS.encodeVec, GeneralSIS.encodeMatrix,
    GeneralSIS.encodeVec, Decoder.decode_enc]
  exact decryptBits_ofFn hq s ct

/-- A single total native function realizes existing deterministic Module-LWE decryption
over unary rank/degree, binary modulus and complete existing secret/ciphertext words,
agreeing with `moduleLWEDecrypt` on canonical inputs. -/
theorem exists_computableInPolyTime_moduleLWEDecrypt :
    ∃ run : (((ℕ × ℕ) × ℕ) × List Bool × List Bool) → List Bool,
      ComputableInPolyTime run
        (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair encBits encBits)) encBits ∧
      ∀ (k n q : ℕ) (_hq : 0 < q)
        (s : Fin k → Fin n → ℤ)
        (ct : ModuleLWECiphertext k n q),
        run (((k, n), q), (ModuleSIS.encodeVec s,
          GeneralSIS.encodeMatrix (extendCiphertext ct))) =
          List.ofFn (moduleLWEDecrypt (fun j i => (s j i : ZMod q)) ct) :=
  ⟨decryptWords, decryptWords_polyTime, fun _ _ _ hq s ct => decryptWords_encode hq s ct⟩

/-! ### Total execution on off-canonical, zero-modulus and malformed inputs -/

/-- At modulus zero, the total runtime function remains defined, producing `false` for every
output bit without asserting quotient-ring semantics. -/
example : decryptWords (((1, 2), 0), ([], [])) = [false, false] := by
  simp only [decryptWords, Decoder.list, frames_nil, List.map_nil]
  decide

/-- Empty ciphertext and secret words are total: missing rows and coefficients pad with default
values, yielding a total boolean list of length `n`. -/
example : decryptWords (((2, 3), 29), ([], [])) = [false, false, false] := by
  simp only [decryptWords, Decoder.list, frames_nil, List.map_nil]
  decide

/-- Excess rows and secret entries are ignored while charging complete input length: a secret
list with 4 entries when only `k * n = 2` are needed, and a ciphertext matrix with 3 rows when
only `k + 1 = 2` are needed. -/
example :
    decryptWords (((1, 2), 29),
      (encList encIntBin [1, -1, 5, 10],
        encList (encList encNat) [[7, 8], [3, 4], [99, 100]])) =
      [false, false] := by
  simp only [decryptWords, Decoder.decode_enc]
  decide

/-- Incomplete framing and malformed words do not crash: raw bitstreams with irregular frame
delimiters decode via total fallbacks and produce valid output lists of length `n`. -/
example : (frames [true]).map decodeIntBin = [0] := by
  simp [frames, unframe, dropFrame, decodeIntBin, Decoder.nat, ofBits]

example :
    decryptWords (((1, 2), 29), ([true], [true])) = [false, false] := by
  have hf : frames [true] = [[]] := by
    rw [frames_of_ne_nil (by decide)]
    simp [unframe, dropFrame]
  have hs : (Decoder.list Decoder.intBin).decode [true] = [0] := by
    simp [Decoder.list, Decoder.intBin, hf, decodeIntBin, Decoder.nat, ofBits]
  have hct : (Decoder.list (Decoder.list Decoder.nat)).decode [true] = [[]] := by
    simp [Decoder.list, hf]
  simp only [decryptWords, hs, hct]
  decide

end Cslib.Crypto
