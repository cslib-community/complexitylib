/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.SIS.ModuleEncryption
public import Complexity.Computability.PolyTime.Int.DotProduct
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.ZMod.DotProduct
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Native realization of existing Module-LWE key generation

One total word implementation realizes `moduleLWEKeyGen` in the existing
`ModuleLWE.encodeSample` codec. Both dimensions are unary runtime inputs; the modulus and
coefficients are binary. The input matrix is the existing expanded structured rotation-block
encoding, not a seed or an independently sampled scalar matrix. Runtime charges all input words,
including discarded data. Canonical interpretation requires a positive modulus.

## Main results

* `exists_computableInPolyTime_moduleLWEKeyGen`: a single native implementation for all
  dimensions, positive moduli, structured matrices and signed integer secret/error lifts.

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

private def decodeSignedList (w : List Bool) : List ℤ :=
  (frames w).map decodeIntBin

private theorem decodeSignedList_encode (l : List ℤ) :
    decodeSignedList (encList encIntBin l) = l := by
  simp only [decodeSignedList, frames_encList, List.map_map, Function.comp_def,
    decodeIntBin_encIntBin]
  exact List.map_id l

private theorem decodeSignedList_polyTime :
    ComputableInPolyTime decodeSignedList encBits (encList encIntBin) :=
  (ComputableInPolyTime.map computableInPolyTime_decodeIntBin).comp
    computableInDegree_frames.computableInPolyTime

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
      (decodeSignedList a.2.2.1) (decodeSignedList a.2.2.2))

private theorem keyGenWords_polyTime :
    ComputableInPolyTime keyGenWords keyGenInputEncoding encBits := by
  have hrows := (Decoder.list (Decoder.list Decoder.nat)).computableInPolyTime
  have hdecode := decodeSignedList_polyTime
  have hcoeff := keyGenCoefficients_polyTime
  have hinput : ComputableInPolyTime
      (fun a : KeyGenInput => (((a.1.1.1 * a.1.1.2), a.1.2),
        ((Decoder.list (Decoder.list Decoder.nat)).decode a.2.1,
          decodeSignedList a.2.2.1, decodeSignedList a.2.2.2)))
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
  congr 1
  funext i
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
    GeneralSIS.encodeMatrix, GeneralSIS.encodeVec, Decoder.decode_enc,
    decodeSignedList_encode]
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

end Cslib.Crypto
