/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.GenericRAM.Native.IndexFold
public import Complexity.Foundations.Data.Nat.Radix.Measurement
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPower
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeRadix
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Mathlib.Data.Int.Basic

/-!
# Streaming signed measurement values

The dimension is a runtime unary natural and the radius a runtime binary natural. The decoder
uses the existing radix digits to produce ordinary signed integer lists. Count preparation and
individual visits are polynomial in their full encoded input, even though the number of visits
need not be. All coordinates remain present at radius zero; dimension zero has one empty tuple.

Only the current binary index, full parameters and captured accumulator persist. The decoder
may use polynomial scratch (including a dimension-length range), but never constructs the whole
measurement box. Index/box lists in the ordered-fold specification are not used by the native
loop. The generic callback may grow its accumulator: polynomial whole-loop workspace requires an
actual all-prefix accumulator invariant, not just a polynomial per-visit certificate.

This is the measurement-VALUE enumeration of [OpenAI2026ETH], Lemma 3.2 and Proposition 3.4
(pp. 22–26). It is not formal mode-exponent enumeration, subset-pair
traversal, rational coefficient accumulation or a complete runtime/ETH result.
-/

@[expose] public section
namespace Cslib.GenericRAM.MeasurementFold

open Turing.MultiTapeTM

/-- The actual number of signed measurement tuples in dimension `c` and radius `D`. -/
def count (p : ℕ × ℕ) : ℕ := (2 * p.2 + 1) ^ p.1

private theorem radix_polyTime :
    ComputableInPolyTime (fun D : ℕ => 2 * D + 1) encNat encNat := by
  have hbits : ComputableInPolyTime Nat.bits encNat encBits :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have h := ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true) hbits
  apply h.of_enc_eq
  intro D
  change (2 * D + 1).bits = true :: D.bits
  exact Nat.bit1_bits D

/-- Prepare the visit count in binary, charging the unary dimension and binary radius. -/
theorem count_polyTime : ComputableInPolyTime count (encPair encUnary encNat) encNat := by
  exact ComputableInPolyTime.binary_pow.comp
    ((radix_polyTime.comp (ComputableInPolyTime.snd encUnary encNat)).prod
      (ComputableInPolyTime.fst encUnary encNat))

/-- An actual fixed native count-preparation machine; no unary exponential count is produced. -/
noncomputable def clock : NativeCertificate count (encPair encUnary encNat) encNat :=
  NativeCertificate.ofPolyTime count_polyTime

/-- Both preparation bounds are polynomial in the complete runtime pair encoding. -/
theorem clock_isPolynomial : clock.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial count_polyTime

/-- The binary count has polynomial bit length, rather than polynomial numeric value. -/
theorem length_count_le (c D : ℕ) :
    (encNat (count (c, D))).length ≤ c * (D.size + 1) + 1 := by
  change ((2 * D + 1) ^ c).bits.length ≤ _
  rw [Nat.size_eq_bits_len]
  have hb := Nat.size_bit (b := true) (n := D) (by simp [Nat.bit])
  simp only [Nat.bit_val, Bool.toNat_true, Nat.succ_eq_add_one] at hb
  simpa only [hb] using Nat.size_pow_le (2 * D + 1) c

/-- Decode the actual signed measurement values with unary dimension and binary radius/index.
No fitting-index hypothesis is needed for this total polynomial-time decoder. -/
theorem decoder_polyTime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ =>
      Cslib.Radix.measurementValues p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encNat) encNat) (encList encIntBin) := by
  let ei := encPair (encPair encUnary encNat) encNat
  have hp := ComputableInPolyTime.fst (encPair encUnary encNat) encNat
  have hc := (ComputableInPolyTime.fst encUnary encNat).comp hp
  have hd := (ComputableInPolyTime.snd encUnary encNat).comp hp
  have hj := ComputableInPolyTime.snd (encPair encUnary encNat) encNat
  have ho := ComputableInPolyTime.fst ei encUnary
  have hi := ComputableInPolyTime.snd ei encUnary
  have hbase := (radix_polyTime.comp hd).comp ho
  have hval := ComputableInPolyTime.radix_digit.comp ((hbase.prod (hj.comp ho)).prod hi)
  have hshift := ComputableInPolyTime.intBin_subNatNat.comp (hval.prod (hd.comp ho))
  have hm := ComputableInPolyTime.mapWithInput
    (f := fun (p : (ℕ × ℕ) × ℕ) (i : ℕ) =>
      Int.subNatNat (Cslib.Radix.digit (2 * p.1.2 + 1) p.2 i) p.1.2)
    (ComputableInPolyTime.range.comp hc) hshift
  convert hm using 1
  funext p
  simp only [Cslib.Radix.measurementValues, Int.subNatNat_eq_coe, Function.comp_def]

/-- The fixed signed-tuple decoder has an actual polynomial native implementation. -/
noncomputable def decoder :
    NativeCertificate (fun p : (ℕ × ℕ) × ℕ => Cslib.Radix.measurementValues p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encNat) encNat) (encList encIntBin) :=
  NativeCertificate.ofPolyTime decoder_polyTime

/-- The two selected decoder bounds are polynomial in its complete encoded runtime input. -/
theorem decoder_isPolynomial : decoder.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial decoder_polyTime

/-- The tuple code is polynomial in dimension and binary radius length, not in radius value. -/
theorem length_values_le (c D j : ℕ) :
    (encList encIntBin (Cslib.Radix.measurementValues c D j)).length ≤
      c * (2 * (D.size + 1) + 1) := by
  have h := length_encList_le encIntBin (Cslib.Radix.measurementValues c D j)
    (b := D.size + 1) (by
      intro z hz
      have hr := Cslib.Radix.measurementValues_bounds c D j z hz
      have ha : (z.natAbs : ℤ) ≤ D := by
        rw [Int.natCast_natAbs]
        exact abs_le.mpr hr
      have hs := Nat.size_le_size (Int.ofNat_le.mp ha)
      rw [length_encIntBin]
      omega)
  simpa only [Cslib.Radix.length_measurementValues] using h

variable {β : Type}

/-- Decode the current index while retaining the full runtime parameters outside the user body. -/
def visit (body : ((ℕ × ℕ) × List ℤ) × β → β) (p : ℕ × ((ℕ × ℕ) × β)) : (ℕ × ℕ) × β :=
  (p.2.1, body ((p.2.1, Cslib.Radix.measurementValues p.2.1.1 p.2.1.2 p.1), p.2.2))

/-- A streaming prefix stores only the binary index, complete parameters and captured state. -/
def runPrefix (body : ((ℕ × ℕ) × List ℤ) × β → β) (p : ℕ × ℕ) (j : ℕ) (initial : β) :
    ℕ × ((ℕ × ℕ) × β) := IndexFold.run (visit body) j (p, initial)

/-- Traverse the signed measurement-value box by increasing binary index. -/
def run (body : ((ℕ × ℕ) × List ℤ) × β → β) (p : ℕ × ℕ) (initial : β) : ℕ × ((ℕ × ℕ) × β) :=
  runPrefix body p (count p) initial

/-- Neither dimension nor radius can be overwritten by the callback. -/
@[simp] theorem prefix_parameters (body : ((ℕ × ℕ) × List ℤ) × β → β)
    (p : ℕ × ℕ) (j : ℕ) (initial : β) : (runPrefix body p j initial).2.1 = p := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (IndexFold.run (visit body) (j + 1) (p, initial)).2.1 = p
    rw [IndexFold.run_succ]
    exact ih

/-- All prefixes follow the increasing-index order, with full parameters and captured state. -/
theorem prefix_accumulator (body : ((ℕ × ℕ) × List ℤ) × β → β)
    (p : ℕ × ℕ) (j : ℕ) (initial : β) :
    (runPrefix body p j initial).2.2 = (List.range j).foldl
      (fun acc i => body ((p, Cslib.Radix.measurementValues p.1 p.2 i), acc)) initial := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (IndexFold.run (visit body) (j + 1) (p, initial)).2.2 = _
    rw [IndexFold.run_succ]
    change body (((runPrefix body p j initial).2.1,
      Cslib.Radix.measurementValues (runPrefix body p j initial).2.1.1
        (runPrefix body p j initial).2.1.2 (runPrefix body p j initial).1),
      (runPrefix body p j initial).2.2) = _
    rw [prefix_parameters,
      show (runPrefix body p j initial).1 = j from IndexFold.run_index _ _ _, ih]
    simp [List.range_succ, List.foldl_append]

/-- Exact ordered-fold specification. With `measurementValues_coverage`, every fitting signed
word is visited once. The materialized index/word lists occur only in this specification. -/
theorem run_accumulator (body : ((ℕ × ℕ) × List ℤ) × β → β) (p : ℕ × ℕ) (initial : β) :
    (run body p initial).2.2 =
      ((List.range (count p)).map (Cslib.Radix.measurementValues p.1 p.2)).foldl
        (fun acc word => body ((p, word), acc)) initial := by
  rw [run, prefix_accumulator]
  exact (List.foldl_map (f := Cslib.Radix.measurementValues p.1 p.2)
    (g := fun acc word => body ((p, word), acc))
    (l := List.range (count p)) (init := initial)).symm

variable {encB : β ↪ List Bool}

/-- Full encoded persistent-state bound under the actual prefix accumulator bound. It includes
both retained parameters and the final binary counter, including at base one/dimension zero. -/
theorem length_prefix_le (body : ((ℕ × ℕ) × List ℤ) × β → β)
    (c D j B : ℕ) (initial : β) (hj : j ≤ count (c, D))
    (hB : (encB (runPrefix body (c, D) j initial).2.2).length ≤ B) :
    (encPair encNat (encPair (encPair encUnary encNat) encB)
      (runPrefix body (c, D) j initial)).length ≤
      2 * (c * (D.size + 1) + 1) + 4 * c + 2 * D.size + 4 + B := by
  have hs : (encPair (encPair encUnary encNat) encB
      (runPrefix body (c, D) j initial).2).length ≤
      2 * (encPair encUnary encNat (c, D)).length + 1 + B := by
    rw [length_encPair, prefix_parameters]
    omega
  have hi := IndexFold.length_run_le (visit body) ((c, D), initial) hj hs
  have hp : (encPair encUnary encNat (c, D)).length = 2 * c + 1 + D.size := by
    simp [Nat.size_eq_bits_len]
  have hn := length_count_le c D
  rw [hp] at hi
  exact hi.trans (by omega)

/-- Preparing a callback charges both parameters, every signed coordinate and the full captured
accumulator. This bound is about the encoded input, not uncharged machine scratch. -/
theorem length_callback_input_le (c D j : ℕ) (acc : β) :
    (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encB
      (((c, D), Cslib.Radix.measurementValues c D j), acc)).length ≤
      4 * (2 * c + 1 + D.size) + 2 * (c * (2 * (D.size + 1) + 1)) + 3 +
        (encB acc).length := by
  simp only [length_encPair, encUnary_apply, List.length_replicate]
  have hd : (encNat D).length = D.size := by simp [Nat.size_eq_bits_len]
  rw [hd]
  have ht := length_values_le c D j
  omega

/-- Prepare the complete runtime parameter/tuple/captured-state input to the callback. -/
theorem prepare_polyTime :
    ComputableInPolyTime (fun p : ℕ × ((ℕ × ℕ) × β) =>
      ((p.2.1, Cslib.Radix.measurementValues p.2.1.1 p.2.1.2 p.1), p.2.2))
      (encPair encNat (encPair (encPair encUnary encNat) encB))
      (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encB) := by
  have hs := ComputableInPolyTime.snd encNat (encPair (encPair encUnary encNat) encB)
  have hp := (ComputableInPolyTime.fst (encPair encUnary encNat) encB).comp hs
  have hi := ComputableInPolyTime.fst encNat (encPair (encPair encUnary encNat) encB)
  exact (hp.prod (decoder_polyTime.comp (hp.prod hi))).prod
    ((ComputableInPolyTime.snd (encPair encUnary encNat) encB).comp hs)

/-- The actual captured callback uses the proved direct decoder, retaining both parameters. -/
noncomputable def visitCertificate {body : ((ℕ × ℕ) × List ℤ) × β → β}
    (cb : NativeCertificate body
      (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encB) encB) :
    NativeCertificate (visit body)
      (encPair encNat (encPair (encPair encUnary encNat) encB))
      (encPair (encPair encUnary encNat) encB) :=
  (NativeCertificate.linear ((ComputableInO.fst (encPair encUnary encNat) encB).comp_linear
    (ComputableInO.snd encNat (encPair (encPair encUnary encNat) encB)))).prod
      (cb.comp (NativeCertificate.ofPolyTime prepare_polyTime))

/-- Polynomial per-visit bounds are derived from the actual callback and decoder machines. -/
theorem visitCertificate_isPolynomial {body : ((ℕ × ℕ) × List ℤ) × β → β}
    (cb : NativeCertificate body
      (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encB) encB)
    (hcb : cb.IsPolynomial) : (visitCertificate cb).IsPolynomial := by
  apply NativeCertificate.prod_isPolynomial
  · exact NativeCertificate.linear_isPolynomial _
  · exact NativeCertificate.comp_isPolynomial cb _ hcb
      (NativeCertificate.ofPolyTime_isPolynomial prepare_polyTime)

/-- One fixed native machine streams all measurement values. Count preparation is charged,
time retains the visit-count factor, and workspace uses the existing all-prefix maxima.
No whole-loop polynomial-time bound or polynomial accumulator invariant is assumed. -/
noncomputable def certificate {α : Type} {encIn : α ↪ List Bool}
    {parameters : α → ℕ × ℕ} {initial : α → β} {body : ((ℕ × ℕ) × List ℤ) × β → β}
    (cp : NativeCertificate parameters encIn (encPair encUnary encNat))
    (ci : NativeCertificate initial encIn encB)
    (cb : NativeCertificate body
      (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encB) encB) :
    NativeCertificate (fun a => run body (parameters a) (initial a))
      encIn (encPair encNat (encPair (encPair encUnary encNat) encB)) :=
  IndexFold.certificate (clock.comp cp) (cp.prod ci) (visitCertificate cb)

end Cslib.GenericRAM.MeasurementFold
