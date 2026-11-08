/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORSortedRecords
public import Complexity.Cryptanalysis.AddXNORDecision
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.StreamingFlatMap
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import all Complexity.Cryptanalysis.AddXNORSortedRecords
import all Complexity.Cryptanalysis.AddXNORNativeEnumeration
import all Complexity.Cryptanalysis.AddXNORNativeBuckets
import all Complexity.Computability.GenericRAM.Native.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists

/-!
# Uniform original-operand generation and sorting of quarter states

This executable route receives unary width, binary seed and original-order
binary operands. It generates every packed operator index by real streaming
doubling, evaluates the original chain for each index, and runs the uniform
radix sorter. No materialized quarter list or simulator is supplied as input.
It bypasses sparse association-list interpreter dispatch for these stages.

This integrates the quarter-list construction of [WangLvShenZhang2027],
Lemma 8, PDF pp. 21–22. Complete class counting/matching, smaller-side retention,
release/reuse and original-input dissection resource composition remain separate.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.SortedQuarterMachine
open Turing.MultiTapeTM Cslib.GenericRAM

/-- One streaming generation round, with binary indices and no growing inner accumulator. -/
def double (rows : List ℕ) : List ℕ := rows.flatMap (fun u => [2 * u, 2 * u + 1])

/-- The runtime quarter length controls a fixed binary-counted generation loop. -/
def indices (k : ℕ) : List ℕ := double^[k] [0]

private theorem double_range (n : ℕ) : double (List.range n) = List.range (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [double, List.range_succ, List.flatMap_append, List.flatMap_singleton] at *
    rw [ih]
    have heq : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [heq, List.range_succ, List.range_succ]
    simp

/-- Every packed index is generated exactly once, including all leading-zero operators. -/
theorem indices_eq_range (k : ℕ) : indices k = List.range (2 ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [indices, Function.iterate_succ_apply']
    change double (indices k) = _
    rw [ih, double_range, Nat.pow_succ, Nat.mul_comm 2]

private theorem double_computable :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ComputableInO double (encList encNat) (encList encNat)
        (fun rows => 3 * (encList encNat rows).length + 1 +
          (rows.length + 1) * P (streamRecordLength encNat rows + 1))
        (fun rows => 3 * (encList encNat rows).length + 1 +
          (rows.length + 1) * P (streamRecordLength encNat rows + 1)) := by
  have hcallback : ComputableInPolyTime (fun q : ℕ × ℕ => [2 * q.2, 2 * q.2 + 1])
      (encPair encNat encNat) (encList encNat) := by
    apply ComputableInPolyTime.of_tidy
    fun_prop
  obtain ⟨P, hp, hm, hc⟩ := ComputableInO.flatMap_stream hcallback
  have arg : ComputableInO (fun rows : List ℕ => (0, rows)) (encList encNat)
      (encPair encNat (encList encNat))
      (fun rows => 2 * (encList encNat rows).length)
      (fun rows => 2 * (encList encNat rows).length) := by
    have h := (ComputableInO.const (encIn := encList encNat) (encMid := encNat) 0).prod
      (ComputableInO.of_eq (encIn := encList encNat) (encMid := encList encNat) (fun _ => rfl))
    convert h using 1 <;> (funext rows; omega)
  refine ⟨P, hp, hm, ?_⟩
  have result := (hc.comp arg).of_enc_eq (g := double)
    (encC := encList encNat) (fun _ => rfl)
  convert result using 1 <;>
    (funext rows; simp only [streamFilterWidth, length_encPair, encNat_apply,
      Nat.zero_bits, List.length_nil, Nat.zero_add]; omega)

/-- Actual binary-wire bounds for every generated prefix; these are derived from enumeration. -/
theorem indices_wire (k : ℕ) :
    (indices k).length = 2 ^ k ∧ streamRecordLength encNat (indices k) ≤ k ∧
      (encList encNat (indices k)).length ≤ 2 ^ k * (2 * k + 1) := by
  have size : ∀ u ∈ indices k, (encNat u).length ≤ k := by
    intro u hu
    rw [indices_eq_range, List.mem_range] at hu
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr hu
  have hlen : (indices k).length = 2 ^ k := by rw [indices_eq_range, List.length_range]
  exact ⟨hlen, listMax_le size, by
    simpa only [hlen] using length_encList_le encNat (indices k) size⟩

/-- A uniform generated-index machine with actual all-prefix bounds. Exponential generation
is charged by its output count, with only polynomial unary-length overhead. -/
theorem indices_computable :
    ∃ Q : ℕ → ℕ, Cslib.PolynomiallyBounded Q ∧ Monotone Q ∧
      ComputableInO indices encUnary (encList encNat)
        (fun k => (k + 1) * 2 ^ k * Q (k + 1))
        (fun k => 2 ^ k * Q (k + 1)) := by
  obtain ⟨P, hp, hm, hc⟩ := double_computable
  let step : NativeCertificate double (encList encNat) (encList encNat) :=
    ⟨_, _, hc⟩
  let clock := NativeCertificate.ofPolyTime ComputableInPolyTime.unary_to_binary
  obtain ⟨R, hr, hrm, hrc⟩ := exists_mono_poly_cert ComputableInPolyTime.unary_to_binary
  let initial : NativeCertificate (fun _ : ℕ => [0]) encUnary (encList encNat) :=
    NativeCertificate.const [0]
  let loop := NativeCertificate.iterate clock initial step
  let Q : ℕ → ℕ := fun B => 20 * (P B + R B + (B + 1) ^ 2 + 1)
  have hQ : Cslib.PolynomiallyBounded Q := by dsimp only [Q]; fun_prop
  have hmQ : Monotone Q := fun a b hab => by
    have := hm hab
    have := hrm hab
    have := Nat.pow_le_pow_left (Nat.add_le_add_right hab 1) 2
    dsimp only [Q]
    omega
  refine ⟨Q, hQ, hmQ, loop.computes.mono 4 ?_ ?_⟩
  all_goals intro k
  all_goals
    let E := 2 ^ k
    let H := E * (2 * k + 1)
    have hE : 1 ≤ E := Nat.two_pow_pos k
    have ht := (hrc k).1.trans (hrm (show (encUnary k).length ≤ k + 1 by
      simp only [encUnary_apply, List.length_replicate]; omega))
    have hs := (hrc k).2.trans (hrm (show (encUnary k).length ≤ k + 1 by
      simp only [encUnary_apply, List.length_replicate]; omega))
    change clock.time k ≤ R (k + 1) at ht
    change clock.space k ≤ R (k + 1) at hs
    have hj (j : ℕ) (hjk : j ≤ k) :
        (encList encNat (double^[j] [0])).length ≤ H ∧
        (double^[j] [0]).length ≤ E ∧
        P (streamRecordLength encNat (double^[j] [0]) + 1) ≤ P (k + 1) := by
      change (encList encNat (indices j)).length ≤ H ∧
        (indices j).length ≤ E ∧ P (streamRecordLength encNat (indices j) + 1) ≤ P (k + 1)
      obtain ⟨hlen, hmax, hwire⟩ := indices_wire j
      have hpow : 2 ^ j ≤ E := Nat.pow_le_pow_right (by decide) hjk
      refine ⟨hwire.trans (Nat.mul_le_mul hpow (by omega)), ?_, ?_⟩
      · exact hlen.le.trans hpow
      · exact hm (by omega)
    have hround : NativeCertificate.maxRoundTime step k [0] ≤
        3 * H + 1 + (E + 1) * P (k + 1) := by
      apply NativeCertificate.maxRoundTime_le
      intro j hjk
      obtain ⟨hw, hn, hm'⟩ := hj j hjk
      have hmul := Nat.mul_le_mul (Nat.add_le_add_right hn 1) hm'
      dsimp only [step]
      omega
    have hspace : NativeCertificate.maxRoundSpace step k [0] ≤
        3 * H + 1 + (E + 1) * P (k + 1) := hround
    have hstate : NativeCertificate.maxStateLength (encList encNat) double k [0] ≤ H :=
      NativeCertificate.maxStateLength_le _ _ _ _ (fun j hjk => (hj j hjk).1)
    have hclock : (encNat k).length ≤ k := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using
        (Nat.size_le.mpr Nat.lt_two_pow_self : k.size ≤ k)
    have hclock2 := Nat.pow_le_pow_left (Nat.add_le_add_right hclock 1) 2
    have hP : E * P (k + 1) ≤ E * (P (k + 1) + R (k + 1) + (k + 2) ^ 2 + 1) :=
      Nat.mul_le_mul_left E (by omega)
    have hR : R (k + 1) ≤ E * R (k + 1) := by nlinarith
    have hsmall : k + 1 ≤ E * (k + 2) ^ 2 := by nlinarith
  · change clock.time k + (encUnary k).length +
      (k + 1) * (NativeCertificate.maxRoundTime step k [0] +
        NativeCertificate.maxStateLength (encList encNat) double k [0] +
        ((encNat k).length + 1) ^ 2) ≤ 4 * ((k + 1) * E * Q (k + 1) + 1)
    simp only [encUnary_apply, List.length_replicate]
    have hb : NativeCertificate.maxRoundTime step k [0] +
        NativeCertificate.maxStateLength (encList encNat) double k [0] +
        ((encNat k).length + 1) ^ 2 ≤ E * Q (k + 1) := by
      have hEP := Nat.mul_le_mul_left (P (k + 1)) hE
      dsimp only [Q, H] at *
      nlinarith
    have hmul := Nat.mul_le_mul_left (k + 1) hb
    have hQR : E * R (k + 1) ≤ E * Q (k + 1) := by
      apply Nat.mul_le_mul_left
      dsimp only [Q]
      omega
    have hqSmall : (k + 2) ^ 2 ≤ Q (k + 1) := by dsimp only [Q]; nlinarith
    have hkq := hsmall.trans (Nat.mul_le_mul_left E hqSmall)
    nlinarith
  · change clock.space k + (encUnary k).length +
      NativeCertificate.maxRoundSpace step k [0] +
        NativeCertificate.maxStateLength (encList encNat) double k [0] + (encNat k).length ≤
          4 * (E * Q (k + 1) + 1)
    simp only [encUnary_apply, List.length_replicate]
    have hEP := Nat.mul_le_mul_left (P (k + 1)) hE
    dsimp only [Q, H] at *
    nlinarith

/-- Unary width, binary seed and original-order binary quarter operands. -/
abbrev Input := (ℕ × ℕ) × List ℕ

/-- All original data are charged; there is no enumerated-list input advice. -/
def encoding : Input ↪ List Bool := encPair (encPair encUnary encNat) (encList encNat)

/-- One polynomial-size packed word is decoded before evaluating the original operands. -/
def record (input : Input) (u : ℕ) : ℕ × ℕ :=
  let ((width, seed), operands) := input
  (natEval width ((Native.Quarter.decode operands.length u).zip operands) seed, u)

/-- Generate the indexed records from the actual input and then sort their full-width state. -/
def run (input : Input) : List (ℕ × ℕ) :=
  let ((width, _), operands) := input
  RadixSort.sort (width, (indices operands.length).map (record input))

private theorem decode_bits (k u : ℕ) :
    Native.Quarter.decode k u = (List.range k).map u.testBit := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
    rw [Native.Quarter.decode, List.range_succ_eq_map, List.map_cons, ih, List.map_map]
    congr 1
    · simp [Nat.testBit_eq_decide_div_mod_eq]
    · apply List.map_congr_left
      intro j _
      exact Nat.testBit_div_two u j

/-- Real packed-bit decoding, uniformly in unary length and binary word. -/
theorem decode_polyTime : ComputableInPolyTime
    (fun input : ℕ × ℕ => Native.Quarter.decode input.1 input.2)
    (encPair encUnary encNat) (encList encBool) := by
  have hlist := ComputableTidilyInPolyTime.range.comp
    (ComputableTidilyInPolyTime.fst encUnary encNat)
  have hbit : ComputableTidilyInPolyTime
      (fun q : (ℕ × ℕ) × ℕ => q.1.2.testBit q.2)
      (encPair (encPair encUnary encNat) encUnary) encBool := by
    apply ComputableTidilyInPolyTime.binary_testBit <;> fun_prop
  simpa only [Function.comp_def, decode_bits] using
    ComputableInPolyTime.of_tidy (hlist.mapWithInput hbit)

/-- All arithmetic, original operand reading, packed decoding and state evaluation are executed. -/
theorem record_value_polyTime : ComputableInPolyTime
    (fun q : Input × ℕ => record q.1 q.2) (encPair encoding encNat)
    RadixPartition.recordEncoding := by
  have hwidth : ComputableInPolyTime (fun q : Input × ℕ => q.1.1.1)
      (encPair encoding encNat) encUnary := by dsimp only [encoding]; fun_prop
  have hseed : ComputableInPolyTime (fun q : Input × ℕ => q.1.1.2)
      (encPair encoding encNat) encNat := by dsimp only [encoding]; fun_prop
  have hoperands : ComputableInPolyTime (fun q : Input × ℕ => q.1.2)
      (encPair encoding encNat) (encList encNat) := by dsimp only [encoding]; fun_prop
  have hcount := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.length_list encNat).comp hoperands.tidy)
  have hindex := ComputableInPolyTime.snd encoding encNat
  have hbits := decode_polyTime.comp (hcount.prod hindex)
  have hzip := (ComputableInPolyTime.zip encBool encNat).comp (hbits.prod hoperands)
  have heval := natEval_polyTime.comp ((hwidth.prod hseed).prod hzip)
  simpa only [record, Function.comp_def, RadixPartition.recordEncoding] using
    heval.prod hindex

/-- A record is materialized and emitted as one framed list element. -/
theorem record_polyTime : ComputableInPolyTime
    (fun q : Input × ℕ => [record q.1 q.2]) (encPair encoding encNat)
    (encList RadixPartition.recordEncoding) := by
  have singleton : ComputableTidilyInPolyTime (fun row : ℕ × ℕ => [row])
      RadixPartition.recordEncoding (encList RadixPartition.recordEncoding) :=
    .of_linear (.of_frame (fun _ => by simp))
  exact ComputableInPolyTime.of_tidy (singleton.comp record_value_polyTime.tidy)

/-- Every emitted record computes the original packed-index chain, not a supplied state. -/
theorem record_toNat {m : ℕ} (as : List (BitVec m)) (s : BitVec m) (u : ℕ) :
    record ((m, s.toNat), as.map BitVec.toNat) u =
      ((eval ((Native.Quarter.decode as.length u).zip as) s).toNat, u) := by
  simp only [record, List.length_map]
  have hz : (Native.Quarter.decode as.length u).zip (as.map BitVec.toNat) =
      ((Native.Quarter.decode as.length u).zip as).map (fun q => (q.1, q.2.toNat)) := by
    rw [List.zip_map_right]
    rfl
  rw [hz, natEval_toNat]

/-- Generation matches the approved original-quarter observer exactly, before sorting. -/
theorem generated_records {m : ℕ} (as : List (BitVec m)) (s : BitVec m) :
    (indices as.length).map (record ((m, s.toNat), as.map BitVec.toNat)) =
      SortedRecords.projectedQuarter m as s := by
  rw [indices_eq_range]
  apply List.map_congr_left
  intro u _
  rw [record_toNat]
  simp only [Native.Quarter.indexedState, Nat.mod_eq_of_lt
    (eval ((Native.Quarter.decode as.length u).zip as) s).isLt]

/-- The operand-to-sorted-quarter route is exhaustive and returns actual original witnesses.
No generated-list, record semantics, execution, traversal or sortedness conclusion is a premise. -/
theorem correct {m : ℕ} (as : List (BitVec m)) (s : BitVec m) :
    let sorted := run ((m, s.toNat), as.map BitVec.toNat)
    sorted.Perm (SortedRecords.projectedQuarter m as s) ∧
      sorted.Pairwise (fun a b => a.1 ≤ b.1) ∧
      ∀ r, r ∈ sorted ↔ r.2 < 2 ^ as.length ∧
        r.1 = (eval ((Native.Quarter.decode as.length r.2).zip as) s).toNat := by
  have hr : run ((m, s.toNat), as.map BitVec.toNat) =
      RadixSort.sort (m, SortedRecords.projectedQuarter m as s) := by
    simp only [run, List.length_map, generated_records]
  rw [hr]
  simpa only [Nat.mod_eq_of_lt (eval ((Native.Quarter.decode as.length _).zip as) s).isLt]
    using SortedRecords.projectedQuarter_correct m as s

private theorem eval_wire (m : ℕ) (xs : List (Bool × ℕ)) (s : ℕ) :
    (encNat (natEval m xs s)).length ≤ max (encNat s).length m := by
  induction xs generalizing s with
  | nil => simp [natEval]
  | cons op xs ih =>
    have stepwire : (encNat (natStep m s op)).length ≤ m := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using
        Nat.size_le.mpr (natStep_lt m s op)
    exact (ih (natStep m s op)).trans
      ((max_le stepwire (Nat.le_refl m)).trans (Nat.le_max_right _ _))

private theorem input_fields (input : Input) :
    input.1.1 + (encNat input.1.2).length + input.2.length ≤ (encoding input).length := by
  have h := length_le_length_encList encNat input.2
  simp only [encoding, length_encPair, encUnary_apply, List.length_replicate]
  omega

private theorem records_wire (input : Input) :
    let rows := (indices input.2.length).map (record input)
    rows.length = 2 ^ input.2.length ∧
      streamRecordLength RadixPartition.recordEncoding rows ≤ 3 * (encoding input).length + 1 ∧
      (encList RadixPartition.recordEncoding rows).length ≤
        2 ^ input.2.length * (6 * (encoding input).length + 3) := by
  have fields := input_fields input
  have rowwire : ∀ r ∈ (indices input.2.length).map (record input),
      (RadixPartition.recordEncoding r).length ≤ 3 * (encoding input).length + 1 := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
    have hi : (encNat u).length ≤ input.2.length := by
      rw [indices_eq_range, List.mem_range] at hu
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr hu
    have hs := eval_wire input.1.1
      ((Native.Quarter.decode input.2.length u).zip input.2) input.1.2
    simp only [RadixPartition.recordEncoding, record, length_encPair]
    change 2 * (encNat (natEval input.1.1
      ((Native.Quarter.decode input.2.length u).zip input.2) input.1.2)).length + 1 +
      (encNat u).length ≤ 3 * (encoding input).length + 1
    omega
  have hn : ((indices input.2.length).map (record input)).length = 2 ^ input.2.length := by
    simp only [List.length_map, (indices_wire input.2.length).1]
  refine ⟨hn, listMax_le rowwire, ?_⟩
  have h := length_encList_le RadixPartition.recordEncoding _ rowwire
  rw [hn] at h
  convert h using 1; ring

/-- One uniform machine generates, evaluates and sorts from the original binary operands.
Both time and simultaneous bit workspace are a quarter enumeration times a fixed polynomial
in the original encoded input length; no materialized-list input or simulator is a premise. -/
theorem run_computable :
    ∃ Q : ℕ → ℕ, Cslib.PolynomiallyBounded Q ∧ Monotone Q ∧
      ComputableInO run encoding (encList RadixPartition.recordEncoding)
        (fun input => (2 ^ input.2.length + 1) * Q ((encoding input).length + 1))
        (fun input => (2 ^ input.2.length + 1) * Q ((encoding input).length + 1)) := by
  obtain ⟨G, hG, hmG, hg⟩ := indices_computable
  obtain ⟨F, hF, hmF, hf⟩ := ComputableInO.flatMap_stream record_polyTime
  obtain ⟨S, hS, hmS, hsort⟩ := RadixSort.computable
  have hcount : ComputableInPolyTime (fun input : Input => input.2.length) encoding encUnary :=
    ComputableInPolyTime.of_tidy ((ComputableTidilyInPolyTime.length_list encNat).comp
      (ComputableTidilyInPolyTime.snd (encPair encUnary encNat) (encList encNat)))
  let count := NativeCertificate.ofPolyTime hcount
  obtain ⟨R, hR, hmR, hr⟩ := exists_mono_poly_cert hcount
  let original : NativeCertificate (id : Input → Input) encoding encoding :=
    .linear (.of_eq (fun _ => rfl))
  let generate : NativeCertificate indices encUnary (encList encNat) := ⟨_, _, hg⟩
  let args := original.prod (generate.comp count)
  let evaluate : NativeCertificate
      (fun input : Input × List ℕ => input.2.flatMap (fun u => [record input.1 u]))
      (encPair encoding (encList encNat)) (encList RadixPartition.recordEncoding) := ⟨_, _, hf⟩
  let eval := evaluate.comp args
  let sorting : NativeCertificate RadixSort.sort RadixPartition.inputEncoding
      (encList RadixPartition.recordEncoding) := ⟨_, _, hsort⟩
  let final := sorting.comp ((original.fst.fst).prod eval)
  have computes : ComputableInO run encoding (encList RadixPartition.recordEncoding)
      final.time final.space := final.computes.of_enc_eq (fun input => by
    simp only [run, Function.comp_def, id_eq, ← List.map_eq_flatMap])
  let Q : ℕ → ℕ := fun B => 100 * (B + 1) ^ 2 * (G B + F (3 * B) + S (6 * B) + R B + 1)
  have hQ : Cslib.PolynomiallyBounded Q := by dsimp only [Q]; fun_prop
  have hmQ : Monotone Q := fun a b hab => by
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (by omega) 2)
    · have := hmG hab
      have := hmF (show 3 * a ≤ 3 * b by omega)
      have := hmS (show 6 * a ≤ 6 * b by omega)
      have := hmR hab
      omega
  refine ⟨Q, hQ, hmQ, computes.mono 4 ?_ ?_⟩
  all_goals intro input
  all_goals
    let I := (encoding input).length
    let k := input.2.length
    let E := 2 ^ k
    let rows := (indices k).map (record input)
    have fields := input_fields input
    have hk : k ≤ I := by dsimp only [k, I]; omega
    have hw : input.1.1 ≤ I := by dsimp only [I]; omega
    have he : 1 ≤ E := Nat.two_pow_pos k
    obtain ⟨hn, hm, hi⟩ := indices_wire k
    change (encList encNat (indices k)).length ≤ E * (2 * k + 1) at hi
    obtain ⟨hrn, hrm, hri⟩ := records_wire input
    change rows.length = E at hrn
    change streamRecordLength RadixPartition.recordEncoding rows ≤ 3 * I + 1 at hrm
    change (encList RadixPartition.recordEncoding rows).length ≤ E * (6 * I + 3) at hri
    have hcT := (hr input).1
    have hcS := (hr input).2
    change count.time input ≤ R I at hcT
    change count.space input ≤ R I at hcS
    have hg' := hmG (Nat.add_le_add_right hk 1)
    have hf' : F (streamFilterWidth encoding encNat (input, indices k)) ≤ F (3 * (I + 1)) := by
      apply hmF
      simp only [streamFilterWidth]
      change I + streamRecordLength encNat (indices k) + 1 ≤ 3 * (I + 1)
      omega
    have hs' : S (streamFilterWidth encUnary RadixPartition.recordEncoding
        (input.1.1, rows)) ≤ S (6 * (I + 1)) := by
      apply hmS
      simp only [streamFilterWidth, encUnary_apply, List.length_replicate]
      omega
    have hr' := hmR (Nat.le_succ I)
    change R I ≤ R (I + 1) at hr'
    have hi' : (encPair encoding (encList encNat) (input, indices k)).length ≤
        2 * I + 1 + E * (2 * k + 1) := by
      simp only [length_encPair]
      omega
    have hsI : (RadixPartition.inputEncoding (input.1.1, rows)).length ≤
        2 * I + 1 + E * (6 * I + 3) := by
      simp only [RadixPartition.inputEncoding, length_encPair, encUnary_apply,
        List.length_replicate]
      omega
    let N := E + 1
    let A := I + 2
    let J := G (I + 1) + F (3 * (I + 1)) + S (6 * (I + 1)) + R (I + 1) + 1
    let Base := N * A ^ 2 * J
    have hN : 1 ≤ N := by dsimp only [N]; omega
    have hA : 1 ≤ A := by dsimp only [A]; omega
    have hJ : 1 ≤ J := by dsimp only [J]; omega
    have hA2 : A ≤ A ^ 2 := by nlinarith only [hA]
    have hAJ : A ≤ A * J := by nlinarith only [hJ]
    have hJA : J ≤ A * J := by nlinarith only [hA]
    have hbase : N * A ≤ Base := by
      have h := Nat.mul_le_mul hA2 hJ
      dsimp only [Base]
      nlinarith only [Nat.mul_le_mul_left N h]
    have hbaseJ : N * J ≤ Base := by
      have hAA : 1 ≤ A ^ 2 := by nlinarith only [hA]
      have h := Nat.mul_le_mul_left (N * J) hAA
      dsimp only [Base]
      nlinarith only [h]
    have hinputB : I ≤ Base := by
      have hiA : I ≤ A := by dsimp only [A]; omega
      have hAN := Nat.mul_le_mul_right A hN
      nlinarith only [hbase, hiA, hAN]
    have hGJ : G (k + 1) ≤ J := by dsimp only [J]; omega
    have hFJ : F (streamFilterWidth encoding encNat (input, indices k)) ≤ J := by
      dsimp only [J]; omega
    have hSJ : S (streamFilterWidth encUnary RadixPartition.recordEncoding
        (input.1.1, rows)) ≤ J := by dsimp only [J]; omega
    have hRJ : R I ≤ J := by dsimp only [J]; omega
    have hcountTB : count.time input ≤ Base := by
      have h := Nat.mul_le_mul_left J hN
      nlinarith only [hcT, hRJ, h, hbaseJ]
    have hcountSB : count.space input ≤ Base := by
      have h := Nat.mul_le_mul_left J hN
      nlinarith only [hcS, hRJ, h, hbaseJ]
    have hgenB : (k + 1) * E * G (k + 1) ≤ Base := by
      have hka : k + 1 ≤ A := by dsimp only [A]; omega
      have h' := Nat.mul_le_mul (Nat.mul_le_mul hka (Nat.le_succ E)) hGJ
      have h'' := Nat.mul_le_mul_right (N * J) hA2
      dsimp only [Base, N] at *
      nlinarith only [h', h'']
    have hgenSB : E * G (k + 1) ≤ Base := by
      have h := Nat.mul_le_mul_left (E * G (k + 1)) (Nat.succ_pos k)
      nlinarith only [hgenB, h]
    have hargB : (encPair encoding (encList encNat) (input, indices k)).length ≤ 4 * Base := by
      have hEk := Nat.mul_le_mul_left E hk
      have harg : (encPair encoding (encList encNat) (input, indices k)).length ≤ 4 * N * A := by
        dsimp only [N, A]
        nlinarith only [hi', hEk, he]
      nlinarith only [harg, hbase]
    have hcallbackB : N * F (streamFilterWidth encoding encNat (input, indices k)) ≤ Base :=
      (Nat.mul_le_mul_left N hFJ).trans hbaseJ
    have hsortI : (RadixPartition.inputEncoding (input.1.1, rows)).length ≤ 8 * N * A := by
      dsimp only [N, A]
      nlinarith only [hsI, he]
    have hinner : (RadixPartition.inputEncoding (input.1.1, rows)).length +
        N * S (streamFilterWidth encUnary RadixPartition.recordEncoding (input.1.1, rows)) ≤
        N * (8 * A + J) := by
      have h := Nat.mul_le_mul_left N hSJ
      nlinarith only [hsortI, h]
    have hfactor : 8 * A + J ≤ 9 * A * J := by nlinarith only [hAJ, hJA]
    have hwidthA : input.1.1 + 1 ≤ A := by dsimp only [A]; omega
    have hsortTB : (input.1.1 + 1) *
        ((RadixPartition.inputEncoding (input.1.1, rows)).length +
          N * S (streamFilterWidth encUnary RadixPartition.recordEncoding
            (input.1.1, rows))) ≤ 9 * Base := by
      have h := Nat.mul_le_mul hwidthA hinner
      have h' := Nat.mul_le_mul_left (A * N) hfactor
      dsimp only [Base]
      nlinarith only [h, h']
    have hsortSB : (RadixPartition.inputEncoding (input.1.1, rows)).length +
        S (streamFilterWidth encUnary RadixPartition.recordEncoding (input.1.1, rows)) ≤
        9 * Base := by
      have h := Nat.mul_le_mul_left
        (S (streamFilterWidth encUnary RadixPartition.recordEncoding (input.1.1, rows))) hN
      have h' := Nat.mul_le_mul_left
        ((RadixPartition.inputEncoding (input.1.1, rows)).length +
          N * S (streamFilterWidth encUnary RadixPartition.recordEncoding
            (input.1.1, rows))) (Nat.succ_pos input.1.1)
      nlinarith only [h, h', hsortTB]
    have hbudget : N * Q (I + 1) = 100 * Base := by dsimp only [Q, Base, A, J]; ring
  · dsimp only [final, sorting, eval, evaluate, args, generate, original,
      NativeCertificate.comp, NativeCertificate.prod, NativeCertificate.fst,
      NativeCertificate.post, NativeCertificate.linear]
    simp only [Function.comp_def, id_eq, ← List.map_eq_flatMap]
    change I + (I + (count.time input + (k + 1) * E * G (k + 1)) +
      ((encPair encoding (encList encNat) (input, indices k)).length +
        ((indices k).length + 1) * F (streamFilterWidth encoding encNat (input, indices k)))) +
      (input.1.1 + 1) * ((RadixPartition.inputEncoding (input.1.1, rows)).length +
        (rows.length + 1) * S (streamFilterWidth encUnary RadixPartition.recordEncoding
          (input.1.1, rows))) ≤ 4 * (N * Q (I + 1) + 1)
    rw [hn, hrn, hbudget]
    change I + (I + (count.time input + (k + 1) * E * G (k + 1)) +
      ((encPair encoding (encList encNat) (input, indices k)).length +
        N * F (streamFilterWidth encoding encNat (input, indices k)))) +
      (input.1.1 + 1) * ((RadixPartition.inputEncoding (input.1.1, rows)).length +
        N * S (streamFilterWidth encUnary RadixPartition.recordEncoding
          (input.1.1, rows))) ≤ 4 * (100 * Base + 1)
    omega
  · dsimp only [final, sorting, eval, evaluate, args, generate, original,
      NativeCertificate.comp, NativeCertificate.prod, NativeCertificate.fst,
      NativeCertificate.post, NativeCertificate.linear]
    simp only [Function.comp_def, id_eq, ← List.map_eq_flatMap]
    change I + (I + (count.space input + E * G (k + 1)) +
      ((encPair encoding (encList encNat) (input, indices k)).length +
        ((indices k).length + 1) * F (streamFilterWidth encoding encNat (input, indices k)))) +
      ((RadixPartition.inputEncoding (input.1.1, rows)).length +
        S (streamFilterWidth encUnary RadixPartition.recordEncoding (input.1.1, rows))) ≤
      4 * (N * Q (I + 1) + 1)
    rw [hn, hbudget]
    change I + (I + (count.space input + E * G (k + 1)) +
      ((encPair encoding (encList encNat) (input, indices k)).length +
        N * F (streamFilterWidth encoding encNat (input, indices k)))) +
      ((RadixPartition.inputEncoding (input.1.1, rows)).length +
        S (streamFilterWidth encUnary RadixPartition.recordEncoding (input.1.1, rows))) ≤
      4 * (100 * Base + 1)
    omega

end Cslib.Cryptanalysis.AddXNOR.SortedQuarterMachine
