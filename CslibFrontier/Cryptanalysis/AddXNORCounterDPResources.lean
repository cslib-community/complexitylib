/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORCounterDP
import all CslibFrontier.Cryptanalysis.AddXNORCounterDP
import all CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import all CslibFrontier.Cryptanalysis.AddXNORClasses

/-!
# Original-width resources of the complete reachable-state counter machine

Normalize the actual initialized forward/reverse fold. Callback clocks are summed;
workspace is a simultaneous maximum including every dense counter table and all
mapper/sort/pair/adder/index/control tapes. The faster all-count/balance prepass
of the dissection algorithm remains a separate composition.

## Main results

* `source_certificate`: one original-input DP machine has $O^*(2^p)$ bit time and peak space.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.CounterDP
open Turing.MultiTapeTM Cslib.GenericRAM

private theorem operand_width {m : ℕ} (as : List (BitVec m)) (seed : BitVec m)
    (inverse : Bool) :
    streamRecordLength encNat (orderedOperands (ofWords inverse seed as)) ≤ m := by
  apply listMax_le
  intro n hn
  have member : n ∈ as.map BitVec.toNat := by
    cases inverse <;> simpa [orderedOperands, ofWords] using hn
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp member
  exact length_encNat_le_of_lt_two_pow a.isLt

private theorem operand_length {m : ℕ} (as : List (BitVec m)) (seed : BitVec m)
    (inverse : Bool) : (orderedOperands (ofWords inverse seed as)).length = as.length := by
  cases inverse <;> simp [orderedOperands, ofWords]

private theorem callbacks {m : ℕ} (as : List (BitVec m)) (seed : BitVec m) (inverse : Bool)
    (P : ℕ → ℕ) (bound : ∀ {m B : ℕ} (table : WordTable ℕ m)
      (_ : ∀ s, Nat.size (table.read s) ≤ B) (a : BitVec m) (inverse : Bool),
      stepCertificate.time (((m, inverse), CounterPull.graph table.read), a.toNat) ≤
        2 ^ m * P (m + B + 1) ∧
      stepCertificate.space (((m, inverse), CounterPull.graph table.read), a.toNat) ≤
        2 ^ m * P (m + B + 1)) (j : ℕ)
    (hj : j < (orderedOperands (ofWords inverse seed as)).length) :
    let rows := orderedOperands (ofWords inverse seed as)
    let state := (rows.take j).foldl (step (m, inverse))
      (CounterInitialization.run (m, seed.toNat))
    stepCertificate.time (((m, inverse), state), rows[j]) ≤ 2^m*P (m+as.length+2) ∧
    stepCertificate.space (((m, inverse), state), rows[j]) ≤ 2^m*P (m+as.length+2) := by
  let rows := orderedOperands (ofWords inverse seed as)
  have member : rows[j] ∈ as.map BitVec.toNat := by
    have hm := List.getElem_mem hj
    cases inverse <;> simpa [rows, orderedOperands, ofWords] using hm
  obtain ⟨a, _, ha⟩ := List.mem_map.mp member
  have len : (prefixWords inverse as j).length ≤ as.length := by
    cases inverse <;> simp [prefixWords]
  have count (s : BitVec m) :
      Nat.size ((if inverse then WordTable.backwardCounters (prefixWords inverse as j) seed
        else WordTable.classCounters (prefixWords inverse as j) seed).read s) ≤ as.length+1 :=
    (counter_size _ seed inverse s).trans (by omega)
  dsimp only
  rw [prefix_run, run_words, ← ha]
  exact bound _ count a inverse

/-- Complete original-input native bit time and every-prefix peak workspace are
`2^m` times a polynomial in the original width and operand count. Both directions,
empty chains and width zero use the same installed machine, with no supplied
execution or resource conclusion. This is the all-count DP resource clause of
[WangLvShenZhang2027], Lemma 8; the faster balance-prepass composition is separate. -/
theorem source_certificate : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m (as : List (BitVec m)) (seed : BitVec m) (inverse : Bool),
      runCertificate.time (ofWords inverse seed as) ≤ 2^m*P (m+as.length+1) ∧
      runCertificate.space (ofWords inverse seed as) ≤ 2^m*P (m+as.length+1) := by
  obtain ⟨A, hpA, mA, hA⟩ := step_bounds
  obtain ⟨K, envelope⟩ := runCertificate_bounds
  let U := Classical.choose CounterInitialization.run_computable
  have hpU : Cslib.PolynomiallyBounded U :=
    (Classical.choose_spec CounterInitialization.run_computable).1
  have mU : Monotone U := (Classical.choose_spec CounterInitialization.run_computable).2.1
  obtain ⟨D, hpD, mD, hD⟩ := exists_mono_poly
    ((NativeCertificate.ofPolyTime_isPolynomial ordered_polyTime).1.add
      (NativeCertificate.ofPolyTime_isPolynomial ordered_polyTime).2)
  let R := fun b => 100*(b+1)^2
  let P := fun b => 10*R b+U (R b)+D (R b)+K*((b+1)*A (b+1)+30*(b+1)*R b)
  have hpR : Cslib.PolynomiallyBounded R := by dsimp only [R]; fun_prop
  have mR : Monotone R := fun _ _ h => Nat.mul_le_mul_left 100
    (Nat.pow_le_pow_left (by omega) 2)
  have hp : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have mp : Monotone P := by
    intro x y h
    have r := mR h
    have u := mU r
    have d := mD r
    have a := Nat.mul_le_mul (by omega : x+1 ≤ y+1) (mA (by omega : x+1 ≤ y+1))
    have f := Nat.mul_le_mul (by omega : 30*(x+1) ≤ 30*(y+1)) r
    dsimp only [P]
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 10 r) u) d)
      (Nat.mul_le_mul_left K (Nat.add_le_add a f))
  refine ⟨P, hp, mp, ?_⟩
  intro m as seed inverse
  let input := ofWords inverse seed as
  let b := m+as.length+1
  let rows := orderedOperands input
  let initialized := CounterInitialization.run (m, seed.toNat)
  let loopInput := ((m, inverse), (initialized, rows))
  have positive := Nat.two_pow_pos m
  have rowLength : rows.length = as.length := operand_length as seed inverse
  have rowWidth : streamRecordLength encNat rows ≤ m := operand_width as seed inverse
  have rowWire := length_encList_le encNat rows
    (fun n hn => (le_listMax (f := fun n => (encNat n).length) hn).trans rowWidth)
  have seedWidth := length_encNat_le_of_lt_two_pow seed.isLt
  have inputWire : (encoding input).length ≤ R b := by
    have operands := length_encList_le encNat (as.map BitVec.toNat) (by
      intro n hn
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hn
      exact length_encNat_le_of_lt_two_pow a.isLt)
    simp only [List.length_map] at operands
    simp only [input, ofWords, encoding, SortedQuarterMachine.encoding, length_encPair,
      encBool_apply, List.length_singleton, encUnary_apply, List.length_replicate]
    dsimp only [R, b]
    nlinarith
  have initWidth : (CounterInitialization.encoding (m, seed.toNat)).length+1 ≤ R b := by
    simp only [CounterInitialization.encoding, length_encPair, encUnary_apply,
      List.length_replicate]
    dsimp only [R, b]
    nlinarith
  have paramWire : (parameterEncoding (m, inverse)).length ≤ R b := by
    simp only [parameterEncoding, length_encPair, encUnary_apply,
      List.length_replicate, encBool_apply, List.length_singleton]
    dsimp only [R, b]
    nlinarith
  have states (j : ℕ) : (encNatPairList ((rows.take j).foldl (step (m, inverse))
      initialized)).length ≤ 2^m*R b := by
    have h := prefix_wire as seed inverse j
    have scalar : 4*m+2*as.length+5 ≤ R b := by dsimp only [R, b]; nlinarith
    exact h.trans (Nat.mul_le_mul_left _ scalar)
  have initialWire : (encNatPairList initialized).length ≤ 2^m*R b := by
    simpa only [List.take_zero, List.foldl_nil] using states 0
  have stateWidth : NativeCertificate.foldStateWidth encNatPairList step loopInput ≤
      2^m*R b := by
    apply Finset.sup_le
    intro j _
    exact states j
  have cb (j : ℕ) (hj : j < rows.length) := callbacks as seed inverse A hA j hj
  have rowScalar : (encList encNat rows).length ≤ R b := by
    rw [rowLength] at rowWire
    dsimp only [R, b]
    nlinarith only [rowWire, Nat.zero_le m, Nat.zero_le as.length]
  have copyR := Nat.mul_le_mul_left (R b) (show 1 ≤ 2^m by omega)
  have rPos : 1 ≤ R b := Nat.succ_le_of_lt (by dsimp only [R]; positivity)
  have inputLoopWire : (encPair parameterEncoding
      (encPair encNatPairList (encList encNat)) loopInput).length ≤ 10*2^m*R b := by
    simp only [loopInput, parameterEncoding, length_encPair, encUnary_apply,
      List.length_replicate, encBool_apply, List.length_singleton] at paramWire ⊢
    nlinarith only [rowScalar, initialWire, paramWire, copyR, rPos, positive]
  have sumCallbacks : (∑ j ∈ Finset.range rows.length, if h : j < rows.length then
      stepCertificate.time (((m, inverse), (rows.take j).foldl (step (m, inverse))
        initialized), rows[j]) else 0) ≤ as.length*(2^m*A (b+1)) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range rows.length, 2^m*A (b+1) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [dite_eq_left (Finset.mem_range.mp hj)]
        exact (cb j (Finset.mem_range.mp hj)).1
      _ = _ := by simp [rowLength]
  have maxCallbacks : (Finset.range rows.length).sup (fun j => if h : j < rows.length then
      stepCertificate.space (((m, inverse), (rows.take j).foldl (step (m, inverse))
        initialized), rows[j]) else 0) ≤ 2^m*A (b+1) := by
    apply Finset.sup_le
    intro j hj
    rw [dite_eq_left (Finset.mem_range.mp hj)]
    exact (cb j (Finset.mem_range.mp hj)).2
  have scalar : m+as.length+1 ≤ R b := by dsimp only [R, b]; nlinarith
  have frame : (parameterEncoding (m, inverse)).length+
      NativeCertificate.foldStateWidth encNatPairList step loopInput+
      streamRecordLength encNat rows+1 ≤ 4*2^m*R b := by
    nlinarith only [paramWire, stateWidth, rowWidth, scalar, copyR, positive]
  have frames := (Nat.mul_le_mul_left (rows.length+1) frame).trans_eq
    (congrArg (fun n => (n+1)*(4*2^m*R b)) rowLength)
  have timeBudget : NativeCertificate.foldTimeBudget parameterEncoding encNatPairList encNat
      step stepCertificate loopInput ≤
      2^m*((b+1)*A (b+1)+30*(b+1)*R b) := by
    have copied := Nat.mul_le_mul_left (10*2^m*R b) (show 1 ≤ b+1 by omega)
    have summed := Nat.mul_le_mul_right (2^m*A (b+1))
      (show as.length ≤ b+1 by dsimp only [b]; omega)
    have controlled := Nat.mul_le_mul_right (2^m*R b)
      (show 4*(as.length+1) ≤ 10*(b+1) by dsimp only [b]; omega)
    have one : 1 ≤ 2^m*(10*(b+1)*R b) := Nat.succ_le_of_lt
      (Nat.mul_pos positive (Nat.mul_pos (by omega) (by omega)))
    dsimp only [loopInput] at inputLoopWire frames
    simp only [NativeCertificate.foldTimeBudget, loopInput]
    nlinarith only [inputLoopWire, sumCallbacks, frames, copied, summed, controlled, one]
  have spaceBudget : NativeCertificate.foldSpaceBudget parameterEncoding encNatPairList encNat
      step stepCertificate loopInput ≤
      2^m*((b+1)*A (b+1)+30*(b+1)*R b) := by
    simp only [NativeCertificate.foldSpaceBudget, loopInput]
    dsimp only [loopInput] at frame inputLoopWire
    dsimp only [b] at maxCallbacks ⊢
    nlinarith only [inputLoopWire, maxCallbacks, frame, rPos, positive,
      Nat.zero_le (A (m+as.length+1+1))]
  have orderedBound := (hD input).trans (mD inputWire)
  have initBound := mU initWidth
  have setupBounds :
      setupCertificate.time input ≤ 2^m*(10*R b+U (R b)+D (R b)) ∧
      setupCertificate.space input ≤ 2^m*(10*R b+U (R b)+D (R b)) := by
    constructor <;>
      simp only [setupCertificate, initializationCertificate, NativeCertificate.prod,
        NativeCertificate.comp, NativeCertificate.fst, NativeCertificate.snd,
        NativeCertificate.post,
        NativeCertificate.linear, input, ofWords, Function.comp_def, id_eq]
    all_goals
      dsimp only [input, ofWords, U] at inputWire orderedBound initBound
      nlinarith only [inputWire, orderedBound, copyR,
        Nat.mul_le_mul_left (2^m) initBound,
        Nat.mul_le_mul_left (D (R b)) (show 1 ≤ 2^m by omega)]
  have h := envelope input
  constructor
  · exact h.1.trans ((Nat.add_le_add setupBounds.1 (Nat.mul_le_mul_left K timeBudget)).trans_eq
      (by dsimp only [P]; ring))
  · exact h.2.trans ((Nat.add_le_add setupBounds.2 (Nat.mul_le_mul_left K spaceBudget)).trans_eq
      (by dsimp only [P]; ring))

end Cslib.Cryptanalysis.AddXNOR.CounterDP
