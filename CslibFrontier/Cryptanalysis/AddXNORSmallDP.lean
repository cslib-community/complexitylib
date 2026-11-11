/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORSmallProjection
public import CslibFrontier.Cryptanalysis.AddXNORCounterProjection
-- Unfold the scalar endpoint predicate when certifying original-input preprocessing.
import all CslibFrontier.Cryptanalysis.AddXNORSmallProjection
-- Inspect actual projection/DP profiles and the original-input constructors for composition.
import all CslibFrontier.Cryptanalysis.AddXNORCounterProjection
-- Reuse the existing operator-word counter identity rather than reproving the DP recurrence.
import all CslibFrontier.Cryptanalysis.AddXNORClasses
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native narrow-DP decision for small operands

The machine computes an endpoint check on the unrestricted seed and runs the
existing original-input projected counting DP at width `s + size(q) + 3`, capped
by the physical word width. Readback is linear, not a generic polynomial in the
exponential table. This is the small-operand decision route for
[WangLvShenZhang2027], Proposition 4 (PDF pp. 20–21).

## Main results

* `original_correct`: exact original-input decision for small operands and an unrestricted seed.
* `source_parameter_bounds`: actual uniform bit time and every-prefix space, $2^s P(m+s+q+1)$.

This uses a narrow dense DP instead of implementing the source's sorted-list suggestion.
Its correctness comes from the proved corridor and endpoint check, not projected correctness
as a premise. The original state width and all intermediate physical encodings are charged.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.SmallDP
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Unary magnitude bound followed by the original width, binary seed and operand tape. -/
abbrev Input := ℕ × SortedQuarterMachine.Input

/-- Frame the unary magnitude bound before the existing framed original-instance encoding. -/
abbrev encoding : Input ↪ List Bool := encPair encUnary SortedQuarterMachine.encoding

/-- The small-operand parameter is capped before exponentiation in the scalar precheck. -/
def magnitude (input : Input) : ℕ :=
  let (s, ((width, _), _)) := input
  min s width

/-- Runtime projection request with a signed-displacement safety margin. -/
def requested (input : Input) : ℕ :=
  let (_, (_, operands)) := input
  magnitude input+operands.length.size+3

/-- Only original scalar/data preparation is done outside the existing counting-DP machine. -/
def prepare (input : Input) : CounterProjection.Input :=
  let (_, original) := input
  (requested input, (false, original))

/-- Reject seeds outside both endpoint corridors, without enumerating any full-state set. -/
def near (input : Input) : Bool :=
  let (_, ((width, seed), operands)) := input
  SmallOperands.nearZero (operands.length*2^(magnitude input)) (2^width) seed

/-- Read the actual zero-state counter, with a zero default on malformed empty outputs. -/
def readZero (rows : List (ℕ × ℕ)) : Bool := !decide ((rows.headD (0,0)).2 = 0)

/-- The native decision program: scalar endpoint check and actual projected DP with readback. -/
def run (input : Input) : Bool := near input && readZero (CounterProjection.run (prepare input))

/-- Original full-width typed data, with no projected instance or supplied table. -/
def ofWords {m : ℕ} (s : ℕ) (seed : BitVec m) (as : List (BitVec m)) : Input :=
  (s, ((m, seed.toNat), as.map BitVec.toNat))

private theorem magnitude_polyTime : ComputableInPolyTime magnitude encoding encUnary := by
  unfold magnitude
  fun_prop

private theorem requested_polyTime : ComputableInPolyTime requested encoding encUnary := by
  have len : ComputableInPolyTime (fun input : Input => input.2.2.length) encoding encUnary :=
    .of_tidy ((ComputableTidilyInPolyTime.length encNat).comp (by fun_prop))
  have size := ComputableInPolyTime.binary_size.comp
    (ComputableInPolyTime.unary_to_binary.comp len)
  exact ComputableInPolyTime.unary_add.comp
    ((ComputableInPolyTime.unary_add.comp (magnitude_polyTime.prod size)).prod (.const 3))

private theorem prepare_polyTime :
    ComputableInPolyTime prepare encoding CounterProjection.encoding := by
  unfold prepare
  have original : ComputableInPolyTime (fun input : Input => input.2) encoding
      SortedQuarterMachine.encoding := by fun_prop
  exact requested_polyTime.prod ((ComputableInPolyTime.const false).prod original)

private theorem near_polyTime : ComputableInPolyTime near encoding encBool := by
  unfold near SmallOperands.nearZero
  have mag := ComputableInPolyTime.binary_pow' (.const 2) magnitude_polyTime
  have width : ComputableInPolyTime (fun input : Input => input.2.1.1) encoding encUnary := by
    fun_prop
  have len : ComputableInPolyTime (fun input : Input => input.2.2.length) encoding encUnary :=
    .of_tidy ((ComputableTidilyInPolyTime.length encNat).comp (by fun_prop))
  have radius := ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.unary_to_binary.comp len) mag
  have modulus := ComputableInPolyTime.binary_pow' (.const 2) width
  have seed : ComputableInPolyTime (fun input : Input => input.2.1.2) encoding encNat := by
    fun_prop
  have a := ComputableInPolyTime.binary_le' seed radius
  have b := ComputableInPolyTime.binary_le'
    (ComputableInPolyTime.binary_sub'
      (ComputableInPolyTime.binary_sub' modulus (.const 1)) seed) radius
  simpa [Function.comp_def] using
    (ComputableTidilyInPolyTime.bool_or.comp (a.tidy.prod b.tidy)).computableInPolyTime

private theorem readZero_linear : ComputableInO readZero encNatPairList encBool
    (fun rows => (encNatPairList rows).length) (fun rows => (encNatPairList rows).length) := by
  have head := (ComputableInDegree.headD (enc₁ := encPair encNat encNat)
    (enc := encNatPairList) (0,0)).inO_one
  have second := (ComputableInO.snd encNat encNat).comp_linear head
  exact ((ComputableInDegree.natIsZero.inO_one.comp_linear second).not').of_enc_eq
    (fun _ => rfl)

/-- One actual uniform machine charges preprocessing, both simultaneous branches, the entire
counting DP and linear readback. The operand-size hypothesis is not needed to execute it. -/
noncomputable def runCertificate : NativeCertificate run encoding encBool :=
  let scalar := NativeCertificate.ofPolyTime near_polyTime
  let counts := CounterProjection.runCertificate.comp
    (NativeCertificate.ofPolyTime prepare_polyTime)
  let decision := counts.post readZero_linear
  ((scalar.prod decision).post
    ((ComputableInDegree.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
      (fun p : Bool × Bool => p.1 && p.2)).inO_one))
    |>.congr (fun _ => rfl)

private theorem requested_words {m : ℕ} (s : ℕ) (seed : BitVec m) (as : List (BitVec m)) :
    requested (ofWords s seed as) = min s m+as.length.size+3 := by
  simp [requested, magnitude, ofWords]

private theorem prepare_words {m : ℕ} (s : ℕ) (seed : BitVec m) (as : List (BitVec m)) :
    prepare (ofWords s seed as) =
      CounterProjection.ofWords (min s m+as.length.size+3) false seed as := by
  simp [prepare, requested, magnitude, ofWords, CounterProjection.ofWords, CounterDP.ofWords]

private theorem readZero_graph {m : ℕ} (table : WordTable ℕ m) :
    readZero (CounterPull.graph table.read) = !decide (table.read 0#m = 0) := by
  have nonempty : CounterPull.graph table.read ≠ [] := by simp [CounterPull.graph]
  unfold readZero
  rw [List.headD_eq_head?_getD, List.head?_eq_some_head nonempty]
  simp only [Option.getD_some, CounterPull.graph, List.head_ofFn]
  rfl

private theorem counts_positive {m : ℕ} (as : List (BitVec m)) (seed : BitVec m) :
    readZero (CounterPull.graph (WordTable.classCounters as seed).read) = true ↔
      Solvable as seed 0#m := by
  rw [readZero_graph]
  have counts : (WordTable.classCounters as seed).read 0#m =
      ((operatorWords as.length).map (fun ops =>
        if eval (ops.zip as) seed = 0#m then 1 else 0)).sum := by
    rw [WordTable.classCounters, WordTable.countRun_read]
    simp only [WordTable.indicators_read, WordTable.point_read]
    apply congrArg List.sum
    apply List.map_congr_left
    intro ops _
    have h : seed = backward (ops.zip as) 0#m ↔ eval (ops.zip as) seed = 0#m := by
      constructor
      · intro h; rw [h, eval_backward]
      · intro h; rw [← h, backward_eval]
    simp [h]
  rw [counts]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, ← Nat.pos_iff_ne_zero,
    List.sum_pos_iff_exists_pos_nat, List.mem_map, exists_exists_and_eq_and,
    ]
  simp only [Solvable, mem_operatorWords]
  apply exists_congr
  intro ops
  by_cases h : eval (ops.zip as) seed = 0#m <;> simp [h]

/-- The actual capped width used by the original-input projection machine. -/
def cutoff (s m q : ℕ) : ℕ := min (min s m+q.size+3) m

private theorem cutoff_margin (s m q : ℕ) :
    cutoff s m q = m ∨ 0 < cutoff s m q ∧
      2*(q*2^(min s m))+1 < 2^(cutoff s m q-1) := by
  by_cases h : m ≤ min s m+q.size+3
  · exact Or.inl (Nat.min_eq_right h)
  · have width : cutoff s m q = min s m+q.size+3 := Nat.min_eq_left (by omega)
    refine Or.inr ⟨by rw [width]; omega, ?_⟩
    rw [width, show min s m+q.size+3-1 = (min s m+q.size)+2 by omega,
      pow_add, pow_add]
    have sized := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self q)
      (Nat.two_pow_pos (min s m))
    have positive : 1 ≤ 2^(min s m) := Nat.one_le_two_pow
    norm_num only [Nat.reducePow]
    nlinarith

private theorem cutoff_power (s m q : ℕ) : 2^(cutoff s m q) ≤ 2^s*(16*(q+1)) := by
  have sizeBound : 2^q.size ≤ 2*(q+1) := by
    by_cases zero : q = 0
    · simp [zero]
    · have pos := Nat.size_pos.mpr (Nat.pos_of_ne_zero zero)
      have h := Nat.lt_size.mp (show q.size-1 < q.size by omega)
      have power : 2^q.size = 2*2^(q.size-1) := by
        calc
          2^q.size = 2^((q.size-1)+1) := congrArg (2^·) (by omega)
          _ = _ := by rw [pow_succ]; ring
      rw [power]
      omega
  calc
    2^(cutoff s m q) ≤ 2^(min s m+q.size+3) :=
      Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _)
    _ = 8*2^(min s m)*2^q.size := by rw [pow_add, pow_add]; ring
    _ ≤ 8*2^s*(2*(q+1)) := Nat.mul_le_mul
      (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _))) sizeBound
    _ = _ := by ring

/-- Proposition 4 decision correctness on original full-width inputs. The seed is unrestricted;
only subsequent operands must satisfy the source magnitude bound. -/
theorem original_correct {m : ℕ} (s : ℕ) (seed : BitVec m) (as : List (BitVec m))
    (small : ∀ a ∈ as, a.toNat < 2 ^ s) : run (ofWords s seed as) = true ↔ Solvable as seed 0 := by
  let p := cutoff s m as.length
  have small' (a : BitVec m) (ha : a ∈ as) : a.toNat < 2^(min s m) := by
    rcases le_total s m with h | h
    · simpa only [Nat.min_eq_left h] using small a ha
    · simpa only [Nat.min_eq_right h] using a.isLt
  have correctness := SmallOperands.solvable_iff_project
    (show p ≤ m from Nat.min_le_right _ _) (min s m) as seed small'
    (cutoff_margin s m as.length)
  have counts : readZero (CounterProjection.run
      (CounterProjection.ofWords (min s m+as.length.size+3) false seed as)) = true ↔
      Solvable (as.map (BitVec.setWidth p)) (seed.setWidth p) 0 := by
    rw [CounterProjection.run, CounterProjection.prepare_words, CounterDP.run_words]
    simp only [Bool.false_eq_true, ite_false]
    exact counts_positive _ _
  rw [run, Bool.and_eq_true, prepare_words, counts]
  simpa only [near, magnitude, ofWords, List.length_map] using correctness.symm

/-- Actual small-operand machine bit time and simultaneous every-prefix workspace.
The bound holds even on large operands; only correctness needs the magnitude restriction.
The polynomial is fixed before all widths, bounds, operand tapes and seeds. -/
theorem source_certificate : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m s (seed : BitVec m) (as : List (BitVec m)),
      runCertificate.time (ofWords s seed as) ≤ 2^s*P ((encoding (ofWords s seed as)).length+1) ∧
      runCertificate.space (ofWords s seed as) ≤
        2^s*P ((encoding (ofWords s seed as)).length+1) := by
  obtain ⟨Q, hpQ, mQ, bound⟩ := CounterProjection.source_certificate
  obtain ⟨R, hpR, mR, nearBound⟩ := exists_mono_poly_cert near_polyTime
  obtain ⟨D, hpD, mD, prepBound⟩ := exists_mono_poly_cert prepare_polyTime
  let P := fun b => R b+D b+16*b*Q (20*b+1)
  have hp : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have mp : Monotone P := by
    intro a b h
    exact Nat.add_le_add (Nat.add_le_add (mR h) (mD h))
      (Nat.mul_le_mul (Nat.mul_le_mul_left 16 h) (mQ (by omega)))
  refine ⟨P, hp, mp, fun m s seed as => ?_⟩
  let input := ofWords s seed as
  let I := (encoding input).length
  have nI : as.length ≤ I := by
    have h := length_le_length_encList encNat (as.map BitVec.toNat)
    rw [List.length_map] at h
    simp only [I, input, ofWords, SortedQuarterMachine.encoding, length_encPair,
      encUnary_apply, List.length_replicate]
    omega
  have sI : s ≤ I := by
    simp only [I, input, ofWords, length_encPair, encUnary_apply, List.length_replicate]
    omega
  have size : as.length.size ≤ I+1 :=
    (Nat.size_le_self _).trans (by omega)
  have arg : (CounterProjection.encoding (prepare input)).length+1 ≤ 20*(I+1)+1 := by
    rw [prepare_words]
    simp only [CounterProjection.encoding, CounterProjection.ofWords, CounterDP.ofWords,
      CounterDP.encoding, SortedQuarterMachine.encoding, length_encPair, encUnary_apply,
      List.length_replicate, encBool_apply, List.length_singleton]
    have wire : 2*s+4*m+2*(encNat seed.toNat).length+
        (encList encNat (as.map BitVec.toNat)).length+4 = I := by
      simp only [I, input, ofWords, SortedQuarterMachine.encoding,
        length_encPair, encUnary_apply, List.length_replicate]
      omega
    have capped := Nat.min_le_left s m
    omega
  have counter := bound m (min s m+as.length.size+3) as seed false
  rw [← prepare_words s seed as] at counter
  change CounterProjection.runCertificate.time (prepare input) ≤
      2^(cutoff s m as.length)*Q ((CounterProjection.encoding (prepare input)).length+1) ∧
    CounterProjection.runCertificate.space (prepare input) ≤
      2^(cutoff s m as.length)*Q ((CounterProjection.encoding (prepare input)).length+1) at counter
  have power := cutoff_power s m as.length
  have normal : 2^(cutoff s m as.length)*Q
      ((CounterProjection.encoding (prepare input)).length+1) ≤
      2^s*(16*(I+1)*Q (20*(I+1)+1)) := by
    calc
      _ ≤ (2^s*(16*(as.length+1)))*Q (20*(I+1)+1) :=
        Nat.mul_le_mul power (mQ arg)
      _ ≤ (2^s*(16*(I+1)))*Q (20*(I+1)+1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega)))
      _ = _ := by ring
  have nr := nearBound input
  have dr := prepBound input
  change (NativeCertificate.ofPolyTime near_polyTime).time input ≤ R I ∧
    (NativeCertificate.ofPolyTime near_polyTime).space input ≤ R I at nr
  change (NativeCertificate.ofPolyTime prepare_polyTime).time input ≤ D I ∧
    (NativeCertificate.ofPolyTime prepare_polyTime).space input ≤ D I at dr
  change runCertificate.time input ≤ 2^s*P (I+1) ∧
    runCertificate.space input ≤ 2^s*P (I+1)
  have pt := counter.1.trans normal
  have ps := counter.2.trans normal
  have r := mR (Nat.le_succ I)
  have d := mD (Nat.le_succ I)
  have copies := Nat.mul_le_mul_right (R (I+1)+D (I+1))
    (show 1 ≤ 2^s from Nat.one_le_two_pow)
  constructor
  · change (NativeCertificate.ofPolyTime near_polyTime).time input +
      ((NativeCertificate.ofPolyTime prepare_polyTime).time input+
        CounterProjection.runCertificate.time (prepare input)) ≤ _
    dsimp only [P]
    nlinarith only [nr.1, dr.1, pt, r, d, copies]
  · change (NativeCertificate.ofPolyTime near_polyTime).space input +
      ((NativeCertificate.ofPolyTime prepare_polyTime).space input+
        CounterProjection.runCertificate.space (prepare input)) ≤ _
    dsimp only [P]
    nlinarith only [nr.2, dr.2, ps, r, d, copies]

/-- Proposition 4's $O^*(2^s)$ native decision resources in original scalar widths.
Original input, preprocessing, the projected DP, its internal tapes and linear readback all
contribute. Correctness is `original_correct`; no resource conclusion is an input premise. -/
theorem source_parameter_bounds : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m s (seed : BitVec m) (as : List (BitVec m)),
      runCertificate.time (ofWords s seed as) ≤ 2^s*P (m+s+as.length+1) ∧
      runCertificate.space (ofWords s seed as) ≤ 2^s*P (m+s+as.length+1) := by
  obtain ⟨A, hpA, mA, bound⟩ := source_certificate
  let R := fun b => 10*(b+1)^2
  have hp : Cslib.PolynomiallyBounded (fun b => A (R b)) := by dsimp only [R]; fun_prop
  have mr : Monotone R := fun _ _ h => Nat.mul_le_mul_left 10
    (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2)
  refine ⟨fun b => A (R b), hp, mA.comp mr, fun m s seed as => ?_⟩
  have words := length_encList_le encNat (as.map BitVec.toNat) (b := m) (by
    intro n hn
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hn
    exact length_encNat_le_of_lt_two_pow a.isLt)
  rw [List.length_map] at words
  have seedBits := length_encNat_le_of_lt_two_pow seed.isLt
  have wire : (encoding (ofWords s seed as)).length+1 ≤ R (m+s+as.length+1) := by
    simp only [encoding, ofWords, SortedQuarterMachine.encoding, length_encPair,
      encUnary_apply, List.length_replicate]
    dsimp only [R]
    nlinarith only [words, seedBits, Nat.zero_le (m^2), Nat.zero_le (s^2),
      Nat.zero_le (as.length^2), Nat.zero_le (m*s), Nat.zero_le (s*as.length)]
  have h := bound m s seed as
  exact ⟨h.1.trans (Nat.mul_le_mul_left _ (mA wire)),
    h.2.trans (Nat.mul_le_mul_left _ (mA wire))⟩

end Cslib.Cryptanalysis.AddXNOR.SmallDP
