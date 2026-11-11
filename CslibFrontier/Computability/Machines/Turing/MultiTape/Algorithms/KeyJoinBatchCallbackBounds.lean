/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinBatchBounds
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinBatch
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinBatchBounds
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinStream
import all CslibFrontier.Computability.GenericRAM.Native.StreamingEmitBounds
import all CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts

/-!
# Scalar-width bounds for installed class-window callbacks

Normalize the actual binary counting, filtering, rank arithmetic and row emission.
Polynomial factors use scalar and individual record wires, rather than whole lists.
The installed certificates and their allowance fields are unchanged. Workspace uses actual
callback maxima and all prefix states, with input/output/framing tapes charged separately.
Original-source specialization and global window-phase composition are in
`Cslib.Cryptanalysis.AddXNOR.RestartResources`; this module does not assert a solver bound.

## Main definitions

* `windowWidth`: original binary ranks, largest individual record and binary population budget.

## Main results

* `windowCallback_bounds`: installed count/division/filter/cut/cross time and workspace.
* `windowCertificate_scalar_bounds`: the unchanged installed uniform window machine.
-/

public section
namespace Turing.MultiTapeTM.KeyJoinBatch
open Cslib.GenericRAM

private abbrev er := RadixPartition.recordEncoding
private abbrev el := encList er
private abbrev en := encPair encNat encNat

/-- Binary initial skip/count widths, largest individual record wire, and binary space
for the square of the quarter population. It contains no whole-list polynomial factor. -/
@[expose] def windowWidth (bounds : ℕ × ℕ) (groups : List (List SortedMatch.Record)) : ℕ :=
  (encPair encNat encNat bounds).length+
    streamRecordLength RadixPartition.recordEncoding groups.flatten+
    (encNat (groups.flatten.length^2+1)).length+1

private theorem lengthCertificate_bounds :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ∀ (rows : List SortedMatch.Record) (B : ℕ),
        (encNat rows.length).length ≤ B → streamRecordLength er rows ≤ B →
        lengthCertificate.time rows+lengthCertificate.space rows ≤ (rows.length+1)*P B := by
  delta lengthCertificate
  extract_lets ei step loop input
  obtain ⟨A, hA, mA, callback⟩ := exists_mono_poly_cert step
  obtain ⟨K, bound⟩ := NativeCertificate.foldlStream_bounds encBool encNat er
    (fun _ n _ => n+1) (NativeCertificate.ofPolyTime step)
  let P := fun B => 100*(K+1)*(A (10*(B+1))+B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have h := mA (show 10*(a+1) ≤ 10*(b+1) by omega)
    dsimp only [P]
    exact Nat.mul_le_mul_left (100*(K+1)) (by omega)
  · intro rows B countWire rowWire
    let args := (false, (0, rows))
    let M := A (10*(B+1))
    have state (j : ℕ) : (encNat ((rows.take j).foldl (fun n _ => n+1) 0)).length ≤ B := by
      simp only [List.foldl_add_const, Nat.zero_add, Nat.one_mul]
      exact (length_encNat_mono (List.length_take_le' j rows)).trans countWire
    have sw : NativeCertificate.foldStateWidth encNat (fun (_ : Bool) n (_ : SortedMatch.Record) =>
        n+1) args ≤ B := by
      apply Finset.sup_le
      intro j _
      exact state j
    have wire := length_encList_le er rows (fun r hr =>
      (le_listMax (f := fun r => (er r).length) hr).trans rowWire)
    have inputWire : (encPair encBool (encPair encNat el) args).length ≤
        (rows.length+1)*(2*B+4) := by
      simp only [length_encPair, encBool_apply, List.length_singleton]
      change 2*1+1+(2*0+1+(el rows).length) ≤ _
      nlinarith only [wire]
    have each (j : ℕ) (hj : j < rows.length) :
        (NativeCertificate.ofPolyTime step).time
            ((false, (rows.take j).foldl (fun n _ => n+1) 0), rows[j]) ≤ M ∧
          (NativeCertificate.ofPolyTime step).space
            ((false, (rows.take j).foldl (fun n _ => n+1) 0), rows[j]) ≤ M := by
      have s := state j
      have r : (er rows[j]).length ≤ B :=
        (le_listMax (f := fun r => (er r).length) (List.getElem_mem hj)).trans rowWire
      have w : (ei ((false, (rows.take j).foldl (fun n _ => n+1) 0), rows[j])).length ≤
          10*(B+1) := by
        dsimp only [ei]
        simp only [length_encPair, encBool_apply, List.length_singleton]
        change 2*(2*1+1+(encNat ((rows.take j).foldl (fun n _ => n+1) 0)).length)+1+
          (er rows[j]).length ≤ _
        omega
      have h := callback ((false, (rows.take j).foldl (fun n _ => n+1) 0), rows[j])
      exact ⟨h.1.trans (mA w), h.2.trans (mA w)⟩
    have timeSum : (∑ j ∈ Finset.range rows.length, if h : j < rows.length then
        (NativeCertificate.ofPolyTime step).time
          ((false, (rows.take j).foldl (fun n _ => n+1) 0), rows[j]) else 0) ≤ rows.length*M := by
      calc
        _ ≤ ∑ _ ∈ Finset.range rows.length, M := by
          apply Finset.sum_le_sum
          intro j hj
          rw [dite_eq_left (Finset.mem_range.mp hj)]
          exact (each j (Finset.mem_range.mp hj)).1
        _ = rows.length*M := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
    have spaceMax : (Finset.range rows.length).sup (fun j => if h : j < rows.length then
        (NativeCertificate.ofPolyTime step).space
          ((false, (rows.take j).foldl (fun n _ => n+1) 0), rows[j]) else 0) ≤ M := by
      apply Finset.sup_le
      intro j hj
      rw [dite_eq_left (Finset.mem_range.mp hj)]
      exact (each j (Finset.mem_range.mp hj)).2
    have timeBudget : NativeCertificate.foldTimeBudget encBool encNat er
        (fun _ n _ => n+1) (NativeCertificate.ofPolyTime step) args ≤
          (rows.length+1)*(M+4*B+10) := by
      dsimp only [NativeCertificate.foldTimeBudget, args]
      change (encPair encBool (encPair encNat el) args).length+_+_+1 ≤ _
      have scaled := Nat.mul_le_mul_left (rows.length+1) (show
        (encBool false).length+NativeCertificate.foldStateWidth encNat
          (fun (_ : Bool) n (_ : SortedMatch.Record) => n+1) args+
          streamRecordLength er rows+1 ≤ 2*B+2 by
            simp only [encBool_apply, List.length_singleton]; omega)
      nlinarith only [inputWire, timeSum, scaled]
    have spaceBudget : NativeCertificate.foldSpaceBudget encBool encNat er
        (fun _ n _ => n+1) (NativeCertificate.ofPolyTime step) args ≤
          (rows.length+1)*(M+4*B+10) := by
      dsimp only [NativeCertificate.foldSpaceBudget, args]
      change (encPair encBool (encPair encNat el) args).length+_+1+_+_+1 ≤ _
      nlinarith only [inputWire, spaceMax, sw, rowWire,
        Nat.zero_le (rows.length*M), Nat.zero_le (rows.length*B)]
    have actual := bound args
    have t := actual.1.trans (Nat.mul_le_mul_left K timeBudget)
    have s := actual.2.trans (Nat.mul_le_mul_left K spaceBudget)
    dsimp only [NativeCertificate.congr, NativeCertificate.comp, NativeCertificate.prod,
      NativeCertificate.const, input, NativeCertificate.linear, Function.comp_def, id_eq]
    change ((el rows).length+((el rows).length+(el rows).length)+loop.time args)+
      ((el rows).length+((el rows).length+(el rows).length)+loop.space args) ≤ _
    change loop.time args ≤ _ at t
    change loop.space args ≤ _ at s
    dsimp only [P, M] at *
    nlinarith only [t, s, wire, Nat.zero_le (rows.length*A (10*(B+1))),
      Nat.zero_le (rows.length*K*B), Nat.zero_le (rows.length*B),
      Nat.zero_le (K*A (10*(B+1))), Nat.zero_le (rows.length*K*A (10*(B+1)))]

private theorem cutCertificate_bounds :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ∀ (bounds : ℕ × ℕ) (rows : List SortedMatch.Record) (B : ℕ),
        (en bounds).length ≤ B → streamRecordLength er rows ≤ B →
        cutCertificate.time (bounds, rows)+cutCertificate.space (bounds, rows) ≤
          (rows.length+1)*P B := by
  delta cutCertificate
  extract_lets next emit
  obtain ⟨A, hA, mA, nextBound⟩ := exists_mono_poly_cert next
  obtain ⟨D, hD, mD, emitBound⟩ := exists_mono_poly_cert emit
  obtain ⟨K, bound⟩ := NativeCertificate.emitFoldCertificate_bounds en er er cutNext cutEmit
    (NativeCertificate.ofPolyTime next) (NativeCertificate.ofPolyTime emit)
  let V := fun B => A (10*(B+1))+D (10*(B+1))+10*B+10
  let P := fun B => 100*(K+1)*V B
  refine ⟨P, by dsimp only [P, V]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have ha := mA (show 10*(a+1) ≤ 10*(b+1) by omega)
    have hd := mD (show 10*(a+1) ≤ 10*(b+1) by omega)
    exact Nat.mul_le_mul_left (100*(K+1)) (by dsimp only [V]; omega)
  · intro bounds rows B stateWire rowWire
    let args := (bounds, rows)
    have state (j : ℕ) (hj : j ≤ rows.length) :
        (en (streamState bounds (fun q => cutNext q.1 q.2) rows j)).length ≤ B := by
      have inv := List.foldl_take_invariant rows cutNext bounds
        (fun _ s => s.1 ≤ bounds.1 ∧ s.2 ≤ bounds.2) ⟨le_rfl, le_rfl⟩
        (fun _ _ s hs => by
          dsimp only [cutNext]
          split <;> dsimp only <;> omega)
      have h := inv j hj
      have a := length_encNat_mono h.1
      have b := length_encNat_mono h.2
      change (encNat (streamState bounds (fun q => cutNext q.1 q.2) rows j).1).length ≤
        (encNat bounds.1).length at a
      change (encNat (streamState bounds (fun q => cutNext q.1 q.2) rows j).2).length ≤
        (encNat bounds.2).length at b
      have width : (en (streamState bounds (fun q => cutNext q.1 q.2) rows j)).length ≤
          (en bounds).length := by
        simp only [en, length_encPair]
        omega
      exact width.trans stateWire
    have sw : NativeCertificate.foldStateWidth en (fun (_ : Unit) => cutNext) ((), args) ≤ B := by
      apply Finset.sup_le
      intro j hj
      exact state j (by have := Finset.mem_range.mp hj; omega)
    have wire := length_encList_le er rows (fun r hr =>
      (le_listMax (f := fun r => (er r).length) hr).trans rowWire)
    have inputWire : (encPair en el args).length ≤ (rows.length+1)*(4*B+2) := by
      rw [length_encPair]
      change 2*(en bounds).length+1+(el rows).length ≤ _
      nlinarith only [wire, stateWire]
    have outputWire : (el (NativeCertificate.emitFold cutNext cutEmit bounds rows)).length ≤
        (el rows).length := by
      rw [cut_eq]
      have sub := (List.take_sublist bounds.2 (rows.drop bounds.1)).trans
        (List.drop_sublist bounds.1 rows)
      exact (sub.flatMap (fun r => frame (er r))).length_le
    have each (j : ℕ) (hj : j < rows.length) :
        (NativeCertificate.ofPolyTime next).time
            (streamState bounds (fun q => cutNext q.1 q.2) rows j, rows[j])+
          (NativeCertificate.ofPolyTime emit).time
            (streamState bounds (fun q => cutNext q.1 q.2) rows j, rows[j])+
          (er rows[j]).length ≤ V B ∧
        (NativeCertificate.ofPolyTime next).space
            (streamState bounds (fun q => cutNext q.1 q.2) rows j, rows[j])+
          (NativeCertificate.ofPolyTime emit).space
            (streamState bounds (fun q => cutNext q.1 q.2) rows j, rows[j]) ≤ V B := by
      have s := state j (by omega)
      have r : (er rows[j]).length ≤ B :=
        (le_listMax (f := fun r => (er r).length) (List.getElem_mem hj)).trans rowWire
      have w : (encPair en er
          (streamState bounds (fun q => cutNext q.1 q.2) rows j, rows[j])).length ≤ 10*(B+1) := by
        rw [length_encPair]
        dsimp only
        omega
      have a := nextBound (streamState bounds (fun q => cutNext q.1 q.2) rows j, rows[j])
      have d := emitBound (streamState bounds (fun q => cutNext q.1 q.2) rows j, rows[j])
      have atime := a.1.trans (mA w)
      have aspace := a.2.trans (mA w)
      have dtime := d.1.trans (mD w)
      have dspace := d.2.trans (mD w)
      dsimp only [V]
      exact ⟨by omega, by omega⟩
    have timeSum : (∑ j ∈ Finset.range rows.length, if h : j < rows.length then
        (NativeCertificate.ofPolyTime next).time
            (streamState bounds (fun q => cutNext q.1 q.2) rows j, rows[j])+
          (NativeCertificate.ofPolyTime emit).time
            (streamState bounds (fun q => cutNext q.1 q.2) rows j, rows[j])+
          (er rows[j]).length else 0) ≤ rows.length*V B := by
      calc
        _ ≤ ∑ _ ∈ Finset.range rows.length, V B := by
          apply Finset.sum_le_sum
          intro j hj
          rw [dite_eq_left (Finset.mem_range.mp hj)]
          exact (each j (Finset.mem_range.mp hj)).1
        _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
    have spaceMax : (Finset.range rows.length).sup (fun j => if h : j < rows.length then
        (NativeCertificate.ofPolyTime next).space
            (streamState bounds (fun q => cutNext q.1 q.2) rows j, rows[j])+
          (NativeCertificate.ofPolyTime emit).space
            (streamState bounds (fun q => cutNext q.1 q.2) rows j, rows[j]) else 0) ≤ V B := by
      apply Finset.sup_le
      intro j hj
      rw [dite_eq_left (Finset.mem_range.mp hj)]
      exact (each j (Finset.mem_range.mp hj)).2
    have vb : B+1 ≤ V B := by dsimp only [V]; omega
    have tb : NativeCertificate.emitTimeBudget en er er cutNext cutEmit
        (NativeCertificate.ofPolyTime next) (NativeCertificate.ofPolyTime emit) args ≤
          10*((rows.length+1)*V B) := by
      dsimp only [NativeCertificate.emitTimeBudget, args]
      have copies := Nat.mul_le_mul_left (rows.length+1) (Nat.add_le_add_right sw 1)
      nlinarith only [inputWire, timeSum, copies, rowWire, vb,
        Nat.mul_le_mul_left (rows.length+1) vb]
    have sb : NativeCertificate.emitSpaceBudget en er er cutNext cutEmit
        (NativeCertificate.ofPolyTime next) (NativeCertificate.ofPolyTime emit) args ≤
          10*((rows.length+1)*V B) := by
      dsimp only [NativeCertificate.emitSpaceBudget, args]
      nlinarith only [inputWire, spaceMax, sw, rowWire, outputWire, wire, vb,
        Nat.mul_le_mul_left (rows.length+1) vb]
    have actual := bound args
    have t := actual.1.trans (Nat.mul_le_mul_left K tb)
    have s := actual.2.trans (Nat.mul_le_mul_left K sb)
    change (NativeCertificate.emitFoldCertificate en er er cutNext cutEmit
      (NativeCertificate.ofPolyTime next) (NativeCertificate.ofPolyTime emit)).time args+
      (NativeCertificate.emitFoldCertificate en er er cutNext cutEmit
        (NativeCertificate.ofPolyTime next) (NativeCertificate.ofPolyTime emit)).space args ≤ _
    dsimp only [P]
    nlinarith only [t, s, Nat.zero_le (K*((rows.length+1)*V B))]

private theorem sideCertificate_bounds :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ∀ (right : Bool) (rows : List SortedMatch.Record) (B : ℕ),
        streamRecordLength er rows ≤ B →
        (sideCertificate right).time rows+(sideCertificate right).space rows ≤
          (rows.length+1)*P B := by
  let F := Classical.choose (ComputableInO.filter_stream KeyJoinStream.test_polyTime)
  have hF := (Classical.choose_spec (ComputableInO.filter_stream KeyJoinStream.test_polyTime)).1
  have mF : Monotone F :=
    (Classical.choose_spec (ComputableInO.filter_stream KeyJoinStream.test_polyTime)).2.1
  let P := fun B => 100*(B+1)+4*F (B+2)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have h := mF (show a+2 ≤ b+2 by omega)
    dsimp only [P]; omega
  · intro right rows B rowWire
    have wire := length_encList_le er rows (fun r hr =>
      (le_listMax (f := fun r => (er r).length) hr).trans rowWire)
    have w : streamFilterWidth encBool er (right, rows) ≤ B+2 := by
      simp only [streamFilterWidth, encBool_apply, List.length_singleton]
      omega
    have h := mF w
    have profile : (sideCertificate right).time rows+(sideCertificate right).space rows =
        4*(el rows).length+2*(encPair encBool el (right, rows)).length+
          (rows.length+1)*F (streamFilterWidth encBool er (right, rows))+
          F (streamFilterWidth encBool er (right, rows)) := by
      delta sideCertificate
      dsimp only [NativeCertificate.congr, NativeCertificate.comp, NativeCertificate.prod,
        NativeCertificate.const, NativeCertificate.linear, Function.comp_def, id_eq, F, el, er]
      ring
    rw [profile]
    rw [length_encPair]
    change 4*(el rows).length+2*(2*1+1+(el rows).length)+_+_ ≤ _
    dsimp only [P]
    nlinarith only [wire, h, Nat.mul_le_mul_left (rows.length+1) h]

private theorem populationCertificate_bounds :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ∀ (rows : List SortedMatch.Record) (B : ℕ),
        (encNat rows.length).length ≤ B → streamRecordLength er rows ≤ B →
        populationCertificate.time rows+populationCertificate.space rows ≤
            (rows.length+1)*P B ∧ (encNat (KeyJoin.population rows)).length ≤ P B := by
  delta populationCertificate
  extract_lets mul
  obtain ⟨L, hL, mL, lengths⟩ := lengthCertificate_bounds
  obtain ⟨S, hS, mS, sides⟩ := sideCertificate_bounds
  obtain ⟨A, hA, mA, multiplication⟩ := exists_mono_poly_cert mul
  obtain ⟨D, hD, mD, output⟩ := exists_mono_poly mul.polyBounded_length
  let P := fun B => 10*(L B+S B+A (4*B+1)+D (4*B+1)+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have hl := mL hab
    have hs := mS hab
    have ha := mA (show 4*a+1 ≤ 4*b+1 by omega)
    have hd := mD (show 4*a+1 ≤ 4*b+1 by omega)
    dsimp only [P]; omega
  · intro rows B countWire rowWire
    have sideLength (r : Bool) : (KeyJoin.side r rows).length ≤ rows.length :=
      List.length_filter_le _ _
    have sideWire (r : Bool) : streamRecordLength er (KeyJoin.side r rows) ≤ B := by
      apply listMax_le
      intro row hr
      exact (le_listMax (f := fun row => (er row).length) (List.mem_filter.mp hr).1).trans rowWire
    have sideCount (r : Bool) : (encNat (KeyJoin.side r rows).length).length ≤ B :=
      (length_encNat_mono (sideLength r)).trans countWire
    have lb (r : Bool) := (lengths (KeyJoin.side r rows) B (sideCount r) (sideWire r)).trans
      (Nat.mul_le_mul_right (L B) (Nat.add_le_add_right (sideLength r) 1))
    have sl := sides false rows B rowWire
    have sr := sides true rows B rowWire
    let pair := ((KeyJoin.side false rows).length, (KeyJoin.side true rows).length)
    have w : (en pair).length ≤ 4*B+1 := by
      rw [length_encPair]
      have a := sideCount false
      have b := sideCount true
      dsimp only [pair]
      omega
    have a := multiplication pair
    have atime := a.1.trans (mA w)
    have aspace := a.2.trans (mA w)
    have o := (output pair).trans (mD w)
    have profile :
        ((NativeCertificate.ofPolyTime mul).comp
          ((lengthCertificate.comp (sideCertificate false)).prod
            (lengthCertificate.comp (sideCertificate true)))).time rows+
        ((NativeCertificate.ofPolyTime mul).comp
          ((lengthCertificate.comp (sideCertificate false)).prod
            (lengthCertificate.comp (sideCertificate true)))).space rows =
          (sideCertificate false).time rows+(sideCertificate false).space rows+
          (sideCertificate true).time rows+(sideCertificate true).space rows+
          lengthCertificate.time (KeyJoin.side false rows)+
          lengthCertificate.space (KeyJoin.side false rows)+
          lengthCertificate.time (KeyJoin.side true rows)+
          lengthCertificate.space (KeyJoin.side true rows)+
          (NativeCertificate.ofPolyTime mul).time pair+
          (NativeCertificate.ofPolyTime mul).space pair := by
      dsimp only [NativeCertificate.comp, NativeCertificate.prod, Function.comp_def, pair]
      ring
    dsimp only [NativeCertificate.congr]
    rw [profile]
    constructor
    · have a := lb false
      have b := lb true
      dsimp only [P]
      nlinarith only [a, b, sl, sr, atime, aspace,
        Nat.zero_le (rows.length*A (4*B+1)), Nat.zero_le (rows.length*D (4*B+1))]
    · exact o.trans (by dsimp only [P]; omega)

private theorem advanceCertificate_bounds :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ∀ (bounds : ℕ × ℕ) (rows : List SortedMatch.Record) (B : ℕ),
        (en bounds).length ≤ B → (encNat rows.length).length ≤ B →
        streamRecordLength er rows ≤ B →
        advanceCertificate.time (bounds, rows)+advanceCertificate.space (bounds, rows) ≤
          (rows.length+1)*P B := by
  delta advanceCertificate
  extract_lets original population update
  obtain ⟨C, hC, mC, counted⟩ := populationCertificate_bounds
  obtain ⟨A, hA, mA, changed⟩ := exists_mono_poly_cert update
  let P := fun B => 100*(C B+A (2*B+C B+1)+B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have hc := mC hab
    have ha := mA (show 2*a+C a+1 ≤ 2*b+C b+1 by omega)
    dsimp only [P]; omega
  · intro bounds rows B stateWire countWire rowWire
    have count := counted rows B countWire rowWire
    have wire := length_encList_le er rows (fun r hr =>
      (le_listMax (f := fun r => (er r).length) hr).trans rowWire)
    let args := (bounds, rows)
    have inputWire : (encPair en el args).length ≤ (rows.length+1)*(4*B+2) := by
      rw [length_encPair]
      change 2*(en bounds).length+1+(el rows).length ≤ _
      nlinarith only [wire, stateWire]
    have w : (encPair en encNat (bounds, KeyJoin.population rows)).length ≤ 2*B+C B+1 := by
      rw [length_encPair]
      dsimp only
      omega
    have a := changed (bounds, KeyJoin.population rows)
    have atime := a.1.trans (mA w)
    have aspace := a.2.trans (mA w)
    have profile :
        ((NativeCertificate.ofPolyTime update).comp (original.fst.prod population)).time args+
        ((NativeCertificate.ofPolyTime update).comp (original.fst.prod population)).space args =
          4*(encPair en el args).length+
          populationCertificate.time rows+populationCertificate.space rows+
          (NativeCertificate.ofPolyTime update).time (bounds, KeyJoin.population rows)+
          (NativeCertificate.ofPolyTime update).space (bounds, KeyJoin.population rows) := by
      dsimp only [population, original, NativeCertificate.comp, NativeCertificate.prod,
        NativeCertificate.fst, NativeCertificate.snd, NativeCertificate.post,
        NativeCertificate.linear, Function.comp_def, id_eq, args]
      ring
    dsimp only [NativeCertificate.congr]
    rw [profile]
    dsimp only [P]
    nlinarith only [inputWire, count.1, atime, aspace,
      Nat.zero_le (rows.length*A (2*B+C B+1))]

private theorem groupWindowCertificate_bounds :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ∀ (initial : ℕ × ℕ) (rows : List SortedMatch.Record) (B : ℕ),
        (en initial).length ≤ B → (encNat rows.length).length ≤ B →
        streamRecordLength er rows ≤ B →
        groupWindowCertificate.time (initial, rows)+groupWindowCertificate.space (initial, rows) ≤
          (rows.length+(groupWindow initial rows).length+1)*P B := by
  delta groupWindowCertificate
  extract_lets original left right size ceil bounds limits selected proof cross
  obtain ⟨S, hS, mS, sides⟩ := sideCertificate_bounds
  obtain ⟨L, hL, mL, lengths⟩ := lengthCertificate_bounds
  obtain ⟨C, hC, mC, cuts⟩ := cutCertificate_bounds
  obtain ⟨A, hA, mA, arithmetic⟩ := exists_mono_poly_cert bounds
  obtain ⟨D, hD, mD, output⟩ := exists_mono_poly bounds.polyBounded_length
  let F := Classical.choose KeyJoinStream.cross_computable
  have hF := (Classical.choose_spec KeyJoinStream.cross_computable).1
  have mF : Monotone F := (Classical.choose_spec KeyJoinStream.cross_computable).2.1
  let U := fun B => D (4*B+1)+B+1
  let P := fun B => 100*(B+1+S B+L B+C (U B)+A (4*B+1)+F (2*B+1))
  refine ⟨P, by dsimp only [P, U]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have hs := mS hab
    have hl := mL hab
    have hd := mD (show 4*a+1 ≤ 4*b+1 by omega)
    have hc := mC (show U a ≤ U b by dsimp only [U]; omega)
    have ha := mA (show 4*a+1 ≤ 4*b+1 by omega)
    have hf := mF (show 2*a+1 ≤ 2*b+1 by omega)
    dsimp only [P]; omega
  · intro initial rows B stateWire countWire rowWire
    let args := (initial, rows)
    let ls := KeyJoin.side false rows
    let rs := KeyJoin.side true rows
    let cutBounds := (initial.1 ⌈/⌉ rs.length,
      (initial.1+initial.2) ⌈/⌉ rs.length - initial.1 ⌈/⌉ rs.length)
    let chosen := (ls.drop cutBounds.1).take cutBounds.2
    have sideLength (r : Bool) : (KeyJoin.side r rows).length ≤ rows.length :=
      List.length_filter_le _ _
    have sideWire (r : Bool) : streamRecordLength er (KeyJoin.side r rows) ≤ B := by
      apply listMax_le
      intro row hr
      exact (le_listMax (f := fun row => (er row).length) (List.mem_filter.mp hr).1).trans rowWire
    have sideCount (r : Bool) : (encNat (KeyJoin.side r rows).length).length ≤ B :=
      (length_encNat_mono (sideLength r)).trans countWire
    have sl := sides false rows B rowWire
    have sr := sides true rows B rowWire
    have lengthBound := (lengths rs B (sideCount true) (sideWire true)).trans
      (Nat.mul_le_mul_right (L B) (Nat.add_le_add_right (sideLength true) 1))
    have scalarWire : (encPair en encNat (initial, rs.length)).length ≤ 4*B+1 := by
      rw [length_encPair]
      dsimp only
      have h := sideCount true
      change (encNat rs.length).length ≤ B at h
      omega
    have ar := arithmetic (initial, rs.length)
    have atime := ar.1.trans (mA scalarWire)
    have aspace := ar.2.trans (mA scalarWire)
    have cutWire : (en cutBounds).length ≤ U B :=
      (output (initial, rs.length)).trans ((mD scalarWire).trans
        (by dsimp only [U]; omega))
    have rowCut : streamRecordLength er ls ≤ U B :=
      (sideWire false).trans (by dsimp only [U]; omega)
    have cutBound := (cuts cutBounds ls (U B) cutWire rowCut).trans
      (Nat.mul_le_mul_right (C (U B)) (Nat.add_le_add_right (sideLength false) 1))
    have chosenSub : List.Sublist chosen ls := (List.take_sublist _ _).trans (List.drop_sublist _ _)
    have chosenLength : chosen.length ≤ rows.length := chosenSub.length_le.trans (sideLength false)
    have chosenWire : streamRecordLength er chosen ≤ B := by
      apply listMax_le
      intro row hr
      exact (le_listMax (f := fun row => (er row).length) (chosenSub.subset hr)).trans
        (sideWire false)
    have crossWire : KeyJoinStream.crossWidth (rs, chosen) ≤ 2*B+1 := by
      change streamRecordLength er rs+streamRecordLength er chosen+1 ≤ 2*B+1
      have h := sideWire true
      change streamRecordLength er rs ≤ B at h
      omega
    have crossWidthBound := mF crossWire
    have outputLength : chosen.length*rs.length = (groupWindow initial rows).length := by
      simp [groupWindow, chosen, cutBounds, ls, rs, List.length_flatMap, List.length_map]
    have crossBound : cross.time (rs, chosen)+cross.space (rs, chosen) ≤
        4*(rows.length+(groupWindow initial rows).length+1)*F (2*B+1) := by
      change (chosen.length+1)*(rs.length+1)*F (KeyJoinStream.crossWidth (rs, chosen))+
        (chosen.length+1)*(rs.length+1)*F (KeyJoinStream.crossWidth (rs, chosen)) ≤ _
      have h := Nat.mul_le_mul_left ((chosen.length+1)*(rs.length+1)) crossWidthBound
      have pop : (chosen.length+1)*(rs.length+1) ≤
          2*(rows.length+(groupWindow initial rows).length+1) := by
        have hr := sideLength true
        change rs.length ≤ rows.length at hr
        nlinarith only [chosenLength, hr, outputLength]
      have scaled := Nat.mul_le_mul_right (F (2*B+1)) pop
      nlinarith only [h, scaled]
    have inputRows := length_encList_le er rows (fun r hr =>
      (le_listMax (f := fun r => (er r).length) hr).trans rowWire)
    have inputWire : (encPair en el args).length ≤ (rows.length+1)*(4*B+2) := by
      rw [length_encPair]
      change 2*(en initial).length+1+(el rows).length ≤ _
      nlinarith only [inputRows, stateWire]
    have profile : (cross.comp (right.prod selected)).time args+
        (cross.comp (right.prod selected)).space args =
        8*(encPair en el args).length+
        2*((sideCertificate true).time rows+(sideCertificate true).space rows)+
        (sideCertificate false).time rows+(sideCertificate false).space rows+
        lengthCertificate.time rs+lengthCertificate.space rs+
        (NativeCertificate.ofPolyTime bounds).time (initial, rs.length)+
        (NativeCertificate.ofPolyTime bounds).space (initial, rs.length)+
        cutCertificate.time (cutBounds, ls)+cutCertificate.space (cutBounds, ls)+
        cross.time (rs, chosen)+cross.space (rs, chosen) := by
      dsimp only [right, selected, limits, size, left, original, NativeCertificate.comp,
        NativeCertificate.prod, NativeCertificate.fst, NativeCertificate.snd,
        NativeCertificate.post, NativeCertificate.linear, Function.comp_def, id_eq,
        args, rs, ls, chosen, cutBounds]
      ring
    dsimp only [NativeCertificate.congr]
    rw [profile]
    dsimp only [P]
    nlinarith only [inputWire, sl, sr, lengthBound, atime, aspace, cutBound, crossBound,
      Nat.zero_le ((groupWindow initial rows).length*(B+S B+L B+C (U B)+A (4*B+1)))]

/-- Actual window callback clocks and simultaneous workspace have a fixed polynomial factor
in binary scalar/individual-record widths. Count scans, division, filtering, cutting and
Cartesian emission are executed and charged. Empty groups contribute their actual control
rounds; the generated quarter grouping has at most one group per input record. -/
theorem windowCallback_bounds :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ∀ (initial : ℕ × ℕ) (groups : List (List SortedMatch.Record)),
        windowCallbackTime initial groups+windowCallbackSpace initial groups ≤
          (initial.2+groups.flatten.length+groups.length+1)*P (windowWidth initial groups) := by
  obtain ⟨A, hA, mA, next⟩ := advanceCertificate_bounds
  obtain ⟨C, hC, mC, emit⟩ := groupWindowCertificate_bounds
  let P := fun B => 4*(A B+C B)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    exact Nat.mul_le_mul_left 4 (Nat.add_le_add (mA hab) (mC hab))
  · intro initial groups
    let B := windowWidth initial groups
    let V := A B+C B
    let st := streamState initial (fun q => advance q.1 q.2) groups
    let weight := fun j => if h : j < groups.length then
      groups[j].length+(groupWindow (st j) groups[j]).length+1 else 0
    have stateWire (j : ℕ) : (en (st j)).length ≤ B := by
      have h : (en (st j)).length ≤ (en initial).length := window_state_wire initial groups j
      exact h.trans (by dsimp only [B, windowWidth, en, er]; omega)
    have rowWire (j : ℕ) (hj : j < groups.length) : streamRecordLength er groups[j] ≤ B := by
      apply listMax_le
      intro row hr
      have flat : row ∈ groups.flatten := List.mem_flatten.mpr ⟨_, List.getElem_mem hj, hr⟩
      have w := le_listMax (f := fun row => (er row).length) flat
      change (er row).length ≤ streamRecordLength er groups.flatten at w
      dsimp only [B, windowWidth, en, er] at w ⊢
      omega
    have countWire (j : ℕ) (hj : j < groups.length) : (encNat groups[j].length).length ≤ B := by
      have n := (List.sublist_flatten_of_mem (List.getElem_mem hj)).length_le
      have square : groups[j].length ≤ groups.flatten.length^2+1 := by nlinarith only [n]
      have w := length_encNat_mono square
      dsimp only [B, windowWidth, en, er] at w ⊢
      omega
    have each (j : ℕ) (hj : j < groups.length) :
        advanceCertificate.time (st j, groups[j])+groupWindowCertificate.time (st j, groups[j])+
        advanceCertificate.space (st j, groups[j])+groupWindowCertificate.space (st j, groups[j]) ≤
          weight j*V := by
      have n := next (st j) groups[j] B (stateWire j) (countWire j hj) (rowWire j hj)
      have e := emit (st j) groups[j] B (stateWire j) (countWire j hj) (rowWire j hj)
      have scaled := Nat.mul_le_mul_right (A B) (show groups[j].length+1 ≤
        groups[j].length+(groupWindow (st j) groups[j]).length+1 by omega)
      dsimp only [weight, V]
      rw [dite_eq_left hj]
      nlinarith only [n, e, scaled]
    have records : (∑ j ∈ Finset.range groups.length,
        if h : j < groups.length then groups[j].length else 0) = groups.flatten.length := by
      rw [Finset.sum_range]
      simp only [dite_eq_left (Fin.isLt _)]
      rw [← List.sum_ofFn (f := fun i : Fin groups.length => groups[(i : ℕ)].length)]
      have mapped := List.map_ofFn (f := fun i : Fin groups.length => groups[(i : ℕ)])
        (g := List.length)
      simp only [List.ofFn_getElem, Function.comp_def] at mapped
      rw [← mapped, List.length_flatten]
    have population := window_emission_sum initial groups
    have total : (∑ j ∈ Finset.range groups.length, weight j) ≤
        initial.2+2*groups.flatten.length+groups.length := by
      have eq : (∑ j ∈ Finset.range groups.length, weight j) =
          (∑ j ∈ Finset.range groups.length, if h : j < groups.length then groups[j].length else 0)+
          (∑ j ∈ Finset.range groups.length, if h : j < groups.length then
            (groupWindow (st j) groups[j]).length else 0)+groups.length := by
        have ones : (∑ _ ∈ Finset.range groups.length, (1 : ℕ)) = groups.length := by simp
        conv_rhs => arg 2; rw [← ones]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [weight]
        simp only [dite_eq_left (Finset.mem_range.mp hj)]
      rw [eq, records]
      change (∑ j ∈ Finset.range groups.length, if h : j < groups.length then
        (groupWindow (st j) groups[j]).length else 0) ≤
          initial.2+groups.flatten.length at population
      omega
    have clocks : windowCallbackTime initial groups ≤
        (initial.2+2*groups.flatten.length+groups.length)*V := by
      have h : windowCallbackTime initial groups ≤
          ∑ j ∈ Finset.range groups.length, weight j*V := by
        change (∑ j ∈ Finset.range groups.length, if h : j < groups.length then
          advanceCertificate.time (st j, groups[j])+groupWindowCertificate.time (st j, groups[j])
          else 0) ≤ _
        apply Finset.sum_le_sum
        intro j hj
        rw [dite_eq_left (Finset.mem_range.mp hj)]
        have h := each j (Finset.mem_range.mp hj)
        omega
      rw [← Finset.sum_mul] at h
      exact h.trans (Nat.mul_le_mul_right V total)
    have spaces : windowCallbackSpace initial groups ≤
        (initial.2+2*groups.flatten.length+groups.length)*V := by
      change (Finset.range groups.length).sup (fun j => if h : j < groups.length then
        advanceCertificate.space (st j, groups[j])+groupWindowCertificate.space (st j, groups[j])
        else 0) ≤ _
      apply Finset.sup_le
      intro j hj
      rw [dite_eq_left (Finset.mem_range.mp hj)]
      have h := each j (Finset.mem_range.mp hj)
      have single := Finset.single_le_sum (f := weight) (fun _ _ => Nat.zero_le _) hj
      have scaled := Nat.mul_le_mul_right V (single.trans total)
      omega
    change _ ≤ (initial.2+groups.flatten.length+groups.length+1)*(4*V)
    nlinarith only [clocks, spaces, Nat.zero_le V]

/-- The installed uniform window machine has capacity/quarter/group-linear bit time and
all-prefix workspace, with a polynomial only in binary scalar and individual-record widths.
All callback and output tapes are charged; this is not yet a whole-source solver bound. -/
theorem windowCertificate_scalar_bounds :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ∀ (initial : ℕ × ℕ) (groups : List (List SortedMatch.Record)),
        windowCertificate.time (initial, groups)+windowCertificate.space (initial, groups) ≤
          (initial.2+groups.flatten.length+groups.length+1)*P (windowWidth initial groups) := by
  obtain ⟨A, hA, mA, callbacks⟩ := windowCallback_bounds
  obtain ⟨K, installed⟩ := windowCertificate_bounds
  let P := fun B => 100*(K+1)*(A B+B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    exact Nat.mul_le_mul_left (100*(K+1)) (by have := mA hab; omega)
  · intro initial groups
    let B := windowWidth initial groups
    let V := initial.2+groups.flatten.length+groups.length+1
    let I := (encPair en (encList el) (initial, groups)).length
    have stateWire : (en initial).length ≤ B := by dsimp only [B, windowWidth, en, er]; omega
    have rows (r : SortedMatch.Record) (hr : r ∈ groups.flatten) : (er r).length ≤ B := by
      have w := le_listMax (f := fun row => (er row).length) hr
      change (er r).length ≤ streamRecordLength er groups.flatten at w
      dsimp only [B, windowWidth, en, er] at w ⊢
      omega
    have wire := length_encList_le er groups.flatten rows
    have nested (xs : List (List SortedMatch.Record)) :
        (encList el xs).length = 2*(el xs.flatten).length+xs.length := by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        simp only [el, encList_cons, encList_append, List.length_append, length_frame,
          List.flatten_cons, List.length_cons] at ih ⊢
        omega
    have inputWire : I ≤ (groups.flatten.length+groups.length+1)*(6*B+4) := by
      dsimp only [I]
      rw [length_encPair, nested]
      dsimp only
      nlinarith only [wire, stateWire, Nat.zero_le (groups.length*B)]
    have outputRows : ∀ r ∈ window initial groups, (er r).length ≤ 3*B+1 := by
      intro r hr
      exact KeyJoinStream.join_record_wire groups B rows r (window_mem_join initial groups r hr)
    have outputWire : (el (window initial groups)).length ≤
        (initial.2+groups.flatten.length)*(6*B+3) :=
      (length_encList_le er (window initial groups) outputRows).trans
        (by nlinarith only [Nat.mul_le_mul_right (6*B+3) (window_length initial groups)])
    have cb := callbacks initial groups
    change windowCallbackTime initial groups+windowCallbackSpace initial groups ≤ V*A B at cb
    have budget :
        (windowCallbackTime initial groups+I+(groups.length+1)*((en initial).length+1)+
          2*(el groups.flatten).length+1)+
        (windowCallbackSpace initial groups+I+(en initial).length+(el groups.flatten).length+
          (el (window initial groups)).length+1) ≤ V*(A B+100*B+100) := by
      have copies := Nat.mul_le_mul_left (groups.length+1) (Nat.add_le_add_right stateWire 1)
      dsimp only [V] at cb ⊢
      nlinarith only [cb, inputWire, stateWire, copies, wire, outputWire,
        Nat.zero_le (initial.2*B)]
    have actual := installed initial groups
    change windowCertificate.time (initial, groups) ≤
      K*(windowCallbackTime initial groups+I+(groups.length+1)*((en initial).length+1)+
        2*(el groups.flatten).length+1) ∧
      windowCertificate.space (initial, groups) ≤
      K*(windowCallbackSpace initial groups+I+(en initial).length+(el groups.flatten).length+
        (el (window initial groups)).length+1) at actual
    calc
      _ ≤ K*((windowCallbackTime initial groups+I+(groups.length+1)*((en initial).length+1)+
            2*(el groups.flatten).length+1)+
          (windowCallbackSpace initial groups+I+(en initial).length+(el groups.flatten).length+
            (el (window initial groups)).length+1)) := by nlinarith only [actual.1, actual.2]
      _ ≤ K*(V*(A B+100*B+100)) := Nat.mul_le_mul_left K budget
      _ = V*(K*(A B+100*B+100)) := by ring
      _ ≤ V*P B := Nat.mul_le_mul_left V (by
        dsimp only [P]
        nlinarith only [Nat.zero_le (K*A B)])

end Turing.MultiTapeTM.KeyJoinBatch
