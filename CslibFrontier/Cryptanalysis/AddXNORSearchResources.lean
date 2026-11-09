/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORBalanceResources
import all CslibFrontier.Cryptanalysis.AddXNORBalanceResources
import all CslibFrontier.Cryptanalysis.AddXNORWholeRunResources
import all CslibFrontier.Cryptanalysis.AddXNORProducerResources
import all CslibFrontier.Cryptanalysis.AddXNORClassJoin
import all CslibFrontier.Cryptanalysis.AddXNORClassBalance
import all CslibFrontier.Cryptanalysis.AddXNORJoinedDissection
import all CslibFrontier.Cryptanalysis.AddXNORSortedQuarterMachine
import all CslibFrontier.Cryptanalysis.AddXNORSortedMeet
import all CslibFrontier.Cryptanalysis.AddXNORSource
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinStream
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import all CslibFrontier.Computability.GenericRAM.Native.Combinators

/-!
# Resource normalization of installed class searches

Charge actual projected-quarter generation, grouping, retained full-state emission,
count-selected orientation and matching in original physical widths. This develops
the remaining installed search costs in [WangLvShenZhang2027], Lemma 8/Theorem 7,
pp.21–22, under the deterministic multitape convention on p.6. Selected direct
searches are normalized and composed into the whole original-input run. Actual
selected restarted-search sum/max remain explicit costs; this is not the full
sharp source theorem or the faster reachable-state-DP prepass.

## Main definitions

* `restartTime`, `restartSpace`: installed costs of selected restarted searches only.

## Main results

* `witnessesCertificate_bounds`, `recordsCertificate_bounds`: actual generated class resources.
* `classSearch_bounds`: selected direct-search sum/max, including computed orientation/control.
* `sourceCertificate_restart_bounds`: whole run with only selected restarted costs explicit.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.SearchResources
open Turing.MultiTapeTM Cslib.GenericRAM

private abbrev er := RadixPartition.recordEncoding
private abbrev el := encList er

private theorem sorted_wire : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ input : ClassJoin.Input,
      (ClassJoin.sortedRecords input).length = ProducerResources.quarterVolume input ∧
      streamRecordLength er (ClassJoin.sortedRecords input) ≤
        P ((ClassJoin.encoding input).length+1) := by
  obtain ⟨I, hI, mI, inverse⟩ := ProducerResources.inverseCertificate_bounds
  obtain ⟨A, hA, mA, tag⟩ := exists_mono_poly
    (ComputableInPolyTime.of_tidy SortedMatch.tag_polyTime).polyBounded_length
  let D := fun B => 20*(B+1)+I (5*B)
  let P := fun B => A (D B+3)
  have monoD : Monotone D := by
    intro a b hab
    have h := mI (by omega : 5*a ≤ 5*b)
    dsimp only [D]; omega
  refine ⟨P, by dsimp only [P, D]; fun_prop,
    fun _ _ h => mA (Nat.add_le_add_right (monoD h) 3), ?_⟩
  rintro ⟨⟨⟨w, seed⟩, first, second⟩, target⟩
  let input : ClassJoin.Input := (((w, seed), (first, second)), target)
  let B := (ClassJoin.encoding input).length+1
  let forward := ProducerResources.forwardInput input
  let backward := ProducerResources.inverseInput input
  have wires : (SortedQuarterMachine.encoding forward).length+1 ≤ 5*B ∧
      (SortedQuarterMachine.encoding backward).length+1 ≤ 5*B := by
    dsimp only [forward, backward, ProducerResources.forwardInput,
      ProducerResources.inverseInput, B, input]
    simp only [ClassJoin.encoding, SortedMeet.encoding, SortedQuarterMachine.encoding,
      length_encPair]
    omega
  have fw := (ProducerResources.quarter_wire forward).2.1
  have bw := (inverse backward).2.trans (mI wires.2)
  have rows (r : ℕ × ℕ)
      (hr : r ∈ (ClassJoin.batches input).2.1 ++ (ClassJoin.batches input).2.2) :
      (er r).length ≤ D B := by
    rcases List.mem_append.mp hr with h | h
    · have row := (le_listMax (f := fun row => (er row).length) h).trans fw
      dsimp only [D]; omega
    · have row := (le_listMax (f := fun row => (er row).length) h).trans bw
      dsimp only [D]; omega
  have tagged : streamRecordLength er (SortedMatch.tagged (ClassJoin.batches input)) ≤ P B := by
    apply listMax_le
    intro r hr
    rcases List.mem_append.mp hr with hf | hb
    · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hf
      have old := rows row (List.mem_append_left _ hrow)
      have arg : (encPair encBool er (false, row)).length ≤ D B+3 := by
        simp only [length_encPair, encBool_apply, List.length_singleton]; omega
      exact (tag (false, row)).trans (mA arg)
    · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hb
      have old := rows row (List.mem_append_right _ hrow)
      have arg : (encPair encBool er (true, row)).length ≤ D B+3 := by
        simp only [length_encPair, encBool_apply, List.length_singleton]; omega
      exact (tag (true, row)).trans (mA arg)
  refine ⟨?_, ?_⟩
  · simpa only [ClassJoin.groups, KeyGrouping.flatten_run, ProducerResources.quarterVolume]
      using ClassJoin.groups_input_length input
  · apply listMax_le
    intro row hr
    exact (le_listMax (f := fun row => (er row).length)
      ((SortedMatch.sorted_perm (ClassJoin.batches input)).mem_iff.mp hr)).trans tagged

private theorem groups_count_le (rows : List (ℕ × ℕ)) :
    (KeyGrouping.run rows).length ≤ rows.length := by
  calc
    (KeyGrouping.run rows).length = ((KeyGrouping.run rows).map (fun _ => 1)).sum := by simp
    _ ≤ ((KeyGrouping.run rows).map List.length).sum :=
      List.sum_le_sum (fun group hg =>
        List.length_pos_iff.mpr (KeyGrouping.group_nonempty rows group hg))
    _ = rows.length := by rw [← List.length_flatten, KeyGrouping.flatten_run]

/-- The actual quarter generation/sort/group pipeline, before any Cartesian pair emission,
is quarter-linear in time and all-prefix workspace with physical scalar-width factors. -/
theorem groupsCertificate_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ input : ClassJoin.Input,
      ClassJoin.groupsCertificate.time input+ClassJoin.groupsCertificate.space input ≤
        (ProducerResources.quarterVolume input+1)*P ((ClassJoin.encoding input).length+1) := by
  obtain ⟨D, hD, mD, wire⟩ := sorted_wire
  obtain ⟨C, hC, mC, counted⟩ := ProducerResources.countCertificate_bounds
  let K := Classical.choose KeyGrouping.run_computable
  have hK := (Classical.choose_spec KeyGrouping.run_computable).1
  have mK : Monotone K := (Classical.choose_spec KeyGrouping.run_computable).2.1
  let P := fun B => C B+4*(D B+1)+2*K (D B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have hd := mD hab
    have hc := mC hab
    have hk := mK (Nat.add_le_add_right hd 1)
    dsimp only [P]; omega
  · intro input
    let B := (ClassJoin.encoding input).length+1
    let Q := ProducerResources.quarterVolume input
    let rows := ClassJoin.sortedRecords input
    have len : rows.length = Q := (wire input).1
    have maxRow : streamRecordLength er rows ≤ D B := (wire input).2
    have inputWire := length_encList_le er rows (fun r hr =>
      (le_listMax (f := fun row => (er row).length) hr).trans maxRow)
    rw [len] at inputWire
    have sorted : ClassJoin.sortedCertificate.time input+ClassJoin.sortedCertificate.space input ≤
        (Q+1)*C B := by
      have h := counted input
      dsimp only [ClassJoin.countCertificate, NativeCertificate.congr, NativeCertificate.comp] at h
      change _ ≤ (Q+1)*C B at h
      omega
    have callback := Nat.mul_le_mul_left (Q+2) (mK (Nat.add_le_add_right maxRow 1))
    have profile : ClassJoin.groupsCertificate.time input+ClassJoin.groupsCertificate.space input =
        ClassJoin.sortedCertificate.time input+ClassJoin.sortedCertificate.space input+
        2*(el rows).length+(rows.length+2)*K (streamRecordLength er rows+1) := by
      dsimp only [ClassJoin.groupsCertificate, NativeCertificate.congr, NativeCertificate.comp]
      ring
    rw [profile, len]
    change _ ≤ (Q+1)*P B
    dsimp only [P]
    nlinarith only [sorted, inputWire, callback]

/-- Actual quarter generation, sorting, grouping and class-pair emission, including every
internal prefix and the materialized class output. The class population is computed by
this same construction, not supplied as a size hypothesis. -/
theorem witnessesCertificate_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ input : ClassJoin.Input,
      ClassJoin.witnessesCertificate.time input+ClassJoin.witnessesCertificate.space input ≤
          (ProducerResources.quarterVolume input+ClassJoin.count input+1)*
            P ((ClassJoin.encoding input).length+1) ∧
        streamRecordLength RadixPartition.recordEncoding (ClassJoin.witnesses input) ≤
          P ((ClassJoin.encoding input).length+1) := by
  obtain ⟨D, hD, mD, wire⟩ := sorted_wire
  obtain ⟨C, hC, mC, grouped⟩ := groupsCertificate_bounds
  let J := Classical.choose KeyJoinStream.join_computable
  have hJ := (Classical.choose_spec KeyJoinStream.join_computable).1
  have mJ : Monotone J := (Classical.choose_spec KeyJoinStream.join_computable).2.1
  let P := fun B => C B+10*(D B+1)+4*J (D B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have hd := mD hab
    have hc := mC hab
    have hj := mJ (by omega : D a+1 ≤ D b+1)
    dsimp only [P]; omega
  · intro input
    let B := (ClassJoin.encoding input).length+1
    let Q := ProducerResources.quarterVolume input
    let N := ClassJoin.count input
    let rows := ClassJoin.sortedRecords input
    let groups := ClassJoin.groups input
    have len : rows.length = Q := (wire input).1
    have maxRow : streamRecordLength er rows ≤ D B := (wire input).2
    have inputWire := length_encList_le er rows (fun r hr =>
      (le_listMax (f := fun row => (er row).length) hr).trans maxRow)
    rw [len] at inputWire
    have numGroups : groups.length ≤ Q := (groups_count_le rows).trans_eq len
    have flatten : groups.flatten = rows := KeyGrouping.flatten_run rows
    have width : KeyJoinStream.width groups ≤ D B+1 := by
      change streamRecordLength er groups.flatten+1 ≤ D B+1
      rw [flatten]; omega
    have population : KeyJoinStream.volume groups ≤ 2*Q+N+1 := by
      have sumEq : (groups.map (fun group => group.length+KeyJoin.population group+1)).sum =
          groups.flatten.length+KeyJoin.count groups+groups.length := by
        induction groups with
        | nil => simp [KeyJoin.count]
        | cons g gs ih =>
          simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append,
            List.length_cons, KeyJoin.count] at *
          omega
      dsimp only [KeyJoinStream.volume]
      rw [sumEq, flatten, len]
      change Q+N+groups.length+1 ≤ _
      omega
    have grouping : ClassJoin.groupsCertificate.time input+
        ClassJoin.groupsCertificate.space input ≤ (Q+1)*C B := grouped input
    have joined : ClassJoin.witnessesCertificate.time input+
        ClassJoin.witnessesCertificate.space input ≤
          (Q+1)*C B+2*(2*Q+N+1)*J (D B+1) := by
      have callback := Nat.mul_le_mul population (mJ width)
      have profile : ClassJoin.witnessesCertificate.time input+
          ClassJoin.witnessesCertificate.space input =
          ClassJoin.groupsCertificate.time input+ClassJoin.groupsCertificate.space input+
            2*KeyJoinStream.volume groups*J (KeyJoinStream.width groups) := by
        dsimp only [ClassJoin.witnessesCertificate, NativeCertificate.congr, NativeCertificate.comp]
        ring
      rw [profile]
      nlinarith only [grouping, callback]
    constructor
    · change _ ≤ (Q+N+1)*P B
      dsimp only [P]
      nlinarith only [joined, Nat.zero_le (N*C B), Nat.zero_le (N*(D B+1))]
    · apply listMax_le
      intro pair hp
      have rows (r : ℕ × ℕ) (hr : r ∈ groups.flatten) : (er r).length ≤ D B := by
        rw [flatten] at hr
        exact (le_listMax (f := fun row => (er row).length) hr).trans maxRow
      have pairWidth := KeyJoinStream.join_record_wire groups (D B) rows pair hp
      have upper : 3*D B+1 ≤ P B := by dsimp only [P]; omega
      exact pairWidth.trans upper

/-- Full-state class retention reconstructs actual generated witnesses. Every quarter,
group, pair, original-state callback and output tape is included in the installed allowance. -/
theorem recordsCertificate_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (input : ClassBalance.Input) (right : Bool) (g : ℕ),
      ClassBalance.recordsCertificate.time ((input, right), g)+
        ClassBalance.recordsCertificate.space ((input, right), g) ≤
          (ProducerResources.countVolume input right+ClassBalance.count input right g+1)*
            P ((encPair (encPair ClassBalance.encoding encBool) encNat
              ((input, right), g)).length+1) := by
  obtain ⟨C, hC, mC, joins⟩ := witnessesCertificate_bounds
  obtain ⟨E, hE, mE, emitted⟩ := ProducerResources.emission_bounds
  obtain ⟨A, hA, mA, query⟩ := exists_mono_poly_cert ClassBalance.queryInput_polyTime
  obtain ⟨D, hD, mD, queryWire⟩ :=
    exists_mono_poly ClassBalance.queryInput_polyTime.polyBounded_length
  let R := fun B => B+C (D B+1)+1
  let P := fun B => 10*(B+1)+2*A B+C (D B+1)+E (R B)
  have monoR : Monotone R := by
    intro a b hab
    have hd := mD hab
    have hc := mC (by omega : D a+1 ≤ D b+1)
    dsimp only [R]; omega
  refine ⟨P, by dsimp only [P, R]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have ha := mA hab
    have hd := mD hab
    have hc := mC (by omega : D a+1 ≤ D b+1)
    have he := mE (monoR hab)
    dsimp only [P]; omega
  · intro input right g
    let task := ((input, right), g)
    let B := (ClassBalance.taskEncoding task).length+1
    let prepared := ClassBalance.queryInput input right g
    let Q := ProducerResources.countVolume input right
    let N := ClassBalance.count input right g
    have layout : (ClassJoin.encoding prepared).length ≤ D B := by
      have h := queryWire task
      exact h.trans (mD (by dsimp only [B]; omega))
    have normalized := mC (Nat.add_le_add_right layout 1)
    have produced := joins prepared
    have volume : ProducerResources.quarterVolume prepared = Q :=
      ProducerResources.countVolume_eq input right g
    have countEq : ClassJoin.count prepared = N := rfl
    rw [volume, countEq] at produced
    have pairMax : streamRecordLength er (ClassJoin.witnesses prepared) ≤ C (D B+1) :=
      produced.2.trans normalized
    have joined : ClassJoin.witnessesCertificate.time prepared+
        ClassJoin.witnessesCertificate.space prepared ≤ (Q+N+1)*C (D B+1) :=
      produced.1.trans (Nat.mul_le_mul_left _ normalized)
    have side : (ClassBalance.sideEncoding (input, right)).length ≤ R B := by
      have h := length_le_encPair_left ClassBalance.sideEncoding encNat task
      dsimp only [R, B, task, ClassBalance.taskEncoding] at *
      omega
    have each (r : ℕ × ℕ) (hr : r ∈ ClassJoin.witnesses prepared) : (er r).length ≤ R B := by
      have h := (le_listMax (f := fun row => (er row).length) hr).trans pairMax
      dsimp only [R]; omega
    have emitBound := emitted input right (ClassJoin.witnesses prepared) (R B) side each
    have lengthEq : (ClassJoin.witnesses prepared).length = N :=
      (ClassJoin.count_eq_length prepared).symm
    rw [lengthEq] at emitBound
    have preparedBound := query task
    have inputWire : (ClassBalance.taskEncoding task).length ≤ B := by dsimp only [B]; omega
    have prepareScale := mA inputWire
    have profile : ClassBalance.recordsCertificate.time task+
        ClassBalance.recordsCertificate.space task = 2*(ClassBalance.taskEncoding task).length+
          (NativeCertificate.ofPolyTime ClassBalance.queryInput_polyTime).time task+
          (NativeCertificate.ofPolyTime ClassBalance.queryInput_polyTime).space task+
          ClassJoin.witnessesCertificate.time prepared+
          ClassJoin.witnessesCertificate.space prepared+
          ClassBalance.emitCertificate.time ((input, right), ClassJoin.witnesses prepared)+
          ClassBalance.emitCertificate.space ((input, right), ClassJoin.witnesses prepared) := by
      dsimp only [ClassBalance.recordsCertificate, NativeCertificate.congr, NativeCertificate.comp,
        NativeCertificate.prod, NativeCertificate.fst, NativeCertificate.post,
        NativeCertificate.linear, Function.comp_def, id_eq, prepared, task]
      ring
    change _ ≤ (Q+N+1)*P B
    rw [profile]
    dsimp only [P]
    nlinarith only [joined, emitBound, preparedBound.1, preparedBound.2, prepareScale, inputWire,
      Nat.zero_le ((Q+N)*A B), Nat.zero_le (Q*E (R B))]

private theorem orientation_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (input : ClassBalance.Input) (g B : ℕ),
      (ClassBalance.encoding input).length+(encNat g).length+
        (encNat (ClassBalance.count input false g)).length+
        (encNat (ClassBalance.count input true g)).length+1 ≤ B →
      ClassBalance.orientationCertificate.time (input, g)+
        ClassBalance.orientationCertificate.space (input, g) ≤
          ProducerResources.countAllowance input g+P B := by
  delta ClassBalance.orientationCertificate
  extract_lets test
  obtain ⟨A, hA, mA, bound⟩ := exists_mono_poly_cert test
  let P := fun B => 24*B+2*A (2*B)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have := mA (by omega : 2*a ≤ 2*b)
    dsimp only [P]; omega
  · intro input g B wire
    let counts := (ClassBalance.count input false g, ClassBalance.count input true g)
    have countsWire : (encPair encNat encNat counts).length ≤ 2*B := by
      simp only [length_encPair, counts]
      omega
    have classWire : (ClassBalance.classEncoding (input, g)).length ≤ 2*B := by
      dsimp only [ClassBalance.classEncoding]
      rw [length_encPair]
      dsimp only
      omega
    have testBound := bound counts
    have scale := mA countsWire
    have profile :
        ((NativeCertificate.ofPolyTime test).comp
          ((ClassBalance.countOn false).prod (ClassBalance.countOn true))).time (input, g)+
        ((NativeCertificate.ofPolyTime test).comp
          ((ClassBalance.countOn false).prod (ClassBalance.countOn true))).space (input, g) =
          12*(ClassBalance.classEncoding (input, g)).length+
          ProducerResources.countAllowance input g+
          (NativeCertificate.ofPolyTime test).time counts+
          (NativeCertificate.ofPolyTime test).space counts := by
      dsimp only [NativeCertificate.congr, NativeCertificate.comp, NativeCertificate.prod,
        ClassBalance.countOn, NativeCertificate.fst, NativeCertificate.snd,
        NativeCertificate.post, NativeCertificate.linear, NativeCertificate.const,
        Function.comp_def, id_eq, ProducerResources.countAllowance, counts]
      ring
    dsimp only [NativeCertificate.congr]
    rw [profile]
    dsimp only [P]
    nlinarith only [classWire, testBound.1, testBound.2, scale]

private theorem original_components : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m) (g : BitVec p),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let q := as.length+bs.length+cs.length+ds.length
      let B := (ClassBalance.encoding input).length+q+p+1
      let Q := JoinedDissection.quarterBudget input
      ClassBalance.orientationCertificate.time (input, g.toNat)+
          ClassBalance.orientationCertificate.space (input, g.toNat) ≤ (Q+1)*P B ∧
        ∀ right : Bool,
          (ClassBalance.countCertificate.time ((input, right), g.toNat)+
            ClassBalance.countCertificate.space ((input, right), g.toNat) ≤ (Q+1)*P B) ∧
          (ClassBalance.recordsCertificate.time ((input, right), g.toNat)+
            ClassBalance.recordsCertificate.space ((input, right), g.toNat) ≤
              (Q+ClassBalance.count input right g.toNat+1)*P B) := by
  obtain ⟨C, hC, mC, countBound⟩ := ProducerResources.projectedCount_bounds
  obtain ⟨R, hR, mR, recordBound⟩ := recordsCertificate_bounds
  obtain ⟨O, hO, mO, orientation⟩ := orientation_bounds
  let P := fun B => 2*C (10*B)+R (10*B)+O (10*B)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have hc := mC (by omega : 10*a ≤ 10*b)
    have hr := mR (by omega : 10*a ≤ 10*b)
    have ho := mO (by omega : 10*a ≤ 10*b)
    dsimp only [P]; omega
  · intro m p hp as bs cs ds s g
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length+bs.length+cs.length+ds.length
    let B := (ClassBalance.encoding input).length+q+p+1
    let Q := JoinedDissection.quarterBudget input
    have taskWire (right : Bool) :
        (encPair (encPair ClassBalance.encoding encBool) encNat
          ((input, right), g.toNat)).length+1 ≤
          10*B := by
      exact (ProducerResources.count_task_wire input g right).trans
        (Nat.mul_le_mul_left 10 (by dsimp only [B]; omega))
    have volume (right : Bool) : ProducerResources.countVolume input right ≤ Q := by
      cases right with
      | false =>
        change 2^input.2.1.1.length+2^input.2.1.2.length ≤ Q
        exact (Nat.le_add_right _ (2^input.2.2.1.length)).trans
          (Nat.le_add_right _ (2^input.2.2.2.length))
      | true =>
        simp only [ProducerResources.countVolume, ClassBalance.halfInput, ite_true,
          List.length_reverse]
        calc
          2^input.2.2.2.length+2^input.2.2.1.length =
              2^input.2.2.1.length+2^input.2.2.2.length := Nat.add_comm _ _
          _ ≤ (2^input.2.1.1.length+2^input.2.1.2.length)+
              (2^input.2.2.1.length+2^input.2.2.2.length) := Nat.le_add_left _ _
          _ = Q := by dsimp only [Q, JoinedDissection.quarterBudget]; ring
    have counted (right : Bool) :
        ClassBalance.countCertificate.time ((input, right), g.toNat)+
          ClassBalance.countCertificate.space ((input, right), g.toNat) ≤ (Q+1)*C (10*B) := by
      have scale := Nat.mul_le_mul (Nat.add_le_add_right (volume right) 1) (mC (taskWire right))
      with_reducible exact (countBound input right g.toNat).trans scale
    have left := BalanceResources.count_wire hp as bs cs ds s false g
    have right := BalanceResources.count_wire hp as bs cs ds s true g
    with_reducible
      change (encNat (ClassBalance.count input false g.toNat)).length ≤ q+1 at left
      change (encNat (ClassBalance.count input true g.toNat)).length ≤ q+1 at right
    have label : (encNat g.toNat).length ≤ p := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr g.isLt
    have oriented := orientation input g.toNat (10*B) (by dsimp only [B]; omega)
    have hf := counted false
    have hb := counted true
    constructor
    · change _ ≤ (Q+1)*P B
      dsimp only [ProducerResources.countAllowance] at oriented
      dsimp only [P]
      nlinarith only [oriented, hf, hb, Nat.zero_le (Q*O (10*B)),
        Nat.zero_le ((Q+1)*R (10*B))]
    · intro right
      constructor
      · change _ ≤ (Q+1)*P B
        exact (counted right).trans (Nat.mul_le_mul_left (Q+1) (by dsimp only [P]; omega))
      · change _ ≤ (Q+ClassBalance.count input right g.toNat+1)*P B
        have scale := Nat.mul_le_mul
          (Nat.add_le_add_right
            (Nat.add_le_add_right (volume right) (ClassBalance.count input right g.toNat)) 1)
          (mR (taskWire right))
        have h : ClassBalance.recordsCertificate.time ((input, right), g.toNat)+
            ClassBalance.recordsCertificate.space ((input, right), g.toNat) ≤
              (Q+ClassBalance.count input right g.toNat+1)*R (10*B) := by
          with_reducible exact (recordBound input right g.toNat).trans scale
        exact h.trans (Nat.mul_le_mul_left _ (by dsimp only [P]; omega))

private theorem quarter_counter_wire {m p : ℕ} (as bs cs ds : List (BitVec m)) (s : BitVec m) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length+bs.length+cs.length+ds.length
    (encNat (JoinedDissection.quarterBudget input)).length ≤ q+3 := by
  let q := as.length+bs.length+cs.length+ds.length
  have ha := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (show as.length ≤ q by dsimp only [q]; omega)
  have hb := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (show bs.length ≤ q by dsimp only [q]; omega)
  have hc := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (show cs.length ≤ q by dsimp only [q]; omega)
  have hd := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (show ds.length ≤ q by dsimp only [q]; omega)
  have strict : 2^as.length+2^bs.length+2^cs.length+2^ds.length < 2^(q+3) := by
    rw [pow_add]
    norm_num
    have := Nat.two_pow_pos q
    omega
  simpa only [JoinedDissection.quarterBudget, ProgramGeneration.originalSource,
    BitInput.words, List.length_map, encNat_apply, ← Nat.size_eq_bits_len] using
    Nat.size_le.mpr strict

private theorem materialize_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m) (g : BitVec p),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let q := as.length+bs.length+cs.length+ds.length
      let B := (ClassBalance.encoding input).length+q+p+1
      JoinedDissection.materializeCertificate.time (input, g.toNat)+
        JoinedDissection.materializeCertificate.space (input, g.toNat) ≤
          (JoinedDissection.quarterBudget input+1)*P B := by
  delta JoinedDissection.materializeCertificate
  extract_lets original right selected small neg opposite large budget test
  obtain ⟨A, hA, mA, components⟩ := original_components
  obtain ⟨U, hU, mU, quarter⟩ := exists_mono_poly_cert JoinedDissection.quarterBudget_polyTime
  obtain ⟨N, hN, mN, negate⟩ := exists_mono_poly_cert neg
  obtain ⟨T, hT, mT, testBound⟩ := exists_mono_poly_cert test
  let P := fun B => 100*(A B+U B+N (B+1)+T (20*(B+1))+B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have ha := mA hab
    have hu := mU hab
    have hn := mN (by omega : a+1 ≤ b+1)
    have ht := mT (by omega : 20*(a+1) ≤ 20*(b+1))
    dsimp only [P]; omega
  · intro m p hp as bs cs ds s g
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length+bs.length+cs.length+ds.length
    let B := (ClassBalance.encoding input).length+q+p+1
    let Q := JoinedDissection.quarterBudget input
    let orient := ClassBalance.retainRight input g.toNat
    let kept := ClassBalance.count input orient g.toNat
    let other := ClassBalance.count input (!orient) g.toNat
    have component := components hp as bs cs ds s g
    change _ ≤ (Q+1)*A B ∧ _ at component
    have ori := component.1
    have keptCount := (component.2 orient).1
    have otherCount := (component.2 (!orient)).1
    have countsWire (r : Bool) : (encNat (ClassBalance.count input r g.toNat)).length ≤ q+1 :=
      BalanceResources.count_wire hp as bs cs ds s r g
    have kWire := countsWire orient
    have oWire := countsWire (!orient)
    have qWire : (encNat Q).length ≤ q+3 := quarter_counter_wire as bs cs ds s
    have label : (encNat g.toNat).length ≤ p := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr g.isLt
    have originalWire : (JoinedDissection.classEncoding (input, g.toNat)).length ≤ 3*B := by
      dsimp only [JoinedDissection.classEncoding]
      rw [length_encPair]
      dsimp only [B]
      omega
    have quarterBound := quarter input
    have quarterScale := mU (show (ClassBalance.encoding input).length ≤ B by dsimp only [B]; omega)
    have negBound := negate orient
    have negScale := mN (show (encBool orient).length ≤ B+1 by
      simp only [encBool_apply, List.length_singleton]; omega)
    have testWire : (encPair JoinedDissection.recEncoding encNat ((kept, other), Q)).length ≤
        20*(B+1) := by
      dsimp only [JoinedDissection.recEncoding]
      rw [length_encPair, length_encPair]
      dsimp only
      dsimp only [kept, other] at *
      dsimp only [B]
      omega
    have tested := testBound ((kept, other), Q)
    have testScale := mT testWire
    have profile :
        ((NativeCertificate.ofPolyTime test).comp ((small.prod large).prod budget)).time
          (input, g.toNat)+
        ((NativeCertificate.ofPolyTime test).comp ((small.prod large).prod budget)).space
          (input, g.toNat) =
          10*(JoinedDissection.classEncoding (input, g.toNat)).length+
          2*(ClassBalance.orientationCertificate.time (input, g.toNat)+
            ClassBalance.orientationCertificate.space (input, g.toNat))+
          (NativeCertificate.ofPolyTime neg).time orient+
          (NativeCertificate.ofPolyTime neg).space orient+
          ClassBalance.countCertificate.time ((input, orient), g.toNat)+
          ClassBalance.countCertificate.space ((input, orient), g.toNat)+
          ClassBalance.countCertificate.time ((input, !orient), g.toNat)+
          ClassBalance.countCertificate.space ((input, !orient), g.toNat)+
          (NativeCertificate.ofPolyTime JoinedDissection.quarterBudget_polyTime).time input+
          (NativeCertificate.ofPolyTime JoinedDissection.quarterBudget_polyTime).space input+
          (NativeCertificate.ofPolyTime test).time ((kept, other), Q)+
          (NativeCertificate.ofPolyTime test).space ((kept, other), Q) := by
      dsimp only [small, large, budget, opposite, selected, right, original,
        NativeCertificate.comp, NativeCertificate.prod, NativeCertificate.fst,
        NativeCertificate.snd, NativeCertificate.post, NativeCertificate.linear,
        Function.comp_def, id_eq, orient, kept, other, Q]
      ring
    dsimp only [NativeCertificate.congr]
    rw [profile]
    change _ ≤ (Q+1)*P B
    dsimp only [P]
    nlinarith only [ori, keptCount, otherCount, originalWire,
      quarterBound.1, quarterBound.2, quarterScale, negBound.1, negBound.2, negScale,
      tested.1, tested.2, testScale, Nat.zero_le (Q*U B), Nat.zero_le (Q*N (B+1)),
      Nat.zero_le (Q*T (20*(B+1))), Nat.zero_le (Q*B)]

private theorem original_width {m p : ℕ} (as bs cs ds : List (BitVec m)) (s : BitVec m) :
    m ≤ (ClassBalance.encoding (ProgramGeneration.originalSource p as bs cs ds s 0)).length := by
  simp only [ClassBalance.encoding, ProgramGeneration.sourceEncoding,
    ProgramGeneration.originalSource, length_encPair, encUnary_apply, List.length_replicate]
  omega

private theorem directSearch_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m) (g : BitVec p),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let q := as.length+bs.length+cs.length+ds.length
      let B := (ClassBalance.encoding input).length+q+p+1
      JoinedDissection.directSearchCertificate.time (input, g.toNat)+
        JoinedDissection.directSearchCertificate.space (input, g.toNat) ≤
          (JoinedDissection.quarterBudget input+ClassBalance.count input false g.toNat+
            ClassBalance.count input true g.toNat+1)*P B := by
  delta JoinedDissection.directSearchCertificate
  extract_lets original right kept parameter neg opposite generated
  obtain ⟨A, hA, mA, components⟩ := original_components
  obtain ⟨N, hN, mN, negate⟩ := exists_mono_poly_cert neg
  obtain ⟨M, hM, mM, matchBound⟩ := MatcherResources.matchCertificate_bounds
  let P := fun B => 100*(A B+N (B+1)+M (4*(B+1))+B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have ha := mA hab
    have hn := mN (by omega : a+1 ≤ b+1)
    have hm := mM (by omega : 4*(a+1) ≤ 4*(b+1))
    dsimp only [P]; omega
  · intro m p hp as bs cs ds s g
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length+bs.length+cs.length+ds.length
    let B := (ClassBalance.encoding input).length+q+p+1
    let Q := JoinedDissection.quarterBudget input
    let orient := ClassBalance.retainRight input g.toNat
    let stored := ClassBalance.retain input g.toNat
    let produced := ClassBalance.records input (!orient) g.toNat
    let leftCount := ClassBalance.count input false g.toNat
    let rightCount := ClassBalance.count input true g.toNat
    have component := components hp as bs cs ds s g
    change _ ≤ (Q+1)*A B ∧ _ at component
    have ori := component.1
    with_reducible
      change ClassBalance.orientationCertificate.time (input, g.toNat)+
        ClassBalance.orientationCertificate.space (input, g.toNat) ≤ (Q+1)*A B at ori
    have retainBound := (component.2 orient).2
    have produceBound := (component.2 (!orient)).2
    with_reducible
      change ClassBalance.recordsCertificate.time ((input, orient), g.toNat)+
        ClassBalance.recordsCertificate.space ((input, orient), g.toNat) ≤
          (Q+ClassBalance.count input orient g.toNat+1)*A B at retainBound
      change ClassBalance.recordsCertificate.time ((input, !orient), g.toNat)+
        ClassBalance.recordsCertificate.space ((input, !orient), g.toNat) ≤
          (Q+ClassBalance.count input (!orient) g.toNat+1)*A B at produceBound
    have rawWidth : m ≤ (ClassBalance.encoding input).length :=
      original_width (p := p) as bs cs ds s
    have width : m ≤ B := rawWidth.trans (by dsimp only [B]; omega)
    have rowWire (r : ℕ × ℕ) (hr : r ∈ stored++produced) : (er r).length ≤ 4*(B+1) := by
      have h : (er r).length ≤ 2*m+1+q := by
        rcases List.mem_append.mp hr with h | h
        · exact ClassBalance.record_wire hp as bs cs ds s orient g r h
        · exact ClassBalance.record_wire hp as bs cs ds s (!orient) g r h
      have qWire : q ≤ B := by dsimp only [B]; omega
      omega
    have matching := matchBound m (4*(B+1)) orient stored produced (by omega) rowWire
    have counts : ClassBalance.count input orient g.toNat+
        ClassBalance.count input (!orient) g.toNat =
        leftCount+rightCount := by
      dsimp only [orient]
      cases ClassBalance.retainRight input g.toNat <;>
        simp only [Bool.not_false, Bool.not_true, leftCount, rightCount]; omega
    have totalLength : stored.length+produced.length = leftCount+rightCount := by
      dsimp only [stored, produced, ClassBalance.retain]
      rw [ClassBalance.records_length, ClassBalance.records_length]
      exact counts
    rw [totalLength] at matching
    have label : (encNat g.toNat).length ≤ p := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr g.isLt
    have originalWire : (JoinedDissection.classEncoding (input, g.toNat)).length ≤ 3*B := by
      dsimp only [JoinedDissection.classEncoding]
      rw [length_encPair]
      dsimp only [B]
      omega
    have negBound := negate orient
    have negScale := mN (show (encBool orient).length ≤ B+1 by
      simp only [encBool_apply, List.length_singleton]; omega)
    have profile :
        (BatchedAccess.matchCertificate.comp (parameter.prod generated)).time (input, g.toNat)+
        (BatchedAccess.matchCertificate.comp (parameter.prod generated)).space (input, g.toNat) =
          10*(JoinedDissection.classEncoding (input, g.toNat)).length+
          3*(ClassBalance.orientationCertificate.time (input, g.toNat)+
            ClassBalance.orientationCertificate.space (input, g.toNat))+
          (NativeCertificate.ofPolyTime neg).time orient+
          (NativeCertificate.ofPolyTime neg).space orient+
          ClassBalance.recordsCertificate.time ((input, orient), g.toNat)+
          ClassBalance.recordsCertificate.space ((input, orient), g.toNat)+
          ClassBalance.recordsCertificate.time ((input, !orient), g.toNat)+
          ClassBalance.recordsCertificate.space ((input, !orient), g.toNat)+
          BatchedAccess.matchCertificate.time ((m, (orient, stored)), produced)+
          BatchedAccess.matchCertificate.space ((m, (orient, stored)), produced) := by
      dsimp only [parameter, generated, opposite, right, kept, original,
        ClassBalance.retainCertificate, NativeCertificate.congr,
        NativeCertificate.comp, NativeCertificate.prod, NativeCertificate.fst,
        NativeCertificate.snd, NativeCertificate.post, NativeCertificate.linear,
        Function.comp_def, id_eq, orient, stored, produced, ClassBalance.retain,
        input, ProgramGeneration.originalSource]
      ring
    dsimp only [NativeCertificate.congr]
    rw [profile]
    change _ ≤ (Q+leftCount+rightCount+1)*P B
    dsimp only [P]
    nlinarith only [ori, retainBound, produceBound, matching, counts, originalWire,
      negBound.1, negBound.2, negScale, Nat.zero_le (Q*M (4*(B+1))),
      Nat.zero_le ((Q+leftCount+rightCount)*N (B+1)),
      Nat.zero_le ((Q+leftCount+rightCount)*B)]

/-- Sum of installed search allowances on classes selecting restart, including skipped classes.
This is an unresolved cost expression, not a supplied runtime bound. -/
noncomputable def restartTime (input : ClassBalance.Input) : ℕ :=
  (Finset.range (2^ClassBalance.depth input)).sum (fun g =>
    if JoinedDissection.materialize input g then 0 else
      JoinedDissection.searchCertificate.time (input, g))

/-- Maximum installed workspace on classes selecting restart, including skipped classes. -/
noncomputable def restartSpace (input : ClassBalance.Input) : ℕ :=
  (Finset.range (2^ClassBalance.depth input)).sup (fun g =>
    if JoinedDissection.materialize input g then 0 else
      JoinedDissection.searchCertificate.space (input, g))

/-- Normalize all selected direct searches and their actual orientation/materialization
control, deriving simultaneous space from the computed smaller class. Only the selected
restarted searches remain explicit; no correctness or runtime conclusion is assumed. -/
theorem classSearch_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let q := as.length+bs.length+cs.length+ds.length
      let B := (ClassBalance.encoding input).length+q+p+1
      let Q := JoinedDissection.quarterBudget input
      let H := 2^(as.length+bs.length)+2^(cs.length+ds.length)
      WholeRunResources.classTime input ≤ restartTime input+(H+2^p*(Q+1))*P B ∧
        WholeRunResources.classSpace input ≤
          restartSpace input+(Q+ClassBalance.balance input+1)*P B := by
  obtain ⟨A, hA, mA, control⟩ := materialize_bounds
  obtain ⟨D, hD, mD, direct⟩ := directSearch_bounds
  let R := fun B => 2*(A B+D B)
  let P := fun B => 3*R B
  have monoR : Monotone R := fun _ _ h =>
    Nat.mul_le_mul_left 2 (Nat.add_le_add (mA h) (mD h))
  refine ⟨P, by dsimp only [P, R]; fun_prop,
    fun _ _ h => Nat.mul_le_mul_left 3 (monoR h), ?_⟩
  intro m p hp as bs cs ds s
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let q := as.length+bs.length+cs.length+ds.length
  let B := (ClassBalance.encoding input).length+q+p+1
  let Q := JoinedDissection.quarterBudget input
  let H := 2^(as.length+bs.length)+2^(cs.length+ds.length)
  have selected (g : BitVec p) (h : JoinedDissection.materialize input g.toNat = true) :
      JoinedDissection.searchCertificate.time (input, g.toNat)+
        JoinedDissection.searchCertificate.space (input, g.toNat) ≤
          (Q+ClassBalance.count input false g.toNat+
            ClassBalance.count input true g.toNat+1)*R B := by
    have tested := control hp as bs cs ds s g
    have searched := direct hp as bs cs ds s g
    change _ ≤ (Q+1)*A B at tested
    change _ ≤ (Q+ClassBalance.count input false g.toNat+
      ClassBalance.count input true g.toNat+1)*D B at searched
    have profile : JoinedDissection.searchCertificate.time (input, g.toNat)+
        JoinedDissection.searchCertificate.space (input, g.toNat) =
        JoinedDissection.materializeCertificate.time (input, g.toNat)+
        JoinedDissection.materializeCertificate.space (input, g.toNat)+
        JoinedDissection.directSearchCertificate.time (input, g.toNat)+
        JoinedDissection.directSearchCertificate.space (input, g.toNat) := by
      simp only [JoinedDissection.searchCertificate, NativeCertificate.congr,
        NativeCertificate.branch, h, ite_true]
      ring
    rw [profile]
    dsimp only [R]
    nlinarith only [tested, searched,
      Nat.zero_le ((ClassBalance.count input false g.toNat+
        ClassBalance.count input true g.toNat)*A B)]
  have pointTime (g : BitVec p) : JoinedDissection.searchCertificate.time (input, g.toNat) ≤
      (if JoinedDissection.materialize input g.toNat then 0 else
        JoinedDissection.searchCertificate.time (input, g.toNat))+
      (Q+ClassBalance.count input false g.toNat+ClassBalance.count input true g.toNat+1)*P B := by
    by_cases h : JoinedDissection.materialize input g.toNat = true
    · simp only [h, ite_true, Nat.zero_add]
      exact (Nat.le_add_right _ _).trans ((selected g h).trans
        (Nat.mul_le_mul_left _ (by dsimp only [P]; omega)))
    · simp only [h]
      exact Nat.le_add_right _ _
  have sums (f : ℕ → ℕ) : (∑ g : BitVec p, f g.toNat) =
      ∑ g ∈ Finset.range (2^p), f g :=
    (Fintype.sum_equiv BitVec.equivFin.toEquiv _ (fun g => f g.val) (fun _ => rfl)).trans
      (Fin.sum_univ_eq_sum_range f _)
  have depthEq : ClassBalance.depth input = p := rfl
  constructor
  · change WholeRunResources.classTime input ≤ restartTime input+(H+2^p*(Q+1))*P B
    have total := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => pointTime g)
    rw [Finset.sum_add_distrib, ← Finset.sum_mul,
      sums (fun n => JoinedDissection.searchCertificate.time (input, n))] at total
    have population : (∑ g : BitVec p,
        (Q+ClassBalance.count input false g.toNat+ClassBalance.count input true g.toNat+1)) =
          H+2^p*(Q+1) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        JoinedDissection.sum_counts hp as bs cs ds s false,
        JoinedDissection.sum_counts hp as bs cs ds s true]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_congr BitVec.equivFin.toEquiv, Fintype.card_fin, Nat.cast_id,
        Bool.false_eq_true, ite_false, ite_true]
      dsimp only [H]
      ring
    rw [population, sums (fun n => if JoinedDissection.materialize input n then 0 else
      JoinedDissection.searchCertificate.time (input, n))] at total
    dsimp only [WholeRunResources.classTime, restartTime]
    rw [depthEq]
    exact total
  · dsimp only [WholeRunResources.classSpace]
    rw [show ClassBalance.depth (ProgramGeneration.originalSource p as bs cs ds s 0) = p from rfl]
    with_reducible
      change (Finset.range (2^p)).sup
          (fun g => JoinedDissection.searchCertificate.space (input, g)) ≤
        restartSpace input+(Q+ClassBalance.balance input+1)*P B
    apply Finset.sup_le
    intro n hn
    have hn' : n < 2^p := Finset.mem_range.mp hn
    let g := BitVec.ofNat p n
    have natEq : g.toNat = n := Nat.mod_eq_of_lt hn'
    by_cases h : JoinedDissection.materialize input n = true
    · have actual := selected g (by simpa only [natEq] using h)
      rw [natEq] at actual
      have kept := ClassBalance.class_le_balance input n hn'
      rw [ClassBalance.retain, ClassBalance.records_length] at kept
      have test := of_decide_eq_true h
      change 0 < ClassBalance.count input (ClassBalance.retainRight input n) n ∧
        ClassBalance.count input (!(ClassBalance.retainRight input n)) n ≤
          ClassBalance.count input (ClassBalance.retainRight input n) n+Q at test
      have countSum : ClassBalance.count input false n+ClassBalance.count input true n =
          ClassBalance.count input (ClassBalance.retainRight input n) n+
          ClassBalance.count input (!(ClassBalance.retainRight input n)) n := by
        cases ClassBalance.retainRight input n <;>
          simp only [Bool.not_false, Bool.not_true]; omega
      have volume : Q+ClassBalance.count input false n+ClassBalance.count input true n+1 ≤
          3*(Q+ClassBalance.balance input+1) := by omega
      have upper := actual.trans (Nat.mul_le_mul_right (R B) volume)
      change _ ≤ restartSpace input+(Q+ClassBalance.balance input+1)*P B
      dsimp only [P]
      nlinarith only [upper, Nat.zero_le (restartSpace input)]
    · have maximum := Finset.le_sup (f := fun g =>
        if JoinedDissection.materialize input g then 0 else
          JoinedDissection.searchCertificate.space (input, g)) hn
      simp only [h] at maximum
      change _ ≤ restartSpace input at maximum
      exact maximum.trans (Nat.le_add_right _ _)

/-- Whole original-input resource composition after normalizing selected direct searches.
Only actual selected restarted-search clocks/workspaces remain explicit. Those expressions
are not hypotheses; sharp normalization of them is still required for the full source theorem. -/
theorem sourceCertificate_restart_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (m p : ℕ) (s : BitVec m) (tail : List (BitVec m)),
      let original := Source.ofWords p s tail
      let prepared := Source.prepare original
      let I := (Source.encoding original).length
      JoinedDissection.sourceCertificate.time original ≤
          (restartTime prepared+2^(tail.length/2))*P I ∧
        JoinedDissection.sourceCertificate.space original ≤
          (restartSpace prepared+2^(tail.length/4)+ClassBalance.balance prepared)*P I := by
  obtain ⟨A, hA, mA, classes⟩ := classSearch_bounds
  obtain ⟨D, hD, mD, layout⟩ := WholeRunResources.sourceScalarWidth
  obtain ⟨W, hW, mW, whole⟩ := BalanceResources.sourceCertificate_search_bounds
  let P := fun I => 20*(A (D I)+1)*(W I+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 20
      (Nat.add_le_add_right (mA (mD hab)) 1)) (Nat.add_le_add_right (mW hab) 1)
  · intro m p s tail
    let original := Source.ofWords p s tail
    let prepared := Source.prepare original
    let I := (Source.encoding original).length
    let k := tail.length/4
    let d := min p (min m k)
    let Q := JoinedDissection.quarterBudget prepared
    let G := 2^d
    let quarter := 2^k
    let half := 2^(tail.length/2)
    let H := 2^((Source.quarters tail).1.1.length+(Source.quarters tail).1.2.length)+
      2^((Source.quarters tail).2.1.length+(Source.quarters tail).2.2.length)
    have hp : d ≤ m := (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
    have hk : d ≤ k := (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
    have preparedEq : prepared = ProgramGeneration.originalSource d
        (Source.quarters tail).1.1 (Source.quarters tail).1.2
        (Source.quarters tail).2.1 (Source.quarters tail).2.2 s 0 := Source.prepare_ofWords p s tail
    have depthEq : ClassBalance.depth prepared = d := by rw [preparedEq]; rfl
    have total := congrArg List.length (Source.quarters_append tail)
    simp only [List.length_append] at total
    have total' : (Source.quarters tail).1.1.length+(Source.quarters tail).1.2.length+
        (Source.quarters tail).2.1.length+(Source.quarters tail).2.2.length = tail.length := by
      omega
    have scalar : (ClassBalance.encoding prepared).length+tail.length+d+1 ≤ D I := by
      have h := layout m p s tail
      change (ClassBalance.encoding prepared).length+tail.length+
        ClassBalance.depth prepared+1 ≤ D I at h
      rw [depthEq] at h
      exact h
    have normalized := mA scalar
    have actual := classes hp (Source.quarters tail).1.1 (Source.quarters tail).1.2
      (Source.quarters tail).2.1 (Source.quarters tail).2.2 s
    have searched : WholeRunResources.classTime prepared ≤
          restartTime prepared+(H+G*(Q+1))*A (D I) ∧
        WholeRunResources.classSpace prepared ≤
          restartSpace prepared+(Q+ClassBalance.balance prepared+1)*A (D I) := by
      have typed : WholeRunResources.classTime prepared ≤
            restartTime prepared+(H+G*(Q+1))*
              A ((ClassBalance.encoding prepared).length+tail.length+d+1) ∧
          WholeRunResources.classSpace prepared ≤
            restartSpace prepared+(Q+ClassBalance.balance prepared+1)*
              A ((ClassBalance.encoding prepared).length+tail.length+d+1) := by
        dsimp only [H, G, Q]
        rw [preparedEq]
        simpa only [total'] using actual
      exact ⟨typed.1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ normalized) _),
        typed.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ normalized) _)⟩
    have quarters : Q ≤ 11*quarter := JoinedDissection.quarterBudget_source p s tail
    have labels : G ≤ quarter := Nat.pow_le_pow_right (by decide) hk
    have positive : 1 ≤ quarter := Nat.two_pow_pos _
    have square : quarter*quarter ≤ half := by
      dsimp only [quarter, half]
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by dsimp only [k]; omega)
    have lengths := Source.quarters_lengths tail
    dsimp only at lengths
    have leftExp : (Source.quarters tail).1.1.length+(Source.quarters tail).1.2.length ≤
        tail.length/2 := by omega
    have rightExp : (Source.quarters tail).2.1.length+(Source.quarters tail).2.2.length ≤
        tail.length/2+2 := by omega
    have leftSize := Nat.pow_le_pow_right (by decide : 1 ≤ 2) leftExp
    have rightSize := Nat.pow_le_pow_right (by decide : 1 ≤ 2) rightExp
    have rightCeiling : (2 : ℕ)^(tail.length/2+2) = 4*half := by
      dsimp only [half]
      rw [pow_add]
      norm_num
      ring
    rw [rightCeiling] at rightSize
    have halves : H ≤ 5*half := by dsimp only [H, half]; omega
    have work : H+G*(Q+1) ≤ 20*half := by
      have scale := Nat.mul_le_mul labels (show Q+1 ≤ 12*quarter by omega)
      nlinarith only [halves, scale, square]
    have workspace : Q+ClassBalance.balance prepared+1 ≤
        12*(quarter+ClassBalance.balance prepared) := by omega
    have classTime := searched.1.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right (A (D I)) work) _)
    have classSpace := searched.2.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right (A (D I)) workspace) _)
    have source := whole m p s tail
    constructor
    · have upper := source.1.trans (Nat.mul_le_mul_right (W I)
        (Nat.add_le_add_right classTime half))
      change _ ≤ (restartTime prepared+half)*P I
      dsimp only [P]
      nlinarith only [upper, Nat.zero_le (restartTime prepared*A (D I)*W I),
        Nat.zero_le (restartTime prepared*A (D I)), Nat.zero_le (restartTime prepared),
        Nat.zero_le (half*A (D I)), Nat.zero_le half]
    · have upper := source.2.trans (Nat.mul_le_mul_right (W I)
        (Nat.add_le_add_right classSpace quarter))
      change _ ≤ (restartSpace prepared+quarter+ClassBalance.balance prepared)*P I
      dsimp only [P]
      nlinarith only [upper, Nat.zero_le (restartSpace prepared*A (D I)*W I),
        Nat.zero_le (restartSpace prepared*A (D I)), Nat.zero_le (restartSpace prepared),
        Nat.zero_le ((quarter+ClassBalance.balance prepared)*A (D I)),
        Nat.zero_le (quarter+ClassBalance.balance prepared)]

end Cslib.Cryptanalysis.AddXNOR.SearchResources
