/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORMatcherResources
import all CslibFrontier.Cryptanalysis.AddXNORSortedMeet
import all CslibFrontier.Cryptanalysis.AddXNORSortedQuarterMachine
import all CslibFrontier.Cryptanalysis.AddXNORClassJoin
import all CslibFrontier.Cryptanalysis.AddXNORClassBatches
import all CslibFrontier.Cryptanalysis.AddXNORJoinedDissection
import all CslibFrontier.Cryptanalysis.AddXNORClassBalance
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatchBounds
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyCount
import all CslibFrontier.Computability.GenericRAM.Native.Combinators

/-!
# Physical-width resources of the executed dissection producers

Normalize the actual forward/inverse quarter generation, projected record sorting
and one-pass count certificates. Reversal, reflection and sorting are executed;
no supplied producer or resource contract is used. These bounds are components
of the sorted-list route to [WangLvShenZhang2027], Lemma 8/Theorem 7, PDF pp. 21–22.
Window emission and its scalar count/division control are normalized separately in
`AddXNORRestartResources`; complete solver profile composition remains open.
Count and reconstruction phase sums are not total clocks.

## Main definitions

* `quarterVolume`, `countVolume`: actual generated populations for either direction.
* `countAllowance`, `restartCountAllowance`: count phase budgets before and during restarts.
* `restartPairs`, `reconstructionAllowance`: the actual reconstructed window and its profiles.

## Main results

* `inverseCertificate_bounds`, `countCertificate_bounds`, `projectedCount_bounds`:
  normalization of the installed preparation/generation/sort/count certificates.
* `original_count_bounds`, `original_restarted_count_bounds`: original-width count sums.
* `original_reconstruction_bounds`, `original_reconstruction_sum`: actual full-state callbacks,
  including input/output/intermediate tapes, summed clocks and every-batch prefix workspace.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.ProducerResources
open Turing.MultiTapeTM Cslib.GenericRAM

private abbrev er := RadixPartition.recordEncoding
private abbrev el := encList er

private theorem quarter_wire (input : SortedQuarterMachine.Input) :
    (SortedQuarterMachine.run input).length = 2 ^ input.2.length ∧
      streamRecordLength er (SortedQuarterMachine.run input) ≤
        3*(SortedQuarterMachine.encoding input).length+1 ∧
      (el (SortedQuarterMachine.run input)).length ≤
        2 ^ input.2.length*(6*(SortedQuarterMachine.encoding input).length+3) := by
  have h := SortedQuarterMachine.records_wire input
  have perm := (RadixSort.prefix_invariants
    ((SortedQuarterMachine.indices input.2.length).map (SortedQuarterMachine.record input))
    input.1.1).2
  refine ⟨?_, ?_, ?_⟩
  · exact perm.length_eq.trans h.1
  · apply listMax_le
    intro r hr
    exact (le_listMax (f := fun row => (er row).length) (perm.mem_iff.mp hr)).trans h.2.1
  · exact (length_encList_le er _ (fun r hr =>
      (le_listMax (f := fun row => (er row).length) (perm.mem_iff.mp hr)).trans h.2.1)).trans_eq
        (by rw [perm.length_eq, h.1]; ring)

/-- The installed inverse-quarter certificate, including actual input preparation,
forward generation and output reflection, is quarter-scale in time and prefix workspace.
The same fixed polynomial also bounds every emitted record's physical wire. -/
theorem inverseCertificate_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ input : SortedQuarterMachine.Input,
      SortedMeet.inverseCertificate.time input + SortedMeet.inverseCertificate.space input ≤
          (2 ^ input.2.length+1) * P ((SortedQuarterMachine.encoding input).length+1) ∧
      streamRecordLength RadixPartition.recordEncoding (SortedMeet.inverse input) ≤
        P ((SortedQuarterMachine.encoding input).length+1) := by
  obtain ⟨D, hD, mD, output⟩ := exists_mono_poly SortedMeet.inverseInput_polyTime.polyBounded_length
  obtain ⟨C, hC, mC, preparation⟩ := exists_mono_poly_cert SortedMeet.inverseInput_polyTime
  let G := Classical.choose SortedQuarterMachine.run_computable
  have hG := (Classical.choose_spec SortedQuarterMachine.run_computable).1
  have mG : Monotone G := (Classical.choose_spec SortedQuarterMachine.run_computable).2.1
  let F := Classical.choose SortedMeet.reflect_computable
  have hF := (Classical.choose_spec SortedMeet.reflect_computable).1
  have mF : Monotone F := (Classical.choose_spec SortedMeet.reflect_computable).2.1
  let E := fun B => B + D B + 1
  let U := fun B => E B + C B + G (D B+1) + F (5*E B) + 1
  let P := fun B => 100*U B
  have monoE : Monotone E := by intro a b hab; have := mD hab; dsimp only [E]; omega
  have monoU : Monotone U := by
    intro a b hab
    have he := monoE hab
    have hc : C a ≤ C b := mC hab
    have hg : G (D a+1) ≤ G (D b+1) := mG (by have := mD hab; omega)
    have hf : F (5*E a) ≤ F (5*E b) := mF (by omega)
    dsimp only [U]; omega
  refine ⟨P, by dsimp only [P, U, E]; fun_prop,
    fun _ _ h => Nat.mul_le_mul_left 100 (monoU h), ?_⟩
  intro input
  let B := (SortedQuarterMachine.encoding input).length+1
  let N := 2 ^ input.2.length+1
  let prepared := SortedMeet.inverseInput input
  let rows := SortedQuarterMachine.run prepared
  have fields := SortedQuarterMachine.input_fields input
  have width : input.1.1 ≤ B := by dsimp only [B]; omega
  have prepWire : (SortedQuarterMachine.encoding prepared).length ≤ D B :=
    (output input).trans (mD (by dsimp only [B]; omega))
  obtain ⟨lengthRows, rowWidth, rowWire⟩ := quarter_wire prepared
  have lengthPrepared : prepared.2.length = input.2.length := by
    simp only [prepared, SortedMeet.inverseInput, List.length_reverse]
  rw [lengthPrepared] at lengthRows rowWire
  have positiveU : 1 ≤ U B := by dsimp only [U]; omega
  have eu : E B ≤ U B := by dsimp only [U]; omega
  have cb : C B ≤ U B := by dsimp only [U]; omega
  have gb : G (D B+1) ≤ U B := by dsimp only [U]; omega
  have fb : F (5*E B) ≤ U B := by dsimp only [U]; omega
  have eb : B ≤ E B := by dsimp only [E]; omega
  have db : D B ≤ E B := by dsimp only [E]; omega
  have prepar := preparation input
  have ct := mC (show (SortedQuarterMachine.encoding input).length ≤ B by dsimp only [B]; omega)
  have prepBound :
      (NativeCertificate.ofPolyTime SortedMeet.inverseInput_polyTime).time input +
        (NativeCertificate.ofPolyTime SortedMeet.inverseInput_polyTime).space input ≤
          2*U B := by omega
  have gmono : G ((SortedQuarterMachine.encoding prepared).length+1) ≤ U B :=
    (mG (by omega)).trans gb
  have generation : SortedMeet.quarterCertificate.time prepared +
      SortedMeet.quarterCertificate.space prepared ≤ 2*N*U B := by
    change (2^prepared.2.length+1)*G ((SortedQuarterMachine.encoding prepared).length+1) +
      (2^prepared.2.length+1)*G ((SortedQuarterMachine.encoding prepared).length+1) ≤ _
    rw [lengthPrepared]
    change N*G ((SortedQuarterMachine.encoding prepared).length+1) +
      N*G ((SortedQuarterMachine.encoding prepared).length+1) ≤ _
    have h := Nat.mul_le_mul_left N gmono
    nlinarith only [h]
  have reflectWire : (encPair encUnary el (input.1.1, rows)).length ≤ 10*N*U B := by
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    change (el rows).length ≤ _ at rowWire
    have hN : 1 ≤ N := by dsimp only [N]; omega
    have hrow := rowWire.trans (Nat.mul_le_mul_left (2^input.2.length)
      (by omega : 6*(SortedQuarterMachine.encoding prepared).length+3 ≤ 10*U B))
    have nEq : N = 2^input.2.length+1 := rfl
    nlinarith only [hrow, width, eb, eu, hN, nEq, positiveU]
  have reflectArg : streamFilterWidth encUnary er (input.1.1, rows) ≤ 5*E B := by
    dsimp only [streamFilterWidth]
    simp only [encUnary_apply, List.length_replicate]
    change streamRecordLength er rows ≤ _ at rowWidth
    dsimp only [E]
    omega
  have fmono : F (streamFilterWidth encUnary er (input.1.1, rows)) ≤ U B :=
    (mF reflectArg).trans fb
  have reflection : SortedMeet.reflectCertificate.time (input.1.1, rows) +
      SortedMeet.reflectCertificate.space (input.1.1, rows) ≤ 22*N*U B := by
    change ((encPair encUnary el (input.1.1, rows)).length +
      (rows.length+1)*F (streamFilterWidth encUnary er (input.1.1, rows))) +
      ((encPair encUnary el (input.1.1, rows)).length +
        (rows.length+1)*F (streamFilterWidth encUnary er (input.1.1, rows))) ≤ _
    change rows.length = _ at lengthRows
    rw [lengthRows]
    change (encPair encUnary el (input.1.1, rows)).length +
      N*F (streamFilterWidth encUnary er (input.1.1, rows)) +
      ((encPair encUnary el (input.1.1, rows)).length +
        N*F (streamFilterWidth encUnary er (input.1.1, rows))) ≤ _
    have callback := Nat.mul_le_mul_left N fmono
    nlinarith only [reflectWire, callback]
  constructor
  · have profile : SortedMeet.inverseCertificate.time input +
        SortedMeet.inverseCertificate.space input = 2*(SortedQuarterMachine.encoding input).length +
          ((NativeCertificate.ofPolyTime SortedMeet.inverseInput_polyTime).time input +
            (NativeCertificate.ofPolyTime SortedMeet.inverseInput_polyTime).space input) +
          (SortedMeet.quarterCertificate.time prepared+
            SortedMeet.quarterCertificate.space prepared)+
          (SortedMeet.reflectCertificate.time (input.1.1, rows)+
            SortedMeet.reflectCertificate.space (input.1.1, rows)) := by
      dsimp only [SortedMeet.inverseCertificate, NativeCertificate.congr, NativeCertificate.comp,
        NativeCertificate.prod, NativeCertificate.fst, NativeCertificate.post,
        NativeCertificate.linear, Function.comp_def, id_eq, prepared, rows]
      ring
    rw [profile]
    change _ ≤ N*P B
    dsimp only [P]
    have hN : 1 ≤ N := by dsimp only [N]; omega
    have iBound : (SortedQuarterMachine.encoding input).length ≤ U B := by
      have h : B ≤ U B := eb.trans eu
      dsimp only [B] at h
      omega
    nlinarith only [prepBound, generation, reflection, hN, iBound, Nat.zero_le (N*U B)]
  · apply listMax_le
    intro r hr
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hr
    have old := (le_listMax (f := fun row => (er row).length) hrow).trans rowWidth
    have key : (encNat (2^input.1.1-1-row.1)).length ≤ input.1.1 := by
      have hk : 2^input.1.1-1-row.1 < 2^input.1.1 := by
        have positive : 0 < 2^input.1.1 := Nat.two_pow_pos _
        omega
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr hk
    simp only [er, RadixPartition.recordEncoding, length_encPair] at old ⊢
    change 2*(encNat (2^input.1.1-1-row.1)).length+1+(encNat row.2).length ≤ P B
    dsimp only [P]
    nlinarith only [key, old, width, prepWire, db, eb, eu, positiveU]

/-- Actual quarter population generated for one projected class, before any Cartesian joins. -/
@[expose] def quarterVolume (input : ClassJoin.Input) : ℕ :=
  let ((_, (first, second)), _) := input
  2^first.length + 2^second.length

private def forwardInput (input : ClassJoin.Input) : SortedQuarterMachine.Input :=
  let (((width, seed), (first, _)), _) := input
  ((width, seed), first)

private def inverseInput (input : ClassJoin.Input) : SortedQuarterMachine.Input :=
  let (((width, _), (_, second)), target) := input
  ((width, target), second)

private theorem sorting_profile (input : ClassJoin.Input) :
    ClassJoin.sortedCertificate.time input + ClassJoin.sortedCertificate.space input ≤
      30*(ClassJoin.encoding input).length +
        2*(SortedMeet.quarterCertificate.time (forwardInput input)+
          SortedMeet.quarterCertificate.space (forwardInput input)) +
        2*(SortedMeet.inverseCertificate.time (inverseInput input)+
          SortedMeet.inverseCertificate.space (inverseInput input)) +
        SortedMatch.runCertificate.time (ClassJoin.batches input)+
          SortedMatch.runCertificate.space (ClassJoin.batches input) := by
  have timeEq : ClassJoin.sortedCertificate.time input = 15*(ClassJoin.encoding input).length +
      2*SortedMeet.quarterCertificate.time (forwardInput input)+
      2*SortedMeet.inverseCertificate.time (inverseInput input)+
      SortedMatch.tagCertificate.time (false, (ClassJoin.batches input).2.1)+
      SortedMatch.tagCertificate.time (true, (ClassJoin.batches input).2.2)+
      SortedMatch.sortCertificate.time
        ((ClassJoin.batches input).1, SortedMatch.tagged (ClassJoin.batches input)) := by
    dsimp only [ClassJoin.sortedCertificate, NativeCertificate.congr, NativeCertificate.comp,
      NativeCertificate.prod, NativeCertificate.fst, NativeCertificate.snd, NativeCertificate.post,
      NativeCertificate.const, NativeCertificate.linear, Function.comp_def, id_eq,
      forwardInput, inverseInput, ClassJoin.batches, SortedMatch.tagged]
    ring
  have spaceEq : ClassJoin.sortedCertificate.space input = 15*(ClassJoin.encoding input).length +
      2*SortedMeet.quarterCertificate.space (forwardInput input)+
      2*SortedMeet.inverseCertificate.space (inverseInput input)+
      SortedMatch.tagCertificate.space (false, (ClassJoin.batches input).2.1)+
      SortedMatch.tagCertificate.space (true, (ClassJoin.batches input).2.2)+
      SortedMatch.sortCertificate.space
        ((ClassJoin.batches input).1, SortedMatch.tagged (ClassJoin.batches input)) := by
    dsimp only [ClassJoin.sortedCertificate, NativeCertificate.congr, NativeCertificate.comp,
      NativeCertificate.prod, NativeCertificate.fst, NativeCertificate.snd, NativeCertificate.post,
      NativeCertificate.const, NativeCertificate.linear, Function.comp_def, id_eq,
      forwardInput, inverseInput, ClassJoin.batches, SortedMatch.tagged]
    ring
  rw [timeEq, spaceEq, (SortedMatch.profile_eq (ClassJoin.batches input)).1,
    (SortedMatch.profile_eq (ClassJoin.batches input)).2]
  omega

/-- Actual generation in both directions, tagging, radix sorting and direct one-pass counting
have quarter-scale time and every-prefix workspace in physical input width. Binary counter
size is derived from the generated quarter populations; no class-size, count or runtime
conclusion is supplied. The coefficient is fixed before arbitrary runtime widths/operands. -/
theorem countCertificate_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ input : ClassJoin.Input,
      ClassJoin.countCertificate.time input + ClassJoin.countCertificate.space input ≤
        (quarterVolume input+1)*P ((ClassJoin.encoding input).length+1) := by
  obtain ⟨I, hI, mI, inverse⟩ := inverseCertificate_bounds
  obtain ⟨M, hM, mM, matcher⟩ := SortedMatch.runCertificate_bounds
  obtain ⟨A, hA, mA, tagWire⟩ := exists_mono_poly
    (ComputableInPolyTime.of_tidy SortedMatch.tag_polyTime).polyBounded_length
  let G := Classical.choose SortedQuarterMachine.run_computable
  have hG := (Classical.choose_spec SortedQuarterMachine.run_computable).1
  have mG : Monotone G := (Classical.choose_spec SortedQuarterMachine.run_computable).2.1
  let K := Classical.choose KeyCount.run_computable
  have hK := (Classical.choose_spec KeyCount.run_computable).1
  have mK : Monotone K := (Classical.choose_spec KeyCount.run_computable).2.1
  let D := fun B => 20*(B+1)+I (5*B)
  let R := fun B => A (D B+3)+2*B+10
  let U := fun B => 100*(B+1)+G (5*B)+I (5*B)+M (D B)+K (R B)+A (D B+3)+1
  let P := fun B => 100*U B
  have monoD : Monotone D := by
    intro a b hab
    have h := mI (by omega : 5*a ≤ 5*b)
    dsimp only [D]; omega
  have monoR : Monotone R := by
    intro a b hab
    have h := mA (by have := monoD hab; omega : D a+3 ≤ D b+3)
    dsimp only [R]; omega
  have monoU : Monotone U := by
    intro a b hab
    have hg : G (5*a) ≤ G (5*b) := mG (by omega)
    have hi := mI (by omega : 5*a ≤ 5*b)
    have hm := mM (monoD hab)
    have hk : K (R a) ≤ K (R b) := mK (monoR hab)
    have ha := mA (by have := monoD hab; omega : D a+3 ≤ D b+3)
    dsimp only [U]; omega
  refine ⟨P, by dsimp only [P, U, R, D]; fun_prop,
    fun _ _ h => Nat.mul_le_mul_left 100 (monoU h), ?_⟩
  rintro ⟨⟨⟨w, seed⟩, first, second⟩, target⟩
  let input : ClassJoin.Input := (((w, seed), (first, second)), target)
  let B := (ClassJoin.encoding input).length+1
  let N := quarterVolume input+1
  let forward := forwardInput input
  let backward := inverseInput input
  have wires : (SortedQuarterMachine.encoding forward).length+1 ≤ 5*B ∧
      (SortedQuarterMachine.encoding backward).length+1 ≤ 5*B ∧ w ≤ B ∧
      first.length ≤ B ∧ second.length ≤ B := by
    have hf := length_le_length_encList encNat first
    have hs := length_le_length_encList encNat second
    dsimp only [forward, backward, forwardInput, inverseInput, B, input]
    simp only [ClassJoin.encoding, SortedMeet.encoding, SortedQuarterMachine.encoding,
      length_encPair, encUnary_apply, List.length_replicate]
    omega
  have gu : G (5*B) ≤ U B := by dsimp only [U]; omega
  have iu : I (5*B) ≤ U B := by dsimp only [U]; omega
  have mu : M (D B) ≤ U B := by dsimp only [U]; omega
  have ku : K (R B) ≤ U B := by dsimp only [U]; omega
  have au : A (D B+3) ≤ U B := by dsimp only [U]; omega
  have bu : B+1 ≤ U B := by dsimp only [U]; omega
  have firstPositive : 0 < 2^first.length := Nat.two_pow_pos _
  have secondPositive : 0 < 2^second.length := Nat.two_pow_pos _
  have forwardGen : SortedMeet.quarterCertificate.time forward +
      SortedMeet.quarterCertificate.space forward ≤ 2*N*U B := by
    change (2^first.length+1)*G ((SortedQuarterMachine.encoding forward).length+1) +
      (2^first.length+1)*G ((SortedQuarterMachine.encoding forward).length+1) ≤ _
    have callback := (mG wires.1).trans gu
    have scale : 2^first.length+1 ≤ N := by dsimp only [N, quarterVolume, input]; omega
    have h := Nat.mul_le_mul scale callback
    nlinarith only [h]
  have backwardGen : SortedMeet.inverseCertificate.time backward +
      SortedMeet.inverseCertificate.space backward ≤ N*U B := by
    have h := (inverse backward).1
    have callback := (mI wires.2.1).trans iu
    have scale : 2^backward.2.length+1 ≤ N := by
      dsimp only [backward, inverseInput, N, quarterVolume, input]; omega
    exact h.trans (Nat.mul_le_mul scale callback)
  obtain ⟨forwardLen, forwardMax, _⟩ := quarter_wire forward
  change (SortedQuarterMachine.run forward).length = 2^first.length at forwardLen
  have backwardLen : (SortedMeet.inverse backward).length = 2^second.length := by
    simp only [SortedMeet.inverse, List.length_map, ClassJoin.quarter_length,
      SortedMeet.inverseInput, List.length_reverse, backward, inverseInput, input]
  have backwardMax := (inverse backward).2.trans (mI wires.2.1)
  have rowWidth : ∀ r ∈ (ClassJoin.batches input).2.1 ++ (ClassJoin.batches input).2.2,
      (er r).length ≤ D B - w - 1 := by
    intro r hr
    rcases List.mem_append.mp hr with hf | hb
    · have row := (le_listMax (f := fun row => (er row).length) hf).trans forwardMax
      change (er r).length ≤ 3*(SortedQuarterMachine.encoding forward).length+1 at row
      dsimp only [D]; omega
    · have row := (le_listMax (f := fun row => (er row).length) hb).trans backwardMax
      dsimp only [D]; omega
  have matcherWidth : SortedMatch.inputWidth (ClassJoin.batches input) ≤ D B := by
    have maxRow := listMax_le rowWidth
    change streamRecordLength er _ ≤ D B-w-1 at maxRow
    change w + streamRecordLength er
      ((ClassJoin.batches input).2.1 ++ (ClassJoin.batches input).2.2) + 1 ≤ D B
    dsimp only [D] at maxRow ⊢
    omega
  have matching : SortedMatch.runCertificate.time (ClassJoin.batches input)+
      SortedMatch.runCertificate.space (ClassJoin.batches input) ≤ N*U B := by
    have h := matcher (ClassJoin.batches input)
    have lengthEq : (ClassJoin.batches input).2.1.length +
        (ClassJoin.batches input).2.2.length+1 = N := by
      change (SortedQuarterMachine.run forward).length+(SortedMeet.inverse backward).length+1 = _
      rw [forwardLen, backwardLen]
      rfl
    dsimp only at h
    rw [lengthEq] at h
    exact h.trans (Nat.mul_le_mul_left N ((mM matcherWidth).trans mu))
  have sorted : ClassJoin.sortedCertificate.time input+ClassJoin.sortedCertificate.space input ≤
      40*N*U B := by
    have h := sorting_profile input
    have hN : 1 ≤ N := by dsimp only [N]; omega
    have inputWire : (ClassJoin.encoding input).length ≤ U B := by
      have h := bu; dsimp only [B] at h; omega
    nlinarith only [h, forwardGen, backwardGen, matching, hN, inputWire]
  have lengthSorted : (ClassJoin.sortedRecords input).length = quarterVolume input := by
    simpa only [ClassJoin.groups, KeyGrouping.flatten_run, quarterVolume]
      using ClassJoin.groups_input_length input
  have taggedMax : streamRecordLength er (SortedMatch.tagged (ClassJoin.batches input)) ≤
      A (D B+3) := by
    apply listMax_le
    intro r hr
    rcases List.mem_append.mp hr with hf | hb
    · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hf
      have old := rowWidth row (List.mem_append_left _ hrow)
      have h := tagWire (false, row)
      have arg : (encPair encBool er (false, row)).length ≤ D B+3 := by
        simp only [length_encPair, encBool_apply, List.length_singleton]; omega
      exact h.trans (mA arg)
    · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hb
      have old := rowWidth row (List.mem_append_right _ hrow)
      have h := tagWire (true, row)
      have arg : (encPair encBool er (true, row)).length ≤ D B+3 := by
        simp only [length_encPair, encBool_apply, List.length_singleton]; omega
      exact h.trans (mA arg)
  have sortedMax : streamRecordLength er (ClassJoin.sortedRecords input) ≤ A (D B+3) := by
    apply listMax_le
    intro row hr
    exact (le_listMax (f := fun row => (er row).length)
      ((SortedMatch.sorted_perm (ClassJoin.batches input)).mem_iff.mp hr)).trans taggedMax
  have counter : (encNat ((ClassJoin.sortedRecords input).length^2+1)).length ≤ 2*B+5 := by
    have hf := Nat.pow_le_pow_right (by decide : 1 ≤ 2) wires.2.2.2.1
    have hs := Nat.pow_le_pow_right (by decide : 1 ≤ 2) wires.2.2.2.2
    have population : quarterVolume input ≤ 2^(B+1) := by
      dsimp only [quarterVolume, input]
      rw [pow_succ]
      omega
    have square : (quarterVolume input)^2+1 ≤ 2^(2*(B+2)) := by
      have h := Nat.pow_le_pow_left population 2
      have positive : 0 < 2^(B+1) := Nat.two_pow_pos _
      rw [show 2*(B+2) = (B+1)*2+2 by omega, pow_add, pow_mul]
      norm_num
      nlinarith only [h, positive]
    have size := (Nat.size_le_size square).trans_eq (Nat.size_pow)
    rw [lengthSorted]
    have finalSize : Nat.size ((quarterVolume input)^2+1) ≤ 2*B+5 := by omega
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using finalSize
  have countWidth : KeyCount.width (ClassJoin.sortedRecords input) ≤ R B := by
    change streamRecordLength er (ClassJoin.sortedRecords input) +
      (encNat ((ClassJoin.sortedRecords input).length^2+1)).length+1 ≤ R B
    dsimp only [R]
    omega
  have countWire : (el (ClassJoin.sortedRecords input)).length ≤ 3*N*U B := by
    have h := length_encList_le er (ClassJoin.sortedRecords input) (fun r hr =>
      (le_listMax (f := fun row => (er row).length) hr).trans sortedMax)
    rw [lengthSorted] at h
    have hN : quarterVolume input+1 = N := rfl
    nlinarith only [h, au, bu, hN]
  have countCallback : K (KeyCount.width (ClassJoin.sortedRecords input)) ≤ U B :=
    (mK countWidth).trans ku
  have countProfile : ClassJoin.countCertificate.time input+ClassJoin.countCertificate.space input =
      ClassJoin.sortedCertificate.time input+ClassJoin.sortedCertificate.space input+
        2*(el (ClassJoin.sortedRecords input)).length+
        ((ClassJoin.sortedRecords input).length+2)*
          K (KeyCount.width (ClassJoin.sortedRecords input)) := by
    dsimp only [ClassJoin.countCertificate, NativeCertificate.congr, NativeCertificate.comp]
    ring
  rw [countProfile]
  change _ ≤ N*P B
  dsimp only [P]
  have callback := Nat.mul_le_mul_left N countCallback
  have hN : (ClassJoin.sortedRecords input).length+1 = N := by rw [lengthSorted]
  nlinarith only [sorted, countWire, callback, countCallback, hN]

/-- Quarter population actually generated by a forward or backward projected count. -/
def countVolume (input : ClassBalance.Input) (right : Bool) : ℕ :=
  let (_, (first, second)) := ClassBalance.halfInput input right
  2^first.length + 2^second.length

private abbrev countEncoding := encPair (encPair ClassBalance.encoding encBool) encNat

private theorem countVolume_eq (input : ClassBalance.Input) (right : Bool) (g : ℕ) :
    quarterVolume (ClassBalance.queryInput input right g) = countVolume input right := by
  simp only [quarterVolume, ClassBalance.queryInput, countVolume, List.length_map]

/-- Original full-state input preparation and either projected count use actual quarter-scale
profiles. The physical input includes the binary class index; it never includes a generated
quarter list as advice. -/
theorem projectedCount_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (input : ClassBalance.Input) (right : Bool) (g : ℕ),
      ClassBalance.countCertificate.time ((input, right), g)+
        ClassBalance.countCertificate.space ((input, right), g) ≤
          (countVolume input right+1)*P
            ((encPair (encPair ClassBalance.encoding encBool) encNat
              ((input, right), g)).length+1) := by
  obtain ⟨A, hA, mA, preparation⟩ := exists_mono_poly_cert ClassBalance.queryInput_polyTime
  obtain ⟨D, hD, mD, output⟩ := exists_mono_poly ClassBalance.queryInput_polyTime.polyBounded_length
  obtain ⟨C, hC, mC, counts⟩ := countCertificate_bounds
  let P := fun B => 2*A B+C (D B+1)
  have mono : Monotone P := by
    intro a b hab
    have h₁ := mA hab
    have h₂ := mC (by have := mD hab; omega : D a+1 ≤ D b+1)
    dsimp only [P]; omega
  refine ⟨P, by dsimp only [P]; fun_prop, mono, ?_⟩
  intro input right g
  let task := ((input, right), g)
  let B := (countEncoding task).length+1
  have prep := preparation task
  have monoA := mA (show (countEncoding task).length ≤ B by dsimp only [B]; omega)
  have wire := (output task).trans
    (mD (show (countEncoding task).length ≤ B by dsimp only [B]; omega))
  change (ClassJoin.encoding (ClassBalance.queryInput input right g)).length ≤ D B at wire
  have actual := counts (ClassBalance.queryInput input right g)
  have scalar := mC (by omega :
    (ClassJoin.encoding (ClassBalance.queryInput input right g)).length+1 ≤ D B+1)
  rw [countVolume_eq] at actual
  have counted := actual.trans (Nat.mul_le_mul_left (countVolume input right+1) scalar)
  have profile : ClassBalance.countCertificate.time task+ClassBalance.countCertificate.space task =
      (NativeCertificate.ofPolyTime ClassBalance.queryInput_polyTime).time task+
        (NativeCertificate.ofPolyTime ClassBalance.queryInput_polyTime).space task+
        ClassJoin.countCertificate.time (ClassBalance.queryInput input right g)+
        ClassJoin.countCertificate.space (ClassBalance.queryInput input right g) := by
    dsimp only [ClassBalance.countCertificate, NativeCertificate.congr,
      NativeCertificate.comp, task]
    ring
  rw [profile]
  change _ ≤ (countVolume input right+1)*P B
  dsimp only [P]
  have prepBound : (NativeCertificate.ofPolyTime ClassBalance.queryInput_polyTime).time task+
      (NativeCertificate.ofPolyTime ClassBalance.queryInput_polyTime).space task ≤ 2*A B := by
    change _ ≤ A (countEncoding task).length ∧ _ ≤ A (countEncoding task).length at prep
    omega
  have scale : 1 ≤ countVolume input right+1 := by omega
  nlinarith only [prepBound, counted, scale, Nat.zero_le (A B)]

/-- Both executed projected count allowances at one class. This includes real quarter
preparation/generation/sorting and binary counting, not just count-table entry storage. -/
noncomputable def countAllowance (input : ClassBalance.Input) (g : ℕ) : ℕ :=
  ClassBalance.countCertificate.time ((input, false), g)+
    ClassBalance.countCertificate.space ((input, false), g)+
    ClassBalance.countCertificate.time ((input, true), g)+
    ClassBalance.countCertificate.space ((input, true), g)

private theorem count_task_wire (input : ClassBalance.Input) {p : ℕ} (g : BitVec p)
    (right : Bool) : (countEncoding ((input, right), g.toNat)).length+1 ≤
      10*((ClassBalance.encoding input).length+p+1) := by
  have classWire : (encNat g.toNat).length ≤ p := by
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr g.isLt
  dsimp only [countEncoding]
  simp only [length_encPair, encBool_apply, List.length_singleton]
  omega

/-- Actual count-component global sum and each count's prefix workspace in original-input
physical width. This is a quarter-generation prepass for every class, not Lemma 8's faster
reachable-state-DP all-count algorithm, nor a bound on the whole scalar balance loop. -/
theorem original_count_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ} (as bs cs ds : List (BitVec m)) (s : BitVec m),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let B := (ClassBalance.encoding input).length+p+1
      (∑ g : BitVec p, countAllowance input g.toNat) ≤
        2^p*(JoinedDissection.quarterBudget input+2)*P B ∧
      ∀ (g : BitVec p) (right : Bool),
        ClassBalance.countCertificate.space ((input, right), g.toNat) ≤
          (countVolume input right+1)*P B := by
  obtain ⟨C, hC, mC, bound⟩ := projectedCount_bounds
  let P := fun B => C (10*B)
  refine ⟨P, by dsimp only [P]; fun_prop,
    fun _ _ h => mC (Nat.mul_le_mul_left 10 h), ?_⟩
  intro m p as bs cs ds s
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let B := (ClassBalance.encoding input).length+p+1
  have each (g : BitVec p) (right : Bool) :
      ClassBalance.countCertificate.time ((input, right), g.toNat)+
        ClassBalance.countCertificate.space ((input, right), g.toNat) ≤
          (countVolume input right+1)*P B := by
    have taskWire : (countEncoding ((input, right), g.toNat)).length+1 ≤ 10*B :=
      count_task_wire input g right
    exact (bound input right g.toNat).trans (Nat.mul_le_mul_left _ (mC taskWire))
  constructor
  · have classBound (g : BitVec p) : countAllowance input g.toNat ≤
        (JoinedDissection.quarterBudget input+2)*P B := by
      have hf := each g false
      have hb := each g true
      have volumes : countVolume input false+countVolume input true =
          JoinedDissection.quarterBudget input := by
        simp only [countVolume, ClassBalance.halfInput, Bool.false_eq_true, ↓reduceIte,
          JoinedDissection.quarterBudget, ProgramGeneration.originalSource, input,
          BitInput.words, List.length_map, List.length_reverse]
        ring
      dsimp only [countAllowance]
      nlinarith only [hf, hb, volumes]
    have total := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => classBound g)
    have constant : (∑ _g : BitVec p, (JoinedDissection.quarterBudget input+2)*P B) =
        2^p*((JoinedDissection.quarterBudget input+2)*P B) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_congr BitVec.equivFin.toEquiv, Fintype.card_fin, Nat.cast_id]
    exact total.trans_eq (constant.trans (by ring))
  · intro g right
    exact (Nat.le_add_left _ _).trans (each g right)

/-- Installed opposite-count allowances recomputed once at every generated restart label.
The control/division wrapper and batch/window producer clocks are not included. -/
noncomputable def restartCountAllowance (input : ClassBalance.Input) (g : ℕ) : ℕ :=
  let context := JoinedDissection.probeContext input g
  let right := !(ClassBalance.retainRight input g)
  (ClassBatches.labels context g).length *
    (ClassBalance.countCertificate.time ((input, right), g)+
      ClassBalance.countCertificate.space ((input, right), g))

/-- Recomputed projected counting, including its real generation/sort/binary-count clocks,
is amortized over the actual generated restart labels by capacity, in original widths.
This pays the count component rather than treating restart input volume as bit time;
count/division control, window/full-state emission and whole-run composition remain separate. -/
theorem original_restarted_count_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      (∑ g : BitVec p, restartCountAllowance input g.toNat) ≤
        (6*(2^(as.length+bs.length)+2^(cs.length+ds.length))+
          4*2^p*(JoinedDissection.quarterBudget input+1))*
            P ((ClassBalance.encoding input).length+p+1) := by
  obtain ⟨C, hC, mC, bound⟩ := projectedCount_bounds
  let P := fun B => C (10*B)
  refine ⟨P, by dsimp only [P]; fun_prop,
    fun _ _ h => mC (Nat.mul_le_mul_left 10 h), ?_⟩
  intro m p hp as bs cs ds s
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let B := (ClassBalance.encoding input).length+p+1
  have each (g : BitVec p) : restartCountAllowance input g.toNat ≤
      JoinedDissection.restartCopyWork input g.toNat*P B := by
    let right := !(ClassBalance.retainRight input g.toNat)
    let context := JoinedDissection.probeContext input g.toNat
    have actual := (bound input right g.toNat).trans
      (Nat.mul_le_mul_left _ (mC (count_task_wire input g right)))
    have quarter : countVolume input right+1 ≤ ClassBatches.capacity context := by
      rw [JoinedDissection.restart_capacity_eq]
      change countVolume input right+1 ≤ (ClassBalance.retain input g.toNat).length+1+
        countVolume input right
      omega
    have charged : ClassBalance.countCertificate.time ((input, right), g.toNat)+
        ClassBalance.countCertificate.space ((input, right), g.toNat) ≤
          ClassBatches.capacity context*P B :=
      actual.trans (Nat.mul_le_mul_right (P B) quarter)
    change (ClassBatches.labels context g.toNat).length *
      (ClassBalance.countCertificate.time ((input, right), g.toNat)+
        ClassBalance.countCertificate.space ((input, right), g.toNat)) ≤
          ((ClassBatches.labels context g.toNat).length*ClassBatches.capacity context)*P B
    exact (Nat.mul_le_mul_left _ charged).trans_eq (Nat.mul_assoc _ _ _).symm
  have total := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => each g)
  have copies := JoinedDissection.sum_restartCopyWork hp as bs cs ds s
  rw [← Finset.sum_mul] at total
  exact total.trans (Nat.mul_le_mul_right (P B) copies)

private theorem emission_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ (input : ClassBalance.Input) (right : Bool) (pairs : List (ℕ × ℕ)) (B : ℕ),
      (ClassBalance.sideEncoding (input, right)).length ≤ B →
      (∀ pair ∈ pairs, (er pair).length ≤ B) →
      ClassBalance.emitCertificate.time ((input, right), pairs)+
        ClassBalance.emitCertificate.space ((input, right), pairs) ≤
          (pairs.length+1)*P B := by
  let F := Classical.choose (ComputableInO.flatMap_stream ClassBalance.emit_polyTime)
  have hF := (Classical.choose_spec (ComputableInO.flatMap_stream ClassBalance.emit_polyTime)).1
  have mF : Monotone F :=
    (Classical.choose_spec (ComputableInO.flatMap_stream ClassBalance.emit_polyTime)).2.1
  let P := fun B => 20*(B+1)+2*F (2*B+1)
  refine ⟨P, by dsimp only [P]; fun_prop, ?_, ?_⟩
  · intro a b hab
    have h := mF (by omega : 2*a+1 ≤ 2*b+1)
    dsimp only [P]; omega
  · intro input right pairs B sideWire rows
    have recordWire : streamRecordLength er pairs ≤ B := listMax_le rows
    have inputWire := length_encList_le er pairs rows
    have arg : streamFilterWidth ClassBalance.sideEncoding er ((input, right), pairs) ≤
        2*B+1 := by dsimp only [streamFilterWidth]; omega
    have callback := Nat.mul_le_mul_left (pairs.length+1) (mF arg)
    change ((encPair ClassBalance.sideEncoding el ((input, right), pairs)).length+
      (pairs.length+1)*F (streamFilterWidth ClassBalance.sideEncoding er ((input, right), pairs)))+
      ((encPair ClassBalance.sideEncoding el ((input, right), pairs)).length+
        (pairs.length+1)*
          F (streamFilterWidth ClassBalance.sideEncoding er ((input, right), pairs))) ≤ _
    rw [length_encPair]
    change 2*(ClassBalance.sideEncoding (input, right)).length+1+(el pairs).length+
      (pairs.length+1)*F (streamFilterWidth ClassBalance.sideEncoding er ((input, right), pairs))+
      (2*(ClassBalance.sideEncoding (input, right)).length+1+(el pairs).length+
        (pairs.length+1)*
          F (streamFilterWidth ClassBalance.sideEncoding er ((input, right), pairs))) ≤ _
    dsimp only [P]
    nlinarith only [inputWire, sideWire, callback]

/-- Actual bounded quarter-pair window fed to full-state reconstruction at a restart label. -/
def restartPairs (input : ClassBalance.Input) (g i : ℕ) : List (ℕ × ℕ) :=
  let context := JoinedDissection.probeContext input g
  let capacity := ClassBatches.capacity context
  KeyJoinBatch.window (i*capacity, capacity) (JoinedProbe.groups context g)

/-- Actual full-state evaluation allowances, with the retained dictionary projected away. -/
noncomputable def reconstructionAllowance (input : ClassBalance.Input) (g i : ℕ) : ℕ :=
  let right := !(ClassBalance.retainRight input g)
  let pairs := restartPairs input g i
  ClassBalance.emitCertificate.time ((input, right), pairs)+
    ClassBalance.emitCertificate.space ((input, right), pairs)

/-- Full-state reconstruction of every actual restarted window has only a fixed polynomial
physical-input overhead per occurrence, including simultaneous pair/output/callback tapes.
Original quarter indices supply the width bound, rather than a semantic-record premise. -/
theorem original_reconstruction_bounds : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m)
      (g : BitVec p) (i : ℕ),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let q := as.length+bs.length+cs.length+ds.length
      reconstructionAllowance input g.toNat i ≤
        ((restartPairs input g.toNat i).length+1)*
          P ((ClassBalance.encoding input).length+q+p+1) := by
  obtain ⟨F, hF, mF, bound⟩ := emission_bounds
  let P := fun B => F (4*B+4)
  refine ⟨P, by dsimp only [P]; fun_prop,
    fun _ _ h => mF (by omega), ?_⟩
  intro m p hp as bs cs ds s g i
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let q := as.length+bs.length+cs.length+ds.length
  let B := (ClassBalance.encoding input).length+q+p+1
  let right := !(ClassBalance.retainRight input g.toNat)
  have side : (ClassBalance.sideEncoding (input, right)).length ≤ 4*B+4 := by
    dsimp only [B, ClassBalance.sideEncoding]
    rw [length_encPair]
    simp only [encBool_apply, List.length_singleton]
    omega
  have rows (pair : ℕ × ℕ) (hr : pair ∈ restartPairs input g.toNat i) :
      (er pair).length ≤ 4*B+4 := by
    have joined := KeyJoinBatch.window_mem_join _ _ pair hr
    change pair ∈ ClassJoin.witnesses (ClassBalance.queryInput input right g.toNat) at joined
    have limits : pair.1 < 2^q ∧ pair.2 < 2^q := by
      cases hright : right with
      | false =>
        have indices := (ClassBalance.original_witnesses hp as bs cs ds s 0 false g pair).mp
          (by simpa only [hright] using joined)
        have ha : pair.1 < 2^as.length := indices.1
        have hb : pair.2 < 2^bs.length := indices.2.1
        exact ⟨ha.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp only [q]; omega)),
          hb.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp only [q]; omega))⟩
      | true =>
        have indices := (ClassBalance.original_witnesses hp as bs cs ds s 0 true g pair).mp
          (by simpa only [hright] using joined)
        have ha : ds.reverse.length ≤ q := by rw [List.length_reverse]; dsimp only [q]; omega
        have hb : cs.reverse.length ≤ q := by rw [List.length_reverse]; dsimp only [q]; omega
        exact ⟨indices.1.trans_le (Nat.pow_le_pow_right (by decide) ha),
          indices.2.1.trans_le (Nat.pow_le_pow_right (by decide) hb)⟩
    have firstWire : (encNat pair.1).length ≤ q := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr limits.1
    have secondWire : (encNat pair.2).length ≤ q := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr limits.2
    simp only [er, RadixPartition.recordEncoding, length_encPair]
    dsimp only [B]
    omega
  exact bound input right (restartPairs input g.toNat i) (4*B+4) side rows

/-- Global sum of actual full-state reconstruction allowances over all generated labels and
simultaneous reconstruction workspace allowance at every batch, in original physical widths.
This includes reconstructed output and callback temporaries, but not the window-emission
machine or ambient solver frames. It is a phase sum, not a complete source time theorem. -/
theorem original_reconstruction_sum : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ Monotone P ∧
    ∀ {m p : ℕ}, p ≤ m → ∀ (as bs cs ds : List (BitVec m)) (s : BitVec m),
      let input := ProgramGeneration.originalSource p as bs cs ds s 0
      let q := as.length+bs.length+cs.length+ds.length
      let B := (ClassBalance.encoding input).length+q+p+1
      (∑ g : BitVec p,
        ((ClassBatches.labels (JoinedDissection.probeContext input g.toNat) g.toNat).map
          (reconstructionAllowance input g.toNat)).sum) ≤
        4*(6*(2^(as.length+bs.length)+2^(cs.length+ds.length))+
          4*2^p*(JoinedDissection.quarterBudget input+1))*P B ∧
      ∀ (g : BitVec p) (i : ℕ), reconstructionAllowance input g.toNat i ≤
        2*(ClassBalance.balance input+JoinedDissection.quarterBudget input+1)*P B := by
  obtain ⟨P, hP, mono, bound⟩ := original_reconstruction_bounds
  refine ⟨P, hP, mono, ?_⟩
  intro m p hp as bs cs ds s
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let q := as.length+bs.length+cs.length+ds.length
  let B := (ClassBalance.encoding input).length+q+p+1
  have lengthEq (g : BitVec p) (i : ℕ) : (restartPairs input g.toNat i).length =
      (ClassBatches.batch (JoinedDissection.probeContext input g.toNat) g.toNat i).length := by
    simp only [ClassBatches.batch, restartPairs, List.length_map]
  have installed (g : BitVec p) (i : ℕ) : reconstructionAllowance input g.toNat i ≤
      ((restartPairs input g.toNat i).length+1)*P B := bound hp as bs cs ds s g i
  have classBound (g : BitVec p) :
      ((ClassBatches.labels (JoinedDissection.probeContext input g.toNat) g.toNat).map
        (reconstructionAllowance input g.toNat)).sum ≤
          4*JoinedDissection.restartCopyWork input g.toNat*P B := by
    let context := JoinedDissection.probeContext input g.toNat
    let C := ClassBatches.capacity context
    have each (i : ℕ) : reconstructionAllowance input g.toNat i ≤ 4*C*P B := by
      have actual := installed g i
      rw [lengthEq] at actual
      have batch := ClassBatches.batch_length context g.toNat i
      have capacity : C = (ClassBalance.retain input g.toNat).length+1+
          ClassBatches.quarterVolume context := JoinedDissection.restart_capacity_eq input g.toNat
      have volume : (ClassBatches.batch context g.toNat i).length+1 ≤ 4*C := by
        change _ ≤ C+_ at batch
        omega
      exact actual.trans (Nat.mul_le_mul_right (P B) volume)
    have sumBound (labels : List ℕ) :
        (labels.map (reconstructionAllowance input g.toNat)).sum ≤ labels.length*(4*C*P B) := by
      induction labels with
      | nil => simp
      | cons i labels ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        exact (Nat.add_le_add (each i) ih).trans_eq (by ring)
    exact (sumBound (ClassBatches.labels context g.toNat)).trans_eq (by
      dsimp only [JoinedDissection.restartCopyWork, context, C]; ring)
  constructor
  · have total := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => classBound g)
    rw [← Finset.sum_mul, ← Finset.mul_sum] at total
    have copies := JoinedDissection.sum_restartCopyWork hp as bs cs ds s
    exact total.trans (Nat.mul_le_mul_right (P B) (Nat.mul_le_mul_left 4 copies))
  · intro g i
    have actual := installed g i
    rw [lengthEq] at actual
    have prefixBound := JoinedDissection.restart_prefix_records input g.toNat i
      (ClassBatches.batch (JoinedDissection.probeContext input g.toNat) g.toNat i).length g.isLt
    rw [List.take_length] at prefixBound
    have volume :
        (ClassBatches.batch (JoinedDissection.probeContext input g.toNat) g.toNat i).length+1 ≤
        2*(ClassBalance.balance input+JoinedDissection.quarterBudget input+1) := by omega
    exact actual.trans (Nat.mul_le_mul_right (P B) volume)

end Cslib.Cryptanalysis.AddXNOR.ProducerResources
