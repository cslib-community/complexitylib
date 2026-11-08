/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORSourceQuarter
public import Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import all Complexity.Cryptanalysis.AddXNORSourceQuarter
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORSortedRecords
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping

/-!
# Original-input projected-quarter equal-key groups

The actual quarter generator and radix sorter feed a one-pass nested-frame writer.
The writer remembers only the previous key; a large colliding bucket is written
to the output without a growing bucket in the control state. Counts, original
packed witnesses and all quarter occurrences are preserved. Generation, sorting,
framing and callback temporaries are charged in one uniform bit computation.

This is a grouped first-quarter producer for [WangLvShenZhang2027], Lemma 8,
PDF pp. 21–22. Joining inverse-quarter groups, DP class counts, fused bounded
batch writing/persistent retained tapes and the global sharp bit bounds remain open.


## Main definitions

* `run`: generate, sort and write first-quarter equal-key groups from original input.

## Main results

* `flatten_run`, `original_correct`: exact quarter order and original packed witnesses.
* `groups_correct`: nonempty groups with one projected key, preserving collisions.
* `run_computable`: uniform quarter-scale time and charged peak bit space.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.GroupedQuarter
open Turing.MultiTapeTM

/-- Compute and group the actual original-input first projected quarter. -/
def run (input : Source.Input) : List (List (ℕ × ℕ)) := KeyGrouping.run (SourceQuarter.run input)

/-- Grouping preserves the exact original sorted quarter sequence, including all occurrences. -/
theorem flatten_run (input : Source.Input) : (run input).flatten = SourceQuarter.run input :=
  KeyGrouping.flatten_run _

/-- Each group is nonempty and contains one projected key, without a bucket-validity premise. -/
theorem groups_correct (input : Source.Input) (group : List (ℕ × ℕ)) (hg : group ∈ run input) :
    group ≠ [] ∧ group.Pairwise (fun a b => a.1 = b.1) :=
  ⟨KeyGrouping.group_nonempty _ group hg, KeyGrouping.group_keys _ group hg⟩

/-- Every grouped payload is an actual original packed quarter witness; the flattened sequence
retains permutation multiplicity, not only set membership. -/
theorem original_correct {m p : ℕ} (hm : p ≤ m) (a : BitVec m) (tail : List (BitVec m))
    (hk : p ≤ tail.length / 4) :
    let ((as, _), _) := Source.quarters tail
    let groups := run (Source.ofWords p a tail)
    groups.flatten.Perm (SortedRecords.projectedQuarter p as a) ∧
      ∀ r, r ∈ groups.flatten ↔ r.2 < 2 ^ as.length ∧
        r.1 = (eval ((Native.Quarter.decode as.length r.2).zip as) a).toNat % 2 ^ p := by
  dsimp only
  rw [flatten_run]
  exact ⟨(SourceQuarter.original_correct hm a tail hk).1,
    (SourceQuarter.original_correct hm a tail hk).2.2⟩

private theorem source_wires (input : Source.Input) :
    (SourceQuarter.run input).length = 2 ^ (input.2.tail.length / 4) ∧
      streamRecordLength RadixPartition.recordEncoding (SourceQuarter.run input) + 1 ≤
        3 * ((Source.encoding input).length + 1) ∧
      (encList RadixPartition.recordEncoding (SourceQuarter.run input)).length ≤
        2 ^ (input.2.tail.length / 4) * (6 * ((Source.encoding input).length + 1)) := by
  let source := Source.prepare input
  let p := source.1.1.2
  let as := source.2.1.1.map (BitVec.ofNat p)
  let seed := BitVec.ofNat p source.1.2.1
  let k := input.2.tail.length / 4
  let I := (Source.encoding input).length
  have hi : I = 2 * (2 * input.1.1 + 1 + input.1.2) + 1 +
      (encList encNat input.2).length := by
    simp only [I, Source.encoding, length_encPair, encUnary_apply, List.length_replicate]
  have hwords := length_le_length_encList encNat input.2
  have hm : input.1.1 ≤ I := by omega
  have hk : k ≤ I := by
    have ht := List.length_tail (l := input.2)
    dsimp only [k]
    omega
  have hp : p ≤ input.1.1 := by
    dsimp only [p, source, Source.prepare]
    omega
  have hl : as.length = k := by
    have h := SourceQuarter.prepare_length input
    rw [SourceQuarter.prepare_words] at h
    simpa only [as, source, List.length_map] using h
  have hc := SourceQuarter.correct input
  change (SourceQuarter.run input).Perm (SortedRecords.projectedQuarter p as seed) ∧ _ at hc
  have hn : (SourceQuarter.run input).length = 2 ^ k := by
    simpa only [SortedRecords.projectedQuarter, List.length_map, List.length_range, hl] using
      hc.1.length_eq
  have record (r : ℕ × ℕ) (hr : r ∈ SourceQuarter.run input) :
      (RadixPartition.recordEncoding r).length ≤ 2 * p + 1 + k := by
    have hf := (hc.2.2 r).mp hr
    have hkey : r.1 < 2 ^ p := by rw [hf.2]; exact (eval _ seed).isLt
    have hval : r.2 < 2 ^ as.length := hf.1
    rw [hl] at hval
    have hkl : (encNat r.1).length ≤ p := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr hkey
    have hvl : (encNat r.2).length ≤ k := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr hval
    simp only [RadixPartition.recordEncoding, length_encPair]
    omega
  have hmax : streamRecordLength RadixPartition.recordEncoding (SourceQuarter.run input) ≤
      2 * p + 1 + k := listMax_le record
  have hwire : (encList RadixPartition.recordEncoding (SourceQuarter.run input)).length ≤
      (SourceQuarter.run input).length * (4 * p + 2 * k + 3) :=
    by
      have h := length_encList_le _ _ record
      have he : 2 * (2 * p + 1 + k) + 1 = 4 * p + 2 * k + 3 := by omega
      simpa only [he] using h
  refine ⟨hn, by omega, ?_⟩
  rw [hn] at hwire
  exact hwire.trans (Nat.mul_le_mul_left _ (by omega))

/-- One uniform original-input bit machine computes grouped projected-quarter records in
quarter enumeration time and charged peak space, with fixed polynomial physical-bit overhead.
This is a producer stage, not the global dissection resource theorem. -/
theorem run_computable : ∃ Q : ℕ → ℕ, Cslib.PolynomiallyBounded Q ∧ Monotone Q ∧
    ComputableInO run Source.encoding KeyGrouping.outputEncoding
      (fun input => (2 ^ (input.2.tail.length / 4) + 1) * Q ((Source.encoding input).length + 1))
      (fun input => (2 ^ (input.2.tail.length / 4) + 1) *
        Q ((Source.encoding input).length + 1)) := by
  obtain ⟨P, hP, hmP, group⟩ := KeyGrouping.run_computable
  obtain ⟨Q, hQ, hmQ, quarter⟩ := SourceQuarter.run_computable
  let R : ℕ → ℕ := fun x => Q x + 6 * x + P (3 * x)
  have hR : Cslib.PolynomiallyBounded R := by dsimp only [R]; fun_prop
  have hmR : Monotone R := by
    intro a b hab
    have hq := hmQ hab
    have hp := hmP (show 3*a ≤ 3*b by omega)
    dsimp only [R]
    omega
  refine ⟨R, hR, hmR, (group.comp quarter).mono_le ?_ ?_⟩
  all_goals intro input
  all_goals
    obtain ⟨hn, hmax, hwire⟩ := source_wires input
    have hp := hmP hmax
    have hE : 1 ≤ 2 ^ (input.2.tail.length / 4) + 1 := by omega
    dsimp only [R, Function.comp_def]
  · rw [hn]
    have hmul := Nat.mul_le_mul_left (2 ^ (input.2.tail.length / 4) + 1) hp
    nlinarith only [hwire, hmul]
  · have hscale : P (streamRecordLength RadixPartition.recordEncoding
        (SourceQuarter.run input) + 1) ≤
          (2 ^ (input.2.tail.length / 4) + 1) * P (3 * ((Source.encoding input).length + 1)) := by
      exact hp.trans (Nat.le_mul_of_pos_left _ hE)
    nlinarith only [hwire, hscale]

end Cslib.Cryptanalysis.AddXNOR.GroupedQuarter
