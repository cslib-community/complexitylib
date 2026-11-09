/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
public import CslibFrontier.Cryptanalysis.AddXNORNativeClassSemantics
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import all CslibFrontier.Cryptanalysis.AddXNORNativeEnumeration
import all CslibFrontier.Cryptanalysis.AddXNORNativeBuckets

/-!
# Actual bit sorting of projected quarters and retained full-state records

[WangLvShenZhang2027], Lemma 8 and Theorem 7, PDF pp. 21–22, use
sorted quarter lists and a sorted smaller retained class. The uniform radix
machine sorts exactly the binary key/packed-witness records specified here,
preserving collisions and every admissible packed index. No sortedness or
witness-correctness conclusion is an endpoint premise.

The sorter charges its materialized input, control, output and all prefix
workspace. These observers do not implement or charge quarter/class generation,
counting, class access or reuse. Nor do they replace the existing uniform
interpreter's scans/ALU overhead. Thus this is a concrete sorting component, not
the sharp end-to-end source bit-model bound. The first-operand seed, zero target
and source quarter cut remain those of `AddXNOR.Source`.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.SortedRecords
open Turing.MultiTapeTM Native.Quarter

/-- All packed indices, with their actual low-bit state, including zero and collisions. -/
def projectedQuarter {m : ℕ} (p : ℕ) (as : List (BitVec m)) (s : BitVec m) :
    List (ℕ × ℕ) :=
  (List.range (2 ^ as.length)).map fun u => ((indexedState as s u).toNat % 2 ^ p, u)

/-- Full-state key and a lossless concatenation of the two packed quarter witnesses. -/
def packedEntry (firstLength : ℕ) (e : Native.Dictionary.Entry) : ℕ × ℕ :=
  (e.state, e.first + 2 ^ firstLength * e.second)

/-- The actual forward insertion stream; it retains every hit before dictionary replacement. -/
def retainedClass {m p : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (g : BitVec p) :
    List (ℕ × ℕ) :=
  (classEntries bs g (fun k => Forward.records as s p k.toNat) 0 (2 ^ bs.length)).map
    (packedEntry as.length)

/-- Quarter sorting charges all `2^k` records and the physical `p`-bit key / `k`-bit index.
The list is already materialized at this calling boundary; generation is not free. -/
theorem projectedQuarter_wires {m : ℕ} (p : ℕ) (as : List (BitVec m)) (s : BitVec m) :
    (projectedQuarter p as s).length = 2 ^ as.length ∧
      streamFilterWidth encUnary RadixPartition.recordEncoding
        (p, projectedQuarter p as s) ≤ 3 * p + as.length + 2 ∧
      (RadixPartition.inputEncoding (p, projectedQuarter p as s)).length ≤
        2 * p + 1 + 2 ^ as.length * (4 * p + 2 * as.length + 3) := by
  have fits : ∀ row ∈ projectedQuarter p as s,
      row.1 < 2 ^ p ∧ row.2 < 2 ^ as.length := by
    intro row hr
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
    exact ⟨Nat.mod_lt _ (Nat.two_pow_pos p), List.mem_range.mp hu⟩
  have hlen : (projectedQuarter p as s).length = 2 ^ as.length := by
    simp only [projectedQuarter, List.length_map, List.length_range]
  have h := RadixSort.wire_bounds (p, projectedQuarter p as s) as.length fits
  exact ⟨hlen, h.1, by simpa only [hlen] using h.2⟩

/-- Projection sorting is complete for all admissible original-quarter indices. -/
theorem projectedQuarter_correct {m : ℕ} (p : ℕ) (as : List (BitVec m)) (s : BitVec m) :
    let sorted := RadixSort.sort (p, projectedQuarter p as s)
    sorted.Perm (projectedQuarter p as s) ∧
      sorted.Pairwise (fun a b => a.1 ≤ b.1) ∧
      ∀ r, r ∈ sorted ↔ r.2 < 2 ^ as.length ∧
        r.1 = (eval ((decode as.length r.2).zip as) s).toNat % 2 ^ p := by
  have hfit : ∀ r ∈ projectedQuarter p as s, r.1 < 2 ^ p := by
    intro r hr
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hr
    exact Nat.mod_lt _ (Nat.two_pow_pos p)
  obtain ⟨hp, hs⟩ := RadixSort.correct (p, projectedQuarter p as s) hfit
  refine ⟨hp, hs, ?_⟩
  intro r
  rw [hp.mem_iff]
  rcases r with ⟨key, index⟩
  simp only [projectedQuarter, List.mem_map, List.mem_range, Prod.mk.injEq, indexedState]
  constructor
  · rintro ⟨u, hu, hk, rfl⟩
    exact ⟨hu, hk.symm⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨index, hi, rfl, rfl⟩

/-- Sorting the full-state retained stream preserves precisely original two-quarter witnesses. -/
theorem retainedClass_correct {m p : ℕ} (hp : p ≤ m) (as bs : List (BitVec m))
    (s : BitVec m) (g : BitVec p) :
    let sorted := RadixSort.sort (m, retainedClass as bs s g)
    sorted.Perm (retainedClass as bs s g) ∧
      sorted.Pairwise (fun a b => a.1 ≤ b.1) ∧
      ∀ r, r ∈ sorted ↔ ∃ u v, u < 2 ^ as.length ∧ v < 2 ^ bs.length ∧
        r = ((eval (((decode as.length u).zip as) ++
          ((decode bs.length v).zip bs)) s).toNat, u + 2 ^ as.length * v) ∧
        (eval (((decode as.length u).zip as) ++
          ((decode bs.length v).zip bs)) s).setWidth p = g := by
  have hfit : ∀ r ∈ retainedClass as bs s g, r.1 < 2 ^ m := by
    intro r hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have hs := (mem_forwardClass hp as bs s g e).mp he
    change e.state < 2 ^ m
    rw [hs.2.2.1]
    exact (eval (((decode as.length e.first).zip as) ++
      ((decode bs.length e.second).zip bs)) s).isLt
  obtain ⟨hperm, hsorted⟩ := RadixSort.correct (m, retainedClass as bs s g) hfit
  refine ⟨hperm, hsorted, ?_⟩
  intro r
  rw [hperm.mem_iff]
  constructor
  · intro hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hu, hv, hs, hg⟩ := (mem_forwardClass hp as bs s g e).mp he
    exact ⟨e.first, e.second, hu, hv, by simp only [packedEntry, hs], hg⟩
  · rintro ⟨u, v, hu, hv, rfl, hg⟩
    let e : Native.Dictionary.Entry :=
      ⟨(eval (((decode as.length u).zip as) ++ ((decode bs.length v).zip bs)) s).toNat, u, v⟩
    exact List.mem_map.mpr ⟨e, (mem_forwardClass hp as bs s g e).mpr
      ⟨hu, hv, rfl, hg⟩, rfl⟩

/-- Retained-list sorting depends on its actual hit count, not the full `2^m` address span.
Both packed witnesses are included in the physical payload width. -/
theorem retainedClass_wires {m p : ℕ} (hp : p ≤ m) (as bs : List (BitVec m))
    (s : BitVec m) (g : BitVec p) :
    streamFilterWidth encUnary RadixPartition.recordEncoding
        (m, retainedClass as bs s g) ≤ 3 * m + (as.length + bs.length) + 2 ∧
      (RadixPartition.inputEncoding (m, retainedClass as bs s g)).length ≤
        2 * m + 1 + (retainedClass as bs s g).length *
          (4 * m + 2 * (as.length + bs.length) + 3) := by
  apply RadixSort.wire_bounds
  intro row hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
  obtain ⟨hu, hv, hs, _⟩ := (mem_forwardClass hp as bs s g e).mp he
  constructor
  · change e.state < 2 ^ m
    rw [hs]
    exact (eval (((decode as.length e.first).zip as) ++
      ((decode bs.length e.second).zip bs)) s).isLt
  · change e.first + 2 ^ as.length * e.second < 2 ^ (as.length + bs.length)
    rw [Nat.pow_add]
    have hmul := Nat.mul_le_mul_left (2 ^ as.length) (Nat.succ_le_of_lt hv)
    nlinarith

/-- Packed payload decoding loses no leading zero operator and distinguishes colliding states. -/
theorem unpack_payload {a u v : ℕ} (hu : u < 2 ^ a) :
    (u + 2 ^ a * v) % 2 ^ a = u ∧ (u + 2 ^ a * v) / 2 ^ a = v := by
  constructor
  · simp [Nat.add_mod, Nat.mod_eq_of_lt hu]
  · rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos a), Nat.div_eq_of_lt hu]
    omega

end Cslib.Cryptanalysis.AddXNOR.SortedRecords
