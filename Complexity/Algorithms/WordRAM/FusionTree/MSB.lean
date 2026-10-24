/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.Bitwise.PackedCount
public import Complexity.Algorithms.Lean.FusionTree.Multiplier
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Most-significant-bit arithmetic for fusion trees

The arithmetic expressions use multiplication, subtraction, Boolean operations and shifts.
Their correctness is distinct from execution on a bounded-word RAM: the intermediate
products need multiple physical words. The construction follows pages 7–8 of the
MIT 6.851 Spring 2021 lecture 12 notes,
<https://courses.csail.mit.edu/6.851/spring21/lectures/L12.pdf>.

## Main definitions

* `ones`, `powers`, `guards`, `powerCount`: packed all-ones multiplier, packed power ladder,
  guard bits and comparison count for parallel power-of-two comparisons.
* `powerFlags`: parallel comparisons against consecutive powers of two.
* `smallMSB`: count the successful comparisons and subtract one.
* `clusterMask`, `clusterMarkers`, `compressionShift`, `compressionMultiplier`: cluster mask,
  nonzero-cluster markers, shift and multiplier for compressing cluster markers.
* `clusterSummary`: compress the nonzero-cluster markers by multiplication.
* `msb`, `clusterSize`, `widthMSB`: two-stage MSB expression, cluster width `⌈√w⌉` and
  width-`w` MSB.
* `powerStageValues`, `clusterStageValues`: virtual-register intermediate values for the
  power-of-two and cluster stages.

## Main results

* `smallMSB_eq_log2`: correctness without a most-significant-bit primitive.
* `clusterMarkers_guard`: exact nonzero detection, without intercluster borrowing.
* `widthMSB_eq_log2`: full arithmetic correctness, including zero and nonsquare widths.
* `widthMSB_virtual_bounds`: all recorded arithmetic intermediates fit in `6w` bits.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.MSB

open scoped BigOperators
open Cslib.BitString
open Cslib.Algorithms.Lean.FusionTree (positionMask positionMask_testBit)

/-- One at the low bit of each of `s` fields of width `s + 1`. -/
def ones (s : ℕ) : ℕ := packRadix (2 ^ (s + 1)) s (fun _ => 1)

/-- Field `i` contains the comparison threshold `2 ^ i`. -/
def powers (s : ℕ) : ℕ := packRadix (2 ^ (s + 1)) s (fun i => 2 ^ i)

/-- A guard bit at the top of every field. -/
def guards (s : ℕ) : ℕ := 2 ^ s * ones s

/-- Simultaneously compare `z` with every `2 ^ i`, for `i < s`.
The output has a zero-or-one digit in every radix-`2^(s+1)` field. -/
def powerFlags (s z : ℕ) : ℕ :=
  ((((2 ^ s + z) * ones s - powers s) &&& guards s) >>> s)

/-- Multiplication counts the successful power-of-two comparisons. -/
def powerCount (s z : ℕ) : ℕ :=
  ((powerFlags s z * ones s) >>> ((s - 1) * (s + 1))) &&& (2 ^ (s + 1) - 1)

/-- Most-significant set bit for a positive input of at most `s` bits.
The expression contains no logarithm or bit-search operation; constants depend only on `s`. -/
def smallMSB (s z : ℕ) : ℕ := powerCount s z - 1

private theorem guardedDifference_eq (s z : ℕ) :
    (2 ^ s + z) * ones s - powers s =
      packRadix (2 ^ (s + 1)) s (fun i => 2 ^ s + z - 2 ^ i) := by
  have h (i : ℕ) (hi : i < s) : 2 ^ i ≤ 2 ^ s + z :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show i ≤ s by omega)).trans
      (by omega)
  have he : packRadix (2 ^ (s + 1)) s (fun i => 2 ^ s + z - 2 ^ i) + powers s =
      (2 ^ s + z) * ones s := by
    simp only [packRadix, powers, ones, Finset.mul_sum, one_mul,
      ← Finset.sum_add_distrib, ← add_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.sub_add_cancel (h i (Finset.mem_range.mp hi))]
  omega

private theorem guardedDifference_guard {s z : ℕ} (hz : z < 2 ^ s) (i : Fin s) :
    ((2 ^ s + z) * ones s - powers s).testBit (s + (s + 1) * i.val) =
      decide (2 ^ i.val ≤ z) := by
  have hp : 2 ^ i.val ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) (by omega)
  have hbound (j : ℕ) : 2 ^ s + z - 2 ^ j < 2 ^ (s + 1) := by
    calc
      _ ≤ 2 ^ s + z := Nat.sub_le _ _
      _ < 2 ^ (s + 1) := by rw [pow_succ]; omega
  have hf := packRadix_field (Nat.two_pow_pos (s + 1))
    (fun i => 2 ^ s + z - 2 ^ i) (fun j _ => hbound j) i.isLt
  rw [guardedDifference_eq]
  have he := congrArg (fun x : ℕ => x.testBit s) hf
  simp only [← pow_mul, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    decide_eq_true (show s < s + 1 by omega), Bool.true_and] at he
  rw [he, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : 2 ^ i.val ≤ z
  · have hd : (2 ^ s + z - 2 ^ i.val) / 2 ^ s = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hd, h]
  · have hd : 2 ^ s + z - 2 ^ i.val < 2 ^ s := by omega
    simp [Nat.div_eq_of_lt hd, h]

private theorem guards_eq (s : ℕ) :
    guards s = positionMask (fun i : Fin s => s + (s + 1) * i.val) := by
  simp only [guards, ones, packRadix, positionMask, Finset.mul_sum, one_mul, pow_add,
    pow_mul]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- The comparison expression has exactly the promised Boolean digits; subtraction
does not borrow between fields and no correctness oracle is a hypothesis. -/
private theorem powerFlags_eq {s z : ℕ} (hz : z < 2 ^ s) :
    powerFlags s z =
      packRadix (2 ^ (s + 1)) s (fun i => (decide (2 ^ i ≤ z)).toNat) := by
  have hinj : Function.Injective (fun i : Fin s => s + (s + 1) * i.val) := by
    intro i j h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel h)
  rw [powerFlags, guards_eq, positionMask, Nat.and_sum_two_pow _ hinj]
  simp only [guardedDifference_guard hz, Nat.shiftRight_eq_div_pow]
  have he : (∑ i : Fin s,
      (decide (2 ^ i.val ≤ z)).toNat * 2 ^ (s + (s + 1) * i.val)) =
      2 ^ s * packRadix (2 ^ (s + 1)) s (fun i => (decide (2 ^ i ≤ z)).toNat) := by
    rw [packRadix, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add, pow_mul]
    ring
  rw [he, Nat.mul_div_right _ (Nat.two_pow_pos _)]

/-- Counting the packed flags gives the number of powers of two at most the input. -/
private theorem powerCount_eq {s z : ℕ} (hs : 0 < s) (hz : z < 2 ^ s) :
    powerCount s z = ∑ i ∈ Finset.range s, (decide (2 ^ i ≤ z)).toNat := by
  rw [powerCount, powerFlags_eq hz, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  have hb : s < 2 ^ (s + 1) := by
    have := Nat.lt_two_pow_self (n := s)
    rw [pow_succ]
    omega
  simpa only [ones, pow_mul, Nat.mul_comm (s - 1)] using
    countPackedFlags (fun i => decide (2 ^ i ≤ z)) hs hb

/-- For nonzero inputs, the comparison/count arithmetic returns the highest set-bit index.
`Nat.log2` occurs only in the specification and proof. -/
theorem smallMSB_eq_log2 {s z : ℕ} (hz0 : 0 < z) (hz : z < 2 ^ s) :
    smallMSB s z = z.log2 := by
  have hl : z.log2 < s := (Nat.log2_lt (by omega)).mpr hz
  have hsum : (∑ i ∈ Finset.range s, (decide (2 ^ i ≤ z)).toNat) = z.log2 + 1 := by
    calc
      _ = ∑ i ∈ Finset.range s, if i < z.log2 + 1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [← Nat.le_log2 (n := z) (by omega)]
        by_cases hi : i ≤ z.log2 <;>
          simp [hi, show (i < z.log2 + 1) ↔ i ≤ z.log2 by omega]
      _ = z.log2 + 1 := by
        rw [← Finset.sum_filter]
        have he : (Finset.range s).filter (fun i => i < z.log2 + 1) =
            Finset.range (z.log2 + 1) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
        simp [he]
  rw [smallMSB, powerCount_eq (by omega) hz, hsum, Nat.add_sub_cancel]

/-- The most significant bit of each of `s` clusters, each `s` bits wide. -/
def clusterMask (s : ℕ) : ℕ :=
  positionMask (fun i : Fin s => s - 1 + i.val * s)

/-- Set a cluster's marker exactly when the cluster is nonempty. The original high
bits are separated before subtraction, preventing borrows between clusters. -/
def clusterMarkers (s x : ℕ) : ℕ :=
  let h := x &&& clusterMask s
  let r := x ^^^ h
  h ||| (clusterMask s ^^^ ((clusterMask s - r) &&& clusterMask s))

/-- Shifts moving diagonal marker products to positions `s² + i`. -/
def compressionShift (s j : ℕ) : ℕ := s * s - (s - 1) - j * s + j

/-- Precomputed multiplier for the cluster markers. -/
def compressionMultiplier (s : ℕ) : ℕ :=
  positionMask (fun i : Fin s => compressionShift s i.val)

/-- One bit per nonempty cluster, computed by multiply, shift, and mask.
The final mask removes the off-diagonal multiplication terms. -/
def clusterSummary (s x : ℕ) : ℕ :=
  ((clusterMarkers s x * compressionMultiplier s) >>> (s * s)) &&& (2 ^ s - 1)

private theorem lowMask_eq (s : ℕ) :
    positionMask (fun i : Fin s => i.val) = 2 ^ s - 1 := by
  apply Nat.eq_of_testBit_eq
  intro k
  apply Bool.eq_iff_iff.mpr
  rw [positionMask_testBit _ (fun _ _ h => Fin.ext h), Nat.testBit_two_pow_sub_one]
  simp only [decide_eq_true_eq]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ i.isLt, fun hk => ⟨⟨k, hk⟩, rfl⟩⟩

private theorem compressionShift_add {s : ℕ} (_hs : 0 < s) (i j : Fin s) :
    (s - 1 + i.val * s) + compressionShift s j.val + j.val * s =
      s * s + i.val * s + j.val := by
  have hj : j.val * s + (s - 1) ≤ s * s := by
    have := Nat.mul_le_mul_right s (show j.val + 1 ≤ s from j.isLt)
    have : s - 1 ≤ s := Nat.sub_le _ _
    nlinarith
  unfold compressionShift
  omega

private theorem compression_diagonal {s : ℕ} (hs : 0 < s) (i : Fin s) :
    (s - 1 + i.val * s) + compressionShift s i.val = s * s + i.val := by
  have := compressionShift_add hs i i
  omega

private theorem markerPosition_injective {s : ℕ} (hs : 0 < s) :
    Function.Injective (fun i : Fin s => s - 1 + i.val * s) := by
  intro i j h
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_right hs (Nat.add_left_cancel h)

private theorem compression_injective {s : ℕ} (hs : 0 < s) :
    Function.Injective (fun p : Fin s × Fin s =>
      (s - 1 + p.1.val * s) + compressionShift s p.2.val) := by
  intro p q h
  dsimp only at h
  have hj : p.2 = q.2 := by
    have hp := congrArg (fun a : ℕ => a % s) (compressionShift_add hs p.1 p.2)
    have hq := congrArg (fun a : ℕ => a % s) (compressionShift_add hs q.1 q.2)
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod,
      Nat.add_zero, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt p.2.isLt,
      Nat.mod_eq_of_lt q.2.isLt] at hp hq
    have hm := congrArg (fun a : ℕ => a % s) h
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero,
      Nat.zero_mod, Nat.add_zero, Nat.mod_mod] at hm
    exact Fin.ext (hp.symm.trans (hm.trans hq))
  have hi : p.1 = q.1 := by
    rw [hj] at h
    exact markerPosition_injective hs (Nat.add_right_cancel h)
  exact Prod.ext hi hj

private theorem clusterMarkers_mask (s x : ℕ) :
    clusterMarkers s x &&& clusterMask s = clusterMarkers s x := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [clusterMarkers, Nat.testBit_land, Nat.testBit_lor, Nat.testBit_xor]
  cases x.testBit k <;> cases (clusterMask s).testBit k <;>
    cases (clusterMask s - (x ^^^ (x &&& clusterMask s))).testBit k <;> rfl

private theorem packed_testBit {e n i j : ℕ} (a : ℕ → ℕ)
    (ha : ∀ k < n, a k < 2 ^ e) (hi : i < n) (hj : j < e) :
    (packRadix (2 ^ e) n a).testBit (j + e * i) = (a i).testBit j := by
  have he := congrArg (fun x : ℕ => x.testBit j)
    (packRadix_field (Nat.two_pow_pos e) a ha hi)
  simpa only [← pow_mul, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    decide_eq_true hj, Bool.true_and] using he

private theorem packed_ext {e n a b : ℕ} (he : 0 < e)
    (ha : a < 2 ^ (e * n)) (hb : b < 2 ^ (e * n))
    (h : ∀ i < n, ∀ j < e, a.testBit (j + e * i) = b.testBit (j + e * i)) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < e * n
  · have hi : k / e < n := (Nat.div_lt_iff_lt_mul he).mpr (by nlinarith)
    have heq : k % e + e * (k / e) = k := Nat.mod_add_div _ _
    simpa only [heq] using h (k / e) hi (k % e) (Nat.mod_lt _ he)
  · have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : e * n ≤ k)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hp), Nat.testBit_lt_two_pow (hb.trans_le hp)]

private theorem clusterMask_eq (s : ℕ) :
    clusterMask s = packRadix (2 ^ s) s (fun _ => 2 ^ (s - 1)) := by
  simp only [clusterMask, positionMask, packRadix, pow_add, pow_mul, Nat.mul_comm _ s]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => 2 ^ (s - 1) * (2 ^ s) ^ i) s

private theorem clusterMask_lt {s : ℕ} (hs : 0 < s) : clusterMask s < 2 ^ (s * s) := by
  rw [clusterMask_eq, pow_mul]
  apply packRadix_lt
  intro _ _
  exact Nat.pow_lt_pow_right (by decide) (by omega)

private theorem clusterMask_bit {s i j : ℕ} (hs : 0 < s) (hi : i < s) (hj : j < s) :
    (clusterMask s).testBit (j + s * i) = decide (s - 1 = j) := by
  rw [clusterMask_eq, packed_testBit _ (fun _ _ =>
    Nat.pow_lt_pow_right (by decide) (by omega)) hi hj, Nat.testBit_two_pow]

private theorem clusterRest_eq {s x : ℕ} (hs : 0 < s) (hx : x < 2 ^ (s * s)) :
    x ^^^ (x &&& clusterMask s) =
      packRadix (2 ^ s) s (fun i => x / 2 ^ (s * i) % 2 ^ (s - 1)) := by
  have hr (i : ℕ) : x / 2 ^ (s * i) % 2 ^ (s - 1) < 2 ^ s :=
    (Nat.mod_lt _ (Nat.two_pow_pos _)).trans
      (Nat.pow_lt_pow_right (by decide) (by omega))
  apply packed_ext hs (Nat.xor_lt_two_pow hx (Nat.and_le_left.trans_lt hx))
    (by rw [pow_mul]; exact packRadix_lt _ (fun i _ => hr i))
  intro i hi j hj
  rw [Nat.testBit_xor, Nat.testBit_land, clusterMask_bit hs hi hj,
    packed_testBit _ (fun i _ => hr i) hi hj, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  by_cases he : s - 1 = j
  · simp [he]
  · simp [he, show j < s - 1 by omega]

private theorem clusterDifference_eq {s x : ℕ} (hs : 0 < s)
    (hx : x < 2 ^ (s * s)) :
    clusterMask s - (x ^^^ (x &&& clusterMask s)) =
      packRadix (2 ^ s) s (fun i => 2 ^ (s - 1) - x / 2 ^ (s * i) % 2 ^ (s - 1)) := by
  rw [clusterRest_eq hs hx, clusterMask_eq]
  have he :
      packRadix (2 ^ s) s (fun i => 2 ^ (s - 1) - x / 2 ^ (s * i) % 2 ^ (s - 1)) +
        packRadix (2 ^ s) s (fun i => x / 2 ^ (s * i) % 2 ^ (s - 1)) =
        packRadix (2 ^ s) s (fun _ => 2 ^ (s - 1)) := by
    simp only [packRadix, ← Finset.sum_add_distrib, ← add_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.sub_add_cancel (Nat.mod_lt _ (Nat.two_pow_pos _)).le]
  omega

private theorem clusterDifference_guard {s x i : ℕ} (hs : 0 < s)
    (hx : x < 2 ^ (s * s)) (hi : i < s) :
    (clusterMask s - (x ^^^ (x &&& clusterMask s))).testBit (s - 1 + s * i) =
      decide (x / 2 ^ (s * i) % 2 ^ (s - 1) = 0) := by
  rw [clusterDifference_eq hs hx]
  have hsmall : 2 ^ (s - 1) < 2 ^ s := Nat.pow_lt_pow_right (by decide) (by omega)
  rw [packed_testBit _ (fun j _ => (Nat.sub_le _ _).trans_lt hsmall) hi (by omega)]
  by_cases hz : x / 2 ^ (s * i) % 2 ^ (s - 1) = 0
  · simp [hz]
  · have hd : 2 ^ (s - 1) - x / 2 ^ (s * i) % 2 ^ (s - 1) < 2 ^ (s - 1) := by
      have := Nat.two_pow_pos (s - 1)
      omega
    simp [Nat.testBit_lt_two_pow hd, hz]

/-- Every marker is set precisely when its original cluster is nonzero. This includes
clusters whose only set bit was already at the marker position. -/
theorem clusterMarkers_guard {s x i : ℕ} (hs : 0 < s) (hx : x < 2 ^ (s * s))
    (hi : i < s) :
    (clusterMarkers s x).testBit (s - 1 + s * i) =
      decide (x / 2 ^ (s * i) % 2 ^ s ≠ 0) := by
  rw [clusterMarkers, Nat.testBit_lor, Nat.testBit_land, Nat.testBit_xor,
    Nat.testBit_land, clusterMask_bit hs hi (by omega),
    clusterDifference_guard hs hx hi]
  simp only [decide_true, Bool.and_true, Bool.true_bne]
  have hbit : x.testBit (s - 1 + s * i) =
      (x / 2 ^ (s * i) % 2 ^ s).testBit (s - 1) := by
    simp only [Nat.testBit_mod_two_pow, decide_eq_true (by omega : s - 1 < s),
      Bool.true_and, Nat.testBit_div_two_pow]
  rw [hbit]
  have hl : (x / 2 ^ (s * i) % 2 ^ s) % 2 ^ (s - 1) =
      x / 2 ^ (s * i) % 2 ^ (s - 1) := by
    apply Nat.mod_mod_of_dvd
    exact Nat.pow_dvd_pow 2 (by omega)
  let v := x / 2 ^ (s * i) % 2 ^ s
  have hv : v < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos _)
  have he : v.testBit (s - 1) = false ∧ v % 2 ^ (s - 1) = 0 ↔ v = 0 := by
    constructor
    · rintro ⟨hb, hm⟩
      rw [Nat.testBit_eq_decide_div_mod_eq] at hb
      have hh : s - 1 + 1 = s := by omega
      have hd : v / 2 ^ (s - 1) < 2 := by
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
        simpa only [Nat.mul_comm 2, ← pow_succ, hh] using hv
      simp only [decide_eq_false_iff_not, Nat.mod_eq_of_lt hd] at hb
      have hq : v / 2 ^ (s - 1) = 0 :=
        Nat.lt_one_iff.mp (lt_of_le_of_ne (Nat.le_of_lt_succ hd) hb)
      have hm' := Nat.mod_add_div v (2 ^ (s - 1))
      simpa only [hm, hq, Nat.mul_zero, Nat.add_zero] using hm'.symm
    · intro hv0
      simp [hv0]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq]
  rw [← hl]
  change v.testBit (s - 1) = true ∨ ¬v % 2 ^ (s - 1) = 0 ↔ v ≠ 0
  cases hb : v.testBit (s - 1) <;> simp_all

/-- The masked product compresses exactly the original cluster-marker bits. Cross terms
are collision-free everywhere, including outside the final retained interval. -/
private theorem clusterSummary_eq {s : ℕ} (hs : 0 < s) (x : ℕ) :
    clusterSummary s x =
      ∑ i : Fin s, ((clusterMarkers s x).testBit (s - 1 + i.val * s)).toNat * 2 ^ i.val := by
  have hd (i : Fin s) :
      (s - 1 + i.val * s) + compressionShift s i.val - s * s = i.val := by
    rw [compression_diagonal hs]
    omega
  have he := Cslib.Algorithms.Lean.FusionTree.approximateSketch_eq
    (w := s * s)
    (fun i : Fin s => s - 1 + i.val * s) (fun i => compressionShift s i.val)
    (compression_injective hs) (markerPosition_injective hs)
    (fun i => by rw [compression_diagonal hs]; omega) (clusterMarkers s x)
  simp only [Cslib.Algorithms.Lean.FusionTree.approximateSketch, hd] at he
  change (((clusterMarkers s x &&& clusterMask s) * compressionMultiplier s) >>> (s * s))
      &&& positionMask (fun i : Fin s => i.val) = _ at he
  rw [clusterMarkers_mask, lowMask_eq] at he
  exact he

/-- The compressed summary fits in `s` bits, including for an empty input. -/
theorem clusterSummary_lt (s x : ℕ) : clusterSummary s x < 2 ^ s := by
  rw [clusterSummary, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- A summary bit is set exactly when the corresponding original cluster is nonzero. -/
private theorem clusterSummary_testBit {s x i : ℕ} (hs : 0 < s) (hx : x < 2 ^ (s * s))
    (hi : i < s) :
    (clusterSummary s x).testBit i = decide (x / 2 ^ (s * i) % 2 ^ s ≠ 0) := by
  rw [clusterSummary_eq hs]
  apply Bool.eq_iff_iff.mpr
  rw [Nat.testBit_sum_injective _ _ (fun _ _ _ _ h => Fin.ext h)]
  simp only [Finset.mem_univ, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, he⟩
    have hj' := clusterMarkers_guard hs hx j.isLt
    have hmark : (clusterMarkers s x).testBit (s - 1 + s * j.val) = true := by
      simpa only [Nat.mul_comm] using hj
    rw [hmark] at hj'
    simpa only [he] using of_decide_eq_true hj'.symm
  · intro hx'
    refine ⟨⟨i, hi⟩, ?_, rfl⟩
    simpa only [Nat.mul_comm i s, clusterMarkers_guard hs hx hi,
      decide_eq_true_eq] using hx'

private theorem highestCluster {s x : ℕ} (hs : 0 < s) (hx0 : 0 < x)
    (hx : x < 2 ^ (s * s)) :
    let c := x.log2 / s
    let d := x.log2 % s
    let v := x / 2 ^ (s * c) % 2 ^ s
    c < s ∧ 0 < v ∧ v.log2 = d ∧
      (∀ i, c < i → x / 2 ^ (s * i) % 2 ^ s = 0) := by
  dsimp only
  have hxne : x ≠ 0 := by omega
  have hl : x.log2 < s * s := (Nat.log2_lt hxne).mpr hx
  have hc : x.log2 / s < s := (Nat.div_lt_iff_lt_mul hs).mpr hl
  have hd : x.log2 % s < s := Nat.mod_lt _ hs
  have he : x.log2 % s + s * (x.log2 / s) = x.log2 := Nat.mod_add_div _ _
  have hb : (x / 2 ^ (s * (x.log2 / s)) % 2 ^ s).testBit (x.log2 % s) = true := by
    simpa only [Nat.testBit_mod_two_pow, decide_eq_true hd, Bool.true_and,
      Nat.testBit_div_two_pow, he] using Nat.testBit_log2 hxne
  have hv0 : 0 < x / 2 ^ (s * (x.log2 / s)) % 2 ^ s := by
    have := Nat.ge_two_pow_of_testBit hb
    have := Nat.two_pow_pos (x.log2 % s)
    omega
  refine ⟨hc, hv0, ?_, ?_⟩
  · apply (Nat.log2_eq_iff (by omega)).mpr
    refine ⟨Nat.ge_two_pow_of_testBit hb, ?_⟩
    apply (Nat.mod_le _ _).trans_lt
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    have hp : (x.log2 % s + 1) + s * (x.log2 / s) = x.log2 + 1 := by omega
    rw [← pow_add, hp]
    exact Nat.lt_log2_self
  · intro i hi
    have hli : x.log2 + 1 ≤ s * i := by
      have hh := Nat.mul_le_mul_left s (show x.log2 / s + 1 ≤ i by omega)
      nlinarith
    have hxi : x < 2 ^ (s * i) := Nat.lt_log2_self.trans_le
      (Nat.pow_le_pow_right (by decide) hli)
    simp [Nat.div_eq_of_lt hxi]

/-- The first comparison/count stage identifies the highest nonempty cluster. -/
private theorem clusterSummary_log2 {s x : ℕ} (hs : 0 < s) (hx0 : 0 < x)
    (hx : x < 2 ^ (s * s)) :
    0 < clusterSummary s x ∧ (clusterSummary s x).log2 = x.log2 / s := by
  obtain ⟨hc, hv, _, habove⟩ := highestCluster hs hx0 hx
  have hset : (clusterSummary s x).testBit (x.log2 / s) = true := by
    rw [clusterSummary_testBit hs hx hc]
    exact decide_eq_true (by omega)
  have hz : 0 < clusterSummary s x := by
    have := Nat.ge_two_pow_of_testBit hset
    have := Nat.two_pow_pos (x.log2 / s)
    omega
  refine ⟨hz, le_antisymm ?_ ?_⟩
  · by_contra hn
    have hi : (clusterSummary s x).log2 < s :=
      (Nat.log2_lt (by omega)).mpr (clusterSummary_lt s x)
    have hb := Nat.testBit_log2 (show clusterSummary s x ≠ 0 by omega)
    rw [clusterSummary_testBit hs hx hi, habove _ (by omega)] at hb
    simp at hb
  · exact (Nat.le_log2 (by omega)).mpr (Nat.ge_two_pow_of_testBit hset)

/-- Two parallel power-comparison/count stages, with extraction of the selected cluster.
The value for zero is explicitly zero. All constants depend only on `s`. -/
def msb (s x : ℕ) : ℕ :=
  if x = 0 then 0 else
    let c := smallMSB s (clusterSummary s x)
    let v := (x >>> (c * s)) &&& (2 ^ s - 1)
    c * s + smallMSB s v

/-- Full arithmetic correctness for `s` clusters of `s` bits. This theorem assumes only
the input bound and positive cluster width, not correctness of any algorithmic stage. -/
theorem msb_eq_log2 {s x : ℕ} (hs : 0 < s) (hx : x < 2 ^ (s * s)) :
    msb s x = x.log2 := by
  by_cases hx0 : x = 0
  · simp [msb, hx0]
  · have hxpos : 0 < x := by omega
    obtain ⟨hz, hlog⟩ := clusterSummary_log2 hs hxpos hx
    have hc : smallMSB s (clusterSummary s x) = x.log2 / s := by
      rw [smallMSB_eq_log2 hz (clusterSummary_lt s x), hlog]
    obtain ⟨_, hv, hvlog, _⟩ := highestCluster hs hxpos hx
    rw [msb, ite_eq_right hx0, hc]
    dsimp only
    rw [Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow, Nat.mul_comm (x.log2 / s) s,
      smallMSB_eq_log2 hv (Nat.mod_lt _ (Nat.two_pow_pos _)), hvlog]
    exact Nat.div_add_mod _ _

/-- Ceiling of the square root, with zero width assigned zero clusters. This is a
width-dependent preprocessing constant, not a run-time square-root instruction. -/
def clusterSize (w : ℕ) : ℕ := if w = 0 then 0 else (w - 1).sqrt + 1

/-- The cluster capacity covers nonsquare widths and uses at most twice the input width. -/
theorem clusterSize_bounds {w : ℕ} (hw : 0 < w) :
    0 < clusterSize w ∧ w ≤ clusterSize w * clusterSize w ∧
      clusterSize w * clusterSize w ≤ 2 * w ∧ clusterSize w ≤ w := by
  rw [clusterSize, ite_eq_right (by omega)]
  have hl := Nat.sqrt_le (w - 1)
  have hu := Nat.lt_succ_sqrt (w - 1)
  have hs := Nat.sqrt_le_self (w - 1)
  have hpred : w - 1 + 1 = w := by omega
  simp only [Nat.succ_eq_add_one] at hu
  have hsq : 2 * (w - 1).sqrt ≤ (w - 1).sqrt * (w - 1).sqrt + 1 := by
    by_cases hh : (w - 1).sqrt < 2
    · have hh' : (w - 1).sqrt = 0 ∨ (w - 1).sqrt = 1 := by omega
      rcases hh' with hh' | hh' <;> simp [hh']
    · have := Nat.mul_le_mul_right (w - 1).sqrt (show 2 ≤ (w - 1).sqrt by omega)
      nlinarith
  refine ⟨by omega, by nlinarith, by nlinarith, by omega⟩

/-- Width-specific MSB arithmetic, including zero and nonsquare widths. -/
def widthMSB (w x : ℕ) : ℕ := msb (clusterSize w) x

/-- For every fitting input, the expression computes the most-significant-set-bit index;
zero returns zero. No wider physical word or RAM execution is asserted here. -/
theorem widthMSB_eq_log2 {w x : ℕ} (hx : x < 2 ^ w) : widthMSB w x = x.log2 := by
  by_cases hw : w = 0
  · have hx0 : x = 0 := by simpa only [hw, pow_zero, Nat.lt_one_iff] using hx
    simp [widthMSB, msb, hx0]
  · have hb := clusterSize_bounds (show 0 < w by omega)
    exact msb_eq_log2 hb.1 (hx.trans_le (Nat.pow_le_pow_right (by decide) hb.2.1))

private theorem ones_lt (s : ℕ) : ones s < 2 ^ ((s + 1) * s) := by
  rw [ones, pow_mul]
  exact packRadix_lt _ (fun _ _ => Nat.one_lt_two_pow (by omega))

private theorem powers_lt (s : ℕ) : powers s < 2 ^ ((s + 1) * s) := by
  rw [powers, pow_mul]
  apply packRadix_lt
  intro i hi
  exact Nat.pow_lt_pow_right (by decide) (by omega)

private theorem guards_lt (s : ℕ) : guards s < 2 ^ ((s + 1) * s) := by
  have he : guards s = packRadix (2 ^ (s + 1)) s (fun _ => 2 ^ s) := by
    simp only [guards, ones, packRadix, Finset.mul_sum, one_mul]
  rw [he, pow_mul]
  exact packRadix_lt _ (fun _ _ => Nat.pow_lt_pow_right (by decide) (by omega))

private theorem powerReplicate_lt {s z : ℕ} (hz : z < 2 ^ s) :
    (2 ^ s + z) * ones s < 2 ^ ((s + 1) * s) := by
  have he : (2 ^ s + z) * ones s =
      packRadix (2 ^ (s + 1)) s (fun _ => 2 ^ s + z) := by
    simp only [ones, packRadix, Finset.mul_sum, one_mul]
  rw [he, pow_mul]
  apply packRadix_lt
  intro _ _
  rw [pow_succ]
  omega

private theorem powerFlags_lt {s z : ℕ} (hz : z < 2 ^ s) :
    powerFlags s z < 2 ^ ((s + 1) * s) := by
  rw [powerFlags_eq hz, pow_mul]
  apply packRadix_lt
  intro i _
  have hb : 1 < 2 ^ (s + 1) := Nat.one_lt_two_pow (by omega)
  cases decide (2 ^ i ≤ z) <;> simp_all

/-- Every arithmetic value in one powers-of-two comparison/count stage. This records
intermediates before masking or shifting, so oversized products cannot be hidden. -/
def powerStageValues (s z : ℕ) : List ℕ :=
  let a := (2 ^ s + z) * ones s
  let b := a - powers s
  let c := b &&& guards s
  let d := powerFlags s z * ones s
  [z, 2 ^ s, ones s, powers s, guards s, 2 ^ s + z, a, b, c, powerFlags s z,
    d, d >>> ((s - 1) * (s + 1)), 2 ^ (s + 1) - 1, powerCount s z, smallMSB s z,
    s, s + 1, (s - 1) * (s + 1), 2 ^ (s + 1)]

/-- The largest power-stage intermediate needs at most twice the packed field width.
This is a bound in bits, not permission to use a larger physical RAM word. -/
theorem powerStageValues_lt {s z : ℕ} (hs : 0 < s) (hz : z < 2 ^ s) :
    ∀ a ∈ powerStageValues s z, a < 2 ^ (2 * (s + 1) * s) := by
  have hwidth : (s + 1) * s < 2 * (s + 1) * s := by nlinarith
  have hlift : 2 ^ ((s + 1) * s) < 2 ^ (2 * (s + 1) * s) :=
    Nat.pow_lt_pow_right (by decide) hwidth
  have hsmall : s + 1 ≤ (s + 1) * s := by nlinarith
  have hadd : 2 ^ s + z < 2 ^ (s + 1) := by rw [pow_succ]; omega
  have hpow : 2 ^ (s + 1) ≤ 2 ^ ((s + 1) * s) :=
    Nat.pow_le_pow_right (by decide) hsmall
  have ha := powerReplicate_lt hz
  have hb : (2 ^ s + z) * ones s - powers s < 2 ^ ((s + 1) * s) :=
    (Nat.sub_le _ _).trans_lt ha
  have hc : ((2 ^ s + z) * ones s - powers s) &&& guards s <
      2 ^ ((s + 1) * s) := Nat.and_le_left.trans_lt hb
  have hd : powerFlags s z * ones s < 2 ^ (2 * (s + 1) * s) := by
    have hp := Nat.mul_lt_mul_of_lt_of_lt (powerFlags_lt hz) (ones_lt s)
    rw [← pow_add] at hp
    convert hp using 1; congr 1; ring
  have hcount : powerCount s z ≤ powerFlags s z * ones s := by
    unfold powerCount
    exact Nat.and_le_left.trans (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _)
  intro a ha'
  simp only [powerStageValues, List.mem_cons, List.not_mem_nil, or_false] at ha'
  rcases ha' with ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha' |
    ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha' <;> subst a
  · exact (hz.trans_le
      ((Nat.pow_le_pow_right (by decide) (by omega : s ≤ s + 1)).trans hpow)).trans hlift
  · exact ((Nat.pow_le_pow_right (by decide) (by omega : s ≤ s + 1)).trans hpow).trans_lt hlift
  · exact (ones_lt s).trans hlift
  · exact (powers_lt s).trans hlift
  · exact (guards_lt s).trans hlift
  · exact (hadd.trans_le hpow).trans hlift
  · exact ha.trans hlift
  · exact hb.trans hlift
  · exact hc.trans hlift
  · exact (powerFlags_lt hz).trans hlift
  · exact hd
  · rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_le_self _ _).trans_lt hd
  · exact (Nat.sub_le _ _).trans_lt (hpow.trans_lt hlift)
  · exact hcount.trans_lt hd
  · exact (Nat.sub_le _ _).trans_lt (hcount.trans_lt hd)
  · exact (show s ≤ 2 * (s + 1) * s by nlinarith).trans_lt Nat.lt_two_pow_self
  · exact (show s + 1 ≤ 2 * (s + 1) * s by nlinarith).trans_lt Nat.lt_two_pow_self
  · exact (show (s - 1) * (s + 1) ≤ 2 * (s + 1) * s by
      have := Nat.sub_le s 1
      nlinarith).trans_lt Nat.lt_two_pow_self
  · exact hpow.trans_lt hlift

private theorem compressionShift_injective {s : ℕ} (hs : 0 < s) :
    Function.Injective (fun j : Fin s => compressionShift s j.val) := by
  intro i j h
  let k : Fin s := ⟨0, hs⟩
  have he : (k, i) = (k, j) := compression_injective hs
    (congrArg (fun n => (s - 1 + k.val * s) + n) h)
  exact congrArg Prod.snd he

private theorem compressionMultiplier_lt {s : ℕ} (hs : 0 < s) :
    compressionMultiplier s < 2 ^ (s * s + s) := by
  apply Cslib.Algorithms.Lean.FusionTree.positionMask_lt _ (compressionShift_injective hs)
  intro i
  unfold compressionShift
  have hh : s * s - (s - 1) - i.val * s ≤ s * s :=
    (Nat.sub_le _ _).trans (Nat.sub_le _ _)
  omega

private theorem clusterMarkers_lt {s : ℕ} (hs : 0 < s) (x : ℕ) :
    clusterMarkers s x < 2 ^ (s * s) := by
  rw [← clusterMarkers_mask s x]
  exact Nat.and_le_right.trans_lt (clusterMask_lt hs)

/-- Every arithmetic value in marking and compressing the clusters, including the
full product before shifting and masking. -/
def clusterStageValues (s x : ℕ) : List ℕ :=
  let f := clusterMask s
  let h := x &&& f
  let r := x ^^^ h
  let d := f - r
  let e := d &&& f
  let y := clusterMarkers s x
  let a := compressionMultiplier s
  [x, f, h, r, d, e, f ^^^ e, y, a, y * a, (y * a) >>> (s * s),
    2 ^ s - 1, clusterSummary s x, s * s]

/-- The marking/compression stage needs at most `2s² + s` bits for every value,
including its full multiplication intermediate. -/
theorem clusterStageValues_lt {s x : ℕ} (hs : 0 < s) (hx : x < 2 ^ (s * s)) :
    ∀ a ∈ clusterStageValues s x, a < 2 ^ (2 * (s * s) + s) := by
  have hmono : 2 ^ (s * s) ≤ 2 ^ (2 * (s * s) + s) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hf := clusterMask_lt hs
  have hh : x &&& clusterMask s < 2 ^ (s * s) := Nat.and_le_right.trans_lt hf
  have hr := Nat.xor_lt_two_pow hx hh
  have hd : clusterMask s - (x ^^^ (x &&& clusterMask s)) < 2 ^ (s * s) :=
    (Nat.sub_le _ _).trans_lt hf
  have he : (clusterMask s - (x ^^^ (x &&& clusterMask s))) &&& clusterMask s <
      2 ^ (s * s) := Nat.and_le_right.trans_lt hf
  have hy := clusterMarkers_lt hs x
  have ha := compressionMultiplier_lt hs
  have hp : clusterMarkers s x * compressionMultiplier s < 2 ^ (2 * (s * s) + s) := by
    have hprod := Nat.mul_lt_mul_of_lt_of_lt hy ha
    rw [← pow_add] at hprod
    convert hprod using 1; congr 1; ring
  have hsmono : 2 ^ s ≤ 2 ^ (s * s) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  intro a ha'
  simp only [clusterStageValues, List.mem_cons, List.not_mem_nil, or_false] at ha'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact hx.trans_le hmono
  · exact hf.trans_le hmono
  · exact hh.trans_le hmono
  · exact hr.trans_le hmono
  · exact hd.trans_le hmono
  · exact he.trans_le hmono
  · exact (Nat.xor_lt_two_pow hf he).trans_le hmono
  · exact hy.trans_le hmono
  · exact ha.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · exact hp
  · rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_le_self _ _).trans_lt hp
  · have hmask : 2 ^ s - 1 < 2 ^ s := by have := Nat.two_pow_pos s; omega
    exact hmask.trans_le (hsmono.trans hmono)
  · exact (clusterSummary_lt s x).trans_le (hsmono.trans hmono)
  · exact (show s * s ≤ 2 * (s * s) + s by omega).trans_lt Nat.lt_two_pow_self

/-- The small-input arithmetic returns an index below the supplied bit width, even
for zero (where its saturating subtraction returns zero). -/
theorem smallMSB_lt {s z : ℕ} (hs : 0 < s) (hz : z < 2 ^ s) : smallMSB s z < s := by
  by_cases hz0 : z = 0
  · have hcount : powerCount s 0 = 0 := by
      rw [powerCount_eq hs (Nat.two_pow_pos _)]
      apply Finset.sum_eq_zero
      intro i _
      have hp := Nat.two_pow_pos i
      simp [show ¬2 ^ i ≤ 0 by omega]
    simpa only [hz0, smallMSB, hcount, Nat.zero_sub] using hs
  · rw [smallMSB_eq_log2 (by omega) hz]
    exact (Nat.log2_lt hz0).mpr hz

/-- Every value in both comparison/count stages and the marking/compression stage fits
in `6w` virtual bits. These bounds support a future multiword implementation; they do not
claim execution with a `6w`-bit physical word. -/
theorem widthMSB_virtual_bounds {w x : ℕ} (hw : 0 < w) (hx : x < 2 ^ w) :
    let s := clusterSize w
    let z := clusterSummary s x
    let c := smallMSB s z
    let v := (x >>> (c * s)) &&& (2 ^ s - 1)
    (∀ a ∈ clusterStageValues s x, a < 2 ^ (6 * w)) ∧
    (∀ a ∈ powerStageValues s z, a < 2 ^ (6 * w)) ∧
    (∀ a ∈ powerStageValues s v, a < 2 ^ (6 * w)) ∧
      c * s < 2 ^ (6 * w) ∧ widthMSB w x < 2 ^ (6 * w) := by
  dsimp only
  obtain ⟨hs, hcap, hsq, hsw⟩ := clusterSize_bounds hw
  have hx' := hx.trans_le (Nat.pow_le_pow_right (by decide) hcap)
  have hp : 2 * (clusterSize w + 1) * clusterSize w ≤ 6 * w := by nlinarith
  have hc : 2 * (clusterSize w * clusterSize w) + clusterSize w ≤ 6 * w := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact (clusterStageValues_lt hs hx' a ha).trans_le (Nat.pow_le_pow_right (by decide) hc)
  · intro a ha
    exact (powerStageValues_lt hs (clusterSummary_lt _ _) a ha).trans_le
      (Nat.pow_le_pow_right (by decide) hp)
  · intro a ha
    have hv : (x >>> (smallMSB (clusterSize w) (clusterSummary (clusterSize w) x) *
        clusterSize w)) &&& (2 ^ clusterSize w - 1) < 2 ^ clusterSize w := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    exact (powerStageValues_lt hs hv a ha).trans_le (Nat.pow_le_pow_right (by decide) hp)
  · have hi := smallMSB_lt hs (clusterSummary_lt (clusterSize w) x)
    have hh : smallMSB (clusterSize w) (clusterSummary (clusterSize w) x) *
        clusterSize w ≤ 6 * w := by nlinarith
    exact hh.trans_lt Nat.lt_two_pow_self
  · rw [widthMSB_eq_log2 hx]
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hi : x.log2 < w := (Nat.log2_lt hx0).mpr hx
      exact (hi.trans_le (show w ≤ 6 * w by omega)).trans Nat.lt_two_pow_self

end Cslib.Algorithms.WordRAM.FusionTree.MSB
