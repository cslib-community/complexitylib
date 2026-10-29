/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.BucketCounts
public import Complexity.Computability.WordRAM.Signed.Arithmetic
import Mathlib.Tactic.FinCases

/-!
# Native heavy extraction and light placement

The input, unsigned residue array and histogram are supplied by the actual `Count.program`.
One scan copies heavy integers, in input order, to a compact output. Each light integer is
tagged and placed directly in the packed node array. The third pass negates its integer and
its residue, and writes both copies required by `arrZ`.

The mathematical comparator is Anthropic's [Buckets.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Buckets.lean)
and `NodeArray.lean` at `formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
The native code, encoding arithmetic and execution proofs here are original. No `Light`
execution theorem or source-machine simulation is assumed.

## Main definitions

* `Place.program`: a fixed scan with runtime bases, length, modulus, tag and column.
* `Place.heavyList`: compact heavy elements in input order.
* `Place.memory`: exact writes of a prefix of the scan, including both third-column copies.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Place

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Input array base. -/
abbrev src : Fin 32 := 9
/-- Unsigned residue array base. -/
abbrev keys : Fin 32 := 10
/-- Input length. -/
abbrev len : Fin 32 := 11
/-- Histogram base. -/
abbrev hist : Fin 32 := 12
/-- Compact heavy output base. -/
abbrev heavy : Fin 32 := 13
/-- Packed node output base. -/
abbrev packed : Fin 32 := 14
/-- Positive modulus, decoded unsigned. -/
abbrev modulus : Fin 32 := 15
/-- Twice the positive tag added to a light integer. -/
abbrev tag : Fin 32 := 16
/-- Column in a four-cell group. -/
abbrev column : Fin 32 := 17
/-- Distance to the second write: zero for X/Y, `4M` for Z. -/
abbrev distance : Fin 32 := 18
/-- Zero for X/Y, one for Z. -/
abbrev negative : Fin 32 := 19
/-- Input cursor. -/
abbrev idx : Fin 32 := 20
/-- Number of heavy integers already written. -/
abbrev count : Fin 32 := 21
/-- Temporary address. -/
abbrev addr : Fin 32 := 22
/-- Current remainder. -/
abbrev key : Fin 32 := 23
/-- Current value and its tagged encoding. -/
abbrev value : Fin 32 := 24
/-- Twice the current magnitude. -/
abbrev magnitude : Fin 32 := 25
/-- Current input sign. -/
abbrev sign : Fin 32 := 26
/-- Constant one. -/
abbrev one : Fin 32 := 27
/-- Constant two. -/
abbrev two : Fin 32 := 28
/-- Constant four. -/
abbrev four : Fin 32 := 29
/-- Constant zero. -/
abbrev zero : Fin 32 := 30
/-- Current histogram count. -/
abbrev bucketSize : Fin 32 := 31

/-- Negating a Euclidean residue needs only a subtraction and a remainder. -/
def targetKey (M : ℕ) (neg : Bool) (z : ℤ) : ℕ :=
  if neg then (M - residueKey M z) % M else residueKey M z

/-- Integer contribution before the positive tag. -/
def signedValue (neg : Bool) (z : ℤ) : ℤ := if neg then -z else z

/-- The target index is exactly the residue of the signed contribution. -/
theorem targetKey_eq {M : ℕ} (hM : 0 < M) (neg : Bool) (z : ℤ) :
    targetKey M neg z = residueKey M (signedValue neg z) := by
  cases neg
  · rfl
  · have hr := residueKey_lt hM z
    apply Int.ofNat_inj.mp
    change (((M - residueKey M z) % M : ℕ) : ℤ) = (residueKey M (-z) : ℤ)
    rw [Int.natCast_emod, Nat.cast_sub (Nat.le_of_lt hr), residueKey_cast hM,
      residueKey_cast hM]
    rw [Int.sub_emod_emod, Int.sub_emod_left]

/-- A prefix of the compact output; membership is tested against the full histogram. -/
def heavyList (values : ℕ → ℤ) (n M : ℕ) : ℕ → List ℤ
  | 0 => []
  | k + 1 => heavyList values n M k ++
      if 1 < Histogram.count (fun i => residueKey M (values i)) n (residueKey M (values k))
      then [values k] else []

/-- A compact prefix has at most as many cells as the corresponding input prefix. -/
theorem length_heavyList_le (values : ℕ → ℤ) (n M k : ℕ) :
    (heavyList values n M k).length ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [heavyList, List.length_append]
    split_ifs <;> simp only [List.length_singleton, List.length_nil] <;> omega

/-- The compact array is the input subsequence selected by the histogram test. -/
theorem heavyList_eq_filter (values : ℕ → ℤ) (n M k : ℕ) :
    heavyList values n M k = ((List.range k).filter fun i =>
      decide (1 < Histogram.count (fun j => residueKey M (values j)) n
        (residueKey M (values i)))).map values := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [heavyList, List.range_succ, List.filter_append, List.map_append, ih]
    split_ifs <;> simp_all

/-- The native compact output has exactly the existing heavy subset as its underlying set. -/
theorem heavyList_toFinset (values : ℕ → ℤ) (n : ℕ) {M : ℕ} (hM : 0 < M)
    (hinj : Set.InjOn values (↑(Finset.range n) : Set ℕ)) :
    (heavyList values n M n).toFinset =
      Cslib.Algorithms.ThreeSum.ChanHe.heavy ((Finset.range n).image values) M := by
  ext z
  rw [heavyList_eq_filter]
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨hi, hc⟩, rfl⟩
    exact (mem_heavy_iff_count values n hM hinj hi).mpr hc
  · intro hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp
      ((Finset.mem_filter.mp hz).1)
    exact ⟨i, ⟨Finset.mem_range.mp hi,
      (mem_heavy_iff_count values n hM hinj (Finset.mem_range.mp hi)).mp hz⟩, rfl⟩

/-- The exact per-input write, either to the next compact heavy cell or to packed light cells. -/
def write (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col dist t : ℕ)
    (neg : Bool) (k : ℕ) : ℕ → ℕ :=
  if 1 < Histogram.count (fun i => residueKey M (values i)) n (residueKey M (values k)) then
    Function.update mem (out + (heavyList values n M k).length) (encode (values k))
  else
    let a := dst + 4 * targetKey M neg (values k) + col
    let v := encode (signedValue neg (values k) + (t : ℤ))
    Function.update (Function.update mem a v) (a + dist) v

/-- All writes of the first `k` iterations, framed by arbitrary initial memory. -/
def memory (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col dist t : ℕ)
    (neg : Bool) : ℕ → ℕ → ℕ
  | 0 => mem
  | k + 1 => write (memory mem values n M out dst col dist t neg k)
      values n M out dst col dist t neg k

/-- Copy a heavy integer without changing its signed encoding. -/
def heavyCode : Code .standard 32 := ram[
  addr ← heavy + count; *addr ← value; count ← count + one ]

/-- Tag a light integer using its magnitude and sign, then write its required cells. -/
def lightCode : Code .standard 32 := ram[
  if negative = zero then [ key ← key ]
  else [ key ← modulus - key; key ← key % modulus ];
  magnitude ← value / two; magnitude ← magnitude + magnitude; sign ← value % two;
  if sign = negative then [ value ← tag + magnitude ] else [ value ← tag - magnitude ];
  addr ← four * key; addr ← packed + addr; addr ← addr + column; *addr ← value;
  addr ← addr + distance; *addr ← value ]

/-- Every iteration reads the original integer, its unsigned key and its exact bucket size. -/
def body : Code .standard 32 := ram[
  addr ← keys + idx; key ← *addr; addr ← hist + key; bucketSize ← *addr;
  addr ← src + idx; value ← *addr;
  if one < bucketSize then [ ⟪heavyCode⟫ ] else [ ⟪lightCode⟫ ];
  idx ← idx + one ]

/-- The same finite code handles every input length, width, modulus and output length. -/
def program : Code .standard 32 :=
  .seq (ram[ idx ← #0; count ← #0; one ← #1; two ← #2; four ← #4; zero ← #0 ])
    (.loop (.lt idx len) body)

/-- All runtime parameters survive the scan. -/
theorem preserves_parameters (i : Fin 32) (hi : 9 ≤ i.val ∧ i.val ≤ 19) :
    program.Preserves i := by
  fin_cases i <;> norm_num at hi <;> decide

/-- A scan can only change its heavy capacity block and its packed output block. -/
theorem memory_outside (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col dist t N : ℕ)
    (neg : Bool) (hM : 0 < M) (hN : 2 * M ≤ N) (hc : col < 4) (hd : dist ≤ 4 * M)
    {k : ℕ} (hk : k ≤ n) {a : ℕ}
    (ha : ¬(out ≤ a ∧ a < out + n)) (hb : ¬(dst ≤ a ∧ a < dst + 4 * N)) :
    memory mem values n M out dst col dist t neg k a = mem a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hh := length_heavyList_le values n M k
    have hr : targetKey M neg (values k) < M := by
      rw [targetKey_eq hM]
      exact residueKey_lt hM _
    have hn₁ : a ≠ out + (heavyList values n M k).length := by omega
    have hn₂ : a ≠ dst + 4 * targetKey M neg (values k) + col := by omega
    have hn₃ : a ≠ dst + 4 * targetKey M neg (values k) + col + dist := by omega
    simp only [memory, write]
    split_ifs <;> simp only [Function.update_of_ne hn₁, Function.update_of_ne hn₂,
      Function.update_of_ne hn₃] <;> exact ih (by omega)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Place
