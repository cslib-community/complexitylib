/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Copy
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Charged word-RAM histograms

A fixed program clears a histogram and inserts the keys of a disjoint input array.
An insertion into a bucket of size `c` creates `2c` ordered collisions. Every address
calculation, load, increment, store and loop test is charged.

## Main definitions

* `Histogram.count`: bucket sizes in an input prefix.
* `Histogram.pairs`: ordered collisions accumulated by prefix insertion.
* `Histogram.program`: clear the buckets, then insert the input keys.

## Main results

* `Histogram.exec`: histogram construction and collision counting with a linear instruction bound.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Histogram

open Cslib.WordRAM
open Finset

/-- Number of occurrences of a key among the first `k` input positions. -/
def count (keys : ℕ → ℕ) (k b : ℕ) : ℕ := #{i ∈ range k | keys i = b}

@[simp] theorem count_zero (keys : ℕ → ℕ) (b : ℕ) : count keys 0 b = 0 := by
  simp [count]

/-- Inserting one key changes just its bucket. -/
theorem count_succ (keys : ℕ → ℕ) (k b : ℕ) :
    count keys (k + 1) b = count keys k b + if keys k = b then 1 else 0 := by
  by_cases h : keys k = b <;> simp [count, range_add_one, filter_insert, h]

/-- A bucket cannot contain more positions than the prefix. -/
theorem count_le (keys : ℕ → ℕ) (k b : ℕ) : count keys k b ≤ k :=
  (card_filter_le _ _).trans_eq (card_range k)

/-- Ordered collisions accumulated while inserting successive keys. -/
def pairs (keys : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => pairs keys k + 2 * count keys k (keys k)

/-- The prefix collision counter is at most the square of the prefix length. -/
theorem pairs_le_sq (keys : ℕ → ℕ) (k : ℕ) : pairs keys k ≤ k * k := by
  induction k with
  | zero => simp [pairs]
  | succ k ih =>
    have := count_le keys k (keys k)
    dsimp only [pairs]
    nlinarith

/-- The insertion counter counts exactly the ordered pairs of different positions
with the same key, including when equal keys occur at different input positions. -/
theorem pairs_eq_card (keys : ℕ → ℕ) (k : ℕ) :
    pairs keys k = #{p ∈ (range k).offDiag | keys p.1 = keys p.2} := by
  induction k with
  | zero => simp [pairs]
  | succ k ih =>
    let S := range k
    let A := {p ∈ S.offDiag | keys p.1 = keys p.2}
    let B := {p ∈ {k} ×ˢ S | keys p.1 = keys p.2}
    let C := {p ∈ S ×ˢ {k} | keys p.1 = keys p.2}
    have hrow : B = {k} ×ˢ {i ∈ S | keys i = keys k} := by
      ext p
      simp only [B, mem_filter, mem_product, mem_singleton]
      aesop
    have hcol : C = {i ∈ S | keys i = keys k} ×ˢ {k} := by
      ext p
      simp only [C, mem_filter, mem_product, mem_singleton]
      aesop
    have hAB : Disjoint A B := by
      rw [disjoint_left]
      intro p hp hq
      have hp' := (mem_offDiag.mp (mem_filter.mp hp).1).1
      have hq' := mem_singleton.mp (mem_product.mp (mem_filter.mp hq).1).1
      have : p.1 < k := mem_range.mp hp'
      omega
    have hAC : Disjoint (A ∪ B) C := by
      rw [disjoint_left]
      intro p hp hq
      have hq' := mem_singleton.mp (mem_product.mp (mem_filter.mp hq).1).2
      rcases mem_union.mp hp with hp | hp
      · have hp' := (mem_offDiag.mp (mem_filter.mp hp).1).2.1
        have : p.2 < k := mem_range.mp hp'
        omega
      · have hp' := (mem_product.mp (mem_filter.mp hp).1).2
        have : p.2 < k := mem_range.mp hp'
        omega
    have hsplit : {p ∈ (range (k + 1)).offDiag | keys p.1 = keys p.2} = A ∪ B ∪ C := by
      rw [range_add_one, offDiag_insert (notMem_range_self : k ∉ range k),
        filter_union, filter_union]
    rw [hsplit, card_union_of_disjoint hAC, card_union_of_disjoint hAB, hrow, hcol,
      card_product, card_product, card_singleton, one_mul, mul_one]
    change pairs keys k + 2 * count keys k (keys k) =
      #{p ∈ (range k).offDiag | keys p.1 = keys p.2} + count keys k (keys k) +
        count keys k (keys k)
    rw [ih]
    omega

/-- The original memory, with the histogram block replaced by prefix bucket counts. -/
def memory (mem : ℕ → ℕ) (keys : ℕ → ℕ) (dst bins k : ℕ) : ℕ → ℕ :=
  fun a => if dst ≤ a ∧ a < dst + bins then count keys k (a - dst) else mem a

/-- Reading a histogram bucket. -/
theorem memory_read (mem : ℕ → ℕ) (keys : ℕ → ℕ) (dst bins k b : ℕ)
    (hb : b < bins) : memory mem keys dst bins k (dst + b) = count keys k b := by
  simp [memory, hb]

/-- Histogram writes preserve all other cells. -/
theorem memory_outside (mem : ℕ → ℕ) (keys : ℕ → ℕ) (dst bins k a : ℕ)
    (ha : ¬(dst ≤ a ∧ a < dst + bins)) : memory mem keys dst bins k a = mem a := by
  simp [memory, ha]

/-- One insertion is a single histogram-cell update. -/
theorem memory_succ (mem : ℕ → ℕ) (keys : ℕ → ℕ) (dst bins k : ℕ)
    (hk : keys k < bins) :
    memory mem keys dst bins (k + 1) = Function.update (memory mem keys dst bins k)
      (dst + keys k) (count keys k (keys k) + 1) := by
  funext a
  by_cases ha : a = dst + keys k
  · subst a
    simp [memory_read, hk, count_succ]
  · rw [Function.update_of_ne ha]
    simp only [memory]
    split_ifs with h
    · have hne : keys k ≠ a - dst := by omega
      simp [count_succ, hne]
    · rfl

/-- Input base. -/
abbrev src : Fin 11 := 0
/-- Histogram base. -/
abbrev dst : Fin 11 := 1
/-- Number of input keys. -/
abbrev len : Fin 11 := 2
/-- Number of buckets. -/
abbrev bins : Fin 11 := 3
/-- Prefix length. -/
abbrev idx : Fin 11 := 4
/-- Temporary address. -/
abbrev addr : Fin 11 := 5
/-- Current key. -/
abbrev key : Fin 11 := 6
/-- Current bucket count. -/
abbrev bucketSize : Fin 11 := 7
/-- Number of ordered collisions. -/
abbrev total : Fin 11 := 8
/-- Constant one. -/
abbrev one : Fin 11 := 9
/-- Constant zero. -/
abbrev zero : Fin 11 := 10

/-- Clear one histogram cell and advance the cursor. -/
def clearBody : Code .standard 11 := ram[
  addr ← dst + idx; *addr ← zero; idx ← idx + one ]

/-- Insert one key and add twice its old bucket count. -/
def body : Code .standard 11 := ram[
  addr ← src + idx; key ← *addr; addr ← dst + key;
  bucketSize ← *addr; total ← total + bucketSize; total ← total + bucketSize;
  bucketSize ← bucketSize + one; *addr ← bucketSize; idx ← idx + one ]

/-- Clear the histogram, retaining the input and all four parameters. -/
def clear : Code .standard 11 :=
  .seq (ram[ idx ← #0; one ← #1; zero ← #0 ]) (.loop (.lt idx bins) clearBody)

/-- Insert all keys into a cleared histogram. -/
def insert : Code .standard 11 :=
  .seq (ram[ idx ← #0; total ← #0 ]) (.loop (.lt idx len) body)

/-- Fixed code, with all bases and lengths supplied in registers. -/
def program : Code .standard 11 := .seq clear insert

private theorem exec_clear {w : ℕ} (x : Data 11) (h1 : Fits w 1)
    (hd : Fits w (x.regs dst + x.regs bins)) :
    ∃ y, ExecWithin w clear x y (5 * x.regs bins + 5) ∧
      y.mem = Cslib.WordRAM.clear x.mem (x.regs dst) (x.regs bins) ∧
      (∀ i, i.val < 4 → y.regs i = x.regs i) ∧ y.regs one = 1 := by
  let I (y : Data 11) : Prop :=
    (∀ i, i.val < 4 → y.regs i = x.regs i) ∧ y.regs one = 1 ∧ y.regs zero = 0 ∧
      y.regs idx ≤ x.regs bins ∧ y.mem = Cslib.WordRAM.clear x.mem (x.regs dst) (y.regs idx)
  have hbody (y : Data 11) (hy : I y) (hc : (Cond.lt idx bins).Holds y) :
      ∃ z, ExecWithin w clearBody y z 3 ∧ I z ∧
        x.regs bins - z.regs idx < x.regs bins - y.regs idx := by
    obtain ⟨hr, ho, hz, hi, hm⟩ := hy
    have hb := hr bins (by decide)
    have hdst := hr dst (by decide)
    have hlt : y.regs idx < x.regs bins := by simpa only [Cond.holds_lt, hb] using hc
    have ha : Fits w (y.regs dst + y.regs idx) := hd.of_le (by rw [hdst]; omega)
    have hn : Fits w (y.regs idx + 1) := hd.of_le (by omega)
    refine ⟨?z, ?run, ?inv, ?decrease⟩
    case run => ram_eval [clearBody, ha, hn, ho]
    case inv =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        have hia : i ≠ addr := by intro h; subst i; norm_num [addr] at hi
        have hii : i ≠ idx := by intro h; subst i; norm_num [idx] at hi
        simpa only [Data.set_regs, Data.write_regs, Function.update_of_ne hia,
          Function.update_of_ne hii] using hr i hi
      · simpa +decide [Function.update_apply] using ho
      · simpa +decide [Function.update_apply] using hz
      · simpa [ho] using Nat.succ_le_of_lt hlt
      · simp only [Data.set_mem, Data.write_mem, Data.set_regs, Function.update_apply]
        rw [hz, hm, hdst, ← Cslib.WordRAM.clear_succ]
        rfl
    case decrease => simp only [Data.set_regs, Function.update_self]; omega
  let x₀ := ((x.set idx 0).set one 1).set zero 0
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hiz : i ≠ zero := by intro h; subst i; norm_num [zero] at hi
      have hio : i ≠ one := by intro h; subst i; norm_num [one] at hi
      have hii : i ≠ idx := by intro h; subst i; norm_num [idx] at hi
      simp only [x₀, Data.set_regs, Function.update_of_ne hiz, Function.update_of_ne hio,
        Function.update_of_ne hii]
    · simp +decide [x₀, one, zero, idx]
    · simp [x₀]
    · simp +decide [x₀, one, zero, idx]
    · simp +decide [x₀, one, zero, idx, Cslib.WordRAM.clear_zero]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => x.regs bins - y.regs idx) hbody hx₀
  obtain ⟨hr, ho, hz, hi, hm⟩ := hy
  have hb := hr bins (by decide)
  have hend : y.regs idx = x.regs bins := by
    simp only [Cond.holds_lt, hb] at hc
    omega
  refine ⟨y, ?_, by simpa only [hend] using hm, hr, ho⟩
  have hinit : ExecWithin (B := .standard) w (ram[ idx ← #0; one ← #1; zero ← #0 ]) x x₀ 3 := by
    ram_eval [x₀, h1]
  convert hinit.seq he using 1
  · rfl
  · simp +decide only [x₀, Data.set_regs, Function.update_apply, idx, one, zero, ↓reduceIte,
      Nat.sub_zero]
    omega

private theorem exec_insert {w : ℕ} (x : Data 11) (keys : ℕ → ℕ)
    (hs : Fits w (x.regs src + x.regs len))
    (hd : Fits w (x.regs dst + x.regs bins))
    (ht : Fits w (x.regs len * x.regs len + x.regs len + 1))
    (hdisj : x.regs src + x.regs len ≤ x.regs dst)
    (hkeys : ∀ i < x.regs len, keys i < x.regs bins)
    (hinput : ∀ i < x.regs len, x.mem (x.regs src + i) = keys i)
    (hzero : ∀ b < x.regs bins, x.mem (x.regs dst + b) = 0)
    (ho : x.regs one = 1) :
    ∃ y, ExecWithin w insert x y (11 * x.regs len + 4) ∧
      y.mem = memory x.mem keys (x.regs dst) (x.regs bins) (x.regs len) ∧
      y.regs total = pairs keys (x.regs len) ∧
      (∀ i, i.val < 4 → y.regs i = x.regs i) ∧ y.regs one = 1 := by
  let I (y : Data 11) : Prop :=
    (∀ i, i.val < 4 → y.regs i = x.regs i) ∧ y.regs one = 1 ∧
      y.regs idx ≤ x.regs len ∧ y.regs total = pairs keys (y.regs idx) ∧
      y.mem = memory x.mem keys (x.regs dst) (x.regs bins) (y.regs idx)
  have hbody (y : Data 11) (hy : I y) (hc : (Cond.lt idx len).Holds y) :
      ∃ z, ExecWithin w body y z 9 ∧ I z ∧
        x.regs len - z.regs idx < x.regs len - y.regs idx := by
    obtain ⟨hr, ho, hi, hp, hm⟩ := hy
    have hl := hr len (by decide)
    have hsrc := hr src (by decide)
    have hdst := hr dst (by decide)
    have hlt : y.regs idx < x.regs len := by simpa only [Cond.holds_lt, hl] using hc
    have hkey := hkeys _ hlt
    have hread : y.mem (y.regs src + y.regs idx) = keys (y.regs idx) := by
      rw [hm, hsrc, memory_outside]
      · exact hinput _ hlt
      · omega
    have hbucket : y.mem (y.regs dst + keys (y.regs idx)) =
        count keys (y.regs idx) (keys (y.regs idx)) := by
      rw [hm, hdst, memory_read _ _ _ _ _ _ hkey]
    have ha : Fits w (y.regs src + y.regs idx) := hs.of_le (by rw [hsrc]; omega)
    have hb : Fits w (y.regs dst + keys (y.regs idx)) := hd.of_le (by rw [hdst]; omega)
    have hn : Fits w (y.regs idx + 1) := ht.of_le (by omega)
    have hc := count_le keys (y.regs idx) (keys (y.regs idx))
    have hpnext := pairs_le_sq keys (y.regs idx + 1)
    have hsquare : (y.regs idx + 1) * (y.regs idx + 1) ≤ x.regs len * x.regs len :=
      Nat.mul_self_le_mul_self (by omega)
    have ht₂ : Fits w (pairs keys (y.regs idx) + count keys (y.regs idx) (keys (y.regs idx)) +
        count keys (y.regs idx) (keys (y.regs idx))) := ht.of_le (by
      dsimp only [pairs] at hpnext
      omega)
    have ht₁ : Fits w (pairs keys (y.regs idx) + count keys (y.regs idx) (keys (y.regs idx))) :=
      ht₂.of_le (by omega)
    have hcount : Fits w (count keys (y.regs idx) (keys (y.regs idx)) + 1) :=
      ht.of_le (by omega)
    refine ⟨?z, ?run, ?inv, ?decrease⟩
    case run => ram_eval [body, ha, hb, hn, ho, hread, hbucket, hp, ht₁, ht₂, hcount]
    case inv =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        have hia : i ≠ addr := by intro h; subst i; norm_num [addr] at hi
        have hik : i ≠ key := by intro h; subst i; norm_num [key] at hi
        have hic : i ≠ bucketSize := by intro h; subst i; norm_num [bucketSize] at hi
        have hit : i ≠ total := by intro h; subst i; norm_num [total] at hi
        have hii : i ≠ idx := by intro h; subst i; norm_num [idx] at hi
        simpa only [Data.set_regs, Data.write_regs, Function.update_of_ne hia,
          Function.update_of_ne hik, Function.update_of_ne hic, Function.update_of_ne hit,
          Function.update_of_ne hii] using hr i hi
      · simpa +decide [Function.update_apply] using ho
      · simpa [ho] using Nat.succ_le_of_lt hlt
      · change pairs keys (y.regs idx) + count keys (y.regs idx) (keys (y.regs idx)) +
          count keys (y.regs idx) (keys (y.regs idx)) = pairs keys (y.regs idx + 1)
        simp only [pairs, two_mul, Nat.add_assoc]
      · change Function.update y.mem (y.regs dst + keys (y.regs idx))
          (count keys (y.regs idx) (keys (y.regs idx)) + 1) =
            memory x.mem keys (x.regs dst) (x.regs bins) (y.regs idx + 1)
        rw [hm, hdst, ← memory_succ _ _ _ _ _ hkey]
    case decrease => simp only [Data.set_regs, Function.update_self]; omega
  let x₀ := (x.set idx 0).set total 0
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hit : i ≠ total := by intro h; subst i; norm_num [total] at hi
      have hii : i ≠ idx := by intro h; subst i; norm_num [idx] at hi
      simp only [x₀, Data.set_regs, Function.update_of_ne hit, Function.update_of_ne hii]
    · simpa +decide [x₀, one, total, idx] using ho
    · simp +decide [x₀, total, idx]
    · simp +decide [x₀, total, idx, pairs]
    · change x.mem = memory x.mem keys (x.regs dst) (x.regs bins) 0
      funext a
      by_cases h : x.regs dst ≤ a ∧ a < x.regs dst + x.regs bins
      · have ha : x.regs dst + (a - x.regs dst) = a := by omega
        simpa [memory, h, ha] using hzero (a - x.regs dst) (by omega)
      · simp only [memory, h, ↓reduceIte]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => x.regs len - y.regs idx) hbody hx₀
  obtain ⟨hr, ho, hi, hp, hm⟩ := hy
  have hl := hr len (by decide)
  have hend : y.regs idx = x.regs len := by
    simp only [Cond.holds_lt, hl] at hc
    omega
  refine ⟨y, ?_, by simpa only [hend] using hm, by simpa only [hend] using hp, hr, ho⟩
  have hinit : ExecWithin (B := .standard) w (ram[ idx ← #0; total ← #0 ]) x x₀ 2 := by
    ram_eval [x₀]
  convert hinit.seq he using 1
  · rfl
  · simp +decide only [x₀, Data.set_regs, Function.update_apply, idx, total, ↓reduceIte,
      Nat.sub_zero]
    omega

/-- Build a histogram and count ordered collisions within `5M + 11n + 9` native instructions.
The input keys lie in `[0,M)`. The input precedes the output block. Both one-past-end
addresses and the quadratic counter bound must fit. These are explicit local contracts;
constructing the keys and deriving a logarithmic width are separate client obligations. -/
theorem exec {w : ℕ} (x : Data 11) (keys : ℕ → ℕ) (h1 : Fits w 1)
    (hs : Fits w (x.regs src + x.regs len))
    (hd : Fits w (x.regs dst + x.regs bins))
    (ht : Fits w (x.regs len * x.regs len + x.regs len + 1))
    (hdisj : x.regs src + x.regs len ≤ x.regs dst)
    (hkeys : ∀ i < x.regs len, keys i < x.regs bins)
    (hinput : ∀ i < x.regs len, x.mem (x.regs src + i) = keys i) :
    ∃ y, ExecWithin w program x y (5 * x.regs bins + 11 * x.regs len + 9) ∧
      y.mem = memory x.mem keys (x.regs dst) (x.regs bins) (x.regs len) ∧
      y.regs total = pairs keys (x.regs len) ∧
      (∀ i, i.val < 4 → y.regs i = x.regs i) := by
  obtain ⟨y, he, hm, hr, ho⟩ := exec_clear x h1 hd
  have hsrc := hr src (by decide)
  have hdst := hr dst (by decide)
  have hlen := hr len (by decide)
  have hbins := hr bins (by decide)
  obtain ⟨z, hz, hzm, hzt, hzr, _⟩ := exec_insert y keys
    (by simpa only [hsrc, hlen] using hs) (by simpa only [hdst, hbins] using hd)
    (by simpa only [hlen] using ht) (by simpa only [hsrc, hlen, hdst] using hdisj)
    (by simpa only [hlen, hbins] using hkeys) (by
      intro i hi
      rw [hsrc, hm]
      have hlt : i < x.regs len := by simpa only [hlen] using hi
      simp only [Cslib.WordRAM.clear, show ¬(x.regs dst ≤ x.regs src + i ∧
        x.regs src + i < x.regs dst + x.regs bins) from by omega, ↓reduceIte]
      exact hinput i hlt) (by
      intro b hb
      rw [hm, hdst]
      have hb' : b < x.regs bins := by simpa only [hbins] using hb
      simp [Cslib.WordRAM.clear, hb']) ho
  refine ⟨z, ?_, ?_, by simpa only [hlen] using hzt, fun i hi => (hzr i hi).trans (hr i hi)⟩
  · exact (he.seq hz).mono (by rw [hlen]; omega)
  · rw [hzm, hm, hdst, hbins, hlen]
    funext a
    simp only [memory, Cslib.WordRAM.clear]
    split_ifs <;> rfl

end Cslib.Algorithms.WordRAM.Histogram
