/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Packed
public import Complexity.Foundations.Data.Nat.Bitwise.Sparse
public import Complexity.Foundations.Data.Nat.Bitwise.PackedCount
public import Complexity.Computability.WordRAM.Notation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Packed sketch ranks

Guard extraction and multiplication count all simultaneous comparisons. Complementing the
sketches reverses the comparison to obtain inclusive ranks. None of these operations assumes
a most-significant-bit primitive. Node constants must be precomputed and loaded separately.

## Main definitions

* `guardMask`, `guardFlags`: extract one zero-or-one digit from each guarded comparison.
* `upperRankExpr`: inclusive rank using complemented sketches.

## Main results

* `guardFlags_eq`: exact packed Boolean comparison digits.
* `upperRankExpr_eq_card`: the resulting inclusive rank.
* `RankProgram.exec`: eight actual checked instructions return the inclusive rank.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree

open Cslib.BitString
open scoped BigOperators

/-- One guard bit per field, with all other bits zero. -/
def guardMask (b n : ℕ) : ℕ := packedNode b n (fun _ => 0)

private theorem guardMask_eq_sum (b n : ℕ) :
    guardMask b n = ∑ i ∈ Finset.range n, 2 ^ (b + (b + 1) * i) := by
  simp only [guardMask, packedNode_eq_sum, add_zero, pow_add]

/-- The guard mask has no other set bits. -/
private theorem guardMask_testBit (b n k : ℕ) :
    (guardMask b n).testBit k = true ↔
      ∃ i ∈ Finset.range n, b + (b + 1) * i = k := by
  have hf : Function.Injective (fun i : ℕ => b + (b + 1) * i) := by
    intro i j he
    exact Nat.mul_left_cancel (by omega) (Nat.add_left_cancel he)
  simpa only [guardMask_eq_sum, Bool.toNat_true, one_mul, true_and] using
    Nat.testBit_sum_injective (Finset.range n) (fun i => b + (b + 1) * i)
      (fun _ _ _ _ he => hf he) (fun _ => true) k

/-- Move each comparison's guard to the lowest bit of its radix field. -/
def guardFlags (b n : ℕ) (s : ℕ → ℕ) (q : ℕ) : ℕ :=
  (packedDifference b n s q &&& guardMask b n) >>> b

/-- Guard extraction returns exactly the packed zero-or-one comparison digits. -/
theorem guardFlags_eq {b n q : ℕ} (s : ℕ → ℕ)
    (hs : ∀ i < n, s i < 2 ^ b) (hq : q < 2 ^ b) :
    guardFlags b n s q =
      packRadix (2 ^ (b + 1)) n (fun i => (decide (q ≤ s i)).toNat) := by
  have hf : Function.Injective (fun i : ℕ => (b + 1) * i) := by
    intro i j he
    exact Nat.mul_left_cancel (by omega) he
  apply Nat.eq_of_testBit_eq
  intro k
  apply Bool.eq_iff_iff.mpr
  simp only [guardFlags, Nat.testBit_shiftRight, Nat.testBit_land, Bool.and_eq_true,
    guardMask_testBit, packRadix, ← pow_mul]
  rw [Nat.testBit_sum_injective _ _ (fun _ _ _ _ he => hf he)]
  constructor
  · rintro ⟨hd, i, hi, he⟩
    refine ⟨i, hi, ?_, Nat.add_left_cancel he⟩
    rw [← he, packedDifference_guard s hs hq (Finset.mem_range.mp hi)] at hd
    exact hd
  · rintro ⟨i, hi, hc, he⟩
    refine ⟨?_, i, hi, by omega⟩
    rw [← he, packedDifference_guard s hs hq (Finset.mem_range.mp hi)]
    exact hc

/-- Count all set comparison guards through the middle field of one product. -/
def countGuards (b n : ℕ) (s : ℕ → ℕ) (q : ℕ) : ℕ :=
  (guardFlags b n s q * queryMultiplier b n) / 2 ^ ((b + 1) * (n - 1)) % 2 ^ (b + 1)

theorem countGuards_eq {b n q : ℕ} (s : ℕ → ℕ) (hn : 0 < n)
    (hb : n < 2 ^ (b + 1)) (hs : ∀ i < n, s i < 2 ^ b) (hq : q < 2 ^ b) :
    countGuards b n s q = ∑ i ∈ Finset.range n, (decide (q ≤ s i)).toNat := by
  rw [countGuards, guardFlags_eq s hs hq, queryMultiplier, pow_mul]
  exact countPackedFlags _ hn hb

/-- An inclusive sketch rank, obtained by complementing both sides of each comparison. -/
def upperRankExpr (b n : ℕ) (s : ℕ → ℕ) (q : ℕ) : ℕ :=
  countGuards b n (fun i => 2 ^ b - 1 - s i) (2 ^ b - 1 - q)

/-- The expression returns the number of sketches at or below the query. Sortedness is
unnecessary for the arithmetic identity; a tree uses sorted sketches to interpret the rank. -/
theorem upperRankExpr_eq_card {b n q : ℕ} (s : ℕ → ℕ) (hn : 0 < n)
    (hb : n < 2 ^ (b + 1)) (hs : ∀ i < n, s i < 2 ^ b) (hq : q < 2 ^ b) :
    upperRankExpr b n s q = ((Finset.range n).filter (fun i => s i ≤ q)).card := by
  have hp := Nat.two_pow_pos b
  have hs' (i : ℕ) (hi : i < n) : 2 ^ b - 1 - s i < 2 ^ b := by omega
  have hq' : 2 ^ b - 1 - q < 2 ^ b := by omega
  rw [upperRankExpr, countGuards_eq _ hn hb hs' hq', Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := hs i (Finset.mem_range.mp hi)
  by_cases he : s i ≤ q <;> simp [he, show 2 ^ b - 1 - q ≤ 2 ^ b - 1 - s i ↔ s i ≤ q by omega]

namespace RankProgram

open Cslib.WordRAM

/-- Query sketch. -/
abbrev query : Fin 10 := 0
/-- Packed guarded complements of the stored sketches. -/
abbrev node : Fin 10 := 1
/-- Replication multiplier. -/
abbrev copies : Fin 10 := 2
/-- Mask selecting all guard bits. -/
abbrev guards : Fin 10 := 3
/-- Number of payload bits per field. -/
abbrev bits : Fin 10 := 4
/-- Power selecting the count product's middle digit. -/
abbrev middle : Fin 10 := 5
/-- Field radix. -/
abbrev base : Fin 10 := 6
/-- Largest possible payload. -/
abbrev maximum : Fin 10 := 7
/-- Replicated complemented query. -/
abbrev temp : Fin 10 := 8
/-- Scratch register and final inclusive rank. -/
abbrev out : Fin 10 := 9

/-- Eight standard instructions compute the complete inclusive sketch rank. All eight input
registers and all memory are preserved. The precomputed constants are supplied by the caller. -/
def code : Code .standard 10 := ram[
  out ← maximum - query;
  temp ← out * copies;
  out ← node - temp;
  out ← out &&& guards;
  out ← out >>> bits;
  out ← out * copies;
  out ← out / middle;
  out ← out % base ]

/-- The exact final data, retaining the intermediate temporary register. -/
def result (x : Data 10) (b n : ℕ) (s : ℕ → ℕ) (q : ℕ) : Data 10 :=
  let cq := 2 ^ b - 1 - q
  let cs := fun i => 2 ^ b - 1 - s i
  let d := packedDifference b n cs cq
  let f := guardFlags b n cs cq
  let p := f * queryMultiplier b n
  ((((((((x.set out cq).set temp (cq * queryMultiplier b n)).set out d).set out
    (d &&& guardMask b n)).set out f).set out p).set out
    (p / 2 ^ ((b + 1) * (n - 1)))).set out (upperRankExpr b n s q))

/-- Checked execution of the full inclusive rank in eight instructions. The packed word
occupies at most half the physical width, making the count multiplication legal too.
Construction/loading of the node constants and compressed query remain separate. -/
theorem exec {w b n q : ℕ} (s : ℕ → ℕ) (x : Data 10) (hn : 0 < n)
    (hb : n < 2 ^ (b + 1)) (hs : ∀ i < n, s i < 2 ^ b) (hq : q < 2 ^ b)
    (hw : 2 * ((b + 1) * n) ≤ w)
    (hxq : x.regs query = q)
    (hxn : x.regs node = packedNode b n (fun i => 2 ^ b - 1 - s i))
    (hxc : x.regs copies = queryMultiplier b n) (hxg : x.regs guards = guardMask b n)
    (hxb : x.regs bits = b) (hxm : x.regs middle = 2 ^ ((b + 1) * (n - 1)))
    (hxr : x.regs base = 2 ^ (b + 1)) (hxmax : x.regs maximum = 2 ^ b - 1) :
    Exec w code x (result x b n s q) 8 ∧
      (result x b n s q).regs out = ((Finset.range n).filter (fun i => s i ≤ q)).card ∧
      (result x b n s q).mem = x.mem := by
  let cq := 2 ^ b - 1 - q
  let cs := fun i => 2 ^ b - 1 - s i
  have hp := Nat.two_pow_pos b
  have hcq : cq < 2 ^ b := by dsimp only [cq]; omega
  have hcs (i : ℕ) (_ : i < n) : cs i < 2 ^ b := by dsimp only [cs]; omega
  have hpacked : (b + 1) * n ≤ w := by omega
  have hbitwidth : b ≤ w := by
    have hm := Nat.mul_le_mul_left (b + 1) (show 1 ≤ n by omega)
    simp only [mul_one] at hm
    omega
  have hqfit : Fits w cq := hcq.trans_le (Nat.pow_le_pow_right (by decide) hbitwidth)
  have hrep : Fits w (cq * queryMultiplier b n) :=
    (query_mul_multiplier_lt hcq).trans_le (Nat.pow_le_pow_right (by decide) hpacked)
  have hdiff : Fits w (packedDifference b n cs cq) :=
    (packedDifference_lt cs hcs).trans_le (Nat.pow_le_pow_right (by decide) hpacked)
  have hmask : Fits w (packedDifference b n cs cq &&& guardMask b n) :=
    hdiff.of_le Nat.and_le_left
  have hflag_le : guardFlags b n cs cq ≤ packedDifference b n cs cq := by
    rw [guardFlags, Nat.shiftRight_eq_div_pow]
    exact (Nat.div_le_self _ _).trans Nat.and_le_left
  have hflag : Fits w (guardFlags b n cs cq) := hdiff.of_le hflag_le
  have hcount : Fits w (guardFlags b n cs cq * queryMultiplier b n) := by
    have h₁ := hflag_le.trans_lt (packedDifference_lt cs hcs)
    have h₂ := queryMultiplier_lt b n
    have h₃ := Nat.mul_lt_mul_of_lt_of_lt h₁ h₂
    rw [← pow_add] at h₃
    exact h₃.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hdiv : Fits w ((guardFlags b n cs cq * queryMultiplier b n) /
      2 ^ ((b + 1) * (n - 1))) := hcount.of_le (Nat.div_le_self _ _)
  have hmod : Fits w (upperRankExpr b n s q) := hdiv.of_le (Nat.mod_le _ _)
  simp only [cq, cs, upperRankExpr, countGuards, guardFlags,
    packedDifference] at hqfit hrep hdiff hmask hflag hcount hdiv hmod
  refine ⟨?_, ?_, rfl⟩
  · ram_eval [code, result, hxq, hxn, hxc, hxg, hxb, hxm, hxr, hxmax,
      hqfit, hrep, hdiff, hmask, hflag, hcount, hdiv, hmod,
      cq, cs, upperRankExpr, countGuards, guardFlags, packedDifference]
  · simpa only [result, Data.set_regs, Function.update_self] using
      upperRankExpr_eq_card s hn hb hs hq

end RankProgram

end Cslib.Algorithms.WordRAM.FusionTree
