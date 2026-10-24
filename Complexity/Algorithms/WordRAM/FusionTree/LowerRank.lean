/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Rank

/-!
# Strict packed sketch ranks

The zero-bit branch of arbitrary-query correction requires a strict rank. Subtracting the
number of sketches at least the query from the node occupancy handles equality and zero
queries directly.

## Main definitions

* `LowerRankProgram.query`, `LowerRankProgram.node`, `LowerRankProgram.copies`,
  `LowerRankProgram.guards`, `LowerRankProgram.bits`, `LowerRankProgram.middle`,
  `LowerRankProgram.base`, `LowerRankProgram.count`, `LowerRankProgram.temp`,
  `LowerRankProgram.out`: register indices for strict sketch rank.
* `LowerRankProgram.code`, `LowerRankProgram.result`: eight standard instructions for strict sketch
  rank and the resulting machine state.

## Main results

* `LowerRankProgram.exec`: checked execution returning the number of sketches below the query.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.LowerRankProgram

open Cslib.WordRAM Cslib.BitString

/-- The input register layout agrees with `RankProgram`, except register seven is occupancy
and register one contains the original sketches rather than their complements. -/
abbrev query : Fin 10 := 0
/-- Packed guarded sketches. -/
abbrev node : Fin 10 := 1
/-- Replication multiplier. -/
abbrev copies : Fin 10 := 2
/-- Mask of field guards. -/
abbrev guards : Fin 10 := 3
/-- Payload width. -/
abbrev bits : Fin 10 := 4
/-- Middle digit divisor. -/
abbrev middle : Fin 10 := 5
/-- Field radix. -/
abbrev base : Fin 10 := 6
/-- Number of stored sketches. -/
abbrev count : Fin 10 := 7
/-- Scratch for the replicated query. -/
abbrev temp : Fin 10 := 8
/-- Final strict rank. -/
abbrev out : Fin 10 := 9

/-- Count guards for `q ≤ sᵢ`, then subtract the count from the occupancy. -/
def code : Code .standard 10 := ram[
  temp ← query * copies;
  out ← node - temp;
  out ← out &&& guards;
  out ← out >>> bits;
  out ← out * copies;
  out ← out / middle;
  out ← out % base;
  out ← count - out ]

/-- Exact state after all eight instructions. -/
def result (x : Data 10) (b n : ℕ) (s : ℕ → ℕ) (q : ℕ) : Data 10 :=
  let d := packedDifference b n s q
  let f := guardFlags b n s q
  let p := f * queryMultiplier b n
  ((((((((x.set temp (q * queryMultiplier b n)).set out d).set out
    (d &&& guardMask b n)).set out f).set out p).set out
    (p / 2 ^ ((b + 1) * (n - 1)))).set out (countGuards b n s q)).set out
    (n - countGuards b n s q))

/-- Subtracting the number of sketches at least `q` from `n` counts the sketches strictly below
`q`. -/
theorem countGuards_complement {b n q : ℕ} (s : ℕ → ℕ) (hn : 0 < n)
    (hb : n < 2 ^ (b + 1)) (hs : ∀ i < n, s i < 2 ^ b) (hq : q < 2 ^ b) :
    n - countGuards b n s q = ((Finset.range n).filter (fun i => s i < q)).card := by
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.range n) (fun i => q ≤ s i)
  simp only [Finset.card_range, not_le] at hc
  rw [countGuards_eq s hn hb hs hq]
  simp only [Finset.card_filter] at hc ⊢
  have he : (∑ i ∈ Finset.range n, (decide (q ≤ s i)).toNat) =
      ∑ i ∈ Finset.range n, if q ≤ s i then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : q ≤ s i <;> simp [h]
  rw [he]
  omega

/-- Eight checked instructions return the strict rank, including zero and equality queries.
The node parameters and memory are preserved; query compression and constant loading are
separate. The full guard-count product fits under the stated packed-width bound. -/
theorem exec {w b n q : ℕ} (s : ℕ → ℕ) (x : Data 10) (hn : 0 < n)
    (hb : n < 2 ^ (b + 1)) (hs : ∀ i < n, s i < 2 ^ b) (hq : q < 2 ^ b)
    (hw : 2 * ((b + 1) * n) ≤ w)
    (hxq : x.regs query = q) (hxn : x.regs node = packedNode b n s)
    (hxc : x.regs copies = queryMultiplier b n) (hxg : x.regs guards = guardMask b n)
    (hxb : x.regs bits = b) (hxm : x.regs middle = 2 ^ ((b + 1) * (n - 1)))
    (hxr : x.regs base = 2 ^ (b + 1)) (hxn' : x.regs count = n) :
    Exec w code x (result x b n s q) 8 ∧
      (result x b n s q).regs out = ((Finset.range n).filter (fun i => s i < q)).card ∧
      (result x b n s q).mem = x.mem := by
  have hpacked : (b + 1) * n ≤ w := by omega
  have hbitwidth : b + 1 ≤ w := by
    have hm := Nat.mul_le_mul_left (b + 1) (show 1 ≤ n by omega)
    simp only [mul_one] at hm
    omega
  have hnfit : Fits w n := hb.trans_le (Nat.pow_le_pow_right (by decide) hbitwidth)
  have hrep : Fits w (q * queryMultiplier b n) :=
    (query_mul_multiplier_lt hq).trans_le (Nat.pow_le_pow_right (by decide) hpacked)
  have hdiff : Fits w (packedDifference b n s q) :=
    (packedDifference_lt s hs).trans_le (Nat.pow_le_pow_right (by decide) hpacked)
  have hmask : Fits w (packedDifference b n s q &&& guardMask b n) :=
    hdiff.of_le Nat.and_le_left
  have hflag_le : guardFlags b n s q ≤ packedDifference b n s q := by
    rw [guardFlags, Nat.shiftRight_eq_div_pow]
    exact (Nat.div_le_self _ _).trans Nat.and_le_left
  have hflag : Fits w (guardFlags b n s q) := hdiff.of_le hflag_le
  have hcount : Fits w (guardFlags b n s q * queryMultiplier b n) := by
    have h₁ := hflag_le.trans_lt (packedDifference_lt s hs)
    have h₂ := queryMultiplier_lt b n
    have h₃ := Nat.mul_lt_mul_of_lt_of_lt h₁ h₂
    rw [← pow_add] at h₃
    exact h₃.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hdiv : Fits w ((guardFlags b n s q * queryMultiplier b n) /
      2 ^ ((b + 1) * (n - 1))) := hcount.of_le (Nat.div_le_self _ _)
  have hmod : Fits w (countGuards b n s q) := hdiv.of_le (Nat.mod_le _ _)
  have hsub : Fits w (n - countGuards b n s q) := hnfit.of_le (Nat.sub_le _ _)
  simp only [countGuards, guardFlags, packedDifference] at hdiff hmask hflag hcount hdiv hmod hsub
  refine ⟨?_, ?_, rfl⟩
  · ram_eval [code, result, hxq, hxn, hxc, hxg, hxb, hxm, hxr, hxn',
      hrep, hdiff, hmask, hflag, hcount, hdiv, hmod, hsub,
      countGuards, guardFlags, packedDifference]
  · simpa only [result, Data.set_regs, Function.update_self] using
      countGuards_complement s hn hb hs hq

end Cslib.Algorithms.WordRAM.FusionTree.LowerRankProgram
