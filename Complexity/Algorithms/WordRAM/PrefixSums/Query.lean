/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PrefixSums.Update

/-!
# Fixed Word-RAM prefix queries

The query descends through an aggregation tree, adding the complete left subtree whenever
it descends right. It stops at an empty prefix or a complete subtree. The program is fixed;
the array size, query position and tree pointer are register inputs.

## Main definitions

* `queryBody`, `queryLoop`, `queryNext`: one iteration of a prefix query, the fixed prefix-query
  loop, and the state transition of one iteration.

## Main results

* `queryLoop_spec`: the answer equals the mathematical prefix sum within `13 (h + 1) + 2`
  instructions, with all memory preserved.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PrefixSums

open Cslib.WordRAM Reg

/-- One prefix-query iteration. -/
def queryBody : Code .standard 14 := ram[
  if idx = len then [val ← *ptr; ans ← ans + val; idx ← #0]
  else [len ← len / two;
    if idx < len then [ptr ← ptr + one]
    else [tmp ← ptr + one; val ← *tmp; ans ← ans + val;
      ptr ← ptr + len; ptr ← ptr + len; idx ← idx - len]] ]

/-- Fixed prefix-query loop. Its answer is added to the initial accumulator. -/
def queryLoop : Code .standard 14 := ram[while zero < idx do [⟪queryBody⟫]]

/-- Mathematical description of one query iteration, used only in the proof. -/
def queryNext (x : Data 14) (b n i a : ℕ) : Data 14 :=
  if i = n then ((x.set val (x.mem b)).set ans (a + x.mem b)).set idx 0
  else
    let y := x.set len (n / 2)
    if i < n / 2 then y.set ptr (b + 1)
    else
      let z := ((y.set tmp (b + 1)).set val (x.mem (b + 1))).set ans (a + x.mem (b + 1))
      ((z.set ptr (b + n / 2)).set ptr (b + n / 2 + n / 2)).set idx (i - n / 2)

variable {w h b n i δ a : ℕ} {x : Data 14}

private theorem queryBody_exec (hx : Entry b n i δ x) (hi : i ≤ n) (hn : 0 < n)
    (hxans : x.regs ans = a) (ha : Fits w (b + 2 * n))
    (hv : Fits w (a + x.mem b))
    (hl : i ≠ n → n / 2 ≤ i → Fits w (a + x.mem (b + 1))) :
    ExecWithin w queryBody x (queryNext x b n i a) 11 := by
  obtain ⟨hz, ho, ht, hp, hn', hi', hd⟩ := hx
  have hf : Fits w (n / 2) := ha.of_le (by omega)
  have hb : Fits w (b + 1) := ha.of_le (by omega)
  have hb' : Fits w (b + n / 2) := ha.of_le (by omega)
  have hb'' : Fits w (b + n / 2 + n / 2) := ha.of_le (by omega)
  have hi'' : Fits w (i - n / 2) := ha.of_le (by omega)
  by_cases he : i = n
  · ram_eval [queryBody, queryNext, hp, hn', hi', hxans, he, hv]
  · by_cases hc : i < n / 2
    · ram_eval [queryBody, queryNext, hp, hn', hi', hxans, he, ho, ht, hc, hf, hb]
    · have hs := hl he (by omega)
      ram_eval [queryBody, queryNext, hp, hn', hi', hxans, he, ho, ht, hc, hf, hb, hb',
        hb'', hi'', hs]

/-- One prefix-query iteration leaves RAM memory unchanged. -/
@[simp]
theorem queryNext_mem : (queryNext x b n i a).mem = x.mem := by
  simp only [queryNext]
  split
  · rfl
  · split <;> rfl

private theorem queryNext_entry (hx : Entry b n i δ x) (he : i ≠ n) :
    Entry (if i < n / 2 then b + 1 else b + n / 2 + n / 2) (n / 2)
      (if i < n / 2 then i else i - n / 2) δ (queryNext x b n i a) := by
  rcases hx with ⟨hz, ho, ht, hp, hn, hi, hd⟩
  by_cases hc : i < n / 2 <;>
    simp +decide [queryNext, he, hc, Entry.mk, hz, ho, ht, hi, hd]

private theorem queryLoop_full (hx : Entry b n n δ x) (hn : 0 < n)
    (hxans : x.regs ans = a) (ha : Fits w (b + 2 * n)) (hv : Fits w (a + x.mem b)) :
    ∃ y, ExecWithin w queryLoop x y 15 ∧ y.regs ans = a + x.mem b ∧ y.mem = x.mem := by
  have he := queryBody_exec hx le_rfl hn hxans ha hv (fun h => (h rfl).elim)
  refine ⟨_, he.loop_once (cond := .lt zero idx) ?_ ?_, ?_,
    queryNext_mem⟩
  · simp only [Cond.holds_lt, hx.zero_eq, hx.idx_eq, hn]
  · simp +decide [queryNext]
  · simp +decide [queryNext]

/-- A query adds precisely the first `i` leaf values to its initial accumulator, using at
most `13 (h + 1) + 2` instructions. The whole memory is unchanged. Bounds include the loop
tests and jumps, but entry-register installation and tree construction are separate. -/
theorem queryLoop_spec (t : Tree h) (hx : Entry b (2 ^ h) i δ x) (hi : i ≤ 2 ^ h)
    (hxans : x.regs ans = a) (hr : t.Rep b x.mem) (ha : Fits w (b + 2 * 2 ^ h))
    (hv : Fits w (a + t.total)) :
    ∃ y, ExecWithin w queryLoop x y (13 * (h + 1) + 2) ∧
      y.regs ans = a + t.prefixSum i ∧ y.mem = x.mem := by
  induction h generalizing b i x a with
  | zero =>
    by_cases hi0 : i = 0
    · refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), ?_, rfl⟩
      · simp only [Cond.holds_lt, hx.zero_eq, hx.idx_eq, hi0, lt_self_iff_false, not_false_eq_true]
      · simpa [hi0] using hxans
    · have hie : i = 1 := by simp only [pow_zero] at hi; omega
      subst i
      obtain ⟨y, he, hans, hm⟩ := queryLoop_full hx (by decide) hxans ha
        (by simpa [hr.root] using hv)
      exact ⟨y, he, by simpa [hr.root, ← Tree.prefixSum_length t] using hans, hm⟩
  | succ h ih =>
    by_cases hi0 : i = 0
    · refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), ?_, rfl⟩
      · simp only [Cond.holds_lt, hx.zero_eq, hx.idx_eq, hi0, lt_self_iff_false, not_false_eq_true]
      · simpa [hi0] using hxans
    by_cases hie : i = 2 ^ (h + 1)
    · subst i
      obtain ⟨y, he, hans, hm⟩ := queryLoop_full hx (Nat.two_pow_pos _) hxans ha
        (by simpa [hr.root] using hv)
      exact ⟨y, he.mono (by omega), by simpa [hr.root] using hans, hm⟩
    cases t with
    | node l r =>
      have hp := Nat.two_pow_pos h
      have hhalf : 2 ^ (h + 1) / 2 = 2 ^ h := by simp [pow_succ]
      have hsize : 2 ^ (h + 1) = 2 * 2 ^ h := by simp [pow_succ, Nat.mul_comm]
      have hs : Fits w (a + x.mem (b + 1)) := by
        rw [hr.2.1.root]
        exact hv.of_le (by simp only [Tree.total]; omega)
      let y := queryNext x b (2 ^ (h + 1)) i a
      have he := queryBody_exec hx hi (Nat.two_pow_pos _) hxans ha
        (by simpa [hr.root] using hv) (fun _ _ => hs)
      have hy := queryNext_entry (a := a) hx hie
      have hcond : (Cond.lt zero idx).Holds x := by
        simp only [Cond.holds_lt, hx.zero_eq, hx.idx_eq]
        omega
      by_cases hleft : i < 2 ^ h
      · have hy' : Entry (b + 1) (2 ^ h) i δ y := by simpa [hhalf, hleft] using hy
        have hyans : y.regs ans = a := by simp +decide [y, queryNext, hie, hhalf, hleft, hxans]
        obtain ⟨z, hz, hans, hm⟩ := ih l hy' hleft.le hyans
          (by simpa [y] using hr.2.1) (ha.of_le (by rw [hsize]; omega))
          (hv.of_le (by simp only [Tree.total]; omega))
        refine ⟨z, (he.loop_iter hcond hz).mono (by omega), ?_, hm.trans queryNext_mem⟩
        simpa [Tree.prefixSum, hleft] using hans
      · have hy' : Entry (b + 2 * 2 ^ h) (2 ^ h) (i - 2 ^ h) δ y := by
          simpa [hhalf, hleft, Nat.mul_two, Nat.two_mul, Nat.add_assoc] using hy
        have hyans : y.regs ans = a + l.total := by
          simp +decide [y, queryNext, hie, hhalf, hleft, hr.2.1.root]
        obtain ⟨z, hz, hans, hm⟩ := ih r hy' (by rw [hsize] at hi; omega) hyans
          (by simpa [y] using hr.2.2) (ha.of_le (by rw [hsize]; omega))
          (by simpa [Tree.total, Nat.add_assoc] using hv)
        refine ⟨z, (he.loop_iter hcond hz).mono (by omega), ?_, hm.trans queryNext_mem⟩
        simpa [Tree.prefixSum, hleft, Nat.add_assoc] using hans

end Cslib.Algorithms.WordRAM.PrefixSums

end
