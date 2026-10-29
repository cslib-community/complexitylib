/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
public import Complexity.Foundations.Data.Nat.CeilDiv

/-!
# Native query-chunk descriptors

For one computed query class, the program writes consecutive triples `(residue, pair pointer,
pair count)`. It computes the last chunk's shorter length and advances over the actual two-word
coordinate representation. The input query list is preserved.

This adapts the chunk loop in the pinned
[Theorem 17 chunk builder](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Instances/Chunks.lean).

## Main definitions

* `Chunks.program`: fixed fourteen-register descriptor writer.

## Main results

* `Chunks.exec`: exact chunk count, descriptor readback and a memory frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.Chunks

open Cslib.WordRAM

/-- Query pair array base. -/
abbrev queries : Fin 14 := 0
/-- Descriptor output base. -/
abbrev dst : Fin 14 := 1
/-- Actual number of query pairs. -/
abbrev total : Fin 14 := 2
/-- Positive maximum pairs per chunk. -/
abbrev capacity : Fin 14 := 3
/-- Class residue. -/
abbrev residue : Fin 14 := 4
/-- Consumed pair count. -/
abbrev pos : Fin 14 := 5
/-- Number of written chunks. -/
abbrev count : Fin 14 := 6
/-- Constant one. -/
abbrev one : Fin 14 := 7
/-- Number of words per descriptor. -/
abbrev three : Fin 14 := 8
/-- Current chunk length. -/
abbrev length : Fin 14 := 9
/-- Output address. -/
abbrev addr : Fin 14 := 10
/-- Current pair pointer. -/
abbrev ptr : Fin 14 := 11

/-- Compute a nonempty chunk, write its descriptor and advance both counters. -/
def body : Code .standard 14 := ram[
  length ← total - pos;
  if capacity < length then [ length ← capacity ] else [ length ← length ];
  addr ← count * three; addr ← addr + dst; *addr ← residue; addr ← addr + one;
  *addr ← ptr; addr ← addr + one; *addr ← length;
  ptr ← ptr + length; ptr ← ptr + length; pos ← pos + length; count ← count + one ]

/-- Initialize all loop state with charged instructions. -/
def program : Code .standard 14 :=
  .seq (ram[ one ← #1; three ← #3; pos ← #0; count ← #0; ptr ← queries ])
    (.loop (.lt pos total) body)

/-- Fixed code and no physical-width reads. -/
theorem program_fixed : program.size ≤ 48 ∧ ¬program.ReadsWidth := by decide

private theorem body_preserves : ∀ i : Fin 14,
    (i.val < 5 ∨ i = one ∨ i = three) → body.Preserves i := by decide

private theorem exec_body {w : ℕ} (x : Data 14) (ho : x.regs one = 1)
    (hthree : x.regs three = 3) (hp : x.regs pos < x.regs total)
    (hc : x.regs count ≤ x.regs pos)
    (hptr : x.regs ptr = x.regs queries + 2 * x.regs pos)
    (hfit : Fits w (x.regs dst + 3 * x.regs total + 3))
    (hquery : Fits w (x.regs queries + 2 * x.regs total)) :
    ∃ y, ExecWithin w body x y 15 ∧
      y.regs pos = x.regs pos + min (x.regs capacity) (x.regs total - x.regs pos) ∧
      y.regs count = x.regs count + 1 ∧
      y.regs ptr = x.regs queries +
        2 * (x.regs pos + min (x.regs capacity) (x.regs total - x.regs pos)) ∧
      y.mem = Function.update (Function.update (Function.update x.mem
        (x.regs dst + 3 * x.regs count) (x.regs residue))
          (x.regs dst + 3 * x.regs count + 1) (x.regs queries + 2 * x.regs pos))
            (x.regs dst + 3 * x.regs count + 2)
              (min (x.regs capacity) (x.regs total - x.regs pos)) := by
  let L := min (x.regs capacity) (x.regs total - x.regs pos)
  have hL : L ≤ x.regs total - x.regs pos := min_le_right ..
  have hsub : Fits w (x.regs total - x.regs pos) := hfit.of_le (by omega)
  have hlen : Fits w L := hsub.of_le hL
  have htriple : Fits w (x.regs count * 3) := hfit.of_le (by omega)
  have haddr : Fits w (x.regs count * 3 + x.regs dst) := hfit.of_le (by omega)
  have haddr1 : Fits w (x.regs count * 3 + x.regs dst + 1) := hfit.of_le (by omega)
  have haddr2 : Fits w (x.regs count * 3 + x.regs dst + 1 + 1) := hfit.of_le (by omega)
  have hptr1 : Fits w (x.regs ptr + L) := hquery.of_le (by omega)
  have hptr2 : Fits w (x.regs ptr + L + L) := hquery.of_le (by omega)
  have hpos : Fits w (x.regs pos + L) := hfit.of_le (by omega)
  have hcount : Fits w (x.regs count + 1) := hfit.of_le (by omega)
  let a := x.set length (x.regs total - x.regs pos) |>.set length L
    |>.set addr (x.regs count * 3) |>.set addr (x.regs count * 3 + x.regs dst)
    |>.write (x.regs count * 3 + x.regs dst) (x.regs residue)
    |>.set addr (x.regs count * 3 + x.regs dst + 1)
    |>.write (x.regs count * 3 + x.regs dst + 1) (x.regs ptr)
    |>.set addr (x.regs count * 3 + x.regs dst + 1 + 1)
    |>.write (x.regs count * 3 + x.regs dst + 1 + 1) L
    |>.set ptr (x.regs ptr + L) |>.set ptr (x.regs ptr + L + L)
    |>.set pos (x.regs pos + L) |>.set count (x.regs count + 1)
  refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h : x.regs capacity < x.regs total - x.regs pos
    · have he : L = x.regs capacity := min_eq_left h.le
      rw [he] at hlen hptr1 hptr2 hpos
      ram_eval [body, a, ho, hthree, h, he, hsub, hlen, htriple, haddr, haddr1, haddr2,
        hptr1, hptr2, hpos, hcount, length, total, pos, capacity, addr, count, three,
        dst, residue, one, ptr, Fin.mk.injEq]
    · have he : L = x.regs total - x.regs pos := min_eq_right (by omega)
      rw [he] at hlen hptr1 hptr2 hpos
      ram_eval [body, a, ho, hthree, h, he, hsub, hlen, htriple, haddr, haddr1, haddr2,
        hptr1, hptr2, hpos, hcount, length, total, pos, capacity, addr, count, three,
        dst, residue, one, ptr, Fin.mk.injEq]
  · change a.regs pos = x.regs pos + L
    simp +decide [a, pos, count]
  · simp [a]
  · change a.regs ptr = x.regs queries + 2 * (x.regs pos + L)
    simp +decide only [a, Data.set_regs, Data.write_regs, Function.update_apply,
      pos, count, ptr, ↓reduceIte]
    simp only [pos, ptr] at hptr
    omega
  · simp only [a, Data.set_mem, Data.write_mem, hptr]
    have haddr' : x.regs count * 3 + x.regs dst = x.regs dst + 3 * x.regs count := by omega
    rw [haddr']

/-- Write the exact nonempty chunks of one class. Descriptor `k` names the query slice beginning
at pair `k * capacity`, with its final length truncated to the class size. All other memory is
preserved, so placing the query array outside the descriptor block preserves its coordinates.
The final halt is excluded from the `17 total + 7` bound. -/
theorem exec {w : ℕ} (x : Data 14) (hcap : 0 < x.regs capacity)
    (hfit : Fits w (x.regs dst + 3 * x.regs total + 3))
    (hquery : Fits w (x.regs queries + 2 * x.regs total)) :
    ∃ y, ExecWithin w program x y (17 * x.regs total + 7) ∧
      y.regs count = x.regs total ⌈/⌉ x.regs capacity ∧
      (∀ i : Fin 14, i.val < 5 → y.regs i = x.regs i) ∧
      (∀ k < y.regs count,
        y.mem (x.regs dst + 3 * k) = x.regs residue ∧
        y.mem (x.regs dst + 3 * k + 1) = x.regs queries + 2 * (k * x.regs capacity) ∧
        y.mem (x.regs dst + 3 * k + 2) =
          min (x.regs capacity) (x.regs total - k * x.regs capacity)) ∧
      (∀ a, ¬(x.regs dst ≤ a ∧ a < x.regs dst + 3 * y.regs count) → y.mem a = x.mem a) := by
  let N := x.regs total
  let Q := x.regs capacity
  let d := x.regs dst
  let b := x.regs queries
  change 0 < Q at hcap
  let I (y : Data 14) : Prop :=
    (∀ i : Fin 14, i.val < 5 → y.regs i = x.regs i) ∧
      y.regs one = 1 ∧ y.regs three = 3 ∧ y.regs pos ≤ N ∧
      y.regs pos = min N (y.regs count * Q) ∧ y.regs count ≤ y.regs pos ∧
      (y.regs count = 0 ∨ (y.regs count - 1) * Q < N) ∧
      y.regs ptr = b + 2 * y.regs pos ∧
      (∀ k < y.regs count,
        y.mem (d + 3 * k) = x.regs residue ∧
        y.mem (d + 3 * k + 1) = b + 2 * (k * Q) ∧
        y.mem (d + 3 * k + 2) = min Q (N - k * Q)) ∧
      (∀ a, ¬(d ≤ a ∧ a < d + 3 * y.regs count) → y.mem a = x.mem a)
  have hbody (y : Data 14) (hy : I y) (hc : (Cond.lt pos total).Holds y) :
      ∃ z, ExecWithin w body y z 15 ∧ I z ∧ N - z.regs pos < N - y.regs pos := by
    obtain ⟨hyr, hyo, hyt, hyp, hymin, hyc, hylast, hyptr, hycells, hyframe⟩ := hy
    have hyN : y.regs total = N := hyr total (by decide)
    have hyQ : y.regs capacity = Q := hyr capacity (by decide)
    have hyd : y.regs dst = d := hyr dst (by decide)
    have hyb : y.regs queries = b := hyr queries (by decide)
    have hyrho : y.regs residue = x.regs residue := hyr residue (by decide)
    have hlt : y.regs pos < N := by simpa only [Cond.holds_lt, hyN] using hc
    have hprod : y.regs pos = y.regs count * Q := by
      by_cases h : y.regs count * Q ≤ N
      · simpa only [min_eq_right h] using hymin
      · rw [min_eq_left (by omega)] at hymin
        omega
    have hQ : 0 < Q := hcap
    let L := min Q (N - y.regs pos)
    have hL : 0 < L := lt_min hQ (by omega)
    have hLle : L ≤ N - y.regs pos := min_le_right ..
    obtain ⟨z, he, hzp, hzc, hzptr, hzmem⟩ := exec_body y hyo hyt
      (by simpa only [hyN] using hlt) hyc (by simpa only [hyb] using hyptr)
      (by simpa only [hyd, hyN] using hfit) (by simpa only [hyb, hyN] using hquery)
    simp only [hyN, hyQ, hyb, hyd, hyrho] at hzp hzptr hzmem
    have hzmin : z.regs pos = min N (z.regs count * Q) := by
      rw [hzp, hzc, Nat.add_mul, Nat.one_mul, ← hprod]
      omega
    have hpres (i : Fin 14) (hi : i.val < 5 ∨ i = one ∨ i = three) :
        z.regs i = y.regs i := he.regs_eq (body_preserves i hi)
    refine ⟨z, he, ⟨fun i hi => (hpres i (Or.inl hi)).trans (hyr i hi),
      (hpres one (by simp)).trans hyo, (hpres three (by simp)).trans hyt,
      by omega, hzmin, by omega, Or.inr ?_, by simpa only [hzp] using hzptr,
      ?_, ?_⟩, by omega⟩
    · rw [hzc, Nat.add_sub_cancel, ← hprod]
      exact hlt
    · intro k hk
      rw [hzc] at hk
      by_cases h : k = y.regs count
      · rw [h, hzmem]
        refine ⟨?_, ?_, ?_⟩
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]
        · rw [Function.update_of_ne (by omega), Function.update_self, hprod]
        · rw [Function.update_self, hprod]
      · have hk' : k < y.regs count := by omega
        obtain ⟨h0, h1, h2⟩ := hycells k hk'
        rw [hzmem]
        refine ⟨?_, ?_, ?_⟩ <;>
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
        · exact h0
        · exact h1
        · exact h2
    · intro a ha
      rw [hzmem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact hyframe a (by omega)
  let x₀ := x.set one 1 |>.set three 3 |>.set pos 0 |>.set count 0 |>.set ptr b
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hne : i ≠ one ∧ i ≠ three ∧ i ≠ pos ∧ i ≠ count ∧ i ≠ ptr := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> subst i <;>
          simp only [one, three, pos, count, ptr] at hi <;> omega
      simp only [x₀, Data.set_regs, Function.update_of_ne hne.1,
        Function.update_of_ne hne.2.1, Function.update_of_ne hne.2.2.1,
        Function.update_of_ne hne.2.2.2.1, Function.update_of_ne hne.2.2.2.2]
    · simp +decide [x₀, one, three, pos, count, ptr]
    · simp +decide [x₀, three, pos, count, ptr]
    · simp +decide [x₀, pos, count, ptr]
    · simp +decide [x₀, pos, count, ptr]
    · simp +decide [x₀, pos, count, ptr]
    · exact Or.inl (by simp +decide [x₀, count, ptr])
    · simp +decide [x₀, ptr, pos, count]
    · simp +decide [x₀, ptr, count]
    · intro a _
      rfl
  have hinit : ExecWithin (B := .standard) w
      (ram[ one ← #1; three ← #3; pos ← #0; count ← #0; ptr ← queries ]) x x₀ 5 := by
    have h1 : Fits w 1 := hfit.of_le (by omega)
    have h3 : Fits w 3 := hfit.of_le (by omega)
    ram_eval [x₀, b, h1, h3, one, three, pos, count, ptr, queries, Fin.mk.injEq]
  obtain ⟨y, hy, hI, hc⟩ := ExecWithin.loop_invariant I
    (fun y => N - y.regs pos) hbody hx₀
  obtain ⟨hyr, -, -, hyp, hymin, hyc, hylast, -, hycells, hyframe⟩ := hI
  have hyN : y.regs total = N := hyr total (by decide)
  have hend : y.regs pos = N := by
    simp only [Cond.holds_lt, hyN] at hc
    omega
  have hcover : N ≤ y.regs count * Q := by omega
  have hcount : y.regs count = N ⌈/⌉ Q := by
    apply Nat.le_antisymm
    · rcases hylast with h | h
      · omega
      · have hcov := Nat.le_ceilDiv_mul hcap (a := N)
        by_contra hgt
        have hm : (N ⌈/⌉ Q) * Q ≤ (y.regs count - 1) * Q :=
          Nat.mul_le_mul_right Q (by omega)
        omega
    · exact (Nat.ceilDiv_le_iff hcap).mpr hcover
  refine ⟨y, ?_, hcount, hyr, hycells, hyframe⟩
  convert hinit.seq hy using 1
  · rfl
  · simp +decide only [x₀, Data.set_regs, Function.update_apply, pos, count, ptr,
      ↓reduceIte]
    dsimp [N]
    omega

end Cslib.Algorithms.WordRAM.ExactTriangle.Chunks
