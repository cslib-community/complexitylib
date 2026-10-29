/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.Chunks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Native enumeration of all query chunks

The controller reads the actual class-count table produced by `Classes.program` and calls the
existing native chunk writer for each class. Descriptors are concatenated without padding;
their query pointers refer to the original disjoint class arrays. No descriptor layout or
prefix table is supplied by the caller.

This composes the class and chunk loops in the pinned
[Theorem 17 construction](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Instances/Classes.lean).

## Main definitions

* `ChunkCatalogue.program`: fixed thirty-two-register descriptor controller.
* `ChunkCatalogue.before`: the mathematical number of descriptors preceding a class.

## Main results

* `ChunkCatalogue.exec`: charged enumeration of the actual class counts, exact descriptor
  readback and preservation outside the concatenated output.
* `ChunkCatalogue.before_index`: unique class/chunk coordinates for every occupied output slot,
  using Mathlib's existing finite sigma enumeration.
* `ChunkCatalogue.before_le`, `ChunkCatalogue.before_add_lt`: descriptor allocation bounds.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ChunkCatalogue

open Cslib.WordRAM

/-- Class-count table pointer. -/
abbrev counts : Fin 32 := 14
/-- Base of the class query blocks, each of capacity `2n²` words. -/
abbrev queries : Fin 32 := 15
/-- Matrix side length. -/
abbrev size : Fin 32 := 16
/-- Number of residue classes. -/
abbrev modulus : Fin 32 := 17
/-- Beginning of the contiguous output descriptor array. -/
abbrev dst : Fin 32 := 18
/-- Positive maximum pairs per chunk. -/
abbrev capacity : Fin 32 := 19
/-- Current class. -/
abbrev cursor : Fin 32 := 20
/-- Total number of descriptors written so far. -/
abbrev written : Fin 32 := 21
/-- First free descriptor address. -/
abbrev heap : Fin 32 := 22
/-- Constant one. -/
abbrev one : Fin 32 := 23
/-- Number of words per descriptor. -/
abbrev three : Fin 32 := 24
/-- Current count-table address. -/
abbrev addr : Fin 32 := 25
/-- Capacity of one class query block, in words. -/
abbrev stride : Fin 32 := 26
/-- Descriptor-length temporary. -/
abbrev temp : Fin 32 := 27

private abbrev bank : Fin 14 → Fin 32 := Fin.castLE (by decide)

private theorem bank_injective : Function.Injective bank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 32 => k.val) h)

/-- Query pointer passed to the chunk writer. -/
abbrev chunkQueries : Fin 32 := 0
/-- Output pointer passed to the chunk writer. -/
abbrev chunkDst : Fin 32 := 1
/-- Loaded class count passed to the chunk writer. -/
abbrev chunkTotal : Fin 32 := 2
/-- Chunk capacity passed to the chunk writer. -/
abbrev chunkCapacity : Fin 32 := 3
/-- Residue passed to the chunk writer. -/
abbrev chunkResidue : Fin 32 := 4
/-- Number of descriptors returned by the chunk writer. -/
abbrev chunkCount : Fin 32 := 6

/-- Call the existing native chunk writer in the lower register bank. -/
@[expose]
def chunks : Code .standard 32 := Chunks.program.rename (Fin.castLE (by decide))

/-- Read the current count and deliver its actual query pointer to the chunk writer. -/
@[expose]
def deliver : Code .standard 32 := ram[
  addr ← counts + cursor; chunkTotal ← *addr;
  chunkQueries ← cursor * stride; chunkQueries ← chunkQueries + queries;
  chunkDst ← heap; chunkCapacity ← capacity; chunkResidue ← cursor ]

/-- Advance the output heap by the number of descriptors actually written. -/
@[expose]
def advance : Code .standard 32 := ram[
  temp ← chunkCount * three; heap ← heap + temp;
  written ← written + chunkCount; cursor ← cursor + one ]

/-- One class, including empty classes. -/
@[expose]
def body : Code .standard 32 := .seq deliver (.seq chunks advance)

/-- Initialize the concatenation cursor and run every residue class. -/
@[expose]
def program : Code .standard 32 :=
  .seq (ram[ one ← #1; three ← #3; cursor ← #0; written ← #0; heap ← dst;
    stride ← size * size; stride ← stride + stride ])
    (.loop (.lt cursor modulus) body)

/-- The complete controller is fixed code and does not inspect physical width. -/
theorem program_fixed : program.size ≤ 80 ∧ ¬program.ReadsWidth := by decide

/-- Number of actual chunk descriptors for all classes strictly below `rho`. -/
@[expose]
def before (C : ℕ → ℕ) (cap rho : ℕ) : ℕ := ∑ r ∈ Finset.range rho, C r ⌈/⌉ cap

private theorem before_zero (C : ℕ → ℕ) (cap : ℕ) : before C cap 0 = 0 := by
  simp [before]

private theorem before_succ (C : ℕ → ℕ) (cap rho : ℕ) :
    before C cap (rho + 1) = before C cap rho + C rho ⌈/⌉ cap := by
  exact Finset.sum_range_succ _ _

/-- Every actual chunk lies strictly within the concatenated descriptor array. -/
theorem before_add_lt (C : ℕ → ℕ) (cap : ℕ) {rho p k : ℕ}
    (hrho : rho < p) (hk : k < C rho ⌈/⌉ cap) :
    before C cap rho + k < before C cap p := by
  have hsum : before C cap (rho + 1) ≤ before C cap p := by
    unfold before
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (by intro _ _ _; exact Nat.zero_le _)
  rw [before_succ] at hsum
  omega

/-- Every occupied descriptor slot names exactly one class and one chunk. This is the existing
`finSigmaFinEquiv`, expressed with the same prefix sum as the native concatenation loop. -/
theorem before_index (C : ℕ → ℕ) (cap p i : ℕ) (hi : i < before C cap p) :
    ∃! idx : (rho : Fin p) × Fin (C rho.val ⌈/⌉ cap),
      i = before C cap idx.1.val + idx.2.val := by
  have hsum : (∑ rho : Fin p, C rho.val ⌈/⌉ cap) = before C cap p := by
    rw [Fin.sum_univ_eq_sum_range (fun rho => C rho ⌈/⌉ cap)]
    rfl
  let j : Fin (∑ rho : Fin p, C rho.val ⌈/⌉ cap) := ⟨i, by rw [hsum]; exact hi⟩
  have hval (idx : (rho : Fin p) × Fin (C rho.val ⌈/⌉ cap)) :
      (finSigmaFinEquiv idx).val = before C cap idx.1.val + idx.2.val := by
    rw [finSigmaFinEquiv_apply]
    change (∑ r : Fin idx.1.val, C r.val ⌈/⌉ cap) + idx.2.val = _
    rw [Fin.sum_univ_eq_sum_range (fun rho => C rho ⌈/⌉ cap)]
    rfl
  let idx := finSigmaFinEquiv.symm j
  have heq : finSigmaFinEquiv idx = j := finSigmaFinEquiv.apply_symm_apply j
  refine ⟨idx, ?_, ?_⟩
  · exact (congrArg Fin.val heq).symm.trans (hval idx)
  · intro k hk
    apply finSigmaFinEquiv.injective
    apply Fin.ext
    rw [heq, hval]
    exact hk.symm

/-- At most `N` queries per class give at most `rho * N` occupied descriptors, since every
nonempty chunk contains at least one query. This bounds the actual allocation before matrix
preparation as well as the descriptor controller's own arithmetic. -/
theorem before_le {C : ℕ → ℕ} {cap p N : ℕ} (hcap : 0 < cap)
    (hC : ∀ r < p, C r ≤ N) {rho : ℕ} (hrho : rho ≤ p) : before C cap rho ≤ rho * N := by
  apply (Finset.sum_le_sum fun r hr => ?_).trans_eq
    (show (∑ _r ∈ Finset.range rho, N) = rho * N by simp)
  exact (Nat.ceilDiv_le_iff hcap).mpr
    ((hC r ((Finset.mem_range.mp hr).trans_le hrho)).trans
      (Nat.le_mul_of_pos_right N hcap))

private theorem chunks_preserves : ∀ i : Fin 32, 14 ≤ i.val → chunks.Preserves i := by decide

private theorem body_preserves : ∀ i : Fin 32,
    (14 ≤ i.val ∧ i ≠ cursor ∧ i ≠ written ∧ i ≠ heap ∧ i ≠ addr ∧ i ≠ temp) →
      body.Preserves i := by decide

private theorem exec_body {w : ℕ} (x : Data 32) (C : ℕ) (hread : x.mem
    (x.regs counts + x.regs cursor) = C)
    (ho : x.regs one = 1) (ht : x.regs three = 3) (hcap : 0 < x.regs capacity)
    (hheap : Fits w (x.regs heap + 3 * C + 3))
    (hquery : Fits w (x.regs queries + x.regs cursor * x.regs stride + 2 * C))
    (hcount : Fits w (x.regs counts + x.regs cursor))
    (hcursor : Fits w (x.regs cursor + 1))
    (hwritten : Fits w (x.regs written + C)) :
    ∃ y, ExecWithin w body x y (17 * C + 18) ∧
      y.regs cursor = x.regs cursor + 1 ∧
      y.regs written = x.regs written + C ⌈/⌉ x.regs capacity ∧
      y.regs heap = x.regs heap + (C ⌈/⌉ x.regs capacity) * 3 ∧
      (∀ k < C ⌈/⌉ x.regs capacity,
        y.mem (x.regs heap + 3 * k) = x.regs cursor ∧
        y.mem (x.regs heap + 3 * k + 1) =
          x.regs queries + x.regs cursor * x.regs stride + 2 * (k * x.regs capacity) ∧
        y.mem (x.regs heap + 3 * k + 2) = min (x.regs capacity) (C - k * x.regs capacity)) ∧
      (∀ a, ¬(x.regs heap ≤ a ∧
        a < x.regs heap + (C ⌈/⌉ x.regs capacity) * 3) → y.mem a = x.mem a) := by
  let a := x.set addr (x.regs counts + x.regs cursor) |>.set 2 C
    |>.set 0 (x.regs cursor * x.regs stride)
    |>.set 0 (x.regs cursor * x.regs stride + x.regs queries)
    |>.set 1 (x.regs heap) |>.set 3 (x.regs capacity) |>.set 4 (x.regs cursor)
  have hq0 : Fits w (x.regs cursor * x.regs stride) := hquery.of_le (by omega)
  have hq1 : Fits w (x.regs cursor * x.regs stride + x.regs queries) :=
    hquery.of_le (by omega)
  have hd : ExecWithin w deliver x a 7 := by
    ram_eval [deliver, a, hcount, hread, hq0, hq1, counts, cursor, addr, stride,
      queries, heap, capacity, chunkTotal, chunkQueries, chunkDst, chunkCapacity,
      chunkResidue, Fin.mk.injEq]
  have ha (i : Fin 32) (hi : 14 ≤ i.val) (hne : i ≠ addr) : a.regs i = x.regs i := by
    have hlow : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3 ∧ i ≠ 4 := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> subst i <;> simp at hi
    simp only [a, Data.set_regs, Function.update_of_ne hlow.1,
      Function.update_of_ne hlow.2.1, Function.update_of_ne hlow.2.2.1,
      Function.update_of_ne hlow.2.2.2.1, Function.update_of_ne hlow.2.2.2.2,
      Function.update_of_ne hne]
  have hCcap : C ⌈/⌉ x.regs capacity ≤ C :=
    (Nat.ceilDiv_le_iff hcap).mpr (Nat.le_mul_of_pos_right C hcap)
  obtain ⟨v, hv, hvc, -, hcells, hframe⟩ := Chunks.exec (a.comap bank)
    (by simpa +decide [a, bank, Chunks.capacity] using hcap)
    (by simpa +decide [a, bank, Chunks.dst, Chunks.total] using hheap)
    (by simpa +decide [a, bank, Chunks.queries, Chunks.total, Nat.add_comm] using hquery)
  let b := v.extend bank a
  have he : ExecWithin w chunks a b (17 * C + 7) := by
    simpa +decide [chunks, b, a, bank, Chunks.total] using hv.rename bank_injective
  have hb (i : Fin 32) (hi : 14 ≤ i.val) (hne : i ≠ addr) : b.regs i = x.regs i :=
    (he.regs_eq (chunks_preserves i hi)).trans (ha i hi hne)
  have hc : b.regs 6 = C ⌈/⌉ x.regs capacity := by
    change (v.extend bank a).regs (bank Chunks.count) = _
    change Function.extend bank v.regs a.regs (bank Chunks.count) = _
    rw [bank_injective.extend_apply]
    simpa +decide [a, bank, Chunks.total, Chunks.capacity] using hvc
  let z := b.set temp ((C ⌈/⌉ x.regs capacity) * 3)
    |>.set heap (x.regs heap + (C ⌈/⌉ x.regs capacity) * 3)
    |>.set written (x.regs written + C ⌈/⌉ x.regs capacity)
    |>.set cursor (x.regs cursor + 1)
  have hm : Fits w (C ⌈/⌉ x.regs capacity * 3) := hheap.of_le (by omega)
  have hh : Fits w (x.regs heap + C ⌈/⌉ x.regs capacity * 3) := hheap.of_le (by omega)
  have hw : Fits w (x.regs written + C ⌈/⌉ x.regs capacity) := hwritten.of_le (by omega)
  have hf : ExecWithin w advance b z 4 := by
    have bho := hb one (by decide) (by decide)
    have bht := hb three (by decide) (by decide)
    have bhh := hb heap (by decide) (by decide)
    have bhw := hb written (by decide) (by decide)
    have bhc := hb cursor (by decide) (by decide)
    ram_eval [advance, z, hc, bho, bht, bhh, bhw, bhc, ho, ht, hm, hh, hw, hcursor,
      temp, three, heap, written, cursor, one, chunkCount, Fin.mk.injEq]
  refine ⟨z, (hd.seq (he.seq hf)).mono (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [z, cursor]
  · simp +decide [z, written, cursor]
  · simp +decide [z, heap, written, cursor]
  · simpa +decide [z, b, a, bank, Chunks.dst, Chunks.queries, Chunks.residue,
      Chunks.capacity, Chunks.count, Chunks.total, Data.extend, hvc, Nat.add_comm] using hcells
  · simpa +decide [z, b, a, bank, Chunks.dst, Chunks.count, Chunks.total,
      Chunks.capacity, hvc, Data.extend, Nat.mul_comm] using hframe

/-- Read the actual count table and concatenate every class's nonempty chunks. The controller
receives no prefix sums. Both source blocks lie before `dst`; all other memory is preserved.
The charged bound excludes halt. -/
theorem exec {w : ℕ} (x : Data 32) (C : ℕ → ℕ)
    (hread : ∀ r < x.regs modulus, x.mem (x.regs counts + r) = C r)
    (hC : ∀ r < x.regs modulus, C r ≤ x.regs size * x.regs size)
    (hcap : 0 < x.regs capacity)
    (hcounts : x.regs counts + x.regs modulus ≤ x.regs dst)
    (hqueries : x.regs queries + 2 * x.regs modulus * (x.regs size * x.regs size) ≤
      x.regs dst)
    (hfit : Fits w (x.regs dst + 5 * x.regs modulus * (x.regs size * x.regs size) +
      x.regs counts + x.regs modulus + x.regs queries + 2 * (x.regs size * x.regs size) + 5)) :
    ∃ y, ExecWithin w program x y
        (x.regs modulus * (17 * (x.regs size * x.regs size) + 20) + 9) ∧
      y.regs written = before C (x.regs capacity) (x.regs modulus) ∧
      y.regs heap = x.regs dst + 3 * y.regs written ∧
      (∀ i : Fin 32, 14 ≤ i.val → i.val < 20 → y.regs i = x.regs i) ∧
      (∀ r < x.regs modulus, ∀ k < C r ⌈/⌉ x.regs capacity,
        y.mem (x.regs dst + 3 * (before C (x.regs capacity) r + k)) = r ∧
        y.mem (x.regs dst + 3 * (before C (x.regs capacity) r + k) + 1) =
          x.regs queries + 2 * r * (x.regs size * x.regs size) +
            2 * (k * x.regs capacity) ∧
        y.mem (x.regs dst + 3 * (before C (x.regs capacity) r + k) + 2) =
          min (x.regs capacity) (C r - k * x.regs capacity)) ∧
      (∀ a, ¬(x.regs dst ≤ a ∧ a < x.regs dst + 3 * y.regs written) →
        y.mem a = x.mem a) := by
  let N := x.regs size * x.regs size
  let p := x.regs modulus
  let Q := x.regs capacity
  let d := x.regs dst
  let b := x.regs queries
  let c := x.regs counts
  let P := before C Q
  change ∀ r < p, x.mem (c + r) = C r at hread
  change ∀ r < p, C r ≤ N at hC
  change 0 < Q at hcap
  change c + p ≤ d at hcounts
  change b + 2 * p * N ≤ d at hqueries
  change Fits w (d + 5 * p * N + c + p + b + 2 * N + 5) at hfit
  have hP (r : ℕ) (hr : r ≤ p) : P r ≤ r * N := before_le hcap hC hr
  let I (y : Data 32) : Prop :=
    (∀ i : Fin 32, 14 ≤ i.val → i.val < 20 → y.regs i = x.regs i) ∧
      y.regs one = 1 ∧ y.regs three = 3 ∧ y.regs stride = 2 * N ∧
      y.regs cursor ≤ p ∧ y.regs written = P (y.regs cursor) ∧
      y.regs heap = d + 3 * P (y.regs cursor) ∧
      (∀ r < y.regs cursor, ∀ k < C r ⌈/⌉ Q,
        y.mem (d + 3 * (P r + k)) = r ∧
        y.mem (d + 3 * (P r + k) + 1) = b + 2 * r * N + 2 * (k * Q) ∧
        y.mem (d + 3 * (P r + k) + 2) = min Q (C r - k * Q)) ∧
      (∀ a, ¬(d ≤ a ∧ a < d + 3 * P (y.regs cursor)) → y.mem a = x.mem a)
  have hbody (y : Data 32) (hy : I y) (hc : (Cond.lt cursor modulus).Holds y) :
      ∃ z, ExecWithin w body y z (17 * N + 18) ∧ I z ∧
        p - z.regs cursor < p - y.regs cursor := by
    obtain ⟨hyr, hyo, hyt, hys, hyi, hyw, hyh, hycells, hyframe⟩ := hy
    have hyr' (i : Fin 32) (hi : 14 ≤ i.val ∧ i.val < 20) := hyr i hi.1 hi.2
    have hyc : y.regs counts = c := hyr' counts (by decide)
    have hyb : y.regs queries = b := hyr' queries (by decide)
    have hyQ : y.regs capacity = Q := hyr' capacity (by decide)
    have hyp : y.regs modulus = p := hyr' modulus (by decide)
    have hlt : y.regs cursor < p := by simpa only [Cond.holds_lt, hyp] using hc
    have hnext : P (y.regs cursor + 1) = P (y.regs cursor) + C (y.regs cursor) ⌈/⌉ Q :=
      before_succ C Q (y.regs cursor)
    have hbefore := hP (y.regs cursor) hyi
    have hnew := hC (y.regs cursor) hlt
    have hstep : P (y.regs cursor) + C (y.regs cursor) ≤ p * N := by
      have := Nat.mul_le_mul_right N (Nat.succ_le_of_lt hlt)
      rw [Nat.succ_mul] at this
      omega
    have hreadY : y.mem (y.regs counts + y.regs cursor) = C (y.regs cursor) := by
      rw [hyc, hyframe _ (by omega)]
      exact hread _ hlt
    obtain ⟨z, he, hzi, hzw, hzh, hzcells, hzframe⟩ := exec_body y (C (y.regs cursor))
      hreadY hyo hyt (by simpa only [hyQ] using hcap)
      (hfit.of_le (by rw [hyh]; nlinarith only [hstep]))
      (hfit.of_le (by
        rw [hyb, hys]
        have := Nat.mul_le_mul_right (2 * N) (Nat.succ_le_of_lt hlt)
        rw [Nat.succ_mul] at this
        nlinarith only [this, hnew]))
      (hfit.of_le (by rw [hyc]; omega))
      (hfit.of_le (by omega))
      (hfit.of_le (by rw [hyw]; nlinarith only [hstep]))
    rw [hyQ] at hzw hzh hzcells hzframe
    have hpres (i : Fin 32)
        (hi : 14 ≤ i.val ∧ i ≠ cursor ∧ i ≠ written ∧ i ≠ heap ∧ i ≠ addr ∧ i ≠ temp) :
        z.regs i = y.regs i := he.regs_eq (body_preserves i hi)
    have hpr (i : Fin 32) (hi : 14 ≤ i.val) (hi' : i.val < 20) : z.regs i = x.regs i := by
      apply (hpres i ?_).trans (hyr i hi hi')
      refine ⟨hi, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> subst i <;>
        simp only [cursor, written, heap, addr, temp] at hi' <;> omega
    refine ⟨z, he.mono (by omega), ⟨hpr,
      (hpres one (by decide)).trans hyo, (hpres three (by decide)).trans hyt,
      (hpres stride (by decide)).trans hys, by omega, ?_, ?_, ?_, ?_⟩, by omega⟩
    · rw [hzw, hyw, hzi, hnext]
    · rw [hzh, hyh, hzi, hnext]
      omega
    · intro r hr k hk
      rw [hzi] at hr
      by_cases hr' : r = y.regs cursor
      · subst r
        have h := hzcells k hk
        rw [hyh, hyb, hys] at h
        simpa only [Nat.mul_add, Nat.add_assoc, Nat.mul_left_comm, Nat.mul_assoc] using h
      · have hrlt : r < y.regs cursor := by omega
        have hbnd : P r + C r ⌈/⌉ Q ≤ P (y.regs cursor) := by
          rw [← before_succ]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (by omega)) (by intros; exact Nat.zero_le _)
        have h0 : z.mem (d + 3 * (P r + k)) = y.mem (d + 3 * (P r + k)) :=
          hzframe _ (by rw [hyh]; omega)
        have h1 : z.mem (d + 3 * (P r + k) + 1) = y.mem (d + 3 * (P r + k) + 1) :=
          hzframe _ (by rw [hyh]; omega)
        have h2 : z.mem (d + 3 * (P r + k) + 2) = y.mem (d + 3 * (P r + k) + 2) :=
          hzframe _ (by rw [hyh]; omega)
        rw [h0, h1, h2]
        exact hycells r hrlt k hk
    · intro a ha
      rw [hzi, hnext] at ha
      rw [hzframe _ (by rw [hyh]; omega), hyframe _ (by omega)]
  let a := x.set one 1 |>.set three 3 |>.set cursor 0 |>.set written 0 |>.set heap d
    |>.set stride N |>.set stride (2 * N)
  have ha : I a := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi hi'
      have hne : i ≠ one ∧ i ≠ three ∧ i ≠ cursor ∧ i ≠ written ∧ i ≠ heap ∧
          i ≠ stride := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> subst i <;>
          simp only [one, three, cursor, written, heap, stride] at hi' <;> omega
      simp only [a, Data.set_regs, Function.update_of_ne hne.1,
        Function.update_of_ne hne.2.1, Function.update_of_ne hne.2.2.1,
        Function.update_of_ne hne.2.2.2.1, Function.update_of_ne hne.2.2.2.2.1,
        Function.update_of_ne hne.2.2.2.2.2]
    · simp +decide [a, one, three, cursor, written, heap, stride]
    · simp +decide [a, three, cursor, written, heap, stride]
    · simp +decide [a, stride]
    · simp +decide [a, cursor, written, heap, stride]
    · simp +decide [a, cursor, written, heap, stride, P, before_zero]
    · simp +decide [a, cursor, written, heap, stride, P, before_zero]
    · simp +decide [a, cursor, written, heap, stride]
    · intro k _
      rfl
  have hinit : ExecWithin (B := .standard) w
      (ram[ one ← #1; three ← #3; cursor ← #0; written ← #0; heap ← dst;
        stride ← size * size; stride ← stride + stride ]) x a 7 := by
    have h1 : Fits w 1 := hfit.of_le (by omega)
    have h3 : Fits w 3 := hfit.of_le (by omega)
    have hN : Fits w (x.regs size * x.regs size) := hfit.of_le (by dsimp [N]; omega)
    have h2N : Fits w (x.regs size * x.regs size + x.regs size * x.regs size) :=
      hfit.of_le (by dsimp [N]; omega)
    ram_eval [a, d, N, h1, h3, hN, h2N, one, three, cursor, written, heap, stride, size, dst,
      Fin.mk.injEq, two_mul]
  obtain ⟨y, he, hy, hend⟩ := ExecWithin.loop_invariant I
    (fun y => p - y.regs cursor) hbody ha
  obtain ⟨hyr, -, -, -, hyi, hyw, hyh, hycells, hyframe⟩ := hy
  have hyp : y.regs modulus = p := hyr modulus (by decide) (by decide)
  have hdone : y.regs cursor = p := by
    simp only [Cond.holds_lt, hyp] at hend
    omega
  rw [hdone] at hyw hyh hyframe
  refine ⟨y, ?_, hyw, by omega, hyr, ?_, ?_⟩
  · exact (hinit.seq he).mono (by
      simp +decide only [a, Data.set_regs, Function.update_apply, cursor, written,
        heap, stride, ↓reduceIte, Nat.sub_zero]
      dsimp [p, N]
      nlinarith only [])
  · simpa only [hdone] using hycells
  · simpa only [hyw] using hyframe

end Cslib.Algorithms.WordRAM.ExactTriangle.ChunkCatalogue
