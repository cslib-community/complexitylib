/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Model
public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Program
public import Complexity.Computability.WordRAM.Compile
import Mathlib.Tactic.Linarith

/-!
# Van Emde Boas initializer program and Phase 1–2 lookup-table construction

This module defines the fixed 32-register structured initializer program `initProgram` for
recursive van Emde Boas trees and certifies its first two phases:
1. Computing `(universeSize d, span d)` by `d` iterations of the layout recurrences (`sizeLoop`).
2. Populating the `(splitSize k, childSpan k)` lookup table of `2 * (d + 1)` words at
   `[base + span d, base + span d + 2 * (d + 1))` (`tableLoop`).

## Main definitions

* `initProgram`: the fixed 32-register structured initializer program.
* `TableInv`: the lookup-table invariant for `(splitSize j, childSpan j)`.

## Main results

* `sizeLoop_spec`: Phase 1 recurrence loop specification.
* `tableLoop_spec`: Phase 2 lookup-table loop specification.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.VanEmdeBoas

open Cslib.WordRAM
open Cslib.Algorithms.Lean.VanEmdeBoas

/-! ## Structured initializer program -/

/-- Constant and recurrence-seed setup for Phase 1. -/
def initSetup : Code .standard 32 := ram[
  zero ← #0; one ← #1; two ← #2; three ← #3; four ← #4; five ← #5;
  q ← two; t ← five; high ← zero ]

/-- One step of the `(universeSize, span)` recurrence loop. -/
def sizeBody : Code .standard 32 := ram[
  tmp ← q + one; tmp ← tmp * t; tmp ← tmp + five;
  q ← q * q; t ← tmp; high ← high + one ]

/-- Phase 1 loop computing `(universeSize d, span d)`. -/
def sizeLoop : Code .standard 32 := ram[
  while high < depth do [ ⟪sizeBody⟫ ] ]

/-- Setup for the Phase 2 `(splitSize, childSpan)` table construction. -/
def tableSetup : Code .standard 32 := ram[
  payload ← root + t; tableBase ← payload; stackBase ← payload; sp ← tableBase;
  *sp ← zero; sp ← sp + one; *sp ← zero; sp ← sp + one;
  q ← two; t ← five; high ← zero ]

/-- One step of the Phase 2 table-population loop. -/
def tableBody : Code .standard 32 := ram[
  *sp ← q; sp ← sp + one; *sp ← t; sp ← sp + one;
  tmp ← q + one; tmp ← tmp * t; tmp ← tmp + five;
  q ← q * q; t ← tmp; high ← high + one ]

/-- Phase 2 loop writing `(splitSize (k + 1), childSpan (k + 1))` for `k < d`. -/
def tableLoop : Code .standard 32 := ram[
  while high < depth do [ ⟪tableBody⟫ ] ]

/-- Setup for the Phase 3 depth-first header initialization. -/
def dfsSetup : Code .standard 32 := ram[
  low ← sp; p ← root; x ← depth; kind ← zero; runFlag ← one ]

/-- Downward step of the DFS initializer: write the current node's empty header and either
turn around at a leaf or initialize the cluster counter and descend into the summary. -/
def dfsEnterBody : Code .standard 32 := ram[
  *p ← zero;
  tmp ← x * two; addr ← tableBase + tmp; q ← *addr;
  addr ← addr + one; t ← *addr;
  child ← p + three; *child ← q; child ← child + one; *child ← t;
  p ← p + five;
  if x = zero then [ kind ← one ] else [
    addr ← low + x; *addr ← q; x ← x - one
  ] ]

/-- Upward/sibling step of the DFS initializer: ascend to the parent level and either finish
when above `depth`, continue ascending when all clusters are done, or decrement the remaining
cluster counter and descend into the next cluster. -/
def dfsExitBody : Code .standard 32 := ram[
  x ← x + one;
  if depth < x then [ runFlag ← zero ] else [
    addr ← low + x; present ← *addr;
    if present = zero then [ kind ← kind ] else [
      present ← present - one; *addr ← present; x ← x - one; kind ← zero
    ]
  ] ]

/-- Full body of the Phase 3 DFS loop. -/
def dfsBody : Code .standard 32 := ram[
  if kind = zero then [ ⟪dfsEnterBody⟫ ] else [ ⟪dfsExitBody⟫ ] ]

/-- Phase 3 DFS traversal loop. -/
def dfsLoop : Code .standard 32 := ram[
  while zero < runFlag do [ ⟪dfsBody⟫ ] ]

/-- Fixed 32-register structured program initializing an empty van Emde Boas tree of depth
`depth` at `root` and placing `stackBase` at `root + span depth`. -/
def initProgram : Code .standard 32 := ram[
  ⟪initSetup⟫;
  ⟪sizeLoop⟫;
  ⟪tableSetup⟫;
  ⟪tableLoop⟫;
  ⟪dfsSetup⟫;
  ⟪dfsLoop⟫;
  out ← payload ]

theorem initProgram_not_readsWidth : ¬initProgram.ReadsWidth := by decide

theorem compiled_initProgram_not_readsWidth : ¬(initProgram.program out).ReadsWidth :=
  Code.not_readsWidth_program initProgram_not_readsWidth out

/-! ## Phase 1: computing `(universeSize d, span d)` -/

/-- State after `initSetup`. -/
def initSetupData (s : Data 32) : Data 32 :=
  ((((((((s.set zero 0).set one 1).set two 2).set three 3).set four 4).set five 5).set q 2).set
    t 5).set high 0

theorem initSetup_exec {w : ℕ} {s : Data 32} (hw : Fits w 5) :
    Exec w initSetup s (initSetupData s) 9 := by
  have h0 := hw.of_le (by decide : 0 ≤ 5)
  have h1 := hw.of_le (by decide : 1 ≤ 5)
  have h2 := hw.of_le (by decide : 2 ≤ 5)
  have h3 := hw.of_le (by decide : 3 ≤ 5)
  have h4 := hw.of_le (by decide : 4 ≤ 5)
  ram_eval [initSetup, initSetupData, h0, h1, h2, h3, h4, hw]

/-- State after one iteration of `sizeBody` at depth `k`. -/
private def sizeBodyData (s : Data 32) (k : ℕ) : Data 32 :=
  (((((s.set tmp (universeSize k + 1)).set tmp ((universeSize k + 1) * span k)).set
    tmp ((universeSize k + 1) * span k + 5)).set q (universeSize k * universeSize k)).set
    t ((universeSize k + 1) * span k + 5)).set high (k + 1)

private theorem sizeBody_exec {w d k : ℕ} {s : Data 32} (hk : k < d) (hspan : Fits w (span d))
    (hd : Fits w d) (h1 : s.regs one = 1) (h5 : s.regs five = 5)
    (hq : s.regs q = universeSize k) (ht : s.regs t = span k) (hhigh : s.regs high = k) :
    ExecWithin w sizeBody s (sizeBodyData s k) 6 := by
  have hle : span (k + 1) ≤ span d := span_mono (by omega)
  have hu_le : universeSize (k + 1) ≤ span (k + 1) := universeSize_le_span (k + 1)
  have huk_le : universeSize k + 1 ≤ universeSize (k + 1) := by
    have := two_le_universeSize k; rw [universeSize_succ]; nlinarith
  have h_prod_le : (universeSize k + 1) * span k + 5 = span (k + 1) := by
    rw [span_succ]; omega
  have hf1 : Fits w (universeSize k + 1) := hspan.of_le (by omega)
  have hf2 : Fits w ((universeSize k + 1) * span k) := hspan.of_le (by omega)
  have hf3 : Fits w ((universeSize k + 1) * span k + 5) := hspan.of_le (by omega)
  have hf4 : Fits w (universeSize k * universeSize k) :=
    hspan.of_le (by rw [← universeSize_succ]; omega)
  have hf5 : Fits w (k + 1) := hd.of_le (by omega)
  ram_eval [sizeBody, sizeBodyData, h1, h5, hq, ht, hhigh, hf1, hf2, hf3, hf4, hf5]

/-- `sizeLoop` advances `(q, t, high)` from `(universeSize k, span k, k)` to
`(universeSize d, span d, d)` in `8 * (d - k) + 2` instructions without modifying memory. -/
theorem sizeLoop_spec {w d : ℕ} (rem : ℕ) {k : ℕ} {s : Data 32} (hk : k + rem = d)
    (hspan : Fits w (span d)) (hd : Fits w d)
    (h0 : s.regs zero = 0) (h1 : s.regs one = 1) (h2 : s.regs two = 2)
    (h3 : s.regs three = 3) (h4 : s.regs four = 4) (h5 : s.regs five = 5)
    (hdepth : s.regs depth = d) (hq : s.regs q = universeSize k) (ht : s.regs t = span k)
    (hhigh : s.regs high = k) :
    ∃ z, ExecWithin w sizeLoop s z (8 * rem + 2) ∧
      z.regs zero = 0 ∧ z.regs one = 1 ∧ z.regs two = 2 ∧
      z.regs three = 3 ∧ z.regs four = 4 ∧ z.regs five = 5 ∧
      z.regs root = s.regs root ∧ z.regs depth = d ∧
      z.regs q = universeSize d ∧ z.regs t = span d ∧ z.mem = s.mem := by
  induction rem generalizing k s with
  | zero =>
    have hkd : k = d := by omega
    subst hkd
    have hc : ¬(Cond.lt high depth).Holds s := by
      simp +decide [Cond.holds_lt, hhigh, hdepth]
    exact ⟨s, ExecWithin.loop_exit hc, h0, h1, h2, h3, h4, h5, rfl, hdepth, hq, ht, rfl⟩
  | succ rem ih =>
    have hk_lt : k < d := by omega
    have hc : (Cond.lt high depth).Holds s := by
      simp +decide [Cond.holds_lt, hhigh, hdepth, hk_lt]
    have hbody := sizeBody_exec hk_lt hspan hd h1 h5 hq ht hhigh
    let s₁ := sizeBodyData s k
    have hs₁_t : s₁.regs t = span (k + 1) := by
      change (universeSize k + 1) * span k + 5 = span (k + 1)
      rw [span_succ]
      omega
    obtain ⟨z, hz, hz0, hz1, hz2, hz3, hz4, hz5, hzr, hzd, hzq, hzt, hzm⟩ :=
      ih (k := k + 1) (s := s₁) (by omega)
        (by simpa +decide [s₁, sizeBodyData] using h0)
        (by simpa +decide [s₁, sizeBodyData] using h1)
        (by simpa +decide [s₁, sizeBodyData] using h2)
        (by simpa +decide [s₁, sizeBodyData] using h3)
        (by simpa +decide [s₁, sizeBodyData] using h4)
        (by simpa +decide [s₁, sizeBodyData] using h5)
        (by simpa +decide [s₁, sizeBodyData] using hdepth)
        (by simp +decide [s₁, sizeBodyData, universeSize_succ])
        hs₁_t
        (by simp +decide [s₁, sizeBodyData])
    refine ⟨z, (ExecWithin.loop_iter hc hbody hz).mono (by omega),
      hz0, hz1, hz2, hz3, hz4, hz5, ?_, hzd, hzq, hzt, ?_⟩
    · simpa +decide [s₁, sizeBodyData] using hzr
    · simpa +decide [s₁, sizeBodyData] using hzm

/-! ## Phase 2: populating the `(splitSize, childSpan)` table -/

/-- State after `tableSetup`. -/
def tableSetupData (s : Data 32) (base d : ℕ) : Data 32 :=
  let tbl := base + span d
  ((((((((((s.set payload tbl).set tableBase tbl).set stackBase tbl).set sp tbl).write
    tbl 0).set sp (tbl + 1)).write (tbl + 1) 0).set sp (tbl + 1 + 1)).set q 2).set t 5).set high 0

theorem tableSetup_exec {w base d : ℕ} {s : Data 32} (ha : Fits w (base + span d + 4 * (d + 1)))
    (h0 : s.regs zero = 0) (h1 : s.regs one = 1) (h2 : s.regs two = 2) (h5 : s.regs five = 5)
    (hroot : s.regs root = base) (ht : s.regs t = span d) :
    Exec w tableSetup s (tableSetupData s base d) 11 := by
  have hf_tbl : Fits w (base + span d) := ha.of_le (by omega)
  have hf_tbl1 : Fits w (base + span d + 1) := ha.of_le (by omega)
  have hf_tbl2 : Fits w (base + span d + 1 + 1) := ha.of_le (by omega)
  ram_eval [tableSetup, tableSetupData, h0, h1, h2, h5, hroot, ht, hf_tbl, hf_tbl1, hf_tbl2]

/-- State after one iteration of `tableBody` at depth `k` and pointer `sp₀`. -/
private def tableBodyData (s : Data 32) (sp₀ k : ℕ) : Data 32 :=
  (((((((((s.write sp₀ (universeSize k)).set sp (sp₀ + 1)).write (sp₀ + 1) (span k)).set
    sp (sp₀ + 1 + 1)).set tmp (universeSize k + 1)).set tmp ((universeSize k + 1) * span k)).set
    tmp ((universeSize k + 1) * span k + 5)).set q (universeSize k * universeSize k)).set
    t ((universeSize k + 1) * span k + 5)).set high (k + 1)

private theorem tableBody_exec {w base d k : ℕ} {s : Data 32} (hk : k < d)
    (ha : Fits w (base + span d + 4 * (d + 1)))
    (h1 : s.regs one = 1) (h5 : s.regs five = 5)
    (hsp : s.regs sp = base + span d + 2 * (k + 1))
    (hq : s.regs q = universeSize k) (ht : s.regs t = span k) (hhigh : s.regs high = k) :
    ExecWithin w tableBody s (tableBodyData s (base + span d + 2 * (k + 1)) k) 10 := by
  have hle : span (k + 1) ≤ span d := span_mono (by omega)
  have hu_le : universeSize (k + 1) ≤ span (k + 1) := universeSize_le_span (k + 1)
  have huk_le : universeSize k + 1 ≤ universeSize (k + 1) := by
    have := two_le_universeSize k; rw [universeSize_succ]; nlinarith
  have h_prod_le : (universeSize k + 1) * span k + 5 = span (k + 1) := by
    rw [span_succ]; omega
  have hf_sp1 : Fits w (base + span d + 2 * (k + 1) + 1) := ha.of_le (by omega)
  have hf_sp2 : Fits w (base + span d + 2 * (k + 1) + 1 + 1) := ha.of_le (by omega)
  have hf1 : Fits w (universeSize k + 1) := ha.of_le (by omega)
  have hf2 : Fits w ((universeSize k + 1) * span k) := ha.of_le (by omega)
  have hf3 : Fits w ((universeSize k + 1) * span k + 5) := ha.of_le (by omega)
  have hf4 : Fits w (universeSize k * universeSize k) :=
    ha.of_le (by rw [← universeSize_succ]; omega)
  have hf5 : Fits w (k + 1) := ha.of_le (by omega)
  ram_eval [tableBody, tableBodyData, h1, h5, hsp, hq, ht, hhigh,
    hf_sp1, hf_sp2, hf1, hf2, hf3, hf4, hf5]

/-- Lookup-table invariant up to depth `m`: for all `j ≤ m`, `mem (tbl + 2 * j) = splitSize j`
and `mem (tbl + 2 * j + 1) = childSpan j`. -/
def TableInv (tbl m : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ j ≤ m, mem (tbl + 2 * j) = splitSize j ∧ mem (tbl + 2 * j + 1) = childSpan j

/-- `tableLoop` populates the lookup table from depth `k` up to `d` in `12 * (d - k) + 2`
instructions, advancing `sp` to `base + span d + 2 * (d + 1)` and preserving all memory outside
`[base + span d + 2 * (k + 1), base + span d + 2 * (d + 1))`. -/
theorem tableLoop_spec {w base d : ℕ} (rem : ℕ) {k : ℕ} {s : Data 32} (hk : k + rem = d)
    (ha : Fits w (base + span d + 4 * (d + 1)))
    (h0 : s.regs zero = 0) (h1 : s.regs one = 1) (h2 : s.regs two = 2)
    (h3 : s.regs three = 3) (h4 : s.regs four = 4) (h5 : s.regs five = 5)
    (hroot : s.regs root = base) (hdepth : s.regs depth = d)
    (hpay : s.regs payload = base + span d)
    (htbl : s.regs tableBase = base + span d)
    (hstk : s.regs stackBase = base + span d)
    (hsp : s.regs sp = base + span d + 2 * (k + 1))
    (hq : s.regs q = universeSize k) (ht : s.regs t = span k) (hhigh : s.regs high = k)
    (hinv : TableInv (base + span d) k s.mem) :
    ∃ z, ExecWithin w tableLoop s z (12 * rem + 2) ∧
      z.regs zero = 0 ∧ z.regs one = 1 ∧ z.regs two = 2 ∧
      z.regs three = 3 ∧ z.regs four = 4 ∧ z.regs five = 5 ∧
      z.regs root = base ∧ z.regs depth = d ∧
      z.regs payload = base + span d ∧
      z.regs tableBase = base + span d ∧
      z.regs stackBase = base + span d ∧
      z.regs sp = base + span d + 2 * (d + 1) ∧
      TableInv (base + span d) d z.mem ∧
      (∀ a, a < base + span d + 2 * (k + 1) ∨ base + span d + 2 * (d + 1) ≤ a →
        z.mem a = s.mem a) := by
  induction rem generalizing k s with
  | zero =>
    have hkd : k = d := by omega
    subst hkd
    have hc : ¬(Cond.lt high depth).Holds s := by
      simp +decide [Cond.holds_lt, hhigh, hdepth]
    refine ⟨s, ExecWithin.loop_exit hc, h0, h1, h2, h3, h4, h5, hroot, hdepth,
      hpay, htbl, hstk, hsp, hinv, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < d := by omega
    have hc : (Cond.lt high depth).Holds s := by
      simp +decide [Cond.holds_lt, hhigh, hdepth, hk_lt]
    have hbody := tableBody_exec hk_lt ha h1 h5 hsp hq ht hhigh
    let sp₀ := base + span d + 2 * (k + 1)
    let s₁ := tableBodyData s sp₀ k
    have hs₁_sp : s₁.regs sp = base + span d + 2 * (k + 1 + 1) := by
      change sp₀ + 1 + 1 = base + span d + 2 * (k + 1 + 1)
      dsimp only [sp₀]
      omega
    have hs₁_t : s₁.regs t = span (k + 1) := by
      change (universeSize k + 1) * span k + 5 = span (k + 1)
      rw [span_succ]
      omega
    have hs₁_mem_away : ∀ a, a ≠ sp₀ → a ≠ sp₀ + 1 → s₁.mem a = s.mem a := by
      intro a ha0 ha1
      simp only [s₁, tableBodyData, Data.set_mem, Data.write_mem]
      rw [Function.update_of_ne ha1, Function.update_of_ne ha0]
    have hs₁_inv : TableInv (base + span d) (k + 1) s₁.mem := by
      intro j hj
      by_cases hjk : j ≤ k
      · rw [hs₁_mem_away _ (by dsimp only [sp₀]; omega) (by dsimp only [sp₀]; omega),
          hs₁_mem_away _ (by dsimp only [sp₀]; omega) (by dsimp only [sp₀]; omega)]
        exact hinv j hjk
      · have hj_eq : j = k + 1 := by omega
        subst hj_eq
        simp only [s₁, sp₀, tableBodyData, Data.set_mem, Data.write_mem, splitSize, childSpan]
        constructor
        · rw [Function.update_of_ne (by omega), Function.update_self]
        · rw [Function.update_self]
    obtain ⟨z, hz, hz0, hz1, hz2, hz3, hz4, hz5, hzr, hzd, hzp, hztbl, hzstk, hzsp, hzinv,
        hzframe⟩ :=
      ih (k := k + 1) (s := s₁) (by omega)
        (by simpa +decide [s₁, tableBodyData] using h0)
        (by simpa +decide [s₁, tableBodyData] using h1)
        (by simpa +decide [s₁, tableBodyData] using h2)
        (by simpa +decide [s₁, tableBodyData] using h3)
        (by simpa +decide [s₁, tableBodyData] using h4)
        (by simpa +decide [s₁, tableBodyData] using h5)
        (by simpa +decide [s₁, tableBodyData] using hroot)
        (by simpa +decide [s₁, tableBodyData] using hdepth)
        (by simpa +decide [s₁, tableBodyData] using hpay)
        (by simpa +decide [s₁, tableBodyData] using htbl)
        (by simpa +decide [s₁, tableBodyData] using hstk)
        hs₁_sp
        (by simp +decide [s₁, tableBodyData, universeSize_succ])
        hs₁_t
        (by simp +decide [s₁, tableBodyData])
        hs₁_inv
    refine ⟨z, (ExecWithin.loop_iter hc hbody hz).mono (by omega),
      hz0, hz1, hz2, hz3, hz4, hz5, hzr, hzd, hzp, hztbl, hzstk, hzsp, hzinv, ?_⟩
    intro a ha_out
    have ha_out₁ : a < base + span d + 2 * (k + 1 + 1) ∨ base + span d + 2 * (d + 1) ≤ a := by
      omega
    rw [hzframe a ha_out₁,
      hs₁_mem_away a (by dsimp only [sp₀]; omega) (by dsimp only [sp₀]; omega)]

end Cslib.Algorithms.WordRAM.VanEmdeBoas
