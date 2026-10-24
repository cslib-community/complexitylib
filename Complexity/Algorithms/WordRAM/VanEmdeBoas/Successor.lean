/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.VanEmdeBoas.Successor
public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Model
public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Program

/-!
# Native van Emde Boas strict-successor certification

This module certifies the native strict-successor operation (`successorDescent` followed by
`successorUnwind`) in `Complexity.Algorithms.WordRAM.VanEmdeBoas.Program`.

During descent, each recursive cluster or summary call pushes a four-word continuation frame
(`kind`, `payload`, `q`, `t`) into the scratch stack `[stackBase₀, stackBase₀ + 4 * d)`.
Because `Tree.successor` checks the cached maximum before recursing, every recursive descent is
guaranteed to find a key (`found = 1`), and `successorUnwind` pops the pushed frames to
reconstruct the universe key in `out` while restoring `sp = stackBase₀`.

## Main definitions

* `SuccessorEntry`: register invariant at entry to `successorDescent`.
* `successorDescentNext`: mathematical description of one `successorDescentBody` iteration.
* `UnwindState`: register and memory invariant during `successorUnwind`.
* `successorUnwindNext`: mathematical description of one `successorUnwindBody` iteration.

## Main results

* `successorDescentBody_exec`: one descent iteration executes in at most 42 instructions.
* `successorUnwindBody_cluster_exec`, `successorUnwindBody_summary_exec`: one unwind iteration
  executes in at most 19 instructions.
* `successor_loop_spec`: `successorDescent; successorUnwind` executes in at most
  `65 * (d + 1) + 4` instructions, computes `tree.successor query`, restores `sp = stackBase₀`,
  preserves `Rep tree base z.mem`, and leaves all memory outside `[stackBase₀, stackBase₀ + 4 * d)`
  unchanged.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.VanEmdeBoas

open Cslib.WordRAM
open Cslib.Algorithms.Lean.VanEmdeBoas

/-- The constant, stack, and traversal registers at entry to `successorDescent`. -/
structure SuccessorEntry (stackBase₀ sp₀ base query : ℕ) (s : Data 32) : Prop where
  zero_eq : s.regs zero = 0
  one_eq : s.regs one = 1
  two_eq : s.regs two = 2
  three_eq : s.regs three = 3
  four_eq : s.regs four = 4
  five_eq : s.regs five = 5
  stackBase_eq : s.regs stackBase = stackBase₀
  sp_eq : s.regs sp = sp₀
  p_eq : s.regs p = base
  x_eq : s.regs x = query
  runFlag_eq : s.regs runFlag = 1

/-- Effect of pushing a four-word continuation frame `(k, pay, qv, tv)` at `sp₀`. -/
def pushFrameData (s : Data 32) (sp₀ k pay qv tv : ℕ) : Data 32 :=
  let a := (s.set kind k).set payload pay
  let b := ((a.write sp₀ k).set sp (sp₀ + 1)).write (sp₀ + 1) pay
  let c := ((b.set sp (sp₀ + 2)).write (sp₀ + 2) qv).set sp (sp₀ + 3)
  (c.write (sp₀ + 3) tv).set sp (sp₀ + 4)

/-- Mathematical description of one `successorDescentBody` iteration. -/
def successorDescentNext (s : Data 32) (sp₀ base query : ℕ) : Data 32 :=
  let a := s.set present (s.mem base)
  if s.mem base = 0 then
    ((a.set out 0).set found 0).set runFlag 0
  else
    let b := (a.set addr (base + 1)).set mn (s.mem (base + 1))
    if query < s.mem (base + 1) then
      ((b.set out (s.mem (base + 1))).set found 1).set runFlag 0
    else
      let c := (b.set addr (base + 2)).set mx (s.mem (base + 2))
      if query < s.mem (base + 2) then
        let e := (c.set addr (base + 3)).set q (s.mem (base + 3))
        if s.mem (base + 3) = 0 then
          ((e.set out (s.mem (base + 2))).set found 1).set runFlag 0
        else
          let f := (e.set addr (base + 4)).set t (s.mem (base + 4))
          let hi := query / s.mem (base + 3)
          let lo := query % s.mem (base + 3)
          let g := (((f.set high hi).set low lo).set tmp (hi + 1)).set tmp
            ((hi + 1) * s.mem (base + 4))
          let ch := base + 5 + (hi + 1) * s.mem (base + 4)
          let h := ((g.set child (base + 5)).set child ch).set present (s.mem ch)
          if s.mem ch = 0 then
            ((pushFrameData h sp₀ 1 base (s.mem (base + 3)) (s.mem (base + 4))).set p
              (base + 5)).set x hi
          else
            let h₁ := (h.set addr (ch + 2)).set mx (s.mem (ch + 2))
            if lo < s.mem (ch + 2) then
              ((pushFrameData h₁ sp₀ 0 (hi * s.mem (base + 3)) (s.mem (base + 3))
                (s.mem (base + 4))).set p ch).set x lo
            else
              ((pushFrameData h₁ sp₀ 1 base (s.mem (base + 3)) (s.mem (base + 4))).set p
                (base + 5)).set x hi
      else
        ((c.set out 0).set found 0).set runFlag 0

/-- Constant and `stackBase` registers are preserved by `successorDescentNext`. -/
private theorem successorDescentNext_constants {stackBase₀ sp₀ base query : ℕ} {s : Data 32}
    (hs : SuccessorEntry stackBase₀ sp₀ base query s) :
    (successorDescentNext s sp₀ base query).regs zero = 0 ∧
    (successorDescentNext s sp₀ base query).regs one = 1 ∧
    (successorDescentNext s sp₀ base query).regs two = 2 ∧
    (successorDescentNext s sp₀ base query).regs three = 3 ∧
    (successorDescentNext s sp₀ base query).regs four = 4 ∧
    (successorDescentNext s sp₀ base query).regs five = 5 ∧
    (successorDescentNext s sp₀ base query).regs stackBase = stackBase₀ := by
  obtain ⟨hz, ho, ht, hthree, hfour, hfive, hsb, _⟩ := hs
  simp only [successorDescentNext, pushFrameData]
  split_ifs <;> simp +decide [hz, ho, ht, hthree, hfour, hfive, hsb]

/-- Pushing a four-word frame modifies memory only in `[sp₀, sp₀ + 4)`. -/
private theorem pushFrameData_mem_away (s : Data 32) (sp₀ k pay qv tv a : ℕ)
    (ha : a < sp₀ ∨ sp₀ + 4 ≤ a) :
    (pushFrameData s sp₀ k pay qv tv).mem a = s.mem a := by
  have h0 : a ≠ sp₀ := by omega
  have h1 : a ≠ sp₀ + 1 := by omega
  have h2 : a ≠ sp₀ + 2 := by omega
  have h3 : a ≠ sp₀ + 3 := by omega
  simp [pushFrameData, Data.write_mem, Data.set_mem, Function.update_of_ne, h0, h1, h2, h3]

/-- One native successor-descent iteration executes in at most 42 instructions. -/
theorem successorDescentBody_exec {d w stackBase₀ sp₀ base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : SuccessorEntry stackBase₀ sp₀ base query s) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) (hsp : Fits w (sp₀ + 4 * d)) :
    ExecWithin w successorDescentBody s (successorDescentNext s sp₀ base query) 42 := by
  obtain ⟨hz, ho, htwo, hthree, hfour, hfive, _, hsp_eq, hp, hx, _⟩ := hs
  have hb1 : Fits w (base + 1) := ha.of_le (by have := five_le_span d; omega)
  have hb2 : Fits w (base + 2) := ha.of_le (by have := five_le_span d; omega)
  have hb3 : Fits w (base + 3) := ha.of_le (by have := five_le_span d; omega)
  have hb4 : Fits w (base + 4) := ha.of_le (by have := five_le_span d; omega)
  have hb5 : Fits w (base + 5) := ha.of_le (by have := five_le_span d; omega)
  have hheader := hr.header
  cases tree with
  | leaf b =>
    cases b with
    | none =>
      have hempty : s.mem base = 0 := hheader.1
      ram_eval [successorDescentBody, finishNone, successorDescentNext,
        hz, ho, htwo, hthree, hfour, hfive, hsp_eq, hp, hx, hempty]
    | some bounds =>
      obtain ⟨m, M⟩ := bounds
      obtain ⟨hpres_raw, ⟨hm, hM⟩, hq, _⟩ := hheader
      have hpres : s.mem base = 1 := by simpa [Tree.bounds] using hpres_raw
      by_cases hlt_m : query < m
      · ram_eval [successorDescentBody, readAt, finishMin, successorDescentNext,
          hz, ho, htwo, hthree, hfour, hfive, hsp_eq, hp, hx, hpres, hm, hlt_m, hb1]
      · by_cases hlt_M : query < M
        · ram_eval [successorDescentBody, readAt, finishMax, successorDescentNext,
            hz, ho, htwo, hthree, hfour, hfive, hsp_eq, hp, hx,
            hpres, hm, hM, hq, splitSize, hlt_m, hlt_M, hb1, hb2, hb3]
        · ram_eval [successorDescentBody, readAt, finishNone, successorDescentNext,
            hz, ho, htwo, hthree, hfour, hfive, hsp_eq, hp, hx,
            hpres, hm, hM, hlt_m, hlt_M, hb1, hb2]
  | @node d bounds summary cluster =>
    cases bounds with
    | none =>
      have hempty : s.mem base = 0 := hheader.1
      ram_eval [successorDescentBody, finishNone, successorDescentNext,
        hz, ho, htwo, hthree, hfour, hfive, hsp_eq, hp, hx, hempty]
    | some bounds =>
      obtain ⟨m, M⟩ := bounds
      obtain ⟨hpres_raw, ⟨hm, hM⟩, hq, hspan⟩ := hheader
      have hpres : s.mem base = 1 := by simpa [Tree.bounds] using hpres_raw
      by_cases hlt_m : query < m
      · ram_eval [successorDescentBody, readAt, finishMin, successorDescentNext,
          hz, ho, htwo, hthree, hfour, hfive, hsp_eq, hp, hx, hpres, hm, hlt_m, hb1]
      · by_cases hlt_M : query < M
        · have hsafe := member_descent_safe ht hr (by simpa only [hM] using hlt_M)
          have hi : query / universeSize d < universeSize d := hsafe.1
          have hlo : query % universeSize d < universeSize d := hsafe.2.1
          have hend : base + clusterOffset d (query / universeSize d) + span d ≤
              base + span (d + 1) := hsafe.2.2
          have hu_le : universeSize d ≤ span (d + 1) :=
            (universeSize_le_span d).trans (span_le_succ d)
          have hqne : universeSize d ≠ 0 := Nat.ne_of_gt (universeSize_pos d)
          have hw_base : Fits w base := ha.of_le (by omega)
          have hw_hi : Fits w (query / universeSize d) := ha.of_le (by omega)
          have hw_lo : Fits w (query % universeSize d) := ha.of_le (by omega)
          have hw_hi1 : Fits w (query / universeSize d + 1) := ha.of_le (by omega)
          have hw_off : Fits w ((query / universeSize d + 1) * span d) :=
            ha.of_le (by dsimp only [clusterOffset] at hend; omega)
          have hw_ch : Fits w (base + 5 + (query / universeSize d + 1) * span d) :=
            ha.of_le (by dsimp only [clusterOffset] at hend; omega)
          have hw_ch2 : Fits w (base + 5 + (query / universeSize d + 1) * span d + 2) :=
            ha.of_le (by have := five_le_span d; dsimp only [clusterOffset] at hend; omega)
          have hw_pay : Fits w (query / universeSize d * universeSize d) := by
            have hle : query / universeSize d * universeSize d ≤ query :=
              Nat.div_mul_le_self query (universeSize d)
            have hM_lt : M < universeSize (d + 1) := (maximum_lt_universe ht hr rfl).2
            have hu1_le : universeSize (d + 1) ≤ span (d + 1) := universeSize_le_span (d + 1)
            exact ha.of_le (by omega)
          have hsp1 : Fits w (sp₀ + 1) := hsp.of_le (by omega)
          have hsp2 : Fits w (sp₀ + 2) := hsp.of_le (by omega)
          have hsp3 : Fits w (sp₀ + 3) := hsp.of_le (by omega)
          have hsp4 : Fits w (sp₀ + 4) := hsp.of_le (by omega)
          let ch := base + 5 + (query / universeSize d + 1) * span d
          by_cases hch0 : s.mem ch = 0
          · ram_eval [successorDescentBody, readAt, coordinates, descendSummary, pushFrame,
              successorDescentNext, pushFrameData,
              hz, ho, htwo, hthree, hfour, hfive, hsp_eq, hp, hx,
              hpres, hm, hM, hq, hspan, splitSize, childSpan, hlt_m, hlt_M, hqne, hch0, ch,
              hb1, hb2, hb3, hb4, hb5, hw_base, hw_hi, hw_lo, hw_hi1, hw_off, hw_ch,
              hsp1, hsp2, hsp3, hsp4]
          · by_cases hlo_mx : query % universeSize d < s.mem (ch + 2)
            · ram_eval [successorDescentBody, readAt, coordinates, descendCluster, pushFrame,
                successorDescentNext, pushFrameData,
                hz, ho, htwo, hthree, hfour, hfive, hsp_eq, hp, hx,
                hpres, hm, hM, hq, hspan, splitSize, childSpan, hlt_m, hlt_M, hqne, hch0, hlo_mx,
                ch, hb1, hb2, hb3, hb4, hb5, hw_base, hw_hi, hw_lo, hw_hi1, hw_off, hw_ch,
                hw_ch2, hw_pay, hsp1, hsp2, hsp3, hsp4]
            · ram_eval [successorDescentBody, readAt, coordinates, descendSummary, pushFrame,
                successorDescentNext, pushFrameData,
                hz, ho, htwo, hthree, hfour, hfive, hsp_eq, hp, hx,
                hpres, hm, hM, hq, hspan, splitSize, childSpan, hlt_m, hlt_M, hqne, hch0, hlo_mx,
                ch, hb1, hb2, hb3, hb4, hb5, hw_base, hw_hi, hw_lo, hw_hi1, hw_off, hw_ch,
                hw_ch2, hsp1, hsp2, hsp3, hsp4]
        · ram_eval [successorDescentBody, readAt, finishNone, successorDescentNext,
            hz, ho, htwo, hthree, hfour, hfive, hsp_eq, hp, hx,
            hpres, hm, hM, hlt_m, hlt_M, hb1, hb2]

/-- Register and memory invariant at the start of an unwind stage at stack pointer `sp₀`. -/
structure UnwindState (stackBase₀ sp₀ ans : ℕ) (mem : ℕ → ℕ) (s : Data 32) : Prop where
  zero_eq : s.regs zero = 0
  one_eq : s.regs one = 1
  five_eq : s.regs five = 5
  stackBase_eq : s.regs stackBase = stackBase₀
  sp_eq : s.regs sp = sp₀
  found_eq : s.regs found = 1
  out_eq : s.regs out = ans
  mem_eq : s.mem = mem

/-- Mathematical description of one `successorUnwindBody` iteration popping at `sp₀`. -/
def successorUnwindNext (s : Data 32) (sp₀ : ℕ) : Data 32 :=
  let tv := s.mem (sp₀ + 3)
  let qv := s.mem (sp₀ + 2)
  let pay := s.mem (sp₀ + 1)
  let k := s.mem sp₀
  let a := (((((((s.set sp (sp₀ + 3)).set frameT tv).set sp (sp₀ + 2)).set frameQ qv).set sp
    (sp₀ + 1)).set payload pay).set sp sp₀).set kind k
  if k = 0 then
    a.set out (pay + s.regs out)
  else
    let hi := s.regs out
    let ch := pay + 5 + (hi + 1) * tv
    let lo := s.mem (ch + 1)
    let b := ((((((a.set high hi).set tmp (hi + 1)).set tmp ((hi + 1) * tv)).set child
      (pay + 5)).set child ch).set addr (ch + 1)).set low lo
    (b.set out (hi * qv)).set out (hi * qv + lo)

/-- Invariant registers and memory preserved across `successorUnwindNext`. -/
private theorem successorUnwindNext_preserved {stackBase₀ sp₀ childAns : ℕ} {mem : ℕ → ℕ}
    {s : Data 32} (hs : UnwindState stackBase₀ (sp₀ + 4) childAns mem s) :
    (successorUnwindNext s sp₀).regs zero = 0 ∧
    (successorUnwindNext s sp₀).regs one = 1 ∧
    (successorUnwindNext s sp₀).regs five = 5 ∧
    (successorUnwindNext s sp₀).regs stackBase = stackBase₀ ∧
    (successorUnwindNext s sp₀).regs sp = sp₀ ∧
    (successorUnwindNext s sp₀).regs found = 1 ∧
    (successorUnwindNext s sp₀).mem = mem := by
  obtain ⟨hz, ho, hfive, hsb, _, hfound, _, hmem⟩ := hs
  simp only [successorUnwindNext]
  split_ifs <;> simp +decide [hz, ho, hfive, hsb, hfound, hmem]

/-- One cluster-return unwind step (`kind = 0`) executes in at most 19 instructions. -/
theorem successorUnwindBody_cluster_exec {w stackBase₀ sp₀ pay qv tv childAns : ℕ}
    {mem : ℕ → ℕ} {s : Data 32}
    (hs : UnwindState stackBase₀ (sp₀ + 4) childAns mem s)
    (hk : mem sp₀ = 0) (hpay : mem (sp₀ + 1) = pay)
    (hqv : mem (sp₀ + 2) = qv) (htv : mem (sp₀ + 3) = tv)
    (hsp : Fits w (sp₀ + 4)) (hout : Fits w (pay + childAns)) :
    ExecWithin w successorUnwindBody s (successorUnwindNext s sp₀) 19 := by
  obtain ⟨hz, ho, hfive, _, hsp_eq, _, hout_eq, hmem⟩ := hs
  have hsp3 : Fits w (sp₀ + 3) := hsp.of_le (by omega)
  have hsp2 : Fits w (sp₀ + 2) := hsp.of_le (by omega)
  have hsp1 : Fits w (sp₀ + 1) := hsp.of_le (by omega)
  have hsp0 : Fits w sp₀ := hsp.of_le (by omega)
  ram_eval [successorUnwindBody, popFrame, successorUnwindNext,
    hz, ho, hfive, hsp_eq, hout_eq, hmem, hk, hpay, hqv, htv,
    hsp3, hsp2, hsp1, hsp0, hout, Nat.add_sub_assoc, Nat.add_zero]

/-- One summary-return unwind step (`kind = 1`) executes in at most 19 instructions. -/
theorem successorUnwindBody_summary_exec {d w stackBase₀ sp₀ base j cm : ℕ}
    {mem : ℕ → ℕ} {s : Data 32}
    (hs : UnwindState stackBase₀ (sp₀ + 4) j mem s)
    (hk : mem sp₀ = 1) (hpay : mem (sp₀ + 1) = base)
    (hqv : mem (sp₀ + 2) = universeSize d) (htv : mem (sp₀ + 3) = span d)
    (hj : j < universeSize d)
    (hcm : mem (base + 5 + (j + 1) * span d + 1) = cm) (hcm_lt : cm < universeSize d)
    (ha : Fits w (base + span (d + 1))) (hsp : Fits w (sp₀ + 4)) :
    ExecWithin w successorUnwindBody s (successorUnwindNext s sp₀) 19 := by
  obtain ⟨hz, ho, hfive, _, hsp_eq, _, hout_eq, hmem⟩ := hs
  have hsp3 : Fits w (sp₀ + 3) := hsp.of_le (by omega)
  have hsp2 : Fits w (sp₀ + 2) := hsp.of_le (by omega)
  have hsp1 : Fits w (sp₀ + 1) := hsp.of_le (by omega)
  have hsp0 : Fits w sp₀ := hsp.of_le (by omega)
  have hend := cluster_end_le_span d hj
  dsimp only [clusterOffset] at hend
  have hj1 : Fits w (j + 1) :=
    ha.of_le (by have := (universeSize_le_span d).trans (span_le_succ d); omega)
  have hoff : Fits w ((j + 1) * span d) := ha.of_le (by omega)
  have hb5 : Fits w (base + 5) := ha.of_le (by have := five_le_span (d + 1); omega)
  have hch : Fits w (base + 5 + (j + 1) * span d) := ha.of_le (by omega)
  have hch1 : Fits w (base + 5 + (j + 1) * span d + 1) :=
    ha.of_le (by have := five_le_span d; omega)
  have hmul_lt : j * universeSize d + cm < universeSize (d + 1) := by
    rw [universeSize_succ]
    have h := Nat.mul_le_mul_right (universeSize d) (show j + 1 ≤ universeSize d by omega)
    rw [Nat.succ_mul] at h
    omega
  have hu1_le : universeSize (d + 1) ≤ span (d + 1) := universeSize_le_span (d + 1)
  have hmul : Fits w (j * universeSize d) := ha.of_le (by omega)
  have hans : Fits w (j * universeSize d + cm) := ha.of_le (by omega)
  ram_eval [successorUnwindBody, popFrame, readAt, successorUnwindNext,
    hz, ho, hfive, hsp_eq, hout_eq, hmem, hk, hpay, hqv, htv, hcm,
    hsp3, hsp2, hsp1, hsp0, hj1, hoff, hb5, hch, hch1, hmul, hans,
    Nat.add_sub_assoc, Nat.add_zero]

/-- Combined inductive certification of `successorDescent` and CPS `successorUnwind` whenever
`tree.successor query = some ans`. -/
private theorem successor_some_spec {d w stackBase₀ sp₀ base query ans : ℕ} {tree : Tree d}
    {s : Data 32} (hs : SuccessorEntry stackBase₀ sp₀ base query s) (ht : tree.Valid)
    (hr : Rep tree base s.mem) (hans : tree.successor query = some ans)
    (hsp_le : stackBase₀ ≤ sp₀) (hdisj : base + span d ≤ sp₀) (hfit : Fits w (sp₀ + 4 * d)) :
    ∃ s₁ s₃, ExecWithin w successorDescent s s₁ (44 * (d + 1) + 2) ∧
      (∀ a, a < sp₀ ∨ sp₀ + 4 * d ≤ a → s₁.mem a = s.mem a) ∧
      UnwindState stackBase₀ sp₀ ans s₁.mem s₃ ∧
      ∀ z T, ExecWithin w successorUnwind s₃ z T →
        ExecWithin w successorUnwind s₁ z (21 * d + T) := by
  induction d generalizing sp₀ base query ans s with
  | zero =>
    have ha : Fits w (base + span 0) := hfit.of_le (by omega)
    have he := successorDescentBody_exec hs ht hr ha hfit
    have hheader := hr.header
    cases tree with
    | leaf b =>
      cases b with
      | none => simp [Tree.successor] at hans
      | some bounds =>
        obtain ⟨m, M⟩ := bounds
        obtain ⟨hpres_raw, ⟨hm, hM⟩, hq, _⟩ := hheader
        have hpres : s.mem base = 1 := by simpa [Tree.bounds] using hpres_raw
        let s₁ := successorDescentNext s sp₀ base query
        have hconst := successorDescentNext_constants hs
        have hmem₁ : s₁.mem = s.mem := by
          simp only [s₁, successorDescentNext, hpres, hm, hM, hq, splitSize]
          split_ifs <;> rfl
        have hk : (successorDescentNext s sp₀ base query).regs runFlag = 0 := by
          simp only [successorDescentNext, hpres, hm, hM, hq, splitSize, ↓reduceIte]
          split_ifs <;> rfl
        have hfound₁ : s₁.regs found = 1 ∧ s₁.regs out = ans := by
          simp only [Tree.successor] at hans
          simp only [s₁, successorDescentNext, hpres, hm, hM, hq, splitSize, ↓reduceIte]
          split_ifs with h1 h2 <;> simp_all +decide
        have hsp₁ : s₁.regs sp = sp₀ := by
          simp only [s₁, successorDescentNext, hpres, hm, hM, hq, splitSize, ↓reduceIte]
          split_ifs <;> exact hs.sp_eq
        refine ⟨s₁, s₁, ?_, ?_, ⟨hconst.1, hconst.2.1, hconst.2.2.2.2.2.1, hconst.2.2.2.2.2.2,
          hsp₁, hfound₁.1, hfound₁.2, rfl⟩, ?_⟩
        · refine (he.loop_once (cond := .lt zero runFlag) ?_ ?_).mono
            (by omega)
          · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
            decide
          · simp only [Cond.holds_lt, hconst.1, hk, lt_self_iff_false, not_false_eq_true]
        · intro a _
          rw [hmem₁]
        · intro z T hcont
          simpa only [Nat.mul_zero, Nat.zero_add] using hcont
  | succ d ih =>
    have ha : Fits w (base + span (d + 1)) := hfit.of_le (by omega)
    have he := successorDescentBody_exec hs ht hr ha hfit
    have hheader := hr.header
    cases tree with
    | node bounds summary cluster =>
      cases bounds with
      | none => simp [Tree.successor] at hans
      | some bounds =>
        obtain ⟨m, M⟩ := bounds
        obtain ⟨hpres_raw, ⟨hm, hM⟩, hq, hspan⟩ := hheader
        have hpres : s.mem base = 1 := by simpa [Tree.bounds] using hpres_raw
        let next := successorDescentNext s sp₀ base query
        have hconst := successorDescentNext_constants hs
        by_cases hlt_m : query < m
        · have hans_eq : ans = m := by
            have := hans
            simp only [Tree.successor, hlt_m, ↓reduceIte, Option.some.injEq] at this
            exact this.symm
          have hmem₁ : next.mem = s.mem := by
            simp [next, successorDescentNext, hpres, hm, hlt_m]
          have hk : (successorDescentNext s sp₀ base query).regs runFlag = 0 := by
            simp +decide [successorDescentNext, hpres, hm, hlt_m]
          have hfound₁ : next.regs found = 1 ∧ next.regs out = ans := by
            simp +decide [next, successorDescentNext, hpres, hm, hlt_m, hans_eq]
          have hsp₁ : next.regs sp = sp₀ := by
            simp +decide [next, successorDescentNext, hpres, hm, hlt_m, hs.sp_eq]
          refine ⟨next, next, ?_, ?_, ⟨hconst.1, hconst.2.1, hconst.2.2.2.2.2.1,
            hconst.2.2.2.2.2.2, hsp₁, hfound₁.1, hfound₁.2, rfl⟩, ?_⟩
          · refine (he.loop_once (cond := .lt zero runFlag) ?_ ?_).mono
              (by omega)
            · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
              decide
            · simp only [Cond.holds_lt, hconst.1, hk, lt_self_iff_false, not_false_eq_true]
          · intro a _
            rw [hmem₁]
          · intro z T hcont
            exact hcont.mono (by omega)
        · have hlt_M : query < M := by
            by_contra hge
            have hle : M ≤ query := Nat.le_of_not_lt hge
            simp [Tree.successor, hlt_m, hle] at hans
          have hnot_le : ¬M ≤ query := not_le.mpr hlt_M
          have hsafe := member_descent_safe ht hr (by simpa only [hM] using hlt_M)
          have hi : query / universeSize d < universeSize d := hsafe.1
          have hlo : query % universeSize d < universeSize d := hsafe.2.1
          have hend : base + clusterOffset d (query / universeSize d) + span d ≤
              base + span (d + 1) := hsafe.2.2
          have hqne : universeSize d ≠ 0 := Nat.ne_of_gt (universeSize_pos d)
          let i : Fin (universeSize d) := ⟨query / universeSize d, hi⟩
          let lo := query % universeSize d
          let ch := base + clusterOffset d i.val
          have hch_eq : base + 5 + (query / universeSize d + 1) * span d = ch := by
            dsimp only [ch, clusterOffset, i]
            omega
          -- Helper for the summary-descent branch (used both when `cluster i` is empty
          -- and when `cluster i` has maximum `≤ lo`).
          have summary_branch
              (hc_max : (cluster i).maximum.any (lo < ·) = false)
              (hnext_eq : next =
                ((pushFrameData
                  (if s.mem ch = 0 then
                    (((((s.set present 1).set addr (base + 1)).set mn m).set addr
                      (base + 2)).set mx M).set addr (base + 3) |>.set q (universeSize d)
                      |>.set addr (base + 4) |>.set t (span d) |>.set high i.val |>.set low lo
                      |>.set tmp (i.val + 1) |>.set tmp ((i.val + 1) * span d)
                      |>.set child (base + 5) |>.set child ch |>.set present (s.mem ch)
                  else
                    (((((s.set present 1).set addr (base + 1)).set mn m).set addr
                      (base + 2)).set mx M).set addr (base + 3) |>.set q (universeSize d)
                      |>.set addr (base + 4) |>.set t (span d) |>.set high i.val |>.set low lo
                      |>.set tmp (i.val + 1) |>.set tmp ((i.val + 1) * span d)
                      |>.set child (base + 5) |>.set child ch |>.set present (s.mem ch)
                      |>.set addr (ch + 2) |>.set mx (s.mem (ch + 2)))
                  sp₀ 1 base (universeSize d) (span d)).set p (base + 5)).set x i.val) :
              ∃ s₁ s₃, ExecWithin w successorDescent s s₁ (44 * (d + 1 + 1) + 2) ∧
                (∀ a, a < sp₀ ∨ sp₀ + 4 * (d + 1) ≤ a → s₁.mem a = s.mem a) ∧
                UnwindState stackBase₀ sp₀ ans s₁.mem s₃ ∧
                ∀ z T, ExecWithin w successorUnwind s₃ z T →
                  ExecWithin w successorUnwind s₁ z (21 * (d + 1) + T) := by
            have hans' :
                (summary.successor i.val).bind (fun j =>
                  if hj : j < universeSize d then
                    (cluster ⟨j, hj⟩).minimum.map (j * universeSize d + ·)
                  else none) = some ans := by
              simpa only [Tree.successor, hlt_m, hnot_le, hi, ↓reduceDIte, ↓reduceIte,
                i, lo, hc_max, Bool.false_eq_true, bind] using hans
            cases hsuc : summary.successor i.val with
            | none => simp [hsuc] at hans'
            | some j =>
              simp only [hsuc, Option.bind_some] at hans'
              by_cases hj : j < universeSize d
              · simp only [hj, ↓reduceDIte] at hans'
                let k : Fin (universeSize d) := ⟨j, hj⟩
                change (cluster k).minimum.map (j * universeSize d + ·) = some ans at hans'
                cases hck : (cluster k).bounds with
                | none => simp [Tree.minimum, hck] at hans'
                | some cbounds =>
                  obtain ⟨cm, cM⟩ := cbounds
                  have hans_eq : j * universeSize d + cm = ans := by
                    simpa [Tree.minimum, hck] using hans'
                  have hcm_lt : cm < universeSize d := by
                    have hce := (ht.2.2.1 k).extrema
                    simp only [Tree.Extrema, hck] at hce
                    omega
                  have hcm_mem : s.mem (base + 5 + (j + 1) * span d + 1) = cm := by
                    have hh := (hr.2.2 k).header
                    simp only [Header, hck] at hh
                    simpa only [clusterOffset, k, Nat.add_assoc] using hh.2.1.1
                  have hnext_away : ∀ a, a < sp₀ ∨ sp₀ + 4 ≤ a → next.mem a = s.mem a := by
                    intro a ha'
                    rw [hnext_eq]
                    simp only [Data.set_mem]
                    rw [pushFrameData_mem_away _ _ _ _ _ _ _ ha']
                    split_ifs <;> rfl
                  have hentry : SuccessorEntry stackBase₀ (sp₀ + 4) (base + summaryOffset) i.val
                      next := by
                    refine ⟨hconst.1, hconst.2.1, hconst.2.2.1, hconst.2.2.2.1, hconst.2.2.2.2.1,
                      hconst.2.2.2.2.2.1, hconst.2.2.2.2.2.2, ?_, ?_, ?_, ?_⟩
                    · rw [hnext_eq]; rfl
                    · rw [hnext_eq]; rfl
                    · rw [hnext_eq]; rfl
                    · rw [hnext_eq]
                      simp only [pushFrameData]
                      split_ifs <;> simp +decide [hs.runFlag_eq]
                  have hrs_next : Rep summary (base + summaryOffset) next.mem := by
                    apply rep_frame hr.2.1
                    intro a hlo_a hhi_a
                    have hsum_end := summary_end_le_span d
                    dsimp only [summaryOffset] at hlo_a hhi_a hsum_end
                    exact hnext_away a (Or.inl (by omega))
                  have hsp_le' : stackBase₀ ≤ sp₀ + 4 := by omega
                  have hdisj' : base + summaryOffset + span d ≤ sp₀ + 4 := by
                    have hsum_end := summary_end_le_span d
                    omega
                  have hfit' : Fits w (sp₀ + 4 + 4 * d) := by
                    simpa only [Nat.mul_succ, ← Nat.add_assoc, Nat.add_right_comm sp₀ (4 * d) 4]
                      using hfit
                  obtain ⟨s₁, s₂, hs₁, hframe₁, hs₂, hunwind₁⟩ :=
                    ih hentry ht.2.1 hrs_next hsuc hsp_le' hdisj' hfit'
                  have hframe_sp : ∀ a < sp₀ + 4, s₁.mem a = next.mem a :=
                    fun a ha' => hframe₁ a (Or.inl ha')
                  have hk_mem : s₁.mem sp₀ = 1 := by
                    rw [hframe_sp sp₀ (by omega), hnext_eq]
                    simp +decide [pushFrameData, Data.write_mem, Data.set_mem]
                  have hpay_mem : s₁.mem (sp₀ + 1) = base := by
                    rw [hframe_sp (sp₀ + 1) (by omega), hnext_eq]
                    simp +decide [pushFrameData, Data.write_mem, Data.set_mem]
                  have hqv_mem : s₁.mem (sp₀ + 2) = universeSize d := by
                    rw [hframe_sp (sp₀ + 2) (by omega), hnext_eq]
                    simp +decide [pushFrameData, Data.write_mem, Data.set_mem]
                  have htv_mem : s₁.mem (sp₀ + 3) = span d := by
                    rw [hframe_sp (sp₀ + 3) (by omega), hnext_eq]
                    simp +decide [pushFrameData, Data.write_mem, Data.set_mem]
                  have hcm_s₁ : s₁.mem (base + 5 + (j + 1) * span d + 1) = cm := by
                    have hlt_sp : base + 5 + (j + 1) * span d + 1 < sp₀ := by
                      have hend_j := cluster_end_le_span d hj
                      have := five_le_span d
                      dsimp only [clusterOffset] at hend_j
                      omega
                    rw [hframe_sp _ (by omega), hnext_away _ (Or.inl hlt_sp), hcm_mem]
                  have hsp4_fit : Fits w (sp₀ + 4) := hfit.of_le (by omega)
                  have hbody := successorUnwindBody_summary_exec hs₂ hk_mem hpay_mem hqv_mem
                    htv_mem hj hcm_s₁ hcm_lt ha hsp4_fit
                  let s₃ := successorUnwindNext s₂ sp₀
                  have hpres₃ := successorUnwindNext_preserved hs₂
                  have hs₃ : UnwindState stackBase₀ sp₀ ans s₁.mem s₃ := by
                    refine ⟨hpres₃.1, hpres₃.2.1, hpres₃.2.2.1, hpres₃.2.2.2.1, hpres₃.2.2.2.2.1,
                      hpres₃.2.2.2.2.2.1, ?_, hpres₃.2.2.2.2.2.2⟩
                    simp +decide [s₃, successorUnwindNext, hs₂.mem_eq, hs₂.out_eq,
                      hk_mem, hpay_mem, hqv_mem, htv_mem, hcm_s₁, hans_eq]
                  refine ⟨s₁, s₃, (he.loop_iter (cond := .lt zero runFlag) ?_ hs₁).mono (by omega),
                    ?_, hs₃, ?_⟩
                  · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
                    decide
                  · intro a ha'
                    by_cases ha4 : a < sp₀
                    · exact (hframe₁ a (Or.inl (by omega))).trans (hnext_away a (Or.inl ha4))
                    · have ha_ge : sp₀ + 4 + 4 * d ≤ a := by omega
                      exact (hframe₁ a (Or.inr ha_ge)).trans (hnext_away a (Or.inr (by omega)))
                  · intro z T hcont
                    have hiter : ExecWithin w successorUnwind s₂ z (21 + T) := by
                      refine (hbody.loop_iter (cond := .lt stackBase sp) ?_ hcont).mono (by omega)
                      simp only [Cond.holds_lt, hs₂.stackBase_eq, hs₂.sp_eq]
                      omega
                    exact (hunwind₁ z (21 + T) hiter).mono (by omega)
              · simp [hj] at hans'
          cases hcb : (cluster i).bounds with
          | none =>
            have hch0 : s.mem ch = 0 := by
              have hh := (hr.2.2 i).header.1
              simpa only [ch, hcb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using hh
            have hc_max : (cluster i).maximum.any (lo < ·) = false := by
              simp [Tree.maximum, hcb]
            apply summary_branch hc_max
            simp +decide only [next, successorDescentNext, hpres, hm, hM, hq, hspan, splitSize,
              childSpan, ↓reduceIte, hlt_m, hlt_M, hqne, hch_eq, hch0, i, lo]
          | some cbounds =>
            obtain ⟨cm, cM⟩ := cbounds
            have hch1 : s.mem ch = 1 := by
              have hh := (hr.2.2 i).header.1
              simpa only [ch, hcb, Option.isSome_some, ↓reduceIte] using hh
            have hch_ne0 : s.mem ch ≠ 0 := by
              rw [hch1]
              decide
            have hcM : s.mem (ch + 2) = cM := by
              have hh := (hr.2.2 i).header
              simp only [Header, hcb] at hh
              exact hh.2.1.2
            by_cases hlo_cM : lo < cM
            · -- Cluster descent branch
              have hlo_mx : query % universeSize d < s.mem (ch + 2) := by
                simpa only [hcM, lo] using hlo_cM
              have hc_max : (cluster i).maximum.any (lo < ·) = true := by
                simp [Tree.maximum, hcb, hlo_cM]
              have hans' : ((cluster i).successor lo).map (i.val * universeSize d + ·) =
                  some ans := by
                simpa only [Tree.successor, hlt_m, hnot_le, hi, ↓reduceDIte, ↓reduceIte,
                  i, lo, hc_max] using hans
              obtain ⟨y, hy_lt, hy_suc⟩ :=
                Tree.successor_isSome_of_lt_max (ht.2.2.1 i) hcb hlo_cM
              have hans_eq : i.val * universeSize d + y = ans := by
                simpa only [hy_suc, Option.map_some, Option.some.injEq] using hans'
              have hnext_eq : next =
                  ((pushFrameData
                    ((((((s.set present 1).set addr (base + 1)).set mn m).set addr
                      (base + 2)).set mx M).set addr (base + 3) |>.set q (universeSize d)
                      |>.set addr (base + 4) |>.set t (span d) |>.set high i.val |>.set low lo
                      |>.set tmp (i.val + 1) |>.set tmp ((i.val + 1) * span d)
                      |>.set child (base + 5) |>.set child ch |>.set present (s.mem ch)
                      |>.set addr (ch + 2) |>.set mx (s.mem (ch + 2)))
                    sp₀ 0 (i.val * universeSize d) (universeSize d) (span d)).set p ch).set x lo :=
                by
                simp +decide only [next, successorDescentNext, hpres, hm, hM, hq, hspan,
                  splitSize, childSpan, ↓reduceIte, hlt_m, hlt_M, hqne, hch_eq, hch_ne0, hlo_mx,
                  i, lo]
              have hnext_away : ∀ a, a < sp₀ ∨ sp₀ + 4 ≤ a → next.mem a = s.mem a := by
                intro a ha'
                rw [hnext_eq]
                simp only [Data.set_mem]
                exact pushFrameData_mem_away _ _ _ _ _ _ _ ha'
              have hentry : SuccessorEntry stackBase₀ (sp₀ + 4) ch lo next := by
                refine ⟨hconst.1, hconst.2.1, hconst.2.2.1, hconst.2.2.2.1, hconst.2.2.2.2.1,
                  hconst.2.2.2.2.2.1, hconst.2.2.2.2.2.2, ?_, ?_, ?_, ?_⟩
                · rw [hnext_eq]; rfl
                · rw [hnext_eq]; rfl
                · rw [hnext_eq]; rfl
                · rw [hnext_eq]
                  simp +decide [pushFrameData, hs.runFlag_eq]
              have hrc_next : Rep (cluster i) ch next.mem := by
                apply rep_frame (hr.2.2 i)
                intro a hlo_a hhi_a
                dsimp only [ch, i] at hlo_a hhi_a
                exact hnext_away a (Or.inl (by omega))
              have hsp_le' : stackBase₀ ≤ sp₀ + 4 := by omega
              have hdisj' : ch + span d ≤ sp₀ + 4 := by
                dsimp only [ch, i]
                omega
              have hfit' : Fits w (sp₀ + 4 + 4 * d) := by
                simpa only [Nat.mul_succ, ← Nat.add_assoc, Nat.add_right_comm sp₀ (4 * d) 4]
                  using hfit
              obtain ⟨s₁, s₂, hs₁, hframe₁, hs₂, hunwind₁⟩ :=
                ih hentry (ht.2.2.1 i) hrc_next hy_suc hsp_le' hdisj' hfit'
              have hframe_sp : ∀ a < sp₀ + 4, s₁.mem a = next.mem a :=
                fun a ha' => hframe₁ a (Or.inl ha')
              have hk_mem : s₁.mem sp₀ = 0 := by
                rw [hframe_sp sp₀ (by omega), hnext_eq]
                simp +decide [pushFrameData, Data.write_mem, Data.set_mem]
              have hpay_mem : s₁.mem (sp₀ + 1) = i.val * universeSize d := by
                rw [hframe_sp (sp₀ + 1) (by omega), hnext_eq]
                simp +decide [pushFrameData, Data.write_mem, Data.set_mem]
              have hqv_mem : s₁.mem (sp₀ + 2) = universeSize d := by
                rw [hframe_sp (sp₀ + 2) (by omega), hnext_eq]
                simp +decide [pushFrameData, Data.write_mem, Data.set_mem]
              have htv_mem : s₁.mem (sp₀ + 3) = span d := by
                rw [hframe_sp (sp₀ + 3) (by omega), hnext_eq]
                simp +decide [pushFrameData, Data.write_mem, Data.set_mem]
              have hsp4_fit : Fits w (sp₀ + 4) := hfit.of_le (by omega)
              have hout_fit : Fits w (i.val * universeSize d + y) := by
                have hmul_lt : i.val * universeSize d + y < universeSize (d + 1) := by
                  rw [universeSize_succ]
                  have h := Nat.mul_le_mul_right (universeSize d)
                    (show i.val + 1 ≤ universeSize d by exact hi)
                  rw [Nat.succ_mul] at h
                  omega
                have hu1_le := universeSize_le_span (d + 1)
                exact ha.of_le (by omega)
              have hbody := successorUnwindBody_cluster_exec hs₂ hk_mem hpay_mem hqv_mem
                htv_mem hsp4_fit hout_fit
              let s₃ := successorUnwindNext s₂ sp₀
              have hpres₃ := successorUnwindNext_preserved hs₂
              have hs₃ : UnwindState stackBase₀ sp₀ ans s₁.mem s₃ := by
                refine ⟨hpres₃.1, hpres₃.2.1, hpres₃.2.2.1, hpres₃.2.2.2.1, hpres₃.2.2.2.2.1,
                  hpres₃.2.2.2.2.2.1, ?_, hpres₃.2.2.2.2.2.2⟩
                simp +decide [s₃, successorUnwindNext, hs₂.mem_eq, hs₂.out_eq,
                  hk_mem, hpay_mem, hans_eq]
              refine ⟨s₁, s₃, (he.loop_iter (cond := .lt zero runFlag) ?_ hs₁).mono (by omega),
                ?_, hs₃, ?_⟩
              · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
                decide
              · intro a ha'
                by_cases ha4 : a < sp₀
                · exact (hframe₁ a (Or.inl (by omega))).trans (hnext_away a (Or.inl ha4))
                · have ha_ge : sp₀ + 4 + 4 * d ≤ a := by omega
                  exact (hframe₁ a (Or.inr ha_ge)).trans (hnext_away a (Or.inr (by omega)))
              · intro z T hcont
                have hiter : ExecWithin w successorUnwind s₂ z (21 + T) := by
                  refine (hbody.loop_iter (cond := .lt stackBase sp) ?_ hcont).mono (by omega)
                  simp only [Cond.holds_lt, hs₂.stackBase_eq, hs₂.sp_eq]
                  omega
                exact (hunwind₁ z (21 + T) hiter).mono (by omega)
            · -- Summary descent branch when `cM ≤ lo`
              have hlo_mx : ¬query % universeSize d < s.mem (ch + 2) := by
                simpa only [hcM, lo] using hlo_cM
              have hc_max : (cluster i).maximum.any (lo < ·) = false := by
                simp [Tree.maximum, hcb, hlo_cM]
              apply summary_branch hc_max
              simp +decide only [next, successorDescentNext, hpres, hm, hM, hq, hspan, splitSize,
                childSpan, ↓reduceIte, hlt_m, hlt_M, hqne, hch_eq, hch_ne0, hlo_mx, i, lo]

/-- When `tree.successor query = none`, `successorDescent` terminates in one iteration (46
instructions) with `found = 0`, `out = 0`, `sp = sp₀`, and unchanged memory. -/
private theorem successor_none_spec {d w stackBase₀ sp₀ base query : ℕ} {tree : Tree d}
    {s : Data 32} (hs : SuccessorEntry stackBase₀ sp₀ base query s) (ht : tree.Valid)
    (hr : Rep tree base s.mem) (hnone : tree.successor query = none)
    (hdisj : base + span d ≤ sp₀) (hfit : Fits w (sp₀ + 4 * d)) :
    ∃ s₁, ExecWithin w successorDescent s s₁ 46 ∧
      s₁.regs stackBase = stackBase₀ ∧ s₁.regs sp = sp₀ ∧
      s₁.regs found = 0 ∧ s₁.regs out = 0 ∧ s₁.mem = s.mem := by
  have ha : Fits w (base + span d) := hfit.of_le (by omega)
  have he := successorDescentBody_exec hs ht hr ha hfit
  let s₁ := successorDescentNext s sp₀ base query
  have hconst := successorDescentNext_constants hs
  have hheader := hr.header
  have hprops : (successorDescentNext s sp₀ base query).regs runFlag = 0 ∧
      s₁.regs sp = sp₀ ∧ s₁.regs found = 0 ∧ s₁.regs out = 0 ∧ s₁.mem = s.mem := by
    cases tree with
    | leaf b =>
      cases b with
      | none =>
        have hempty : s.mem base = 0 := hheader.1
        simp +decide [s₁, successorDescentNext, hempty, hs.sp_eq]
      | some bounds =>
        obtain ⟨m, M⟩ := bounds
        obtain ⟨hpres_raw, ⟨hm, hM⟩, _⟩ := hheader
        have hpres : s.mem base = 1 := by simpa [Tree.bounds] using hpres_raw
        have hnot_m : ¬query < m := by
          intro hlt
          simp [Tree.successor, hlt] at hnone
        have hnot_M : ¬query < M := by
          intro hlt
          simp [Tree.successor, hnot_m, hlt] at hnone
        simp +decide [s₁, successorDescentNext, hpres, hm, hM, hnot_m, hnot_M, hs.sp_eq]
    | node bounds summary cluster =>
      cases bounds with
      | none =>
        have hempty : s.mem base = 0 := hheader.1
        simp +decide [s₁, successorDescentNext, hempty, hs.sp_eq]
      | some bounds =>
        obtain ⟨m, M⟩ := bounds
        obtain ⟨hpres_raw, ⟨hm, hM⟩, _⟩ := hheader
        have hpres : s.mem base = 1 := by simpa [Tree.bounds] using hpres_raw
        have hnot_M : ¬query < M := by
          intro hlt
          obtain ⟨ans, _, hans⟩ := Tree.successor_isSome_of_lt_max ht rfl hlt
          simp [hans] at hnone
        have hnot_m : ¬query < m := by
          have hext := ht.extrema
          simp only [Tree.Extrema, Tree.bounds] at hext
          have := hext.1
          omega
        simp +decide [s₁, successorDescentNext, hpres, hm, hM, hnot_m, hnot_M, hs.sp_eq]
  refine ⟨s₁, ?_, hconst.2.2.2.2.2.2, hprops.2.1, hprops.2.2.1, hprops.2.2.2.1, hprops.2.2.2.2⟩
  refine he.loop_once (cond := .lt zero runFlag) ?_ ?_
  · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
    decide
  · simp only [Cond.holds_lt, hconst.1, hprops.1, lt_self_iff_false, not_false_eq_true]

/-- Complete certification of `successorDescent; successorUnwind` from `sp = stackBase₀`:
executes in at most `65 * (d + 1) + 4` instructions, computes `tree.successor query`,
restores `sp = stackBase₀`, preserves `Rep tree base z.mem`, and frames memory outside
`[stackBase₀, stackBase₀ + 4 * d)`. -/
theorem successor_loop_spec {d w stackBase₀ base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : SuccessorEntry stackBase₀ stackBase₀ base query s)
    (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hdisj : base + span d ≤ stackBase₀) (hfit : Fits w (stackBase₀ + 4 * d)) :
    ∃ z, ExecWithin w (ram[ ⟪successorDescent⟫; ⟪successorUnwind⟫ ]) s z (65 * (d + 1) + 4) ∧
      (if z.regs found = 0 then none else some (z.regs out)) = tree.successor query ∧
      z.regs sp = stackBase₀ ∧
      Rep tree base z.mem ∧
      (∀ a, a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a → z.mem a = s.mem a) := by
  cases hsuc : tree.successor query with
  | none =>
    obtain ⟨s₁, hs₁, hsb₁, hsp₁, hfound₁, hout₁, hmem₁⟩ :=
      successor_none_spec hs ht hr hsuc hdisj hfit
    have hexit : ExecWithin w successorUnwind s₁ s₁ 2 := by
      apply ExecWithin.loop_exit
      simp only [Cond.holds_lt, hsb₁, hsp₁, lt_self_iff_false, not_false_eq_true]
    refine ⟨s₁, (hs₁.seq hexit).mono (by omega), ?_, hsp₁, ?_, ?_⟩
    · simp [hfound₁]
    · simpa only [hmem₁] using hr
    · intro a _
      rw [hmem₁]
  | some ans =>
    obtain ⟨s₁, z, hs₁, hframe₁, hz, hunwind₁⟩ :=
      successor_some_spec hs ht hr hsuc le_rfl hdisj hfit
    have hexit : ExecWithin w successorUnwind z z 2 := by
      apply ExecWithin.loop_exit
      simp only [Cond.holds_lt, hz.stackBase_eq, hz.sp_eq, lt_self_iff_false, not_false_eq_true]
    have hunwind := hunwind₁ z 2 hexit
    refine ⟨z, (hs₁.seq hunwind).mono (by omega), ?_, hz.sp_eq, ?_, ?_⟩
    · simp [hz.found_eq, hz.out_eq]
    · apply rep_frame hr
      intro a hlo hhi
      rw [hz.mem_eq]
      exact hframe₁ a (Or.inl (by omega))
    · intro a ha
      rw [hz.mem_eq]
      exact hframe₁ a ha

end Cslib.Algorithms.WordRAM.VanEmdeBoas
