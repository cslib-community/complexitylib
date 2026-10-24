/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.VanEmdeBoas.Elements
public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Init
public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Insert
public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Member
public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Successor
public import Complexity.Computability.WordRAM.Dynamic
public import Complexity.Foundations.Data.OrderedSet
public import Mathlib.Data.Nat.Log

/-!
# Complete native van Emde Boas calls and adaptive dynamic realization

All three operations — `insert` (`tag = 0`), `member` (`tag = 1`), and strict `successor`
(`tag = 2`) — execute on the same fixed 32-register dispatcher `program`, charging constant
setup, dispatch branches, every loop instruction, and the final `halt`.

In addition, this module connects `program` to the shared `Stateful.Spec` / `DynamicProgram` /
`DynamicCertificate` interface on finite sets (`Finset ℕ`) and combines the uniform native
initializer `initProgram` with arbitrary adaptive client histories (`run_initialized`).

## Main definitions

* `setupData`: mathematical description of the twelve charged setup instructions.
* `Operation`, `Operation.Result`, `spec`, `dynamicProgram`, `SetRep`, `certificate`: the
  stateful finite-set specification and its fixed-program Word-RAM realization.

## Main results

* `insert_dispatch_spec`, `insert_call`, `insert_executes`, `insert_executes_generic`,
  `insert_executes_log`: complete native insertion calls in `39 * (d + 1) + 16` instructions.
* `member_dispatch_spec`, `member_call`, `member_executes`, `member_executes_generic`,
  `member_executes_log`: complete native membership calls in `28 * (d + 1) + 18` instructions.
* `successor_dispatch_spec`, `successor_call`, `successor_executes`,
  `successor_executes_generic`, `successor_executes_log`: complete native strict-successor calls
  in `65 * (d + 1) + 22` instructions.
* `instruction_bound`, `instruction_bound_log`, `client_spec`, `run_initialized`: adaptive
  history execution and combined initialization-plus-client execution certificates.

## References

* [P. van Emde Boas, R. Kaas and E. Zijlstra, *Design and implementation of an efficient
  priority queue*][VanEmdeBoasKaasZijlstra1977]
* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.VanEmdeBoas

open Cslib.WordRAM
open Cslib.Algorithms.Lean.VanEmdeBoas

/-- The state after the twelve actual setup instructions. -/
def setupData (s : Data 32) : Data 32 :=
  let a := (((((s.set zero 0).set one 1).set two 2).set three 3).set four 4).set five 5
  let b := (((a.set p (s.regs root)).set x (s.regs arg)).set out 0).set found 0
  (b.set sp (s.regs stackBase)).set runFlag 1

/-- Constant and traversal setup has exactly twelve native instructions. -/
private theorem setup_exec {w : ℕ} {s : Data 32} (hw : Fits w 5) :
    Exec w setup s (setupData s) 12 := by
  have h₁ := hw.of_le (by decide : 1 ≤ 5)
  have h₂ := hw.of_le (by decide : 2 ≤ 5)
  have h₃ := hw.of_le (by decide : 3 ≤ 5)
  have h₄ := hw.of_le (by decide : 4 ≤ 5)
  ram_eval [setup, setupData, hw, h₁, h₂, h₃, h₄]

/-- Setup establishes insertion's entry registers from the caller's root and argument. -/
private theorem setup_insertEntry (s : Data 32) :
    InsertEntry (s.regs root) (s.regs arg) (setupData s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp +decide [setupData]

/-- Setup establishes membership's entry registers from the caller's root and argument. -/
private theorem setup_memberEntry (s : Data 32) :
    MemberEntry (s.regs root) (s.regs arg) (setupData s) := by
  constructor <;> simp +decide [setupData]

/-- Setup establishes strict successor's entry registers from the caller's root, stack base,
and argument. -/
private theorem setup_successorEntry (s : Data 32) :
    SuccessorEntry (s.regs stackBase) (s.regs stackBase) (s.regs root) (s.regs arg)
      (setupData s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp +decide [setupData]

/-- The single compiled program contains 212 ordinary instructions and a final halt. -/
theorem compiled_program_length : (program.program out).length = 213 := by
  simp only [Code.program, List.length_append, Code.length_assemble, program_size,
    List.length_cons, List.length_nil]

/-- Compiling the fixed dispatcher introduces no word-width instruction. -/
theorem compiled_program_not_readsWidth : ¬(program.program out).ReadsWidth :=
  Code.not_readsWidth_program program_not_readsWidth out

/-- The supported double-exponential universe has exactly `d` iterated binary logarithms. -/
theorem log_log_universeSize (d : ℕ) : Nat.log 2 (Nat.log 2 (universeSize d)) = d := by
  simp only [universeSize_eq_two_pow, Nat.log_pow Nat.one_lt_two]

/-! ## Complete native insertion calls -/

/-- A complete insertion dispatch (`tag = 0`), including setup and all control flow but not final
halt, executes in at most `39 * (d + 1) + 15` instructions, updates the represented tree to
`tree.insert key`, leaves `out = 0`, and preserves all memory outside `[base, base + span d)`. -/
theorem insert_dispatch_spec {d w base key : ℕ} {tree : Tree d} {s : Data 32}
    (ht : tree.Valid) (hr : Rep tree base s.mem) (hx : key < universeSize d)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = key) (htag : s.regs tag = 0) :
    ∃ z, ExecWithin w program s z (39 * (d + 1) + 15) ∧
      Rep (tree.insert key) base z.mem ∧
      z.regs out = 0 ∧
      (∀ a, a < base ∨ base + span d ≤ a → z.mem a = s.mem a) := by
  have hw : Fits w 5 := ha.of_le (by have := five_le_span d; omega)
  have hentry : InsertEntry base key (setupData s) := by
    simpa only [hroot, harg] using setup_insertEntry s
  obtain ⟨z, hz, hrep, hframe⟩ :=
    insertLoop_spec hentry ht (by simpa [setupData] using hr) hx ha
  have h₀ : (Cond.eq tag zero).Holds (setupData s) := by
    simp +decide [Cond.holds_eq, setupData, htag]
  have hout : z.regs out = 0 := by
    rw [hz.regs_eq (by decide : insertLoop.Preserves out)]
    simp +decide [setupData]
  refine ⟨z, ?_, hrep, hout, ?_⟩
  · exact ((setup_exec hw).within.seq (ExecWithin.branch_pos h₀ hz)).mono (by omega)
  · intro a ha_out
    simpa only [setupData, Data.set_mem] using hframe a ha_out

/-- A bounded caller invoking insertion (`tag = 0`) obtains a bounded state representing
`tree.insert key`, with unchanged persistent `root` and `stackBase` registers and all memory
outside `[base, base + span d)` preserved. -/
theorem insert_call {d w base key : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hx : key < universeSize d) (ha : Fits w (base + span d))
    (hroot : s.regs root = base) (harg : s.regs arg = key) (htag : s.regs tag = 0) :
    ∃ z n, n + 1 ≤ 39 * (d + 1) + 16 ∧ Exec w program s z n ∧
      z.Bounded w ∧ Rep (tree.insert key) base z.mem ∧
      z.regs root = base ∧ z.regs stackBase = s.regs stackBase ∧
      z.regs out = 0 ∧
      (∀ a, a < base ∨ base + span d ≤ a → z.mem a = s.mem a) := by
  obtain ⟨z, ⟨n, hn, he⟩, hrep, hout, hframe⟩ :=
    insert_dispatch_spec ht hr hx ha hroot harg htag
  refine ⟨z, n, by omega, he, he.bounded hs, hrep, ?_, ?_, hout, hframe⟩
  · exact (he.regs_eq (by decide : program.Preserves root)).trans hroot
  · exact he.regs_eq (by decide : program.Preserves stackBase)

/-- Actual flat bounded-word insertion execution, including its final halt, in
`39 * (d + 1) + 16` instructions. -/
theorem insert_executes {d w base key : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hx : key < universeSize d) (ha : Fits w (base + span d))
    (hroot : s.regs root = base) (harg : s.regs arg = key) (htag : s.regs tag = 0) :
    ∃ n ≤ 39 * (d + 1) + 16,
      Executes w (program.program out) ⟨0, s⟩ 0 n := by
  obtain ⟨z, n, hn, he, _, _, _, _, hout, _⟩ :=
    insert_call hs ht hr hx ha hroot harg htag
  exact ⟨n + 1, hn, hout ▸ he.executes out⟩

/-- Exact transfer of the flat insertion call into the shared generic RAM model. -/
theorem insert_executes_generic {d w base key : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hx : key < universeSize d) (ha : Fits w (base + span d))
    (hroot : s.regs root = base) (harg : s.regs arg = key) (htag : s.regs tag = 0) :
    ∃ n ≤ 39 * (d + 1) + 16,
      GenericRAM.Executes w (program.program out).toGeneric
        ((⟨0, s⟩ : State 32).toGeneric .standard) 0 n := by
  obtain ⟨n, hn, he⟩ := insert_executes hs ht hr hx ha hroot harg htag
  exact ⟨n, hn, executes_toGeneric_iff.mpr he⟩

/-- The charged native insertion bound written directly in terms of the universe size. -/
theorem insert_executes_log {d w base key : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hx : key < universeSize d) (ha : Fits w (base + span d))
    (hroot : s.regs root = base) (harg : s.regs arg = key) (htag : s.regs tag = 0) :
    ∃ n ≤ 39 * (Nat.log 2 (Nat.log 2 (universeSize d)) + 1) + 16,
      Executes w (program.program out) ⟨0, s⟩ 0 n := by
  simpa only [log_log_universeSize] using insert_executes hs ht hr hx ha hroot harg htag

/-! ## Complete native membership calls -/

/-- A complete membership dispatch, including setup and all control flow but not final halt.
No query-universe restriction and no zero-filled outside-memory assumption are imposed. -/
theorem member_dispatch_spec {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (ht : tree.Valid) (hr : Rep tree base s.mem) (ha : Fits w (base + span d))
    (hroot : s.regs root = base) (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ z, ExecWithin w program s z (28 * (d + 1) + 17) ∧
      z.regs out = (if tree.member query then 1 else 0) ∧ z.mem = s.mem := by
  have hw : Fits w 5 := ha.of_le (by have := five_le_span d; omega)
  have hentry : MemberEntry base query (setupData s) := by
    simpa only [hroot, harg] using setup_memberEntry s
  obtain ⟨z, hz, hout, hmem⟩ := memberLoop_spec hentry ht (by simpa [setupData] using hr) ha
  have h₀ : ¬(Cond.eq tag zero).Holds (setupData s) := by
    simp +decide [Cond.holds_eq, setupData, htag]
  have h₁ : (Cond.eq tag one).Holds (setupData s) := by
    simp +decide [Cond.holds_eq, setupData, htag]
  refine ⟨z, ?_, hout, ?_⟩
  · exact ((setup_exec hw).within.seq
      (ExecWithin.branch_neg h₀ (ExecWithin.branch_pos h₁ hz))).mono (by omega)
  · simpa only [setupData, Data.set_mem] using hmem

/-- A bounded caller obtains a bounded result, identical represented memory and an unchanged
persistent root. Its query fits the machine word because every caller register does. -/
theorem member_call {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ z n, n + 1 ≤ 28 * (d + 1) + 18 ∧ Exec w program s z n ∧
      z.Bounded w ∧ Rep tree base z.mem ∧ z.regs root = base ∧
      z.regs out = (if tree.member query then 1 else 0) ∧ z.mem = s.mem := by
  obtain ⟨z, ⟨n, hn, he⟩, hout, hmem⟩ := member_dispatch_spec ht hr ha hroot harg htag
  refine ⟨z, n, by omega, he, he.bounded hs, ?_, ?_, hout, hmem⟩
  · simpa only [hmem] using hr
  · exact (he.regs_eq (by decide : program.Preserves root)).trans hroot

/-- Actual flat bounded-word execution, including its final halt, in `28 (d+1) + 18`
instructions. The selected fixed program has no depth or word-width parameter. -/
theorem member_executes {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ n ≤ 28 * (d + 1) + 18,
      Executes w (program.program out) ⟨0, s⟩ (if tree.member query then 1 else 0) n := by
  obtain ⟨z, n, hn, he, _, _, _, hout, _⟩ := member_call hs ht hr ha hroot harg htag
  exact ⟨n + 1, hn, hout ▸ he.executes out⟩

/-- Exact transfer of the actual flat call into the shared generic RAM model; this adds no
semantic operation or uncharged oracle instruction. -/
theorem member_executes_generic {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ n ≤ 28 * (d + 1) + 18,
      GenericRAM.Executes w (program.program out).toGeneric
        ((⟨0, s⟩ : State 32).toGeneric .standard) (if tree.member query then 1 else 0) n := by
  obtain ⟨n, hn, he⟩ := member_executes hs ht hr ha hroot harg htag
  exact ⟨n, hn, executes_toGeneric_iff.mpr he⟩

/-- The charged native membership bound written directly in terms of the universe size. -/
theorem member_executes_log {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ n ≤ 28 * (Nat.log 2 (Nat.log 2 (universeSize d)) + 1) + 18,
      Executes w (program.program out) ⟨0, s⟩ (if tree.member query then 1 else 0) n := by
  simpa only [log_log_universeSize] using member_executes hs ht hr ha hroot harg htag

/-! ## Complete native strict-successor calls -/

/-- A complete strict-successor dispatch (`tag = 2`), including setup, descent, and stack unwind
but not final halt, executes in at most `65 * (d + 1) + 21` instructions, preserves the
represented tree at `base`, restores `sp = stackBase₀`, and modifies no memory outside the
`4 * d`-word stack region `[stackBase₀, stackBase₀ + 4 * d)`. -/
theorem successor_dispatch_spec {d w base stackBase₀ query : ℕ} {tree : Tree d} {s : Data 32}
    (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    (hroot : s.regs root = base) (hstk : s.regs stackBase = stackBase₀)
    (harg : s.regs arg = query) (htag : s.regs tag = 2) :
    ∃ z, ExecWithin w program s z (65 * (d + 1) + 21) ∧
      (if z.regs found = 0 then none else some (z.regs out)) = tree.successor query ∧
      Rep tree base z.mem ∧
      z.regs sp = stackBase₀ ∧
      (∀ a, a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a → z.mem a = s.mem a) := by
  have hw : Fits w 5 := hstk_fit.of_le (by have := five_le_span d; omega)
  have hentry : SuccessorEntry stackBase₀ stackBase₀ base query (setupData s) := by
    simpa only [hroot, hstk, harg] using setup_successorEntry s
  obtain ⟨z, hz, hans, hsp, hrep, hframe⟩ :=
    successor_loop_spec hentry ht (by simpa [setupData] using hr) hstk_lo hstk_fit
  have h₀ : ¬(Cond.eq tag zero).Holds (setupData s) := by
    simp +decide [Cond.holds_eq, setupData, htag]
  have h₁ : ¬(Cond.eq tag one).Holds (setupData s) := by
    simp +decide [Cond.holds_eq, setupData, htag]
  have hrun : ExecWithin w program s z (65 * (d + 1) + 21) :=
    ((setup_exec hw).within.seq
      (ExecWithin.branch_neg h₀ (ExecWithin.branch_neg h₁ hz))).mono (by omega)
  refine ⟨z, hrun, hans, hrep, hsp, ?_⟩
  intro a ha_out
  simpa only [setupData, Data.set_mem] using hframe a ha_out

/-- A bounded caller invoking strict successor (`tag = 2`) obtains a bounded state with the
exact optional successor encoded by `(found, out)`, unchanged persistent `root` and `stackBase`
registers, preserved tree representation, and unchanged memory outside
`[stackBase₀, stackBase₀ + 4 * d)`. -/
theorem successor_call {d w base stackBase₀ query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    (hroot : s.regs root = base) (hstk : s.regs stackBase = stackBase₀)
    (harg : s.regs arg = query) (htag : s.regs tag = 2) :
    ∃ z n, n + 1 ≤ 65 * (d + 1) + 22 ∧ Exec w program s z n ∧
      z.Bounded w ∧ Rep tree base z.mem ∧
      z.regs root = base ∧ z.regs stackBase = stackBase₀ ∧ z.regs sp = stackBase₀ ∧
      (if z.regs found = 0 then none else some (z.regs out)) = tree.successor query ∧
      (∀ a, a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a → z.mem a = s.mem a) := by
  obtain ⟨z, ⟨n, hn, he⟩, hans, hrep, hsp, hframe⟩ :=
    successor_dispatch_spec ht hr hstk_lo hstk_fit hroot hstk harg htag
  refine ⟨z, n, by omega, he, he.bounded hs, hrep, ?_, ?_, hsp, hans, hframe⟩
  · exact (he.regs_eq (by decide : program.Preserves root)).trans hroot
  · exact (he.regs_eq (by decide : program.Preserves stackBase)).trans hstk

/-- Actual flat bounded-word strict-successor execution, including its final halt, in
`65 * (d + 1) + 22` instructions. -/
theorem successor_executes {d w base stackBase₀ query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    (hroot : s.regs root = base) (hstk : s.regs stackBase = stackBase₀)
    (harg : s.regs arg = query) (htag : s.regs tag = 2) :
    ∃ (z : Data 32) (n : ℕ), n ≤ 65 * (d + 1) + 22 ∧
      Executes w (program.program out) ⟨0, s⟩ (z.regs out) n ∧
      (if z.regs found = 0 then none else some (z.regs out)) = tree.successor query ∧
      Rep tree base z.mem ∧
      (∀ a, a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a → z.mem a = s.mem a) := by
  obtain ⟨z, n, hn, he, _, hrep, _, _, _, hans, hframe⟩ :=
    successor_call hs ht hr hstk_lo hstk_fit hroot hstk harg htag
  exact ⟨z, n + 1, hn, he.executes out, hans, hrep, hframe⟩

/-- Exact transfer of the flat strict-successor call into the shared generic RAM model. -/
theorem successor_executes_generic {d w base stackBase₀ query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    (hroot : s.regs root = base) (hstk : s.regs stackBase = stackBase₀)
    (harg : s.regs arg = query) (htag : s.regs tag = 2) :
    ∃ (z : Data 32) (n : ℕ), n ≤ 65 * (d + 1) + 22 ∧
      GenericRAM.Executes w (program.program out).toGeneric
        ((⟨0, s⟩ : State 32).toGeneric .standard) (z.regs out) n ∧
      (if z.regs found = 0 then none else some (z.regs out)) = tree.successor query ∧
      Rep tree base z.mem ∧
      (∀ a, a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a → z.mem a = s.mem a) := by
  obtain ⟨z, n, hn, he, hans, hrep, hframe⟩ :=
    successor_executes hs ht hr hstk_lo hstk_fit hroot hstk harg htag
  exact ⟨z, n, hn, executes_toGeneric_iff.mpr he, hans, hrep, hframe⟩

/-- The charged native strict-successor bound written directly in terms of the universe size. -/
theorem successor_executes_log {d w base stackBase₀ query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    (hroot : s.regs root = base) (hstk : s.regs stackBase = stackBase₀)
    (harg : s.regs arg = query) (htag : s.regs tag = 2) :
    ∃ (z : Data 32) (n : ℕ), n ≤ 65 * (Nat.log 2 (Nat.log 2 (universeSize d)) + 1) + 22 ∧
      Executes w (program.program out) ⟨0, s⟩ (z.regs out) n ∧
      (if z.regs found = 0 then none else some (z.regs out)) = tree.successor query ∧
      Rep tree base z.mem ∧
      (∀ a, a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a → z.mem a = s.mem a) := by
  simpa only [log_log_universeSize] using
    successor_executes hs ht hr hstk_lo hstk_fit hroot hstk harg htag

/-! ## Finite-set `Stateful.Spec` and `DynamicCertificate` realization -/

/-- `Tree.successor` on a valid tree computes the mathematical `OrderedSet.least` of the stored
elements strictly greater than the query. -/
private theorem successor_eq_least {d : ℕ} {t : Tree d} (ht : t.Valid) (q : ℕ) :
    t.successor q = OrderedSet.least (t.elements.filter (q < ·)) := by
  apply OrderedSet.LeastResult.eq_least
  cases hs : t.successor q with
  | none =>
    simp only [OrderedSet.LeastResult, Finset.filter_eq_empty_iff]
    have hnone := (Tree.successor_elements_none_iff ht q).mp hs
    intro z hz
    have := hnone z hz
    omega
  | some y =>
    simp only [OrderedSet.LeastResult, Finset.mem_filter]
    have hsome := (Tree.successor_elements_some_iff ht q y).mp hs
    exact ⟨⟨hsome.1, hsome.2.1⟩, fun z hz => hsome.2.2 z hz.1 hz.2⟩

/-- Dynamic ordered-set operations supported by the van Emde Boas dispatcher. -/
inductive Operation where
  /-- Insert a bounded universe key into the set. -/
  | insert (key : ℕ)
  /-- Query whether a fitting word belongs to the set. -/
  | member (query : ℕ)
  /-- Return the least stored key strictly greater than a fitting query, if any. -/
  | successor (query : ℕ)
  deriving DecidableEq, Repr

/-- Typed observation returned by each van Emde Boas operation. -/
def Operation.Result : Operation → Type
  | .insert _ => PUnit
  | .member _ => Bool
  | .successor _ => Option ℕ

/-- Abstract finite-set specification on the universe `[0, universeSize d)`. -/
def spec (d w : ℕ) : Stateful.Spec where
  State := Finset ℕ
  Op := Operation
  Result := Operation.Result
  step s
    | .insert k => (Insert.insert k s, PUnit.unit)
    | .member q => (s, decide (q ∈ s))
    | .successor q => (s, OrderedSet.least (s.filter (q < ·)))
  valid _
    | .insert k => k < universeSize d
    | .member q => Fits w q
    | .successor q => Fits w q

/-- The single fixed dispatcher `program` packaged as a `DynamicProgram` with a register-only
calling convention (`tag` and `arg`). -/
def dynamicProgram (d w : ℕ) : DynamicProgram (spec d w) 32 where
  code := program
  output := out
  input j := j == tag || j == arg
  encode o j := match o with
    | .insert k => if j = tag then 0 else k
    | .member q => if j = tag then 1 else q
    | .successor q => if j = tag then 2 else q
  decode o regs := match o with
    | .insert _ => some PUnit.unit
    | .member _ => some (regs out != 0)
    | .successor _ => some (if regs found = 0 then none else some (regs out))

/-- Persistent machine representation of an abstract finite set `s : Finset ℕ` by a valid tree
at `base` and scratch stack pointer at `stackBase₀`. -/
structure SetRep (d base stackBase₀ w : ℕ) (s : Finset ℕ) (x : Data 32) : Prop where
  bounded : x.Bounded w
  root_eq : x.regs root = base
  stackBase_eq : x.regs stackBase = stackBase₀
  tree : ∃ t : Tree d, t.Valid ∧ t.elements = s ∧ Rep t base x.mem

/-- Every encoded argument of a valid van Emde Boas operation fits the machine word width. -/
theorem arguments_fit {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    {s : Finset ℕ} (o : Operation) (ho : (spec d w).valid s o) (j : Fin 32) :
    Fits w ((dynamicProgram d w).encode o j) := by
  have h5_le := five_le_span d
  have hu_le := universeSize_le_span d
  have h0 : Fits w 0 := hstk_fit.of_le (by omega)
  have h1 : Fits w 1 := hstk_fit.of_le (by omega)
  have h2 : Fits w 2 := hstk_fit.of_le (by omega)
  cases o with
  | insert k =>
    have hk : Fits w k := hstk_fit.of_le (by dsimp only [spec] at ho; omega)
    simp only [dynamicProgram]
    split
    · exact h0
    · exact hk
  | member q =>
    simp only [dynamicProgram]
    split
    · exact h1
    · exact ho
  | successor q =>
    simp only [dynamicProgram]
    split
    · exact h2
    · exact ho

/-- Unified per-operation dispatch theorem for `(dynamicProgram d w)`: every admissible operation
executes in at most `65 * (d + 1) + 21` structured instructions, produces the decoded abstract
observation, preserves `SetRep`, and modifies no memory outside
`[base, base + span d) ∪ [stackBase₀, stackBase₀ + 4 * d)`. -/
theorem dispatch_spec {d w base stackBase₀ : ℕ} {s : Finset ℕ} {x : Data 32}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    (o : Operation) (hx : SetRep d base stackBase₀ w s x) (ho : (spec d w).valid s o) :
    ∃ y, ExecWithin w program ((dynamicProgram d w).prepare o x) y (65 * (d + 1) + 21) ∧
      (dynamicProgram d w).decode o y.regs = some ((spec d w).step s o).2 ∧
      SetRep d base stackBase₀ w ((spec d w).step s o).1 y ∧
      (∀ a, (a < base ∨ base + span d ≤ a) →
        (a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a) → y.mem a = x.mem a) := by
  obtain ⟨t, hvalid, helem, hrep⟩ := hx.tree
  have ha : Fits w (base + span d) := hstk_fit.of_le (by omega)
  have hprep_bounded : ((dynamicProgram d w).prepare o x).Bounded w :=
    (dynamicProgram d w).prepare_bounded hx.bounded
      (fun j _ => arguments_fit hstk_lo hstk_fit o ho j)
  have hprep_root : ((dynamicProgram d w).prepare o x).regs root = base := by
    simpa +decide [dynamicProgram, DynamicProgram.prepare] using hx.root_eq
  have hprep_stk : ((dynamicProgram d w).prepare o x).regs stackBase = stackBase₀ := by
    simpa +decide [dynamicProgram, DynamicProgram.prepare] using hx.stackBase_eq
  have hprep_rep : Rep t base ((dynamicProgram d w).prepare o x).mem := hrep
  cases o with
  | insert k =>
    have hprep_arg : ((dynamicProgram d w).prepare (.insert k) x).regs arg = k := by
      simp +decide [dynamicProgram, DynamicProgram.prepare]
    have hprep_tag : ((dynamicProgram d w).prepare (.insert k) x).regs tag = 0 := by
      simp +decide [dynamicProgram, DynamicProgram.prepare]
    obtain ⟨y, hy, hy_rep, _, hy_frame⟩ :=
      insert_dispatch_spec hvalid hprep_rep ho ha hprep_root hprep_arg hprep_tag
    have hrun := hy.mono (by omega : 39 * (d + 1) + 15 ≤ 65 * (d + 1) + 21)
    have hy_root : y.regs root = base :=
      (hrun.regs_eq (by decide : program.Preserves root)).trans hprep_root
    have hy_stk : y.regs stackBase = stackBase₀ :=
      (hrun.regs_eq (by decide : program.Preserves stackBase)).trans hprep_stk
    refine ⟨y, hrun, rfl,
      ⟨hrun.bounded hprep_bounded, hy_root, hy_stk,
        t.insert k, Tree.valid_insert hvalid ho, ?_, hy_rep⟩, ?_⟩
    · rw [Tree.elements_insert hvalid ho, helem]; rfl
    · intro a ha_tree _
      exact hy_frame a ha_tree
  | member q =>
    have hprep_arg : ((dynamicProgram d w).prepare (.member q) x).regs arg = q := by
      simp +decide [dynamicProgram, DynamicProgram.prepare]
    have hprep_tag : ((dynamicProgram d w).prepare (.member q) x).regs tag = 1 := by
      simp +decide [dynamicProgram, DynamicProgram.prepare]
    obtain ⟨y, hy, hy_out, hy_mem⟩ :=
      member_dispatch_spec hvalid hprep_rep ha hprep_root hprep_arg hprep_tag
    have hrun := hy.mono (by omega : 28 * (d + 1) + 17 ≤ 65 * (d + 1) + 21)
    have hy_root : y.regs root = base :=
      (hrun.regs_eq (by decide : program.Preserves root)).trans hprep_root
    have hy_stk : y.regs stackBase = stackBase₀ :=
      (hrun.regs_eq (by decide : program.Preserves stackBase)).trans hprep_stk
    refine ⟨y, hrun, ?_,
      ⟨hrun.bounded hprep_bounded, hy_root, hy_stk, t, hvalid, helem, ?_⟩, ?_⟩
    · simp only [dynamicProgram, spec, hy_out, ← helem]
      congr 1
      have hiff := (Tree.mem_elements_iff hvalid q).trans (Tree.member_iff_contains hvalid q).symm
      cases hmem : t.member q <;> simp_all <;> rfl
    · simpa only [hy_mem] using hprep_rep
    · intro a _ _
      exact congrFun hy_mem a
  | successor q =>
    have hprep_arg : ((dynamicProgram d w).prepare (.successor q) x).regs arg = q := by
      simp +decide [dynamicProgram, DynamicProgram.prepare]
    have hprep_tag : ((dynamicProgram d w).prepare (.successor q) x).regs tag = 2 := by
      simp +decide [dynamicProgram, DynamicProgram.prepare]
    obtain ⟨y, hy, hy_ans, hy_rep, _, hy_frame⟩ :=
      successor_dispatch_spec hvalid hprep_rep hstk_lo hstk_fit
        hprep_root hprep_stk hprep_arg hprep_tag
    have hy_root : y.regs root = base :=
      (hy.regs_eq (by decide : program.Preserves root)).trans hprep_root
    have hy_stk : y.regs stackBase = stackBase₀ :=
      (hy.regs_eq (by decide : program.Preserves stackBase)).trans hprep_stk
    refine ⟨y, hy, ?_,
      ⟨hy.bounded hprep_bounded, hy_root, hy_stk, t, hvalid, helem, hy_rep⟩, ?_⟩
    · change some (if y.regs found = 0 then none else some (y.regs out)) =
        some (OrderedSet.least (s.filter (q < ·)))
      rw [hy_ans, successor_eq_least hvalid q, helem]
    · intro a _ ha_stk
      exact hy_frame a ha_stk

/-- Semantic correctness and totality certificate for the fixed bounded-word van Emde Boas
implementation. -/
def certificate {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d)) :
    DynamicCertificate (dynamicProgram d w) w where
  rep := SetRep d base stackBase₀ w
  bounded := SetRep.bounded
  arguments_fit o ho j _ := arguments_fit hstk_lo hstk_fit o ho j
  execute o hx ho := by
    obtain ⟨y, ⟨n, _, he⟩, hans, hy, _⟩ := dispatch_spec hstk_lo hstk_fit o hx ho
    exact ⟨y, n, he, hans, hy⟩

/-- Separate worst-case per-operation instruction certificate, counting the final halt:
every admissible `insert`, `member`, or `successor` call executes in at most `65 * (d + 1) + 22`
instructions. -/
theorem instruction_bound {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d)) :
    Stateful.Bound (certificate hstk_lo hstk_fit).realization
      DynamicProgram.OperationTrace.instructions (fun _ _ => 65 * (d + 1) + 22) := by
  apply (certificate hstk_lo hstk_fit).instruction_bound_const
  intro s x o hx ho
  obtain ⟨z, ⟨k, hk, he'⟩, _, _⟩ := dispatch_spec hstk_lo hstk_fit o hx ho
  exact ⟨z, k, he', by omega⟩

/-- The per-operation instruction certificate written in terms of the universe size. -/
theorem instruction_bound_log {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d)) :
    Stateful.Bound (certificate hstk_lo hstk_fit).realization
      DynamicProgram.OperationTrace.instructions
      (fun _ _ => 65 * (Nat.log 2 (Nat.log 2 (universeSize d)) + 1) + 22) := by
  rw [log_log_universeSize]
  exact instruction_bound hstk_lo hstk_fit

/-- Every actual call preserves memory outside the tree region `[base, base + span d)` and
the scratch stack `[stackBase₀, stackBase₀ + 4 * d)`. -/
theorem execOp_frame {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    {s : Finset ℕ} {o : Operation} {x y : Data 32} {a : (spec d w).Result o}
    {trace : DynamicProgram.OperationTrace}
    (hx : SetRep d base stackBase₀ w s x) (ho : (spec d w).valid s o)
    (he : (dynamicProgram d w).ExecOp w x o a y trace) {j : ℕ}
    (hj_tree : j < base ∨ base + span d ≤ j)
    (hj_stk : j < stackBase₀ ∨ stackBase₀ + 4 * d ≤ j) : y.mem j = x.mem j := by
  obtain ⟨z, ⟨_, _, hk⟩, _, _, hf⟩ := dispatch_spec hstk_lo hstk_fit o hx ho
  exact (he.eq_of_exec hk).1 ▸ hf j hj_tree hj_stk

/-- Every admissible adaptive client execution preserves memory outside the tree and stack
regions across the entire interaction history. -/
theorem executes_client_frame {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    {α : Type} {p : (spec d w).Client α} {s : Finset ℕ} {x y : Data 32} {val : α}
    {traces : List DynamicProgram.OperationTrace}
    (hx : SetRep d base stackBase₀ w s x)
    (hv : (spec d w).ValidHistory s ((spec d w).runClient s p).2.2)
    (he : Stateful.Executes ((dynamicProgram d w).ExecOp w) p x val y traces) {j : ℕ}
    (hj_tree : j < base ∨ base + span d ≤ j)
    (hj_stk : j < stackBase₀ ∨ stackBase₀ + 4 * d ≤ j) : y.mem j = x.mem j :=
  (certificate hstk_lo hstk_fit).executes_client_frame
    (fun hx' ho' he' => execOp_frame hstk_lo hstk_fit hx' ho' he' hj_tree hj_stk) hx hv he

/-- Every admissible adaptive client has a concrete execution with the specified answers and
final finite set, at most `65 * (d + 1) + 22` instructions per operation, and unchanged memory
outside the tree and stack regions. -/
theorem client_spec {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    {α : Type} (p : (spec d w).Client α) {s : Finset ℕ} {x : Data 32}
    (hx : SetRep d base stackBase₀ w s x)
    (hv : (spec d w).ValidHistory s ((spec d w).runClient s p).2.2) :
    ∃ y traces, Stateful.Executes ((dynamicProgram d w).ExecOp w) p x
        ((spec d w).runClient s p).1 y traces ∧
      SetRep d base stackBase₀ w ((spec d w).runClient s p).2.1 y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤
        ((spec d w).runClient s p).2.2.length * (65 * (d + 1) + 22) ∧
      (∀ j, (j < base ∨ base + span d ≤ j) →
        (j < stackBase₀ ∨ stackBase₀ + 4 * d ≤ j) → y.mem j = x.mem j) := by
  obtain ⟨y, traces, he, hr, hcost⟩ :=
    (certificate hstk_lo hstk_fit).run_client_const (instruction_bound hstk_lo hstk_fit) p hx hv
  exact ⟨y, traces, he, hr, hcost, fun j hjt hjs =>
    executes_client_frame hstk_lo hstk_fit hx hv he hjt hjs⟩

/-- Combined native initialization and adaptive client execution: starting from any bounded
machine state `s₀` with `s₀.regs root = base`, `s₀.regs depth = d`, and
`Fits w (base + span d + 4 * (d + 1))` (with arbitrary initial memory), `initProgram` executes
in at most `8 * span d + 20 * d + 25` instructions to produce an empty represented set `x₀`,
from which any admissible adaptive client `p` executes to `y` with at most `65 * (d + 1) + 22`
instructions per operation and no memory modified outside `[base, base + span d + 4 * (d + 1))`.
-/
theorem run_initialized {d w base : ℕ} {s₀ : Data 32}
    (hs₀ : s₀.Bounded w) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hroot : s₀.regs root = base) (hdepth : s₀.regs depth = d)
    {α : Type} (p : (spec d w).Client α)
    (hv : (spec d w).ValidHistory (∅ : Finset ℕ) ((spec d w).runClient (∅ : Finset ℕ) p).2.2) :
    ∃ x₀ n_init y traces,
      n_init + 1 ≤ 8 * span d + 20 * d + 25 ∧
      Exec w initProgram s₀ x₀ n_init ∧
      SetRep d base (base + span d) w (∅ : Finset ℕ) x₀ ∧
      Stateful.Executes ((dynamicProgram d w).ExecOp w) p x₀
        ((spec d w).runClient (∅ : Finset ℕ) p).1 y traces ∧
      SetRep d base (base + span d) w ((spec d w).runClient (∅ : Finset ℕ) p).2.1 y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤
        ((spec d w).runClient (∅ : Finset ℕ) p).2.2.length * (65 * (d + 1) + 22) ∧
      (∀ j, j < base ∨ base + span d + 4 * (d + 1) ≤ j → y.mem j = s₀.mem j) := by
  obtain ⟨x₀, n_init, hn_init, he_init, hbounded₀, hrep₀, hroot₀, hstk₀, _, hframe₀⟩ :=
    init_call hs₀ ha hroot hdepth
  have hx₀ : SetRep d base (base + span d) w (∅ : Finset ℕ) x₀ :=
    ⟨hbounded₀, hroot₀, hstk₀, Tree.empty d, Tree.valid_empty d, Tree.elements_empty d, hrep₀⟩
  have hstk_fit : Fits w (base + span d + 4 * d) := ha.of_le (by omega)
  obtain ⟨y, traces, he_client, hy, hcost, hframe_client⟩ :=
    client_spec le_rfl hstk_fit p hx₀ hv
  refine ⟨x₀, n_init, y, traces, hn_init, he_init, hx₀, he_client, hy, hcost, ?_⟩
  intro j hj
  rw [hframe_client j (by omega) (by omega), hframe₀ j hj]

end Cslib.Algorithms.WordRAM.VanEmdeBoas
