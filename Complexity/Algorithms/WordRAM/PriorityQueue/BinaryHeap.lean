/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PriorityQueue.BinaryHeap.Sift

/-!
# Standalone Word-RAM Indexed Binary Min-Heap

This file proves the full `SubroutineDS` and `PQPackage` specifications for the standalone
word-RAM indexed binary min-heap (`Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.pqCode`) over
`Basis.exact`, and projects it via `Basis.Simulates.exactStandard` to standalone `.standard`-basis
`DynamicProgram`, `DynamicCertificate`, `Stateful.Bound`, and adaptive-client theorems.

The heap uses `space n = 3 * n + 1` words at any base address `base` with `Fits w (base + space n)`
and `Fits w K_max`:
* `initFresh` runs in `O(1)` (`11` instructions);
* `initClear` runs in `O(n)` (`12 * n + 21` instructions, derived generically via `SubroutineDS`);
* `isEmpty` and `getKey` run in `O(1)` worst-case instructions;
* `insert`, `decreaseKey`, and `extractMin` run in `O(log n + 1)` worst-case instructions with zero
  potential (`potential = 0`).

## Main definitions

* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.Rep`: concrete representation invariant.
* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.subroutineDS`: exact-basis `SubroutineDS`
  certificate.
* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.pkg`: `PQPackage .exact rBin` bundle for
  black-box algorithm callers such as `dijkstra_of_pq_spec`.
* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.dynamicProgram`,
  `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.certificate`: standalone `.standard`-basis
  machine realization.

## Main results

* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.instruction_bound`: worst-case per-operation
  `Stateful.Bound` over `Basis.standard`.
* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.run_client_bound`: worst-case total instruction
  bound for any adaptive `Stateful.Client` program.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Reg

/-- Concrete representation invariant of the standalone binary heap at `base` on `n` handles. -/
structure Rep (n w base : ℕ) (s : IndexedMinPQ.State n) (x : Data rBin) : Prop where
  /-- All registers and memory cells fit in `w`-bit words. -/
  bounded : x.Bounded w
  /-- Persistent base-address register `baseReg = base`. -/
  reg_base : x.regs baseReg = base
  /-- Persistent handle-count register `nReg = n`. -/
  reg_n : x.regs nReg = n
  /-- Persistent heap-array base `hb = base + n`. -/
  reg_hb : x.regs hb = base + n
  /-- Persistent position-array base `pb = base + 2 * n + 1`. -/
  reg_pb : x.regs pb = base + 2 * n + 1
  /-- Structural and lexicographic binary-heap invariant on `x.mem`. -/
  heap : HeapInv n base (x.regs sz) x.mem
  /-- Abstract state `s` matches `stateOfMem n base x.mem`. -/
  state_eq : s = stateOfMem n base x.mem

/-- Worst-case instruction bound for `isEmpty`. -/
abbrev tEmpty (_ : ℕ) : ℕ := 10
/-- Worst-case instruction bound for `getKey`. -/
abbrev tGet (_ : ℕ) : ℕ := 14
/-- Worst-case instruction bound for `insert`. -/
abbrev tIns (n : ℕ) : ℕ := 28 * Nat.log 2 n + 20
/-- Worst-case instruction bound for `decreaseKey`. -/
abbrev tDec (n : ℕ) : ℕ := 28 * Nat.log 2 n + 16
/-- Worst-case instruction bound for `extractMin`. -/
abbrev tExt (n : ℕ) : ℕ := 46 * Nat.log 2 n + 28

/-- Per-operation worst-case instruction charge (excluding standalone trailing `halt`). -/
def charge (n : ℕ) : IndexedMinPQ.Op n → ℕ
  | .isEmpty => tEmpty n
  | .getKey _ => tGet n
  | .insert _ _ => tIns n
  | .decreaseKey _ _ => tDec n
  | .extractMin => tExt n

section OpSpecs

variable {n K_max w base : ℕ}

private theorem allocSpan_spec (hS : Fits w (base + space n)) {x : Data rBin}
    (hfr : x.regs frontierReg = base) (hn : x.regs nReg = n) :
    ∃ x₁, ExecWithin w allocSpan x x₁ 6 ∧ x₁.mem = x.mem ∧
      x₁.regs baseReg = base ∧ x₁.regs frontierReg = base + space n ∧ x₁.regs nReg = n := by
  have hsp : space n = 3 * n + 1 := rfl
  have f₁ : Fits w 1 := hS.of_le (by omega)
  have f₂ : Fits w (base + n) := hS.of_le (by omega)
  have f₃ : Fits w (base + n + n) := hS.of_le (by omega)
  have f₄ : Fits w (base + n + n + 1) := hS.of_le (by omega)
  have f₅ : Fits w (base + n + n + 1 + n) := hS.of_le (by omega)
  refine ⟨?z, ?e, ?_, ?_, ?_, ?_⟩
  case e => ram_exact_eval [allocSpan, hfr, hn, f₁, f₂, f₃, f₄, f₅]
  · rfl
  · simp +decide
  · simp +decide only [Data.set_regs, Function.update_self, space]; omega
  · simp +decide [hn]

private theorem initSetup_spec (hS : Fits w (base + space n)) {x₁ : Data rBin}
    (hx₁ : x₁.Bounded w) (hbase : x₁.regs baseReg = base)
    (hfr : x₁.regs frontierReg = base + space n) (hn : x₁.regs nReg = n)
    (hz : ∀ a ∈ (Block.mk base (space n)).footprint, x₁.mem a = 0) :
    ∃ y, ExecWithin w initSetup x₁ y 5 ∧ y.regs frontierReg = base + space n ∧
      Rep n w base (IndexedMinPQ.empty n) y ∧
      Modifies (Block.mk base (space n)).footprint x₁.mem y.mem := by
  have hsp : space n = 3 * n + 1 := rfl
  have f₀ : Fits w 0 := hS.of_le (Nat.zero_le _)
  have f₁ : Fits w 1 := hS.of_le (by omega)
  have f₂ : Fits w (base + n) := hS.of_le (by omega)
  have f₃ : Fits w (base + n + n) := hS.of_le (by omega)
  have f₄ : Fits w (base + n + n + 1) := hS.of_le (by omega)
  obtain ⟨y, he, hym, hfr', hbase', hn', hhb', hpb', hsz'⟩ :
      ∃ y, ExecWithin w initSetup x₁ y 5 ∧ y.mem = x₁.mem ∧
        y.regs frontierReg = base + space n ∧ y.regs baseReg = base ∧
        y.regs nReg = n ∧ y.regs hb = base + n ∧ y.regs pb = base + 2 * n + 1 ∧
        y.regs sz = 0 := by
    refine ⟨?z, ?e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case e => ram_exact_eval [initSetup, hbase, hn, f₀, f₁, f₂, f₃, f₄]
    · rfl
    · simp +decide [hfr]
    · simp +decide [hbase]
    · simp +decide [hn]
    · simp +decide
    · simp +decide only [Data.set_regs, ne_eq, Function.update_of_ne, Function.update_self]; omega
    · simp +decide
  have hpos0 : ∀ v < n, y.mem (base + 2 * n + 1 + v) = 0 := by
    intro v hv
    rw [hym]
    exact hz _ (by rw [Block.mem_footprint]; dsimp only [Block.Owns, space]; omega)
  have hshape : HeapShape n base 0 y.mem :=
    ⟨Nat.zero_le _, fun _ h1 h2 => absurd h2 (by omega), fun _ h1 h2 => absurd h2 (by omega),
      fun v hv => by rw [hpos0 v hv], fun v hv hp => absurd (hpos0 v hv) hp⟩
  have hinv : HeapInv n base (y.regs sz) y.mem := by
    rw [hsz']
    exact ⟨hshape, fun _ h1 h2 => absurd h2 (by omega)⟩
  refine ⟨y, he, hfr', ⟨he.bounded hx₁, hbase', hn', hhb', hpb', hinv,
    hshape.stateOfMem_zero.symm⟩, ?_⟩
  rw [hym]
  exact Modifies.refl _ _

private theorem doIsEmpty_spec {s : IndexedMinPQ.State n} {x : Data rBin}
    (hr : Rep n w base s x) (hz0 : x.regs zero = 0) (ho1 : x.regs one = 1) :
    ∃ y, ExecWithin w doIsEmpty x y 3 ∧
      pqCode.decode (K_max := K_max) .isEmpty y.regs =
        some ((IndexedMinPQ.spec n K_max).step s .isEmpty).2 ∧
      Rep n w base s y ∧ y.mem = x.mem := by
  by_cases hS : x.regs sz = 0
  · obtain ⟨y, he, hyf, hym, hyr⟩ : ∃ y, ExecWithin w doIsEmpty x y 3 ∧
        y.regs outFlag = 1 ∧ y.mem = x.mem ∧ ∀ i, i ≠ outFlag → y.regs i = x.regs i := by
      refine ⟨?z₁, ?e₁, ?_, ?_, ?_⟩
      case e₁ => ram_exact_eval [doIsEmpty, hS, hz0, ho1]
      · simp +decide
      · rfl
      · intro i hi; simp [hi]
    have hdom : IndexedMinPQ.dom s = ∅ := hr.state_eq ▸ (hr.heap.size_eq_zero_iff.mp hS)
    refine ⟨y, he, ?_, ⟨he.bounded hr.bounded, (hyr _ (by decide)).trans hr.reg_base,
      (hyr _ (by decide)).trans hr.reg_n, (hyr _ (by decide)).trans hr.reg_hb,
      (hyr _ (by decide)).trans hr.reg_pb, ?_, hym ▸ hr.state_eq⟩, hym⟩
    · simp only [pqCode, PQCode.decode, IndexedMinPQ.spec, hyf, hdom, ne_eq, one_ne_zero,
        not_false_eq_true, decide_true]
    · rw [hyr sz (by decide), hym]; exact hr.heap
  · obtain ⟨y, he, hyf, hym, hyr⟩ : ∃ y, ExecWithin w doIsEmpty x y 3 ∧
        y.regs outFlag = 0 ∧ y.mem = x.mem ∧ ∀ i, i ≠ outFlag → y.regs i = x.regs i := by
      refine ⟨?z₂, ?e₂, ?_, ?_, ?_⟩
      case e₂ => ram_exact_eval [doIsEmpty, hS, hz0]
      · simp +decide
      · rfl
      · intro i hi; simp [hi]
    have hdom : IndexedMinPQ.dom s ≠ ∅ :=
      fun hd => hS (hr.heap.size_eq_zero_iff.mpr (hr.state_eq ▸ hd))
    refine ⟨y, he, ?_, ⟨he.bounded hr.bounded, (hyr _ (by decide)).trans hr.reg_base,
      (hyr _ (by decide)).trans hr.reg_n, (hyr _ (by decide)).trans hr.reg_hb,
      (hyr _ (by decide)).trans hr.reg_pb, ?_, hym ▸ hr.state_eq⟩, hym⟩
    · simp only [pqCode, PQCode.decode, IndexedMinPQ.spec, hyf, hdom, ne_eq, not_true_eq_false,
        decide_false]
    · rw [hyr sz (by decide), hym]; exact hr.heap

private theorem doGetKey_spec (hS : Fits w (base + space n)) {s : IndexedMinPQ.State n}
    {x : Data rBin} (hr : Rep n w base s x) (hz0 : x.regs zero = 0) (ho1 : x.regs one = 1)
    {v : Fin n} (hv_reg : x.regs argV = v.val) :
    ∃ y, ExecWithin w doGetKey x y 7 ∧
      pqCode.decode (K_max := K_max) (.getKey v) y.regs =
        some ((IndexedMinPQ.spec n K_max).step s (.getKey v)).2 ∧
      Rep n w base s y ∧ y.mem = x.mem := by
  have hsp : space n = 3 * n + 1 := rfl
  have hv_lt := v.isLt
  have f₁ : Fits w (base + 2 * n + 1 + v.val) := hS.of_le (by omega)
  have f₂ : Fits w (base + v.val) := hS.of_le (by omega)
  by_cases hp0 : x.mem (base + 2 * n + 1 + v.val) = 0
  · obtain ⟨y, he, hyf, hym, hyr⟩ : ∃ y, ExecWithin w doGetKey x y 7 ∧
        y.regs outFlag = 0 ∧ y.mem = x.mem ∧
        ∀ i ∉ [t, p, outFlag], y.regs i = x.regs i := by
      refine ⟨?z₁, ?e₁, ?_, ?_, ?_⟩
      case e₁ => ram_exact_eval [doGetKey, hr.reg_pb, hv_reg, hp0, hz0, f₁]
      · simp +decide
      · rfl
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        simp [hi.1, hi.2.1, hi.2.2]
    refine ⟨y, he, ?_, ⟨he.bounded hr.bounded, (hyr _ (by decide)).trans hr.reg_base,
      (hyr _ (by decide)).trans hr.reg_n, (hyr _ (by decide)).trans hr.reg_hb,
      (hyr _ (by decide)).trans hr.reg_pb, ?_, hym ▸ hr.state_eq⟩, hym⟩
    · simp only [pqCode, PQCode.decode, IndexedMinPQ.spec, hyf, ↓reduceIte, hr.state_eq,
        stateOfMem, hp0]
    · rw [hyr sz (by decide), hym]; exact hr.heap
  · obtain ⟨y, he, hyf, hyk, hym, hyr⟩ : ∃ y, ExecWithin w doGetKey x y 7 ∧
        y.regs outFlag = 1 ∧ y.regs outK = x.mem (base + v.val) ∧ y.mem = x.mem ∧
        ∀ i ∉ [t, p, outFlag, outK], y.regs i = x.regs i := by
      refine ⟨?z₂, ?e₂, ?_, ?_, ?_, ?_⟩
      case e₂ =>
        ram_exact_eval [doGetKey, hr.reg_base, hr.reg_pb, hv_reg, hp0, hz0, ho1, f₁, f₂]
      · simp +decide
      · simp +decide
      · rfl
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        simp [hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]
    refine ⟨y, he, ?_, ⟨he.bounded hr.bounded, (hyr _ (by decide)).trans hr.reg_base,
      (hyr _ (by decide)).trans hr.reg_n, (hyr _ (by decide)).trans hr.reg_hb,
      (hyr _ (by decide)).trans hr.reg_pb, ?_, hym ▸ hr.state_eq⟩, hym⟩
    · simp only [pqCode, PQCode.decode, IndexedMinPQ.spec, hyf, one_ne_zero, ↓reduceIte, hyk,
        hr.state_eq, stateOfMem, hp0]
    · rw [hyr sz (by decide), hym]; exact hr.heap

private def insertHead : Code .exact rBin := ram_exact[
  t ← baseReg + argV; *t ← argK;
  sz ← sz + one;
  t ← hb + sz; *t ← argV;
  t ← pb + argV; *t ← sz;
  k ← sz ]

private theorem doInsert_eq : doInsert = appendCode insertHead siftUp := rfl

private theorem doInsert_spec (hS : Fits w (base + space n)) {s : IndexedMinPQ.State n}
    {x : Data rBin} (hr : Rep n w base s x) (hz0 : x.regs zero = 0) (ho1 : x.regs one = 1)
    {v : Fin n} {keyVal : ℕ} (hv_abs : v ∉ IndexedMinPQ.dom s)
    (hv_reg : x.regs argV = v.val) (hk_reg : x.regs argK = keyVal) :
    ∃ y, ExecWithin w doInsert x y (28 * Nat.log 2 n + 10) ∧
      Rep n w base (Function.update s v (some keyVal)) y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem := by
  have hsp : space n = 3 * n + 1 := rfl
  have hv_lt := v.isLt
  have hp0 : x.mem (base + 2 * n + 1 + v.val) = 0 := by
    have hnone := IndexedMinPQ.notMem_dom_iff.mp hv_abs
    rw [hr.state_eq, stateOfMem] at hnone
    by_contra hp
    simp only [hp, ↓reduceIte, reduceCtorEq] at hnone
  obtain ⟨S, hsz_eq⟩ : ∃ S, x.regs sz = S := ⟨_, rfl⟩
  have hheap : HeapInv n base S x.mem := hsz_eq ▸ hr.heap
  have hSn : S < n := hheap.size_lt hv_lt hp0
  have f₁ : Fits w (base + v.val) := hS.of_le (by omega)
  have f₂ : Fits w (S + 1) := hS.of_le (by omega)
  have f₃ : Fits w (base + n + (S + 1)) := hS.of_le (by omega)
  have f₄ : Fits w (base + 2 * n + 1 + v.val) := hS.of_le (by omega)
  obtain ⟨x₁, he₁, hx₁s, hx₁k, hx₁m, hx₁r⟩ : ∃ x₁, ExecWithin w insertHead x x₁ 8 ∧
      x₁.regs sz = S + 1 ∧ x₁.regs k = S + 1 ∧
      x₁.mem = Function.update (Function.update (Function.update x.mem (base + v.val) keyVal)
        (base + n + (S + 1)) v.val) (base + 2 * n + 1 + v.val) (S + 1) ∧
      ∀ i ∉ [t, sz, k], x₁.regs i = x.regs i := by
    refine ⟨?z, ?e, ?_, ?_, ?_, ?_⟩
    case e =>
      ram_exact_eval [insertHead, hr.reg_base, hr.reg_hb, hr.reg_pb, hsz_eq, ho1, hv_reg, hk_reg,
        f₁, f₂, f₃, f₄]
    · simp +decide
    · simp +decide
    · simp
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp [hi.1, hi.2.1, hi.2.2]
  obtain ⟨hsh, hup⟩ := hheap.push (c := keyVal) hv_lt hp0
  obtain ⟨y, he₂, hfr₂, hheap', hpos, hout⟩ := siftUp_spec (N := n) (base := base) (S := S + 1)
    (K := S + 1) ((hx₁r zero (by decide)).trans hz0) ((hx₁r one (by decide)).trans ho1)
    ((hx₁r baseReg (by decide)).trans hr.reg_base) ((hx₁r hb (by decide)).trans hr.reg_hb)
    ((hx₁r pb (by decide)).trans hr.reg_pb) hx₁k (by omega) le_rfl hS
    (hx₁m ▸ hsh) (hx₁m ▸ hup)
  have hlog : Nat.log 2 (S + 1) ≤ Nat.log 2 n := Nat.log_mono_right (by omega)
  have hetot : ExecWithin w doInsert x y (28 * Nat.log 2 n + 10) := by
    rw [doInsert_eq]
    refine (execWithin_append he₁ he₂).mono ?_
    have := Nat.mul_le_mul_left 28 hlog; omega
  have hfr_p : ∀ i, i ∈ [baseReg, nReg, hb, pb] → y.regs i = x.regs i := fun i hi => by
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hfr₂ _ (by decide)).trans (hx₁r _ (by decide))
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hfr₂ _ (by decide)).trans (hx₁r _ (by decide))
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hfr₂ _ (by decide)).trans (hx₁r _ (by decide))
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hfr₂ _ (by decide)).trans (hx₁r _ (by decide))
    · cases hi
  have hys : y.regs sz = S + 1 := (hfr₂ sz (by decide)).trans hx₁s
  refine ⟨y, hetot, ⟨hetot.bounded hr.bounded,
    (hfr_p baseReg (by decide)).trans hr.reg_base,
    (hfr_p nReg (by decide)).trans hr.reg_n,
    (hfr_p hb (by decide)).trans hr.reg_hb,
    (hfr_p pb (by decide)).trans hr.reg_pb, hys ▸ hheap', ?_⟩, ?_⟩
  · funext u
    have hu_lt := u.isLt
    have hkey : y.mem (base + u.val) =
        if u.val = v.val then keyVal else x.mem (base + u.val) := by
      rw [hout (base + u.val) (Or.inl (by omega)), hx₁m,
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_apply]
      split_ifs <;> omega
    by_cases huv : u = v
    · subst huv
      have hy_pos : y.mem (base + 2 * n + 1 + u.val) ≠ 0 := by
        intro h0
        have := (hpos u.val hu_lt).mp h0
        rw [hx₁m, Function.update_self] at this
        omega
      simp only [Function.update_self, stateOfMem, hy_pos, ↓reduceIte, hkey]
    · have huv_val : u.val ≠ v.val := fun e => huv (Fin.ext e)
      have hy_pos : y.mem (base + 2 * n + 1 + u.val) = 0 ↔
          x.mem (base + 2 * n + 1 + u.val) = 0 := by
        rw [hpos u.val hu_lt, hx₁m, Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      simp only [Function.update_of_ne huv, hr.state_eq, stateOfMem, hkey, huv_val, ↓reduceIte]
      by_cases hx0 : x.mem (base + 2 * n + 1 + u.val) = 0
      · simp only [hx0, hy_pos.mpr hx0, ↓reduceIte]
      · have hy0 : y.mem (base + 2 * n + 1 + u.val) ≠ 0 := fun h0 => hx0 (hy_pos.mp h0)
        simp only [hx0, hy0, ↓reduceIte]
  · rw [Modifies.block_iff]
    intro a ha
    dsimp only [space] at ha
    rw [hout a (by omega), hx₁m, Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

private def decreaseHead : Code .exact rBin := ram_exact[
  t ← baseReg + argV; *t ← argK;
  t ← pb + argV; k ← *t ]

private theorem doDecreaseKey_eq : doDecreaseKey = appendCode decreaseHead siftUp := rfl

private theorem doDecreaseKey_spec (hS : Fits w (base + space n)) {s : IndexedMinPQ.State n}
    {x : Data rBin} (hr : Rep n w base s x) (hz0 : x.regs zero = 0) (ho1 : x.regs one = 1)
    {v : Fin n} {keyVal : ℕ} (hdec : ∃ k₀, s v = some k₀ ∧ keyVal ≤ k₀)
    (hv_reg : x.regs argV = v.val) (hk_reg : x.regs argK = keyVal) :
    ∃ y, ExecWithin w doDecreaseKey x y (28 * Nat.log 2 n + 6) ∧
      Rep n w base (Function.update s v (some keyVal)) y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem := by
  have hsp : space n = 3 * n + 1 := rfl
  have hv_lt := v.isLt
  obtain ⟨k₀, hsv, hle₀⟩ := hdec
  rw [hr.state_eq, stateOfMem] at hsv
  have hp_ne : x.mem (base + 2 * n + 1 + v.val) ≠ 0 := by
    intro h0; simp only [h0, ↓reduceIte, reduceCtorEq] at hsv
  simp only [hp_ne, ↓reduceIte, Option.some.injEq] at hsv
  have hle : keyVal ≤ x.mem (base + v.val) := hsv ▸ hle₀
  obtain ⟨S, hsz_eq⟩ : ∃ S, x.regs sz = S := ⟨_, rfl⟩
  have hheap : HeapInv n base S x.mem := hsz_eq ▸ hr.heap
  have hSn := hheap.size_le
  obtain ⟨K, hK_eq⟩ : ∃ K, x.mem (base + 2 * n + 1 + v.val) = K := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := hK_eq ▸ Nat.one_le_iff_ne_zero.2 hp_ne
  have hKS : K ≤ S := hK_eq ▸ hheap.pos_le v.val hv_lt
  have f₁ : Fits w (base + v.val) := hS.of_le (by omega)
  have f₂ : Fits w (base + 2 * n + 1 + v.val) := hS.of_le (by omega)
  have hne_addr : base + 2 * n + 1 + v.val ≠ base + v.val := by omega
  obtain ⟨x₁, he₁, hx₁k, hx₁m, hx₁r⟩ : ∃ x₁, ExecWithin w decreaseHead x x₁ 4 ∧
      x₁.regs k = K ∧ x₁.mem = Function.update x.mem (base + v.val) keyVal ∧
      ∀ i ∉ [t, k], x₁.regs i = x.regs i := by
    refine ⟨?z, ?e, ?_, ?_, ?_⟩
    case e =>
      ram_exact_eval [decreaseHead, hr.reg_base, hr.reg_pb, hv_reg, hk_reg, hK_eq, hne_addr,
        f₁, f₂]
    · simp +decide
    · simp
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp [hi.1, hi.2]
  obtain ⟨hsh, hup⟩ := hheap.decrease hv_lt hp_ne hle
  rw [hK_eq] at hup
  obtain ⟨y, he₂, hfr₂, hheap', hpos, hout⟩ := siftUp_spec (N := n) (base := base) (S := S)
    (K := K) ((hx₁r zero (by decide)).trans hz0) ((hx₁r one (by decide)).trans ho1)
    ((hx₁r baseReg (by decide)).trans hr.reg_base) ((hx₁r hb (by decide)).trans hr.reg_hb)
    ((hx₁r pb (by decide)).trans hr.reg_pb) hx₁k hK1 hKS hS (hx₁m ▸ hsh) (hx₁m ▸ hup)
  have hlog : Nat.log 2 K ≤ Nat.log 2 n := Nat.log_mono_right (by omega)
  have hetot : ExecWithin w doDecreaseKey x y (28 * Nat.log 2 n + 6) := by
    rw [doDecreaseKey_eq]
    refine (execWithin_append he₁ he₂).mono ?_
    have := Nat.mul_le_mul_left 28 hlog; omega
  have hfr_p : ∀ i, i ∈ [baseReg, nReg, hb, pb, sz] → y.regs i = x.regs i := fun i hi => by
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hfr₂ _ (by decide)).trans (hx₁r _ (by decide))
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hfr₂ _ (by decide)).trans (hx₁r _ (by decide))
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hfr₂ _ (by decide)).trans (hx₁r _ (by decide))
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hfr₂ _ (by decide)).trans (hx₁r _ (by decide))
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hfr₂ _ (by decide)).trans (hx₁r _ (by decide))
    · cases hi
  have hys : y.regs sz = S := (hfr_p sz (by decide)).trans hsz_eq
  refine ⟨y, hetot, ⟨hetot.bounded hr.bounded,
    (hfr_p baseReg (by decide)).trans hr.reg_base,
    (hfr_p nReg (by decide)).trans hr.reg_n,
    (hfr_p hb (by decide)).trans hr.reg_hb,
    (hfr_p pb (by decide)).trans hr.reg_pb, hys ▸ hheap', ?_⟩, ?_⟩
  · funext u
    have hu_lt := u.isLt
    have hkey : y.mem (base + u.val) =
        if u.val = v.val then keyVal else x.mem (base + u.val) := by
      rw [hout (base + u.val) (Or.inl (by omega)), hx₁m, Function.update_apply]
      split_ifs <;> omega
    have hy_pos : y.mem (base + 2 * n + 1 + u.val) = 0 ↔
        x.mem (base + 2 * n + 1 + u.val) = 0 := by
      rw [hpos u.val hu_lt, hx₁m, Function.update_of_ne (by omega)]
    by_cases huv : u = v
    · subst huv
      have hy0 : y.mem (base + 2 * n + 1 + u.val) ≠ 0 := fun h0 => hp_ne (hy_pos.mp h0)
      simp only [Function.update_self, stateOfMem, hy0, ↓reduceIte, hkey]
    · have huv_val : u.val ≠ v.val := fun e => huv (Fin.ext e)
      simp only [Function.update_of_ne huv, hr.state_eq, stateOfMem, hkey, huv_val, ↓reduceIte]
      by_cases hx0 : x.mem (base + 2 * n + 1 + u.val) = 0
      · simp only [hx0, hy_pos.mpr hx0, ↓reduceIte]
      · have hy0 : y.mem (base + 2 * n + 1 + u.val) ≠ 0 := fun h0 => hx0 (hy_pos.mp h0)
        simp only [hx0, hy0, ↓reduceIte]
  · rw [Modifies.block_iff]
    intro a ha
    dsimp only [space] at ha
    rw [hout a (by omega), hx₁m, Function.update_of_ne (by omega)]

private theorem doExtractMin_spec (hS : Fits w (base + space n)) {s : IndexedMinPQ.State n}
    {x : Data rBin} (hr : Rep n w base s x) (hz0 : x.regs zero = 0) (ho1 : x.regs one = 1) :
    ∃ y, ExecWithin w doExtractMin x y (46 * Nat.log 2 n + 22) ∧
      pqCode.decode (K_max := K_max) .extractMin y.regs =
        some ((IndexedMinPQ.spec n K_max).step s .extractMin).2 ∧
      Rep n w base ((IndexedMinPQ.spec n K_max).step s .extractMin).1 y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem := by
  have hsp : space n = 3 * n + 1 := rfl
  obtain ⟨S, hsz_eq⟩ : ∃ S, x.regs sz = S := ⟨_, rfl⟩
  have hheap : HeapInv n base S x.mem := hsz_eq ▸ hr.heap
  have hSn := hheap.size_le
  by_cases hS0 : S = 0
  · subst hS0
    have hc : (Cond.eq sz zero).Holds x := by simp only [Cond.holds_eq, hsz_eq, hz0]
    have he0 : ExecWithin (B := .exact) w ram_exact[ outFlag ← zero ] x (x.set outFlag 0) 1 := by
      ram_exact_eval [hz0]
    have hetot : ExecWithin w doExtractMin x (x.set outFlag 0) (46 * Nat.log 2 n + 22) :=
      (ExecWithin.branch_pos hc he0).mono (by omega)
    have hfm : IndexedMinPQ.findMin s = none := by
      rw [IndexedMinPQ.findMin_eq_none_iff, hr.state_eq]
      exact hheap.size_eq_zero_iff.mp rfl
    refine ⟨x.set outFlag 0, hetot, ?_, ⟨hetot.bounded hr.bounded, hr.reg_base, hr.reg_n,
      hr.reg_hb, hr.reg_pb, hsz_eq ▸ hheap, ?_⟩, Modifies.refl _ _⟩
    · simp only [pqCode, PQCode.decode, IndexedMinPQ.spec, hfm, Data.set_regs,
        Function.update_self, ↓reduceIte]
    · simp only [IndexedMinPQ.spec, hfm, Data.set_mem]; exact hr.state_eq
  · have hS1 : 1 ≤ S := Nat.one_le_iff_ne_zero.2 hS0
    have hc : ¬(Cond.eq sz zero).Holds x := by simp only [Cond.holds_eq, hsz_eq, hz0]; omega
    obtain ⟨y, he₁, hfr, hyf, hyu, hyk, hysz, hheap', hpos, hout⟩ :=
      doExtractNonEmpty_spec hz0 ho1 hr.reg_base hr.reg_hb hr.reg_pb hsz_eq hS1 hS hheap
    have hlog : Nat.log 2 S ≤ Nat.log 2 n := Nat.log_mono_right hSn
    have hetot : ExecWithin w doExtractMin x y (46 * Nat.log 2 n + 22) := by
      refine (ExecWithin.branch_neg hc he₁).mono ?_
      have := Nat.mul_le_mul_left 46 hlog; omega
    have hUN : x.mem (base + n + 1) < n := hheap.vertex_lt 1 le_rfl hS1
    have hfm : IndexedMinPQ.findMin s =
        some (⟨x.mem (base + n + 1), hUN⟩, x.mem (base + x.mem (base + n + 1))) := by
      rw [hr.state_eq]
      exact hheap.findMin_eq_root hS1
    refine ⟨y, hetot, ?_, ⟨hetot.bounded hr.bounded,
      (hfr baseReg (by decide)).trans hr.reg_base,
      (hfr nReg (by decide)).trans hr.reg_n,
      (hfr hb (by decide)).trans hr.reg_hb,
      (hfr pb (by decide)).trans hr.reg_pb,
      hysz ▸ hheap', ?_⟩, ?_⟩
    · simp only [pqCode, PQCode.decode, IndexedMinPQ.spec, hfm, hyf, one_ne_zero, ↓reduceIte,
        ↓reduceDIte, hyu, hUN, hyk]
    · simp only [IndexedMinPQ.spec, hfm]
      funext u
      have hu_lt := u.isLt
      have hkey : y.mem (base + u.val) = x.mem (base + u.val) :=
        hout (base + u.val) (Or.inl (by omega))
      by_cases huv : u = ⟨x.mem (base + n + 1), hUN⟩
      · subst huv
        have hy0 : y.mem (base + 2 * n + 1 + x.mem (base + n + 1)) = 0 :=
          (hpos _ hUN).mpr (Or.inr rfl)
        simp only [Function.update_self, stateOfMem, hy0, ↓reduceIte]
      · have huv_val : u.val ≠ x.mem (base + n + 1) := fun e => huv (Fin.ext e)
        have hy_iff : y.mem (base + 2 * n + 1 + u.val) = 0 ↔
            x.mem (base + 2 * n + 1 + u.val) = 0 := by
          rw [hpos u.val hu_lt]
          exact ⟨fun h => h.resolve_right huv_val, Or.inl⟩
        simp only [Function.update_of_ne huv, hr.state_eq, stateOfMem, hkey]
        by_cases hx0 : x.mem (base + 2 * n + 1 + u.val) = 0
        · simp only [hx0, hy_iff.mpr hx0, ↓reduceIte]
        · have hy0 : y.mem (base + 2 * n + 1 + u.val) ≠ 0 := fun h0 => hx0 (hy_iff.mp h0)
          simp only [hx0, hy0, ↓reduceIte]
    · rw [Modifies.block_iff]
      intro a ha
      dsimp only [space] at ha
      exact hout a (by omega)

private def opSetup : Code .exact rBin := ram_exact[ zero ← #0; one ← #1 ]

private theorem opCode_eq : opCode = appendCode opSetup
    (.branch (.eq tag2 zero)
      (.branch (.eq tag1 zero)
        (.branch (.eq tag0 zero) doIsEmpty doGetKey)
        (.branch (.eq tag0 zero) doInsert doDecreaseKey))
      doExtractMin) := rfl

private theorem opCode_spec (hS : Fits w (base + space n)) {s : IndexedMinPQ.State n}
    {x : Data rBin} (o : IndexedMinPQ.Op n) (hr : Rep n w base s x)
    (hv : (IndexedMinPQ.spec n K_max).valid s o) (harg : pqCode.argMatch o x.regs) :
    ∃ y m, Exec w opCode x y m ∧
      pqCode.decode (K_max := K_max) o y.regs =
        some ((IndexedMinPQ.spec n K_max).step s o).2 ∧
      Rep n w base ((IndexedMinPQ.spec n K_max).step s o).1 y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      m ≤ charge n o := by
  have hsp : space n = 3 * n + 1 := rfl
  have f₀ : Fits w 0 := hS.of_le (Nat.zero_le _)
  have f₁ : Fits w 1 := hS.of_le (by omega)
  let x₁ := (x.set zero 0).set one 1
  have hset : ExecWithin w opSetup x x₁ 2 := by ram_exact_eval [opSetup, x₁, f₀, f₁]
  have hr₁ : Rep n w base s x₁ :=
    ⟨hset.bounded hr.bounded, hr.reg_base, hr.reg_n, hr.reg_hb, hr.reg_pb, hr.heap, hr.state_eq⟩
  have hz₁ : x₁.regs zero = 0 := by simp +decide [x₁]
  have ho₁ : x₁.regs one = 1 := by simp +decide [x₁]
  have ht2 : x₁.regs tag2 = x.regs tag2 := by simp +decide [x₁]
  have ht1 : x₁.regs tag1 = x.regs tag1 := by simp +decide [x₁]
  have ht0 : x₁.regs tag0 = x.regs tag0 := by simp +decide [x₁]
  have haV : x₁.regs argV = x.regs argV := by simp +decide [x₁]
  have haK : x₁.regs argK = x.regs argK := by simp +decide [x₁]
  dsimp only [PQCode.argMatch, pqCode] at harg
  cases o with
  | isEmpty =>
    obtain ⟨h2, h1, h0⟩ := harg
    have hc2 : (Cond.eq tag2 zero).Holds x₁ := by simp only [Cond.holds_eq, ht2, hz₁, h2]
    have hc1 : (Cond.eq tag1 zero).Holds x₁ := by simp only [Cond.holds_eq, ht1, hz₁, h1]
    have hc0 : (Cond.eq tag0 zero).Holds x₁ := by simp only [Cond.holds_eq, ht0, hz₁, h0]
    obtain ⟨y, he, hdec, hry, hym⟩ := doIsEmpty_spec (K_max := K_max) hr₁ hz₁ ho₁
    have hetot : ExecWithin w opCode x y (charge n .isEmpty) := by
      rw [opCode_eq]
      exact (execWithin_append hset
        (.branch_pos hc2 (.branch_pos hc1 (.branch_pos hc0 he)))).mono
        (by dsimp [charge, tEmpty]; omega)
    obtain ⟨m, hm, hex⟩ := hetot
    exact ⟨y, m, hex, hdec, hry, hym ▸ Modifies.refl _ _, hm⟩
  | getKey v =>
    obtain ⟨h2, h1, h0, hv_eq⟩ := harg
    have hc2 : (Cond.eq tag2 zero).Holds x₁ := by simp only [Cond.holds_eq, ht2, hz₁, h2]
    have hc1 : (Cond.eq tag1 zero).Holds x₁ := by simp only [Cond.holds_eq, ht1, hz₁, h1]
    have hc0 : ¬(Cond.eq tag0 zero).Holds x₁ := by simp only [Cond.holds_eq, ht0, hz₁]; exact h0
    obtain ⟨y, he, hdec, hry, hym⟩ :=
      doGetKey_spec (K_max := K_max) hS hr₁ hz₁ ho₁ (haV.trans hv_eq)
    have hetot : ExecWithin w opCode x y (charge n (.getKey v)) := by
      rw [opCode_eq]
      exact (execWithin_append hset
        (.branch_pos hc2 (.branch_pos hc1 (.branch_neg hc0 he)))).mono
        (by dsimp [charge, tGet]; omega)
    obtain ⟨m, hm, hex⟩ := hetot
    exact ⟨y, m, hex, hdec, hry, hym ▸ Modifies.refl _ _, hm⟩
  | insert v keyVal =>
    obtain ⟨h2, h1, h0, hv_eq, hk_eq⟩ := harg
    have hc2 : (Cond.eq tag2 zero).Holds x₁ := by simp only [Cond.holds_eq, ht2, hz₁, h2]
    have hc1 : ¬(Cond.eq tag1 zero).Holds x₁ := by simp only [Cond.holds_eq, ht1, hz₁]; exact h1
    have hc0 : (Cond.eq tag0 zero).Holds x₁ := by simp only [Cond.holds_eq, ht0, hz₁, h0]
    obtain ⟨y, he, hry, hmod⟩ :=
      doInsert_spec hS hr₁ hz₁ ho₁ (IndexedMinPQ.notMem_dom_iff.mpr hv.1)
        (haV.trans hv_eq) (haK.trans hk_eq)
    have hetot : ExecWithin w opCode x y (charge n (.insert v keyVal)) := by
      rw [opCode_eq]
      exact (execWithin_append hset
        (.branch_pos hc2 (.branch_neg hc1 (.branch_pos hc0 he)))).mono
        (by dsimp [charge, tIns]; omega)
    obtain ⟨m, hm, hex⟩ := hetot
    exact ⟨y, m, hex, rfl, hry, hmod, hm⟩
  | decreaseKey v keyVal =>
    obtain ⟨h2, h1, h0, hv_eq, hk_eq⟩ := harg
    have hc2 : (Cond.eq tag2 zero).Holds x₁ := by simp only [Cond.holds_eq, ht2, hz₁, h2]
    have hc1 : ¬(Cond.eq tag1 zero).Holds x₁ := by simp only [Cond.holds_eq, ht1, hz₁]; exact h1
    have hc0 : ¬(Cond.eq tag0 zero).Holds x₁ := by simp only [Cond.holds_eq, ht0, hz₁]; exact h0
    obtain ⟨y, he, hry, hmod⟩ :=
      doDecreaseKey_spec hS hr₁ hz₁ ho₁ hv.1 (haV.trans hv_eq) (haK.trans hk_eq)
    have hetot : ExecWithin w opCode x y (charge n (.decreaseKey v keyVal)) := by
      rw [opCode_eq]
      exact (execWithin_append hset
        (.branch_pos hc2 (.branch_neg hc1 (.branch_neg hc0 he)))).mono
        (by dsimp [charge, tDec]; omega)
    obtain ⟨m, hm, hex⟩ := hetot
    exact ⟨y, m, hex, rfl, hry, hmod, hm⟩
  | extractMin =>
    have hc2 : ¬(Cond.eq tag2 zero).Holds x₁ := by
      simp only [Cond.holds_eq, ht2, hz₁]; exact harg
    obtain ⟨y, he, hdec, hry, hmod⟩ := doExtractMin_spec (K_max := K_max) hS hr₁ hz₁ ho₁
    have hetot : ExecWithin w opCode x y (charge n .extractMin) := by
      rw [opCode_eq]
      exact (execWithin_append hset (.branch_neg hc2 he)).mono (by dsimp [charge, tExt]; omega)
    obtain ⟨m, hm, hex⟩ := hetot
    exact ⟨y, m, hex, hdec, hry, hmod, hm⟩

end OpSpecs

/-- Exact-basis `SubroutineDS` certificate for the standalone binary min-heap. -/
def subroutineDS {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max) :
    SubroutineDS pqCode.toSubroutineCode (IndexedMinPQ.spec n K_max) w base ![n]
      (IndexedMinPQ.empty n) where
  space := space n
  spanTime := 6
  setupTime := 5
  initPotential := 0
  charge _ o := charge n o
  rep := Rep n w base
  potential _ := 0
  encode := pqCode.encode
  argMatch := pqCode.argMatch
  decode := pqCode.decode
  bounded hr := hr.bounded
  rep_unique hr₁ hr₂ := hr₁.state_eq.trans hr₂.state_eq.symm
  arguments_fit o hv i _ := pqCode.arguments_fit (space_lower n) hS hK o hv i
  encode_matches := pqCode.encode_matches
  rep_supported {s x x'} hreg hmem hbx' hr := by
    have hbase' : x'.regs baseReg = base := (hreg baseReg (by decide)).trans hr.reg_base
    have hn' : x'.regs nReg = n := (hreg nReg (by decide)).trans hr.reg_n
    have hhb' : x'.regs hb = base + n := (hreg hb (by decide)).trans hr.reg_hb
    have hpb' : x'.regs pb = base + 2 * n + 1 := (hreg pb (by decide)).trans hr.reg_pb
    have hsz' : x'.regs sz = x.regs sz := hreg sz (by decide)
    refine ⟨hbx', hbase', hn', hhb', hpb', ?_, ?_⟩
    · rw [hsz']
      exact hr.heap.congr_mem hmem
    · rw [hr.state_eq]
      exact (stateOfMem_congr hmem).symm
  potential_supported _ _ _ := rfl
  clear_nodup := by decide
  params_not_clear j := by fin_cases j; decide
  incCur_eval {x} hone hfit := by
    dsimp only [pqCode, PQCode.toSubroutineCode] at hone hfit ⊢
    simp only [Op.eval_exactBin, BinOp.evalExact, hone, Option.bind_some, Data.put_of_fits hfit]
  span_exec {x} _ hfr hpar := by
    obtain ⟨x₁, he, hm, hb', hfr', hn'⟩ := allocSpan_spec hS hfr (hpar 0)
    refine ⟨x₁, he, hm, hb', hfr', fun j => ?_⟩
    fin_cases j
    exact hn'
  setup_exec {x₁} hx₁ hb' hfr' hpar hz := by
    obtain ⟨y, he, hfr_y, hry, hmod⟩ := initSetup_spec hS hx₁ hb' hfr' (hpar 0) hz
    exact ⟨y, he, hfr_y, hry, le_rfl, hmod⟩
  step_exec {s x} o hr hv harg := by
    obtain ⟨y, m, hex, hdec, hry, hmod, hm⟩ := opCode_spec hS o hr hv harg
    exact ⟨y, m, hex, hdec, hry, hmod, by omega⟩

/-- Packaged `PQPackage .exact rBin` for plug-and-play subroutine callers (`dijkstra_of_pq_spec`).
-/
def pkg : PQPackage .exact rBin where
  code := pqCode
  space := space
  space_lower := space_lower
  initTime _ := 11
  emptyTime := tEmpty
  getTime := tGet
  insertTime := tIns
  decreaseTime := tDec
  extractTime := tExt
  cert hS hK := subroutineDS hS hK
  cert_space _ _ := rfl
  cert_initTime _ _ := le_rfl
  cert_initPotential _ _ := rfl
  cert_argMatch _ _ := rfl
  cert_decode _ _ := rfl
  charge_isEmpty _ _ _ := le_rfl
  charge_getKey _ _ _ _ := le_rfl
  charge_insert _ _ _ _ _ := le_rfl
  charge_decreaseKey _ _ _ _ _ := le_rfl
  charge_extractMin _ _ _ := le_rfl

/-! ## Standalone `.standard`-Basis Word-RAM Realization and Worst-Case Bounds -/

/-- Standalone `.standard`-basis `DynamicProgram` serving `IndexedMinPQ.spec n K_max`. -/
def dynamicProgram (n K_max : ℕ) : DynamicProgram (IndexedMinPQ.spec n K_max) rBin where
  code := pqCode.toStandard.code
  output := pqCode.output
  input := pqCode.input
  encode := pqCode.encode
  decode := pqCode.decode (K_max := K_max)

/-- Standalone `.standard`-basis `DynamicCertificate` for the binary min-heap. -/
def certificate {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max) :
    DynamicCertificate (dynamicProgram n K_max) w :=
  ((subroutineDS hS hK).toStandard).toCertificate

/-- **Standalone worst-case per-operation bound** for the word-RAM binary min-heap over
`Basis.standard` (`charge n o + 1` instructions including the trailing `halt`). -/
theorem instruction_bound {n K_max w base : ℕ} (hS : Fits w (base + space n))
    (hK : Fits w K_max) :
    Stateful.Bound (certificate hS hK).realization
      DynamicProgram.OperationTrace.instructions
      (fun _ o => charge n o + 1) :=
  ((subroutineDS hS hK).toStandard).toBound fun _ => rfl

/-- **Standalone adaptive-client bound** for the word-RAM binary min-heap over `Basis.standard`. -/
theorem run_client_bound {n K_max w base : ℕ} (hS : Fits w (base + space n))
    (hK : Fits w K_max) {α : Type*} (p : (IndexedMinPQ.spec n K_max).Client α)
    {s : IndexedMinPQ.State n} {x : Data rBin} (hr : Rep n w base s x)
    (hv : (IndexedMinPQ.spec n K_max).ValidHistory s
      ((IndexedMinPQ.spec n K_max).runClient s p).2.2) :
    ∃ y traces,
      Stateful.Executes ((dynamicProgram n K_max).ExecOp w) p x
        ((IndexedMinPQ.spec n K_max).runClient s p).1 y traces ∧
      Rep n w base ((IndexedMinPQ.spec n K_max).runClient s p).2.1 y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤
        (IndexedMinPQ.spec n K_max).totalCost (fun _ o => charge n o + 1) s
          ((IndexedMinPQ.spec n K_max).runClient s p).2.2 :=
  ((subroutineDS hS hK).toStandard).run_client_bound (fun _ => rfl) p hr hv

end Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap
