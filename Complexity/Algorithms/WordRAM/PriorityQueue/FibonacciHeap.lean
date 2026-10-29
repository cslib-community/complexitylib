/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.BasicOps
public import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.Cut
public import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.Consolidate

/-!
# Static-array Word-RAM Fibonacci heap

This file assembles the standalone static-array Word-RAM Fibonacci heap
[Fredman and Tarjan][FredmanTarjan1987] [Cormen et al., Chapter 19][CLRS2009] over
`Cslib.WordRAM.Basis.exact` (and lifted to `Basis.standard`) for
`Cslib.Algorithms.Lean.IndexedMinPQ.spec`.

Over `n` vertex handles in a contiguous memory block `[base, base + 9 * n + 1)` with concrete
integer potential `potential x = 80 * (numRoots + 2 * numMarked)` (`initPotential = 0`,
[Fredman and Tarjan][FredmanTarjan1987], Section 2, p. 604 (the potential defined before Theorem 1);
[Cormen et al.][CLRS2009], Section 19.1, eq. (19.1)):

* `initFresh` initializes an empty heap on zeroed `[base, base + 9 * n + 1)` in `O(1)` (`≤ 26`)
  instructions;
* `initClear` initializes an empty heap on arbitrary dirty `[base, base + 9 * n + 1)` in `O(n)`
  (`≤ 36 * n + 36`) instructions;
* `isEmpty` and `getKey` run in `O(1)` worst-case time (`≤ 12` and `≤ 16` instructions);
* `insert` and `decreaseKey` (with cascading cuts) run in `O(1)` amortized time (`≤ 130` and
  `≤ 340` instructions);
* `extractMin` (with degree-table consolidation and deterministic lexicographic `(key, handle)`
  tie-breaking) runs in `O(log n)` amortized time (`≤ 420 * (Nat.log 2 n + 1)` instructions).

## Main definitions

* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.subroutineDS`: `SubroutineDS` certificate
  over `Basis.exact`.
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.pkg`, `pkgStd`: `PQPackage` bundles over
  `Basis.exact` and `Basis.standard` for plug-and-play graph algorithms (such as Dijkstra).
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.initFreshProg`, `initClearProg`, `opProg`,
  `initRegs`, `prepareRegs`, `RunsOps`: compiled flat `Program .exact rFib` artifacts, register
  calling conventions, and sequential execution predicate for standalone multi-operation execution.

## Main results

* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.amortized`, `run_client_amortized`:
  standalone `Stateful.Amortized` certificate and adaptive-client bound over `Basis.standard`.
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.run_ops_exact_fresh`,
  `run_ops_exact_reusable`: standalone end-to-end `Basis.exact` flat-program execution theorems
  bounding initialization by `t_init + 1 ≤ 421` (`initFreshProg` on zeroed memory) or
  `t_init + 1 ≤ 421 * (n + 1)` (`initClearProg` on arbitrary memory) and total operation
  instructions for `m_q` queries, `m_ins` insertions, `m_dec` key decreases, and `m_ext` minimum
  extractions by `t_ops ≤ 421 * (m_q + m_ins + m_dec + m_ext * (Nat.log 2 n + 1))`.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network optimization
  algorithms*][FredmanTarjan1987], Section 2, Lemma 1, Corollary 1, and Theorem 1 (p. 604).
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 19.1, eq. (19.1), and Sections 19.2–19.4.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap

open Cslib.WordRAM
open Cslib.Algorithms.Lean

/-! ## Unified dispatcher -/

/-- Unified dispatcher `dispatchCode` implements all five `IndexedMinPQ` operations within
`charge n s o` amortized instructions over `Basis.exact`. -/
theorem dispatchCode_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n} {x : Data rFib}
    (o : IndexedMinPQ.Op n) (hinv : FibInv n K_max w base s x)
    (hval : (IndexedMinPQ.spec n K_max).valid s o) (harg : code.argMatch o x.regs) :
    ∃ y m, Exec w dispatchCode x y m ∧
      code.decode (n := n) (K_max := K_max) o y.regs =
        some ((IndexedMinPQ.spec n K_max).step s o).2 ∧
      FibInv n K_max w base ((IndexedMinPQ.spec n K_max).step s o).1 y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      m + potential y ≤ charge n s o + potential x := by
  have hz0 : x.regs zeroP = 0 := hinv.2.1.2.2.2.2.2.2.2.2.2.2.2.1
  cases o with
  | isEmpty =>
    obtain ⟨ht2, ht1, ht0⟩ := harg
    have c2 : (Cond.eq tag2 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht2
    have c1 : (Cond.eq tag1 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht1
    have c0 : (Cond.eq tag0 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht0
    obtain ⟨y, t, ⟨m, hm, he⟩, hdec, hinv_y, hmod, hpot⟩ := isEmptyCode_exec hinv
    refine ⟨y, m + 1 + 1 + 1,
      Exec.branch_pos c2 (Exec.branch_pos c1 (Exec.branch_pos c0 he)), hdec, hinv_y, hmod, ?_⟩
    simp only [charge, tEmpty]
    omega
  | getKey v =>
    obtain ⟨ht2, ht1, ht0, hv_reg⟩ := harg
    have c2 : (Cond.eq tag2 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht2
    have c1 : (Cond.eq tag1 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht1
    have c0 : ¬(Cond.eq tag0 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht0
    obtain ⟨y, t, ⟨m, hm, he⟩, hdec, hinv_y, hmod, hpot⟩ := getKeyCode_exec v hinv hv_reg
    refine ⟨y, m + 2 + 1 + 1,
      Exec.branch_pos c2 (Exec.branch_pos c1 (Exec.branch_neg c0 he)), hdec, hinv_y, hmod, ?_⟩
    simp only [charge, tGet]
    omega
  | insert v k =>
    obtain ⟨ht2, ht1, ht0, hv_reg, hk_reg⟩ := harg
    have c2 : (Cond.eq tag2 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht2
    have c1 : ¬(Cond.eq tag1 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht1
    have c0 : (Cond.eq tag0 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht0
    obtain ⟨y, t, ⟨m, hm, he⟩, hinv_y, hmod, hpot⟩ :=
      insertCode_exec v k hinv hval hv_reg hk_reg
    refine ⟨y, m + 1 + 2 + 1,
      Exec.branch_pos c2 (Exec.branch_neg c1 (Exec.branch_pos c0 he)), rfl, hinv_y, hmod, ?_⟩
    simp only [charge, tIns]
    omega
  | decreaseKey v k =>
    obtain ⟨ht2, ht1, ht0, hv_reg, hk_reg⟩ := harg
    have c2 : (Cond.eq tag2 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht2
    have c1 : ¬(Cond.eq tag1 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht1
    have c0 : ¬(Cond.eq tag0 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht0
    obtain ⟨y, t, ⟨m, hm, he⟩, hinv_y, hmod, hpot⟩ :=
      decreaseKeyCode_exec v k hinv hval hv_reg hk_reg
    refine ⟨y, m + 2 + 2 + 1,
      Exec.branch_pos c2 (Exec.branch_neg c1 (Exec.branch_neg c0 he)), rfl, hinv_y, hmod, ?_⟩
    simp only [charge, tDec]
    omega
  | extractMin =>
    have c2 : ¬(Cond.eq tag2 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact harg
    obtain ⟨y, t, ⟨m, hm, he⟩, hdec, hinv_y, hmod, hpot⟩ := extractMinCode_exec hinv
    refine ⟨y, m + 2, Exec.branch_neg c2 he, hdec, hinv_y, hmod, ?_⟩
    simp only [charge, tExt]
    omega

/-! ## `SubroutineDS` certificate and `PQPackage` bundles -/

/-- Unified standalone and inline-subroutine specification/resource certificate for `FibonacciHeap`
over `Basis.exact`. -/
def subroutineDS {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max) :
    SubroutineDS code.toSubroutineCode (IndexedMinPQ.spec n K_max) w base ![n]
      (IndexedMinPQ.empty n) where
  space := space n
  spanTime := 12
  setupTime := 14
  initPotential := 0
  charge := charge n
  rep := FibInv n K_max w base
  potential := potential
  encode := code.encode
  argMatch := code.argMatch
  decode := code.decode
  bounded h := h.1
  rep_unique h₁ h₂ := h₁.2.2.unique h₂.2.2
  arguments_fit o hv i _ := code.arguments_fit (space_lower n) hS hK o hv i
  encode_matches := code.encode_matches
  rep_supported := FibInv.supported
  potential_supported hreg _ _ := potential_supported hreg
  clear_nodup := by decide
  params_not_clear := by decide
  incCur_eval := incCur_eval
  span_exec := allocSpan_exec hS
  setup_exec := initSetup_exec
  step_exec := dispatchCode_exec

/-- Parametric `PQPackage .exact rFib` bundle for plug-and-play graph algorithms over
`Basis.exact`. -/
def pkg : PQPackage .exact rFib where
  code := code
  space := space
  space_lower := space_lower
  initTime := tInit
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

/-- Parametric `PQPackage .standard rFib` bundle lifted to `Basis.standard`. -/
abbrev pkgStd : PQPackage .standard rFib := pkg.toStandard

/-! ## Standalone `Basis.standard` `DynamicProgram` and `Stateful.Amortized` realizations -/

/-- Standalone `DynamicProgram` realization of `FibonacciHeap` over `Basis.standard`. -/
def dynamicProgram {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max) :
    DynamicProgram (IndexedMinPQ.spec n K_max) rFib :=
  (subroutineDS (n := n) (K_max := K_max) hS hK).toStandard.toDynamicProgram

/-- Standalone `DynamicCertificate` for `FibonacciHeap` over `Basis.standard`. -/
def certificate {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max) :
    DynamicCertificate (dynamicProgram hS hK) w :=
  (subroutineDS hS hK).toStandard.toCertificate

/-- Standalone `Stateful.Amortized` certificate for `FibonacciHeap` over `Basis.standard`, charging
`+ 1` per operation for the trailing `halt` instruction. -/
theorem amortized {n K_max w base : ℕ} (hS : Fits w (base + space n)) (hK : Fits w K_max) :
    Stateful.Amortized (certificate hS hK).realization
      DynamicProgram.OperationTrace.instructions
      (fun _ x => potential x)
      (fun s o => charge n s o + 1) :=
  (subroutineDS hS hK).toStandard.toAmortized

/-- Adaptive-client amortized execution bound for any admissible `IndexedMinPQ` client `p` over
`Basis.standard`. -/
theorem run_client_amortized {n K_max w base : ℕ} (hS : Fits w (base + space n))
    (hK : Fits w K_max) {α : Type*} (p : (IndexedMinPQ.spec n K_max).Client α)
    {s : IndexedMinPQ.State n} {x : Data rFib} (hr : FibInv n K_max w base s x)
    (hv : (IndexedMinPQ.spec n K_max).ValidHistory s
      ((IndexedMinPQ.spec n K_max).runClient s p).2.2) :
    ∃ y traces,
      Stateful.Executes ((dynamicProgram hS hK).ExecOp w) p x
        ((IndexedMinPQ.spec n K_max).runClient s p).1 y traces ∧
      FibInv n K_max w base ((IndexedMinPQ.spec n K_max).runClient s p).2.1 y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces + potential y ≤
        (IndexedMinPQ.spec n K_max).totalCost (fun s o => charge n s o + 1) s
          ((IndexedMinPQ.spec n K_max).runClient s p).2.2 + potential x :=
  (subroutineDS hS hK).toStandard.run_client_amortized p hr hv

/-! ## Standalone end-to-end `Basis.exact` flat-program operation-sequence theorems -/

/-- Compiled flat `Program .exact rFib` for `O(1)` fresh zeroed-memory initialization. -/
def initFreshProg : Program .exact rFib := code.toSubroutineCode.initFresh.program outFlag

/-- Compiled flat `Program .exact rFib` for `O(n)` dirty-memory reusable initialization. -/
def initClearProg : Program .exact rFib := code.toSubroutineCode.initClear.program outFlag

/-- Compiled flat `Program .exact rFib` serving all five priority-queue operations. -/
def opProg : Program .exact rFib := dispatchCode.program outFlag

/-- Initial register assignment supplying `n` in `nReg` (`R[0]`), `base` in `frontierReg` (`R[1]`),
and `0` elsewhere. -/
def initRegs (n base : ℕ) : Fin rFib → ℕ :=
  fun i => if i = nReg then n else if i = frontierReg then base else 0

/-- Deliver operation `o`'s 3-bit tag into `tag2..tag0` (`R[17..19]`) and its handle/key arguments
into `argV, argK` (`R[20..21]`), leaving all other registers unchanged. -/
def prepareRegs {n : ℕ} (o : IndexedMinPQ.Op n) (regs : Fin rFib → ℕ) : Fin rFib → ℕ :=
  fun i =>
    if i = tag2 ∨ i = tag1 ∨ i = tag0 ∨ i = argV ∨ i = argK then code.encode o i else regs i

/-- Count `isEmpty` and `getKey` queries in an operation sequence. -/
def numQueries {n : ℕ} : List (IndexedMinPQ.Op n) → ℕ
  | [] => 0
  | .isEmpty :: ops | .getKey _ :: ops => 1 + numQueries ops
  | _ :: ops => numQueries ops

/-- Count `insert` operations in an operation sequence. -/
def numInserts {n : ℕ} : List (IndexedMinPQ.Op n) → ℕ
  | [] => 0
  | .insert _ _ :: ops => 1 + numInserts ops
  | _ :: ops => numInserts ops

/-- Count `decreaseKey` operations in an operation sequence. -/
def numDecreaseKeys {n : ℕ} : List (IndexedMinPQ.Op n) → ℕ
  | [] => 0
  | .decreaseKey _ _ :: ops => 1 + numDecreaseKeys ops
  | _ :: ops => numDecreaseKeys ops

/-- Count `extractMin` operations in an operation sequence. -/
def numExtractMins {n : ℕ} : List (IndexedMinPQ.Op n) → ℕ
  | [] => 0
  | .extractMin :: ops => 1 + numExtractMins ops
  | _ :: ops => numExtractMins ops

/-- Sequential flat-program execution of `ops` by repeated calls to `opProg`: each call prepares
input registers via `prepareRegs`, runs `opProg` from `pc = 0` to `halt`, decodes the exact
`IndexedMinPQ` result, modifies memory only within `[base, base + space n)`, and accumulates total
instructions executed (each final `halt` included). -/
inductive RunsOps {n K_max : ℕ} (w base : ℕ) :
    IndexedMinPQ.State n → Data rFib → List (IndexedMinPQ.Op n) → Data rFib → ℕ → Prop
  | nil {s x} : RunsOps w base s x [] x 0
  | cons {s x o ops pc y z steps rest} :
      Runs w opProg ⟨0, ⟨prepareRegs o x.regs, x.mem⟩⟩ ⟨pc, y⟩ steps →
      (∃ out, step w opProg ⟨pc, y⟩ = .halt out) →
      code.decode (n := n) (K_max := K_max) o y.regs =
        some ((IndexedMinPQ.spec n K_max).step s o).2 →
      Modifies (Block.mk base (space n)).footprint x.mem y.mem →
      RunsOps w base ((IndexedMinPQ.spec n K_max).step s o).1 y ops z rest →
      RunsOps w base s x (o :: ops) z ((steps + 1) + rest)

private theorem step_program_halt {w : ℕ} (c : Code .exact rFib) (out : Fin rFib)
    (y : Data rFib) : step w (c.program out) ⟨0 + c.size, y⟩ = .halt (y.regs out) :=
  step_halt (by
    simp only [Code.program, Nat.zero_add,
      List.getElem?_append_right (Code.length_assemble c 0).le,
      Code.length_assemble, Nat.sub_self, List.getElem?_cons_zero])

private theorem seq_runsOps {n K_max w base : ℕ} (hS : Fits w (base + space n))
    (hK : Fits w K_max) :
    ∀ (ops : List (IndexedMinPQ.Op n)) {s : IndexedMinPQ.State n} {x : Data rFib},
      FibInv n K_max w base s x → (IndexedMinPQ.spec n K_max).ValidHistory s ops →
      ∃ z total, RunsOps (K_max := K_max) w base s x ops z total ∧
        FibInv n K_max w base
          (ops.foldl (fun st o => ((IndexedMinPQ.spec n K_max).step st o).1) s) z ∧
        total + potential z ≤
          421 * (numQueries ops + numInserts ops + numDecreaseKeys ops +
            numExtractMins ops * (Nat.log 2 n + 1)) + potential x
  | [], _, x, hinv, _ =>
    ⟨x, 0, .nil, hinv,
      by simp only [numQueries, numInserts, numDecreaseKeys, numExtractMins]; omega⟩
  | o :: ops, s, x, hinv, ⟨hv_o, hv_ops⟩ => by
    let x' : Data rFib := ⟨prepareRegs o x.regs, x.mem⟩
    have hb' : x'.Bounded w := by
      refine ⟨fun i => ?_, hinv.1.2⟩
      change Fits w (if _ then code.encode o i else x.regs i)
      split_ifs
      · exact code.arguments_fit (space_lower n) hS hK o hv_o i
      · exact hinv.1.1 i
    have hreg' : ∀ i, inputReg i = false → x'.regs i = x.regs i := fun i hi => by
      have hne : ¬(i = tag2 ∨ i = tag1 ∨ i = tag0 ∨ i = argV ∨ i = argK) := by
        rintro (rfl | rfl | rfl | rfl | rfl) <;> exact absurd hi (by decide)
      simp only [x', prepareRegs, hne, ↓reduceIte]
    have hinv' : FibInv n K_max w base s x' :=
      FibInv.supported hreg' (fun _ _ => rfl) hb' hinv
    have hpot' : potential x' = potential x := potential_supported hreg'
    have harg' : code.argMatch o x'.regs := by
      cases o <;> simp [x', prepareRegs, PQCode.argMatch, PQCode.encode, code,
        tag2, tag1, tag0, argV, argK]
    obtain ⟨y, m, he_op, hdec, hinv_y, hmod, hpot_m⟩ :=
      dispatchCode_exec o hinv' hv_o harg'
    rw [hpot'] at hpot_m
    have hruns : Runs w opProg ⟨0, x'⟩ ⟨0 + dispatchCode.size, y⟩ m :=
      he_op.runs (pc := 0) (p := opProg) (Program.Contains.self _).append_left
    have hhalt : step w opProg ⟨0 + dispatchCode.size, y⟩ = .halt (y.regs outFlag) :=
      step_program_halt dispatchCode outFlag y
    obtain ⟨z, rest, hrest, hinv_z, hpot_rest⟩ := seq_runsOps hS hK ops hinv_y hv_ops
    refine ⟨z, (m + 1) + rest, .cons hruns ⟨_, hhalt⟩ hdec hmod hrest, hinv_z, ?_⟩
    cases o <;>
      simp only [charge, tEmpty, tGet, tIns, tDec, tExt,
        numQueries, numInserts, numDecreaseKeys, numExtractMins,
        Nat.add_mul, Nat.one_mul] at hpot_m ⊢ <;>
      omega

private theorem initRegs_bounded {n base w : ℕ} (hS : Fits w (base + space n))
    {mem₀ : ℕ → ℕ} (hmem : ∀ a, Fits w (mem₀ a)) :
    (⟨initRegs n base, mem₀⟩ : Data rFib).Bounded w := by
  refine ⟨fun i => ?_, hmem⟩
  simp only [initRegs]
  split_ifs
  · exact hS.of_le (by simp only [space]; omega)
  · exact hS.of_le (Nat.le_add_right base _)
  · exact hS.of_le (Nat.zero_le _)

/-- Standalone `Basis.exact` operation-sequence theorem with `O(1)` fresh initialization on zeroed
`[base, base + 9 * n + 1)`. -/
theorem run_ops_exact_fresh {n K_max w base : ℕ} (hS : Fits w (base + space n))
    (hK : Fits w K_max) {mem₀ : ℕ → ℕ} (hmem : ∀ a, Fits w (mem₀ a))
    (hzero : ∀ a ∈ (Block.mk base (space n)).footprint, mem₀ a = 0)
    (ops : List (IndexedMinPQ.Op n))
    (hv : (IndexedMinPQ.spec n K_max).ValidHistory (IndexedMinPQ.empty n) ops) :
    ∃ pc₀ x₀ t_init z t_ops,
      Runs w initFreshProg ⟨0, ⟨initRegs n base, mem₀⟩⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w initFreshProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base (space n)).footprint mem₀ x₀.mem ∧
      RunsOps (K_max := K_max) w base (IndexedMinPQ.empty n) x₀ ops z t_ops ∧
      t_init + 1 ≤ 421 ∧
      t_ops ≤
        421 * (numQueries ops + numInserts ops + numDecreaseKeys ops +
          numExtractMins ops * (Nat.log 2 n + 1)) := by
  let d₀ : Data rFib := ⟨initRegs n base, mem₀⟩
  have hfr_eq : d₀.regs frontierReg = base := by
    simp only [d₀, initRegs, show frontierReg ≠ nReg by decide, ↓reduceIte]
  have hpar : ∀ j : Fin 1, d₀.regs (![nReg] j) = ![n] j := fun j => by
    fin_cases j; rfl
  obtain ⟨x₀, ⟨t_init, ht_init, he_init⟩, _, hinv₀, hpot₀, hmod₀⟩ :=
    (subroutineDS (K_max := K_max) hS hK).initFresh_exec (initRegs_bounded hS hmem) hfr_eq hpar
      hzero
  have hruns₀ : Runs w initFreshProg ⟨0, d₀⟩
      ⟨0 + code.toSubroutineCode.initFresh.size, x₀⟩ t_init :=
    he_init.runs (pc := 0) (p := initFreshProg) (Program.Contains.self _).append_left
  have hhalt₀ : step w initFreshProg ⟨0 + code.toSubroutineCode.initFresh.size, x₀⟩ =
      .halt (x₀.regs outFlag) :=
    step_program_halt code.toSubroutineCode.initFresh outFlag x₀
  obtain ⟨z, t_ops, hruns_ops, _, hbound⟩ := seq_runsOps hS hK ops hinv₀ hv
  refine ⟨_, x₀, t_init, z, t_ops, hruns₀, ⟨_, hhalt₀⟩, hmod₀, hruns_ops, ?_, ?_⟩
  · change t_init ≤ 26 at ht_init
    omega
  · change potential x₀ ≤ 0 at hpot₀
    omega

/-- Standalone `Basis.exact` operation-sequence theorem with `O(n)` reusable initialization on
arbitrary `w`-bounded memory `mem₀`. -/
theorem run_ops_exact_reusable {n K_max w base : ℕ} (hS : Fits w (base + space n))
    (hK : Fits w K_max) {mem₀ : ℕ → ℕ} (hmem : ∀ a, Fits w (mem₀ a))
    (ops : List (IndexedMinPQ.Op n))
    (hv : (IndexedMinPQ.spec n K_max).ValidHistory (IndexedMinPQ.empty n) ops) :
    ∃ pc₀ x₀ t_init z t_ops,
      Runs w initClearProg ⟨0, ⟨initRegs n base, mem₀⟩⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w initClearProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base (space n)).footprint mem₀ x₀.mem ∧
      RunsOps (K_max := K_max) w base (IndexedMinPQ.empty n) x₀ ops z t_ops ∧
      t_init + 1 ≤ 421 * (n + 1) ∧
      t_ops ≤
        421 * (numQueries ops + numInserts ops + numDecreaseKeys ops +
          numExtractMins ops * (Nat.log 2 n + 1)) := by
  let d₀ : Data rFib := ⟨initRegs n base, mem₀⟩
  have hfr_eq : d₀.regs frontierReg = base := by
    simp only [d₀, initRegs, show frontierReg ≠ nReg by decide, ↓reduceIte]
  have hpar : ∀ j : Fin 1, d₀.regs (![nReg] j) = ![n] j := fun j => by
    fin_cases j; rfl
  obtain ⟨x₀, ⟨t_init, ht_init, he_init⟩, _, hinv₀, hpot₀, hmod₀⟩ :=
    (subroutineDS (K_max := K_max) hS hK).initClear_exec (initRegs_bounded hS hmem) hfr_eq hpar
  have hruns₀ : Runs w initClearProg ⟨0, d₀⟩
      ⟨0 + code.toSubroutineCode.initClear.size, x₀⟩ t_init :=
    he_init.runs (pc := 0) (p := initClearProg) (Program.Contains.self _).append_left
  have hhalt₀ : step w initClearProg ⟨0 + code.toSubroutineCode.initClear.size, x₀⟩ =
      .halt (x₀.regs outFlag) :=
    step_program_halt code.toSubroutineCode.initClear outFlag x₀
  obtain ⟨z, t_ops, hruns_ops, _, hbound⟩ := seq_runsOps hS hK ops hinv₀ hv
  refine ⟨_, x₀, t_init, z, t_ops, hruns₀, ⟨_, hhalt₀⟩, hmod₀, hruns_ops, ?_, ?_⟩
  · change t_init ≤ 26 + 4 * (9 * n + 1) + 6 at ht_init
    omega
  · change potential x₀ ≤ 0 at hpot₀
    omega

end Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap
