/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.MinPQ
public import Complexity.Computability.WordRAM.RelSubroutine
public import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.BasicOps
public import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.Cut
public import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.Consolidate

/-!
# Fibonacci Heap with Handles and Satellite Values

This file realizes the relational priority-queue specification `Cslib.Algorithms.Lean.MinPQ.spec`
(returning an opaque handle `h : Fin n_max` on `insert` and `(u, v, h)` on `extractMin`) as a
Word-RAM `RelSubroutineDS` over `Cslib.WordRAM.Basis.exact` (and lifted to `Basis.standard`),
layered on top of `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap`.

Over capacity `n_max` in a contiguous memory block `[base, base + 11 * n_max + 1)`:
* `[base, base + 9 * n_max + 1)` holds the inner Fibonacci heap arrays (`key`, `par`, `child`,
  `left`, `right`, `deg`, `mark`, `inHeap`, `cons`);
* `[base + (9 * n_max + 1), base + (10 * n_max + 1))` holds satellite values `val[0..n_max-1]`;
* `[base + (10 * n_max + 1), base + (11 * n_max + 1))` holds the recycled-handle stack
  `freeStack[0..n_max-1]`, paired with persistent bump pointer `freshReg` and stack height
  `freeTopReg`.

## Main definitions

* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.MinPQ.rMinPQ`, `space`, `subroutineCode`:
  `48`-register, `(11 * n_max + 1)`-word `SubroutineCode .exact rMinPQ 1`.
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.MinPQ.Rep`, `charge`: relational
  representation invariant and per-operation amortized instruction charges (`O(log n + 1)` on
  `extractMin` in the current number of stored elements `n = MinPQ.size s`).
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.MinPQ.relSubroutineDS`:
  `RelSubroutineDS` certificate over `Basis.exact`.

## Main results

* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.MinPQ.relAmortized`,
  `run_client_amortized`: standalone `Stateful.RelAmortized` certificate and adaptive-client bound
  over `Basis.standard`.
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.MinPQ.run_ops_exact_fresh`,
  `run_ops_exact_reusable`: standalone `Basis.exact` flat-program execution theorems.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network optimization
  algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 19][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.MinPQ

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open scoped Cslib.WordRAM

/-! ## Register file (`rMinPQ = 48`), embedding `f42`, and footprint size -/

/-- Total register count of the key–value Fibonacci heap with handle allocation. -/
abbrev rMinPQ : ℕ := 48

/-- Outer bump-pointer frontier register (`base` before `allocSpan`, `base + space n_max` after). -/
abbrev outerFrontierReg : Fin rMinPQ := ⟨1, by decide⟩
/-- Persistent base address of `val[0..n_max-1]` (`base + 9 * n_max + 1`). Also serves as the
relocated image of the inner `FibonacciHeap.frontierReg`. -/
abbrev valBaseReg : Fin rMinPQ := ⟨42, by decide⟩
/-- Persistent base address of `freeStack[0..n_max-1]` (`base + 10 * n_max + 1`). -/
abbrev freeBaseReg : Fin rMinPQ := ⟨43, by decide⟩
/-- Persistent bump-pointer watermark `fresh` for never-allocated handles. -/
abbrev freshReg : Fin rMinPQ := ⟨44, by decide⟩
/-- Persistent stack height `freeTop` for recycled handles in `freeStack`. -/
abbrev freeTopReg : Fin rMinPQ := ⟨45, by decide⟩
/-- Caller input register carrying the satellite value `v` on `insert`. -/
abbrev inValReg : Fin rMinPQ := ⟨46, by decide⟩
/-- Output register carrying the satellite value `v` on `get` and `extractMin`. -/
abbrev outValReg : Fin rMinPQ := ⟨47, by decide⟩

/-- Injective register embedding from the inner `rFib = 42` Fibonacci heap into `rMinPQ = 48`,
mapping `FibonacciHeap.frontierReg` (`R[1]`) to `valBaseReg` (`R[42]`) so `outerFrontierReg`
(`R[1]`) remains outside `Set.range f42`. -/
def f42 (i : Fin rFib) : Fin rMinPQ :=
  if i = FibonacciHeap.frontierReg then valBaseReg else Fin.castLE (by decide) i

theorem f42_injective : Function.Injective f42 := by
  decide

theorem outerFrontierReg_notMem_range : outerFrontierReg ∉ Set.range f42 := by
  decide

theorem freeBaseReg_notMem_range : freeBaseReg ∉ Set.range f42 := by
  decide

theorem freshReg_notMem_range : freshReg ∉ Set.range f42 := by
  decide

theorem freeTopReg_notMem_range : freeTopReg ∉ Set.range f42 := by
  decide

theorem inValReg_notMem_range : inValReg ∉ Set.range f42 := by
  decide

theorem outValReg_notMem_range : outValReg ∉ Set.range f42 := by
  decide

/-- Persistent register holding handle capacity `n_max` (`R[0]`). -/
abbrev nReg : Fin rMinPQ := ⟨0, by decide⟩
/-- Persistent base address of `key[0..n_max-1]` (`R[2]`). -/
abbrev baseReg : Fin rMinPQ := ⟨2, by decide⟩
/-- Persistent constant register `0` (`R[11]`). -/
abbrev zeroP : Fin rMinPQ := ⟨11, by decide⟩
/-- Persistent constant register `1` (`R[12]`). -/
abbrev oneP : Fin rMinPQ := ⟨12, by decide⟩
/-- Caller high tag bit (`R[17]`, `≠ 0` selects `extractMin`). -/
abbrev tag2 : Fin rMinPQ := ⟨17, by decide⟩
/-- Caller middle tag bit (`R[18]`). -/
abbrev tag1 : Fin rMinPQ := ⟨18, by decide⟩
/-- Caller low tag bit (`R[19]`). -/
abbrev tag0 : Fin rMinPQ := ⟨19, by decide⟩
/-- Handle register (`R[20]`, input for `get`/`decreaseKey`, scratch for `insert`). -/
abbrev argV : Fin rMinPQ := ⟨20, by decide⟩
/-- Key input register (`R[21]`, `u` for `insert`, `u'` for `decreaseKey`). -/
abbrev argK : Fin rMinPQ := ⟨21, by decide⟩
/-- Primary output flag register (`R[22]`). -/
abbrev outFlag : Fin rMinPQ := ⟨22, by decide⟩
/-- Output handle register (`R[23]`, `h.val` for `insert` and non-empty `extractMin`). -/
abbrev outV : Fin rMinPQ := ⟨23, by decide⟩
/-- Output key register (`R[24]`, `u` for present `get` and non-empty `extractMin`). -/
abbrev outK : Fin rMinPQ := ⟨24, by decide⟩
/-- Scratch pointer register for `zeroFillCode` (`R[25]`). -/
abbrev curReg : Fin rMinPQ := ⟨25, by decide⟩
/-- Scratch zero register for `zeroFillCode` (`R[26]`). -/
abbrev zeroReg : Fin rMinPQ := ⟨26, by decide⟩
/-- Scratch one register for `zeroFillCode` (`R[27]`). -/
abbrev oneReg : Fin rMinPQ := ⟨27, by decide⟩
/-- Scratch address register (`R[35]`). -/
abbrev s0 : Fin rMinPQ := ⟨35, by decide⟩

/-- Persistent registers are `0..16` and `42..45` (`false`); caller/scratch registers are `17..41`
and `46..47` (`true`). -/
def inputReg (i : Fin rMinPQ) : Bool :=
  decide ((17 ≤ i.val ∧ i.val < 42) ∨ 46 ≤ i.val)

theorem inputReg_f42_of_false :
    ∀ i : Fin rFib, FibonacciHeap.inputReg i = false → inputReg (f42 i) = false := by
  decide

/-- Static memory footprint on capacity `n_max`: `11 * n_max + 1` words (`9 * n_max + 1` for the
inner Fibonacci heap plus `n_max` for `val` and `n_max` for `freeStack`). -/
def space (n_max : ℕ) : ℕ :=
  11 * n_max + 1

theorem space_eq_fib_add (n_max : ℕ) :
    space n_max = FibonacciHeap.space n_max + n_max + n_max := by
  unfold space FibonacciHeap.space
  omega

theorem space_lower (n_max : ℕ) : n_max + 1 ≤ space n_max := by
  unfold space
  omega

/-- Fresh-initialization instruction bound (`allocSpan` 15 + `initSetup` 18 = 33). -/
def tInit (_n_max : ℕ) : ℕ := 33
/-- Instruction bound for `isEmpty` (including dispatch). -/
def tEmpty (_n_max : ℕ) : ℕ := 12
/-- Instruction bound for `get` (including dispatch and value read). -/
def tGet (_n_max : ℕ) : ℕ := 20
/-- Amortized instruction bound for `insert` (including handle allocation, value write, and `+80`
root potential). -/
def tIns (_n_max : ℕ) : ℕ := 140
/-- Amortized instruction bound for `decreaseKey` (including dispatch and cascading cuts). -/
def tDec (_n_max : ℕ) : ℕ := 340
/-- Amortized instruction bound for `extractMin` (`420 * (Nat.log 2 n + 1)`). -/
def tExt (n : ℕ) : ℕ := 420 * (Nat.log 2 n + 1)

/-- Per-operation amortized instruction charge for the key–value Fibonacci heap, charging
`tExt (MinPQ.size s)` on `.extractMin` in terms of the current number of stored elements
`MinPQ.size s`. -/
def charge (n_max : ℕ) (s : Cslib.Algorithms.Lean.MinPQ.State n_max) :
    Cslib.Algorithms.Lean.MinPQ.Op n_max → ℕ
  | .isEmpty => tEmpty n_max
  | .get _ => tGet n_max
  | .insert _ _ => tIns n_max
  | .decreaseKey _ _ => tDec n_max
  | .extractMin => tExt (Cslib.Algorithms.Lean.MinPQ.size s)

/-- Since `MinPQ.size s ≤ n_max`, `charge n_max s .extractMin ≤ tExt n_max`. -/
theorem charge_extractMin_le_tExt (n_max : ℕ) (s : Cslib.Algorithms.Lean.MinPQ.State n_max) :
    charge n_max s .extractMin ≤ tExt n_max := by
  simp only [charge, tExt]
  have hlog : Nat.log 2 (Cslib.Algorithms.Lean.MinPQ.size s) ≤ Nat.log 2 n_max :=
    Nat.log_mono_right (Cslib.Algorithms.Lean.MinPQ.size_le s)
  omega

/-- Concrete integer potential `80 * (numRoots + 2 * numMarked)` inherited from the inner
Fibonacci heap. -/
def potential (x : Data rMinPQ) : ℕ :=
  FibonacciHeap.potential (x.comap f42)

/-! ## Structured `Basis.exact` subprograms and `subroutineCode` -/

/-- Copy `outerFrontierReg` into `valBaseReg`, run `FibonacciHeap.allocSpan.rename f42` to set
`baseReg = base` and `valBaseReg = base + 9 * n_max + 1`, then advance `freeBaseReg` and
`outerFrontierReg` by `n_max` each (`15` steps total). -/
def allocSpan : Code .exact rMinPQ :=
  ram_exact[
    valBaseReg ← outerFrontierReg;
    ⟪FibonacciHeap.allocSpan.rename f42⟫;
    freeBaseReg ← valBaseReg + nReg;
    outerFrontierReg ← freeBaseReg + nReg
  ]

/-- Initialize `freeBaseReg = outerFrontierReg - nReg`, `valBaseReg = freeBaseReg - nReg`,
`freshReg = 0`, `freeTopReg = 0`, and run `FibonacciHeap.initSetup.rename f42` (`18` steps
total). -/
def initSetup : Code .exact rMinPQ :=
  ram_exact[
    freeBaseReg ← outerFrontierReg - nReg;
    valBaseReg ← freeBaseReg - nReg;
    freshReg ← #0;
    freeTopReg ← #0;
    ⟪FibonacciHeap.initSetup.rename f42⟫
  ]

/-- `isEmpty`: delegates directly to `FibonacciHeap.isEmptyCode.rename f42`. -/
def isEmptyCode : Code .exact rMinPQ :=
  FibonacciHeap.isEmptyCode.rename f42

/-- `get h`: runs `FibonacciHeap.getKeyCode.rename f42` and, when `outFlag ≠ 0`, loads the
satellite value `outValReg ← val[argV]`. -/
def getCode : Code .exact rMinPQ :=
  ram_exact[
    ⟪FibonacciHeap.getKeyCode.rename f42⟫;
    if outFlag = zeroP then [
      s0 ← zeroP
    ] else [
      s0 ← valBaseReg + argV;
      outValReg ← *s0
    ]
  ]

/-- Handle-allocation branch of `insertCode`: pops a recycled handle from
`freeStack[freeTopReg - 1]` when `freeTopReg ≠ 0`, or allocates `freshReg` and increments
`freshReg` when `freeTopReg = 0`. -/
def allocHandleBranch : Code .exact rMinPQ :=
  ram_exact[
    if freeTopReg = zeroP then [
      argV ← freshReg;
      freshReg ← freshReg + oneP
    ] else [
      freeTopReg ← freeTopReg - oneP;
      s0 ← freeBaseReg + freeTopReg;
      argV ← *s0
    ]
  ]

/-- `insert u v`: allocates a handle `argV` from `freeStack` (if `freeTopReg > 0`) or bumps
`freshReg` via `allocHandleBranch`, stores `val[argV] ← inValReg`, runs
`FibonacciHeap.insertCode.rename f42` with key `argK = u`, and outputs `outV ← argV`. -/
def insertCode : Code .exact rMinPQ :=
  ram_exact[
    ⟪allocHandleBranch⟫;
    s0 ← valBaseReg + argV;
    *s0 ← inValReg;
    ⟪FibonacciHeap.insertCode.rename f42⟫;
    outV ← argV
  ]

/-- `decreaseKey h u'`: delegates directly to `FibonacciHeap.decreaseKeyCode.rename f42`. -/
def decreaseKeyCode : Code .exact rMinPQ :=
  FibonacciHeap.decreaseKeyCode.rename f42

/-- `extractMin`: runs `FibonacciHeap.extractMinCode.rename f42` and, when `outFlag ≠ 0`, loads
`outValReg ← val[outV]` and pushes `outV` onto `freeStack[freeTopReg]`. -/
def extractMinCode : Code .exact rMinPQ :=
  ram_exact[
    ⟪FibonacciHeap.extractMinCode.rename f42⟫;
    if outFlag = zeroP then [
      s0 ← zeroP
    ] else [
      s0 ← valBaseReg + outV;
      outValReg ← *s0;
      s0 ← freeBaseReg + freeTopReg;
      *s0 ← outV;
      freeTopReg ← freeTopReg + oneP
    ]
  ]

/-- Unified dispatcher over 1-bit tags `(tag2, tag1, tag0)`. -/
def dispatchCode : Code .exact rMinPQ :=
  ram_exact[
    if tag2 = zeroP then [
      if tag1 = zeroP then [
        if tag0 = zeroP then [
          ⟪isEmptyCode⟫
        ] else [
          ⟪getCode⟫
        ]
      ] else [
        if tag0 = zeroP then [
          ⟪insertCode⟫
        ] else [
          ⟪decreaseKeyCode⟫
        ]
      ]
    ] else [
      ⟪extractMinCode⟫
    ]
  ]

/-- Uniform `SubroutineCode .exact rMinPQ 1` for the key–value Fibonacci heap with handles. -/
def subroutineCode : SubroutineCode .exact rMinPQ 1 where
  allocSpan := allocSpan
  initSetup := initSetup
  code := dispatchCode
  frontierReg := outerFrontierReg
  baseReg := baseReg
  initParams := ![nReg]
  curReg := curReg
  zeroReg := zeroReg
  oneReg := oneReg
  incCur := .exactBin .add curReg curReg oneReg
  input := inputReg
  output := outFlag

/-! ## Calling convention: `encode`, `argMatch`, `decode` -/

/-- Raw register encoding for `Cslib.Algorithms.Lean.MinPQ.Op n_max` using 1-bit tags
`(tag2, tag1, tag0)`. -/
def rawEncode {n_max : ℕ} : Cslib.Algorithms.Lean.MinPQ.Op n_max → Fin rMinPQ → ℕ
  | .isEmpty => fun _ => 0
  | .get h => fun i => if i = tag0 then 1 else if i = argV then h.val else 0
  | .insert u v => fun i =>
      if i = tag1 then 1 else if i = argK then u else if i = inValReg then v else 0
  | .decreaseKey h u' => fun i =>
      if i = tag1 then 1 else if i = tag0 then 1
      else if i = argV then h.val else if i = argK then u' else 0
  | .extractMin => fun i => if i = tag2 then 1 else 0

/-- Register encoding for `Cslib.Algorithms.Lean.MinPQ.Op n_max` bounded by `U` on `decreaseKey`
so `arguments_fit` holds on arbitrary states; coincides with `rawEncode` on every represented
state (`encode_eq_rawEncode_of_rep`). -/
def encode {n_max : ℕ} (U : ℕ) : Cslib.Algorithms.Lean.MinPQ.Op n_max → Fin rMinPQ → ℕ
  | .decreaseKey h u' => fun i =>
      if i = tag1 then 1 else if i = tag0 then 1
      else if i = argV then h.val else if i = argK then (if u' < U then u' else 0) else 0
  | o => rawEncode o

/-- Standard argument-matching predicate for `Cslib.Algorithms.Lean.MinPQ.Op n_max`. -/
def rawArgMatch {n_max : ℕ} : Cslib.Algorithms.Lean.MinPQ.Op n_max → (Fin rMinPQ → ℕ) → Prop
  | .isEmpty => fun regs => regs tag2 = 0 ∧ regs tag1 = 0 ∧ regs tag0 = 0
  | .get h => fun regs =>
      regs tag2 = 0 ∧ regs tag1 = 0 ∧ regs tag0 ≠ 0 ∧ regs argV = h.val
  | .insert u v => fun regs =>
      regs tag2 = 0 ∧ regs tag1 ≠ 0 ∧ regs tag0 = 0 ∧ regs argK = u ∧ regs inValReg = v
  | .decreaseKey h u' => fun regs =>
      regs tag2 = 0 ∧ regs tag1 ≠ 0 ∧ regs tag0 ≠ 0 ∧ regs argV = h.val ∧ regs argK = u'
  | .extractMin => fun regs => regs tag2 ≠ 0

/-- Argument-matching predicate paired with `encode U` for `RelSubroutineDS`. -/
def argMatch {n_max : ℕ} (U : ℕ) : Cslib.Algorithms.Lean.MinPQ.Op n_max → (Fin rMinPQ → ℕ) → Prop
  | .decreaseKey h u' => fun regs =>
      regs tag2 = 0 ∧ regs tag1 ≠ 0 ∧ regs tag0 ≠ 0 ∧ regs argV = h.val ∧
        regs argK = (if u' < U then u' else 0)
  | o => rawArgMatch o

/-- Output decoder for `Cslib.Algorithms.Lean.MinPQ.spec n_max U V`. -/
def decode {n_max U V : ℕ} :
    (o : (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).Op) → (Fin rMinPQ → ℕ) →
      Option ((Cslib.Algorithms.Lean.MinPQ.spec n_max U V).Result o)
  | .isEmpty, regs => some (decide (regs outFlag ≠ 0))
  | .get _, regs =>
      if regs outFlag = 0 then some none else some (some (regs outK, regs outValReg))
  | .insert _ _, regs =>
      if h : regs outV < n_max then some (some ⟨regs outV, h⟩) else none
  | .decreaseKey _ _, _ => some ()
  | .extractMin, regs =>
      if regs outFlag = 0 then some none
      else if h : regs outV < n_max then some (some (regs outK, regs outValReg, ⟨regs outV, h⟩))
      else none

theorem arguments_fit {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V)
    {s : Cslib.Algorithms.Lean.MinPQ.State n_max} (o : Cslib.Algorithms.Lean.MinPQ.Op n_max)
    (hv : (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).valid s o) (i : Fin rMinPQ) :
    Fits w (encode U o i) := by
  have hsp := space_lower n_max
  have h0 : Fits w 0 := hS.of_le (Nat.zero_le _)
  have h1 : Fits w 1 := hS.of_le (by omega)
  cases o with
  | isEmpty => exact h0
  | get h =>
    simp only [encode, rawEncode]
    split_ifs
    · exact h1
    · exact hS.of_le (by have := h.isLt; omega)
    · exact h0
  | insert u v =>
    obtain ⟨_, hu, hv_lt⟩ := hv
    simp only [encode, rawEncode]
    split_ifs
    · exact h1
    · exact hU.of_le (Nat.le_of_lt hu)
    · exact hV.of_le (Nat.le_of_lt hv_lt)
    · exact h0
  | decreaseKey h u' =>
    simp only [encode]
    split_ifs with _ _ _ _ hu'
    · exact h1
    · exact h1
    · exact hS.of_le (by have := h.isLt; omega)
    · exact hU.of_le (Nat.le_of_lt hu')
    · exact h0
    · exact h0
  | extractMin =>
    simp only [encode, rawEncode]
    split_ifs
    · exact h1
    · exact h0

theorem encode_matches {n_max U : ℕ} (o : Cslib.Algorithms.Lean.MinPQ.Op n_max)
    (regs : Fin rMinPQ → ℕ) :
    argMatch U o (fun i => if subroutineCode.input i then encode U o i else regs i) := by
  cases o with
  | isEmpty =>
    refine ⟨rfl, rfl, rfl⟩
  | get h =>
    refine ⟨rfl, rfl, Nat.one_ne_zero, rfl⟩
  | insert u v =>
    refine ⟨rfl, Nat.one_ne_zero, rfl, rfl, rfl⟩
  | decreaseKey h u' =>
    refine ⟨rfl, Nat.one_ne_zero, Nat.one_ne_zero, rfl, rfl⟩
  | extractMin =>
    exact Nat.one_ne_zero


/-! ## Representation invariant (`AllocRep`, `Rep`) and framing lemmas -/

/-- Full machine-state representation invariant for an internal allocator state
`s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max`. -/
def AllocRep (n_max U V w base : ℕ) (s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max)
    (x : Data rMinPQ) : Prop :=
  x.Bounded w ∧
  FibonacciHeap.FibInv n_max U w base (Cslib.Algorithms.Lean.MinPQ.toIndexed s.entries)
    (x.comap f42) ∧
  s.WellFormed ∧
  x.regs outerFrontierReg = base + space n_max ∧
  x.regs freeBaseReg = base + FibonacciHeap.space n_max + n_max ∧
  x.regs freshReg = s.fresh ∧
  x.regs freeTopReg = s.freeList.length ∧
  (∀ (h : Fin n_max) (u v : ℕ), s.entries h = some (u, v) →
    u < U ∧ v < V ∧ x.mem (base + FibonacciHeap.space n_max + h.val) = v) ∧
  (∀ (i : ℕ) (hi : i < s.freeList.length),
    x.mem (base + FibonacciHeap.space n_max + n_max + (s.freeList.length - 1 - i)) =
      (s.freeList[i]).val)

/-- Existential relational representation invariant over abstract state
`e : Cslib.Algorithms.Lean.MinPQ.State n_max`. -/
def Rep (n_max U V w base : ℕ) (e : Cslib.Algorithms.Lean.MinPQ.State n_max)
    (x : Data rMinPQ) : Prop :=
  ∃ s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max,
    s.entries = e ∧ AllocRep n_max U V w base s x

theorem owns_val_addr {n_max base idx : ℕ} (hidx : idx < n_max) :
    (Block.mk base (space n_max)).Owns (base + FibonacciHeap.space n_max + idx) := by
  dsimp only [Block.Owns, space, FibonacciHeap.space]
  omega

theorem owns_free_addr {n_max base idx : ℕ} (hidx : idx < n_max) :
    (Block.mk base (space n_max)).Owns (base + FibonacciHeap.space n_max + n_max + idx) := by
  dsimp only [Block.Owns, space, FibonacciHeap.space]
  omega

theorem notMem_fib_footprint_of_ge {n_max base a : ℕ} (ha : base + FibonacciHeap.space n_max ≤ a) :
    a ∉ (Block.mk base (FibonacciHeap.space n_max)).footprint := by
  rw [Block.mem_footprint, Block.Owns]
  dsimp only
  omega

theorem fib_footprint_subset {n_max base : ℕ} :
    (Block.mk base (FibonacciHeap.space n_max)).footprint ⊆
      (Block.mk base (space n_max)).footprint := by
  intro a ha
  rw [Block.mem_footprint, Block.Owns] at ha ⊢
  dsimp only [space, FibonacciHeap.space] at ha ⊢
  omega

theorem modifies_of_fib {n_max base : ℕ} {m₁ m₂ : ℕ → ℕ}
    (h : Modifies (Block.mk base (FibonacciHeap.space n_max)).footprint m₁ m₂) :
    Modifies (Block.mk base (space n_max)).footprint m₁ m₂ :=
  fun a ha => h a fun ha' => ha (fib_footprint_subset ha')

theorem AllocRep.supported {n_max U V w base : ℕ}
    {s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max} {x x' : Data rMinPQ}
    (hreg : ∀ i : Fin rMinPQ, inputReg i = false → x'.regs i = x.regs i)
    (hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, x'.mem a = x.mem a)
    (hb' : x'.Bounded w) (h : AllocRep n_max U V w base s x) :
    AllocRep n_max U V w base s x' := by
  obtain ⟨_, hfib, hwf, hfr, hfb, hfresh, htop, hval, hfree⟩ := h
  refine ⟨hb', ?_, hwf,
    (hreg outerFrontierReg (by decide)).trans hfr,
    (hreg freeBaseReg (by decide)).trans hfb,
    (hreg freshReg (by decide)).trans hfresh,
    (hreg freeTopReg (by decide)).trans htop, ?_, ?_⟩
  · refine FibonacciHeap.FibInv.supported (fun j hj => ?_) (fun a ha => ?_) (hb'.comap f42) hfib
    · exact hreg (f42 j) (inputReg_f42_of_false j hj)
    · exact hmem a (fib_footprint_subset ha)
  · intro h u v hsh
    obtain ⟨hu, hv, hm⟩ := hval h u v hsh
    refine ⟨hu, hv, ?_⟩
    rw [hmem _ (Block.mem_footprint.mpr (owns_val_addr h.isLt))]
    exact hm
  · intro i hi
    have hlt : s.freeList.length - 1 - i < n_max := by
      have := hwf.1
      have := hwf.2.2.2.2
      omega
    rw [hmem _ (Block.mem_footprint.mpr (owns_free_addr hlt))]
    exact hfree i hi

theorem Rep.supported {n_max U V w base : ℕ}
    {e : Cslib.Algorithms.Lean.MinPQ.State n_max} {x x' : Data rMinPQ}
    (hreg : ∀ i : Fin rMinPQ, inputReg i = false → x'.regs i = x.regs i)
    (hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, x'.mem a = x.mem a)
    (hb' : x'.Bounded w) (h : Rep n_max U V w base e x) :
    Rep n_max U V w base e x' := by
  obtain ⟨s, rfl, hs⟩ := h
  exact ⟨s, rfl, hs.supported hreg hmem hb'⟩

theorem potential_supported {x x' : Data rMinPQ}
    (hreg : ∀ i : Fin rMinPQ, inputReg i = false → x'.regs i = x.regs i) :
    potential x' = potential x :=
  FibonacciHeap.potential_supported fun j hj => hreg (f42 j) (inputReg_f42_of_false j hj)

theorem rawArgMatch_of_argMatch {n_max U V w base : ℕ}
    {s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max} {x : Data rMinPQ}
    {o : Cslib.Algorithms.Lean.MinPQ.Op n_max}
    (hrep : AllocRep n_max U V w base s x)
    (hv : (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).valid s.entries o)
    (harg : argMatch U o x.regs) :
    rawArgMatch o x.regs := by
  cases o with
  | isEmpty | get _ | insert _ _ | extractMin => exact harg
  | decreaseKey h u' =>
    obtain ⟨u, v, hsh, hu'⟩ := hv
    have hu_lt : u < U := (hrep.2.2.2.2.2.2.2.1 h u v hsh).1
    have hu'_lt : u' < U := Nat.lt_of_le_of_lt hu' hu_lt
    simp only [argMatch, hu'_lt, ↓reduceIte] at harg
    exact harg

theorem encode_eq_rawEncode_of_rep {n_max U V w base : ℕ}
    {e : Cslib.Algorithms.Lean.MinPQ.State n_max} {x : Data rMinPQ}
    {o : Cslib.Algorithms.Lean.MinPQ.Op n_max}
    (hr : Rep n_max U V w base e x)
    (hv : (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).valid e o) :
    encode U o = rawEncode o := by
  cases o with
  | isEmpty | get _ | insert _ _ | extractMin => rfl
  | decreaseKey h u' =>
    obtain ⟨s, rfl, hrep⟩ := hr
    obtain ⟨u, v, hsh, hu'⟩ := hv
    have hu_lt : u < U := (hrep.2.2.2.2.2.2.2.1 h u v hsh).1
    have hu'_lt : u' < U := Nat.lt_of_le_of_lt hu' hu_lt
    funext i
    simp only [encode, rawEncode, hu'_lt, ↓reduceIte]

/-! ## Initialization: `incCur_eval`, `allocSpan_exec`, `initSetup_exec` -/

theorem incCur_eval {w : ℕ} {x : Data rMinPQ} (h1 : x.regs oneReg = 1)
    (hfit : Fits w (x.regs curReg + 1)) :
    (Op.exactBin .add curReg curReg oneReg).eval w x =
      some (x.set curReg (x.regs curReg + 1)) := by
  rw [Op.eval_exactBin]
  simp only [BinOp.evalExact, h1, Option.bind_some]
  exact Data.put_of_fits hfit

theorem allocSpan_exec {n_max w base : ℕ} (hS : Fits w (base + space n_max))
    {x : Data rMinPQ} (hx : x.Bounded w) (hfr : x.regs outerFrontierReg = base)
    (hpar : ∀ j : Fin 1, x.regs (![nReg] j) = ![n_max] j) :
    ∃ x₁, ExecWithin w allocSpan x x₁ 15 ∧ x₁.mem = x.mem ∧
      x₁.regs baseReg = base ∧ x₁.regs outerFrontierReg = base + space n_max ∧
      (∀ j : Fin 1, x₁.regs (![nReg] j) = ![n_max] j) := by
  have hn : x.regs nReg = n_max := hpar 0
  have hS_fib : Fits w (base + FibonacciHeap.space n_max) := by
    rw [space_eq_fib_add] at hS
    exact hS.of_le (by omega)
  let x0 := x.set valBaseReg base
  have e0 : ExecWithin (B := .exact) w (.op (.copy valBaseReg outerFrontierReg)) x x0 1 := by
    simpa only [hfr] using
      (ExecWithin.copy (B := .exact) (w := w) (x := x) (d := valBaseReg) (s := outerFrontierReg))
  have hx0_b : (x0.comap f42).Bounded w := (e0.bounded hx).comap f42
  have hx0_fr : (x0.comap f42).regs FibonacciHeap.frontierReg = base := by
    change x0.regs valBaseReg = base
    simp only [x0, Data.set_regs, Function.update_self]
  have hx0_par : ∀ j : Fin 1, (x0.comap f42).regs (![FibonacciHeap.nReg] j) = ![n_max] j := by
    intro j
    fin_cases j
    change x0.regs nReg = n_max
    simp only [x0, Data.set_regs, Function.update_of_ne (by decide : nReg ≠ valBaseReg), hn]
  obtain ⟨y_fib, he_fib, hm_fib, hb_fib, hfr_fib, hpar_fib⟩ :=
    FibonacciHeap.allocSpan_exec hS_fib hx0_b hx0_fr hx0_par
  let x1 := y_fib.extend f42 x0
  have e1 : ExecWithin w (FibonacciHeap.allocSpan.rename f42) x0 x1 12 :=
    he_fib.rename f42_injective
  have hx1_vb : x1.regs valBaseReg = base + FibonacciHeap.space n_max := by
    change (x1.comap f42).regs FibonacciHeap.frontierReg = base + FibonacciHeap.space n_max
    rw [Data.comap_extend f42_injective]
    exact hfr_fib
  have hx1_b : x1.regs baseReg = base := by
    change (x1.comap f42).regs FibonacciHeap.baseReg = base
    rw [Data.comap_extend f42_injective]
    exact hb_fib
  have hx1_n : x1.regs nReg = n_max := by
    change (x1.comap f42).regs FibonacciHeap.nReg = n_max
    rw [Data.comap_extend f42_injective]
    exact hpar_fib 0
  let x2 := x1.set freeBaseReg (base + FibonacciHeap.space n_max + n_max)
  have e2 : ExecWithin w (.op (.exactBin .add freeBaseReg valBaseReg nReg)) x1 x2 1 := by
    simpa only [hx1_vb, hx1_n] using
      FibonacciHeap.execWithin_exactAdd (x := x1) (d := freeBaseReg) (i := valBaseReg) (j := nReg)
        (by rw [hx1_vb, hx1_n]; rw [space_eq_fib_add] at hS; exact hS.of_le (by omega))
  have hx2_fb : x2.regs freeBaseReg = base + FibonacciHeap.space n_max + n_max := by
    simp only [x2, Data.set_regs, Function.update_self]
  have hx2_n : x2.regs nReg = n_max := by
    simp only [x2, Data.set_regs, Function.update_of_ne (by decide : nReg ≠ freeBaseReg), hx1_n]
  let x3 := x2.set outerFrontierReg (base + space n_max)
  have e3 : ExecWithin w (.op (.exactBin .add outerFrontierReg freeBaseReg nReg)) x2 x3 1 := by
    have heq : base + FibonacciHeap.space n_max + n_max + n_max = base + space n_max := by
      rw [space_eq_fib_add]; omega
    simpa only [hx2_fb, hx2_n, heq] using
      FibonacciHeap.execWithin_exactAdd
        (x := x2) (d := outerFrontierReg) (i := freeBaseReg) (j := nReg)
        (by rw [hx2_fb, hx2_n, heq]; exact hS)
  have he : ExecWithin w allocSpan x x3 15 := by
    unfold allocSpan
    exact (e0.seq (e1.seq (e2.seq e3))).mono (by omega)
  refine ⟨x3, he, hm_fib, ?_, ?_, ?_⟩
  · simp only [x3, x2, Data.set_regs,
      Function.update_of_ne (by decide : baseReg ≠ outerFrontierReg),
      Function.update_of_ne (by decide : baseReg ≠ freeBaseReg), hx1_b]
  · simp only [x3, Data.set_regs, Function.update_self]
  · intro j
    fin_cases j
    change x3.regs nReg = n_max
    simp only [x3, Data.set_regs,
      Function.update_of_ne (by decide : nReg ≠ outerFrontierReg), hx2_n]

theorem initSetup_exec {n_max U V w base : ℕ} {x₁ : Data rMinPQ}
    (hx₁ : x₁.Bounded w) (hb₁ : x₁.regs baseReg = base)
    (hfr₁ : x₁.regs outerFrontierReg = base + space n_max)
    (hpar₁ : ∀ j : Fin 1, x₁.regs (![nReg] j) = ![n_max] j)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x₁.mem a = 0) :
    ∃ y, ExecWithin w initSetup x₁ y 18 ∧ y.regs outerFrontierReg = base + space n_max ∧
      Rep n_max U V w base (Cslib.Algorithms.Lean.MinPQ.empty n_max) y ∧ potential y ≤ 0 ∧
      Modifies (Block.mk base (space n_max)).footprint x₁.mem y.mem := by
  have hn : x₁.regs nReg = n_max := hpar₁ 0
  have hS : Fits w (base + space n_max) := hfr₁ ▸ hx₁.1 outerFrontierReg
  have hfit0 : Fits w 0 := hS.of_le (Nat.zero_le _)
  let s1 := x₁.set freeBaseReg (base + FibonacciHeap.space n_max + n_max)
  have e1 : ExecWithin w (.op (.exactBin .sub freeBaseReg outerFrontierReg nReg)) x₁ s1 1 := by
    have hsub : base + space n_max - n_max = base + FibonacciHeap.space n_max + n_max := by
      rw [space_eq_fib_add]; omega
    simpa only [hfr₁, hn, hsub] using
      FibonacciHeap.execWithin_exactSub
        (x := x₁) (d := freeBaseReg) (i := outerFrontierReg) (j := nReg)
        (by rw [hfr₁, hn, space_eq_fib_add]; omega)
        (by rw [hfr₁, hn, hsub]; rw [space_eq_fib_add] at hS; exact hS.of_le (by omega))
  have hs1_fb : s1.regs freeBaseReg = base + FibonacciHeap.space n_max + n_max := by
    simp only [s1, Data.set_regs, Function.update_self]
  have hs1_n : s1.regs nReg = n_max := by
    simp only [s1, Data.set_regs, Function.update_of_ne (by decide : nReg ≠ freeBaseReg), hn]
  let s2 := s1.set valBaseReg (base + FibonacciHeap.space n_max)
  have e2 : ExecWithin w (.op (.exactBin .sub valBaseReg freeBaseReg nReg)) s1 s2 1 := by
    simpa only [hs1_fb, hs1_n, Nat.add_sub_cancel] using
      FibonacciHeap.execWithin_exactSub (x := s1) (d := valBaseReg) (i := freeBaseReg) (j := nReg)
        (by rw [hs1_fb, hs1_n]; omega)
        (by
          rw [hs1_fb, hs1_n, Nat.add_sub_cancel]
          rw [space_eq_fib_add] at hS
          exact hS.of_le (by omega))
  let s3 := s2.set freshReg 0
  have e3 : ExecWithin (B := .exact) w (.op (.const freshReg 0)) s2 s3 1 :=
    ExecWithin.const hfit0
  let s4 := s3.set freeTopReg 0
  have e4 : ExecWithin (B := .exact) w (.op (.const freeTopReg 0)) s3 s4 1 :=
    ExecWithin.const hfit0
  have hs4_b : s4.Bounded w := e4.bounded (e3.bounded (e2.bounded (e1.bounded hx₁)))
  have hs4_base : (s4.comap f42).regs FibonacciHeap.baseReg = base := by
    change s4.regs baseReg = base
    simp only [s4, s3, s2, s1, Data.set_regs,
      Function.update_of_ne (by decide : baseReg ≠ freeTopReg),
      Function.update_of_ne (by decide : baseReg ≠ freshReg),
      Function.update_of_ne (by decide : baseReg ≠ valBaseReg),
      Function.update_of_ne (by decide : baseReg ≠ freeBaseReg), hb₁]
  have hs4_fr : (s4.comap f42).regs FibonacciHeap.frontierReg =
      base + FibonacciHeap.space n_max := by
    change s4.regs valBaseReg = base + FibonacciHeap.space n_max
    simp only [s4, s3, s2, Data.set_regs,
      Function.update_of_ne (by decide : valBaseReg ≠ freeTopReg),
      Function.update_of_ne (by decide : valBaseReg ≠ freshReg),
      Function.update_self]
  have hs4_par : ∀ j : Fin 1, (s4.comap f42).regs (![FibonacciHeap.nReg] j) = ![n_max] j := by
    intro j
    fin_cases j
    change s4.regs nReg = n_max
    simp only [s4, s3, s2, Data.set_regs,
      Function.update_of_ne (by decide : nReg ≠ freeTopReg),
      Function.update_of_ne (by decide : nReg ≠ freshReg),
      Function.update_of_ne (by decide : nReg ≠ valBaseReg), hs1_n]
  have hz_fib : ∀ a ∈ (Block.mk base (FibonacciHeap.space n_max)).footprint,
      (s4.comap f42).mem a = 0 :=
    fun a ha => hz a (fib_footprint_subset ha)
  obtain ⟨y_fib, he_fib, hfr_fib, hinv_fib, hpot_fib, hmod_fib⟩ :=
    FibonacciHeap.initSetup_exec (K_max := U) (hs4_b.comap f42) hs4_base hs4_fr hs4_par hz_fib
  let y := y_fib.extend f42 s4
  have e5 : ExecWithin w (FibonacciHeap.initSetup.rename f42) s4 y 14 :=
    he_fib.rename f42_injective
  have he : ExecWithin w initSetup x₁ y 18 := by
    unfold initSetup
    exact (e1.seq (e2.seq (e3.seq (e4.seq e5)))).mono (by omega)
  have hy_ofr : y.regs outerFrontierReg = base + space n_max := by
    rw [Data.extend_regs_of_notMem y_fib s4 outerFrontierReg_notMem_range]
    simp only [s4, s3, s2, s1, Data.set_regs,
      Function.update_of_ne (by decide : outerFrontierReg ≠ freeTopReg),
      Function.update_of_ne (by decide : outerFrontierReg ≠ freshReg),
      Function.update_of_ne (by decide : outerFrontierReg ≠ valBaseReg),
      Function.update_of_ne (by decide : outerFrontierReg ≠ freeBaseReg), hfr₁]
  refine ⟨y, he, hy_ofr,
    ⟨Cslib.Algorithms.Lean.MinPQ.AllocState.empty n_max, rfl,
      he.bounded hx₁, ?_,
      Cslib.Algorithms.Lean.MinPQ.AllocState.wellFormed_empty n_max,
      hy_ofr, ?_, ?_, ?_, ?_,
      fun _ hi => absurd hi (Nat.not_lt_zero _)⟩,
    ?_, modifies_of_fib hmod_fib⟩
  · rw [Data.comap_extend f42_injective]
    exact hinv_fib
  · rw [Data.extend_regs_of_notMem y_fib s4 freeBaseReg_notMem_range]
    simp only [s4, s3, s2, Data.set_regs,
      Function.update_of_ne (by decide : freeBaseReg ≠ freeTopReg),
      Function.update_of_ne (by decide : freeBaseReg ≠ freshReg),
      Function.update_of_ne (by decide : freeBaseReg ≠ valBaseReg), hs1_fb]
  · rw [Data.extend_regs_of_notMem y_fib s4 freshReg_notMem_range]
    simp only [s4, s3, Data.set_regs,
      Function.update_of_ne (by decide : freshReg ≠ freeTopReg), Function.update_self]
    rfl
  · rw [Data.extend_regs_of_notMem y_fib s4 freeTopReg_notMem_range]
    simp only [s4, Data.set_regs, Function.update_self]
    rfl
  · rintro _ _ _ ⟨⟩
  · unfold potential
    rw [Data.comap_extend f42_injective]
    exact hpot_fib

/-! ## Operation specifications: `isEmptyCode`, `getCode`, `insertCode` -/

theorem AllocRep.fits_stop {n_max U V w base : ℕ}
    {s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x) : Fits w (base + space n_max) :=
  hrep.2.2.2.1 ▸ hrep.1.1 outerFrontierReg

theorem AllocRep.valBase_eq {n_max U V w base : ℕ}
    {s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x) :
    x.regs valBaseReg = base + FibonacciHeap.space n_max :=
  hrep.2.1.2.1.2.1

theorem AllocRep.zeroP_eq {n_max U V w base : ℕ}
    {s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x) : x.regs zeroP = 0 :=
  hrep.2.1.2.1.2.2.2.2.2.2.2.2.2.2.2.1

theorem AllocRep.oneP_eq {n_max U V w base : ℕ}
    {s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x) : x.regs oneP = 1 :=
  hrep.2.1.2.1.2.2.2.2.2.2.2.2.2.2.2.2

theorem isEmptyCode_exec {n_max U V w base : ℕ}
    {s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x) :
    ∃ y t, ExecWithin w isEmptyCode x y t ∧
      decode (n_max := n_max) (U := U) (V := V) .isEmpty y.regs =
        some (Cslib.Algorithms.Lean.MinPQ.stepAlloc s .isEmpty).2 ∧
      AllocRep n_max U V w base (Cslib.Algorithms.Lean.MinPQ.stepAlloc s .isEmpty).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      t + potential y ≤ 3 + potential x := by
  obtain ⟨hb, hfib, hwf, hfr, hfb, hfresh, htop, hval, hfree⟩ := hrep
  obtain ⟨y_fib, t, he_fib, hdec_fib, hinv_fib, hmod_fib, hpot_fib⟩ :=
    FibonacciHeap.isEmptyCode_exec hfib
  let y := y_fib.extend f42 x
  have he : ExecWithin w isEmptyCode x y t := he_fib.rename f42_injective
  have hmem_ge : ∀ a, base + FibonacciHeap.space n_max ≤ a → y.mem a = x.mem a :=
    fun a ha => hmod_fib a (notMem_fib_footprint_of_ge ha)
  refine ⟨y, t, he, ?_,
    ⟨he.bounded hb, ?_, hwf,
      (Data.extend_regs_of_notMem y_fib x outerFrontierReg_notMem_range).trans hfr,
      (Data.extend_regs_of_notMem y_fib x freeBaseReg_notMem_range).trans hfb,
      (Data.extend_regs_of_notMem y_fib x freshReg_notMem_range).trans hfresh,
      (Data.extend_regs_of_notMem y_fib x freeTopReg_notMem_range).trans htop,
      fun h u v hsh => ⟨(hval h u v hsh).1, (hval h u v hsh).2.1,
        (hmem_ge _ (Nat.le_add_right _ _)).trans (hval h u v hsh).2.2⟩,
      fun i hi => (hmem_ge _ (by omega)).trans (hfree i hi)⟩,
    modifies_of_fib hmod_fib, ?_⟩
  · simp only [PQCode.decode, FibonacciHeap.code, Cslib.Algorithms.Lean.MinPQ.dom_toIndexed]
      at hdec_fib
    have hfl_eq : y.regs outFlag = y_fib.regs FibonacciHeap.outFlag := by
      change (y.comap f42).regs FibonacciHeap.outFlag = y_fib.regs FibonacciHeap.outFlag
      rw [Data.comap_extend f42_injective]
    simp only [decode, Cslib.Algorithms.Lean.MinPQ.stepAlloc, hfl_eq]
    exact hdec_fib
  · simp only [Cslib.Algorithms.Lean.MinPQ.stepAlloc]
    rw [Data.comap_extend f42_injective]
    exact hinv_fib
  · unfold potential
    rw [Data.comap_extend f42_injective]
    exact hpot_fib

theorem getCode_exec {n_max U V w base : ℕ}
    {s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (h : Fin n_max) (hrep : AllocRep n_max U V w base s x) (hv_reg : x.regs argV = h.val) :
    ∃ y t, ExecWithin w getCode x y t ∧
      decode (n_max := n_max) (U := U) (V := V) (.get h) y.regs =
        some (Cslib.Algorithms.Lean.MinPQ.stepAlloc s (.get h)).2 ∧
      AllocRep n_max U V w base (Cslib.Algorithms.Lean.MinPQ.stepAlloc s (.get h)).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      t + potential y ≤ 11 + potential x := by
  have hfit_stop := hrep.fits_stop
  obtain ⟨hb, hfib, hwf, hfr, hfb, hfresh, htop, hval, hfree⟩ := hrep
  obtain ⟨y_fib, t1, he_fib, hdec_fib, hinv_fib, hmod_fib, hpot_fib⟩ :=
    FibonacciHeap.getKeyCode_exec h hfib hv_reg
  let x1 := y_fib.extend f42 x
  have he1 : ExecWithin w (FibonacciHeap.getKeyCode.rename f42) x x1 t1 :=
    he_fib.rename f42_injective
  have hmem1_ge : ∀ a, base + FibonacciHeap.space n_max ≤ a → x1.mem a = x.mem a :=
    fun a ha => hmod_fib a (notMem_fib_footprint_of_ge ha)
  have hrep1 : AllocRep n_max U V w base s x1 :=
    ⟨he1.bounded hb, by rw [Data.comap_extend f42_injective]; exact hinv_fib, hwf,
      (Data.extend_regs_of_notMem y_fib x outerFrontierReg_notMem_range).trans hfr,
      (Data.extend_regs_of_notMem y_fib x freeBaseReg_notMem_range).trans hfb,
      (Data.extend_regs_of_notMem y_fib x freshReg_notMem_range).trans hfresh,
      (Data.extend_regs_of_notMem y_fib x freeTopReg_notMem_range).trans htop,
      fun h' u' v' hsh' => ⟨(hval h' u' v' hsh').1, (hval h' u' v' hsh').2.1,
        (hmem1_ge _ (Nat.le_add_right _ _)).trans (hval h' u' v' hsh').2.2⟩,
      fun i hi => (hmem1_ge _ (by omega)).trans (hfree i hi)⟩
  have hx1_z0 : x1.regs zeroP = 0 := hrep1.zeroP_eq
  have hx1_vb : x1.regs valBaseReg = base + FibonacciHeap.space n_max := hrep1.valBase_eq
  have hx1_v : x1.regs argV = h.val := by
    change (x1.comap f42).regs FibonacciHeap.argV = h.val
    rw [Data.comap_extend f42_injective]
    exact (he_fib.regs_eq (by decide)).trans hv_reg
  have hx1_fl : x1.regs outFlag = y_fib.regs FibonacciHeap.outFlag := by
    change (x1.comap f42).regs FibonacciHeap.outFlag = y_fib.regs FibonacciHeap.outFlag
    rw [Data.comap_extend f42_injective]
  have hx1_ok : x1.regs outK = y_fib.regs FibonacciHeap.outK := by
    change (x1.comap f42).regs FibonacciHeap.outK = y_fib.regs FibonacciHeap.outK
    rw [Data.comap_extend f42_injective]
  cases hsh : s.entries h with
  | none =>
    have hfl0 : x1.regs outFlag = 0 := by
      rw [hx1_fl]
      simp only [PQCode.decode, FibonacciHeap.code, Cslib.Algorithms.Lean.MinPQ.toIndexed_apply,
        hsh, Option.map_none] at hdec_fib
      by_contra hne
      simp only [hne, ↓reduceIte] at hdec_fib
      nomatch hdec_fib
    have hc : (Cond.eq outFlag zeroP).Holds x1 := by simp only [Cond.Holds, hx1_z0, hfl0]
    let y := x1.set s0 0
    have he2 : ExecWithin (B := .exact) w
        (.branch (.eq outFlag zeroP) (.op (.copy s0 zeroP))
          (.seq (.op (.exactBin .add s0 valBaseReg argV)) (.op (.load outValReg s0)))) x1 y 2 :=
      ExecWithin.branch_pos hc (by simpa only [hx1_z0] using
        (ExecWithin.copy (B := .exact) (w := w) (x := x1) (d := s0) (s := zeroP)))
    have hreg_y : ∀ i : Fin rMinPQ, inputReg i = false → y.regs i = x1.regs i := fun i hi => by
      have hne : i ≠ s0 := fun e => by subst e; cases hi
      simp only [y, Data.set_regs, Function.update_of_ne hne]
    refine ⟨y, t1 + 2, he1.seq he2, ?_,
      hrep1.supported hreg_y (fun _ _ => rfl) (he2.bounded hrep1.1),
      modifies_of_fib hmod_fib, ?_⟩
    · simp only [decode, Cslib.Algorithms.Lean.MinPQ.stepAlloc, hsh, y, Data.set_regs,
        Function.update_of_ne (by decide : outFlag ≠ s0), hfl0, ↓reduceIte]
      rfl
    · rw [potential_supported hreg_y]
      change t1 + 2 + FibonacciHeap.potential (x1.comap f42) ≤ 11 + potential x
      rw [Data.comap_extend f42_injective]
      change t1 + FibonacciHeap.potential y_fib ≤ 7 + FibonacciHeap.potential (x.comap f42)
        at hpot_fib
      unfold potential
      omega
  | some uv =>
    rcases uv with ⟨u, v⟩
    simp only [PQCode.decode, FibonacciHeap.code, Cslib.Algorithms.Lean.MinPQ.toIndexed_apply,
      hsh, Option.map_some] at hdec_fib
    have hfl_ne : x1.regs outFlag ≠ 0 := by
      rw [hx1_fl]
      intro h0
      simp only [h0, ↓reduceIte] at hdec_fib
      nomatch hdec_fib
    have hok_eq : x1.regs outK = u := by
      rw [hx1_ok]
      simp only [hx1_fl ▸ hfl_ne, ↓reduceIte] at hdec_fib
      exact Option.some.inj (Option.some.inj hdec_fib)
    have hc : ¬(Cond.eq outFlag zeroP).Holds x1 := by simp only [Cond.Holds, hx1_z0]; exact hfl_ne
    let y := (x1.set s0 (base + FibonacciHeap.space n_max + h.val)).set outValReg v
    have he2 : ExecWithin (B := .exact) w
        (.branch (.eq outFlag zeroP) (.op (.copy s0 zeroP))
          (.seq (.op (.exactBin .add s0 valBaseReg argV)) (.op (.load outValReg s0)))) x1 y 4 := by
      have hh_lt := h.isLt
      have ea : ExecWithin w (.op (.exactBin .add s0 valBaseReg argV)) x1
          (x1.set s0 (base + FibonacciHeap.space n_max + h.val)) 1 := by
        simpa only [hx1_vb, hx1_v] using
          FibonacciHeap.execWithin_exactAdd (x := x1) (d := s0) (i := valBaseReg) (j := argV)
            (by rw [hx1_vb, hx1_v]; rw [space_eq_fib_add] at hfit_stop;
                exact hfit_stop.of_le (by omega))
      have el : ExecWithin (B := .exact) w (.op (.load outValReg s0))
          (x1.set s0 (base + FibonacciHeap.space n_max + h.val)) y 1 := by
        have hm_v : x1.mem (base + FibonacciHeap.space n_max + h.val) = v :=
          (hrep1.2.2.2.2.2.2.2.1 h u v hsh).2.2
        simpa only [Data.set_mem, Data.set_regs, Function.update_self, hm_v] using
          (ExecWithin.load (B := .exact) (w := w)
            (x := x1.set s0 (base + FibonacciHeap.space n_max + h.val))
            (d := outValReg) (a := s0))
      exact ExecWithin.branch_neg hc (ea.seq el)
    have hreg_y : ∀ i : Fin rMinPQ, inputReg i = false → y.regs i = x1.regs i := fun i hi => by
      have h1 : i ≠ outValReg := fun e => by subst e; cases hi
      have h2 : i ≠ s0 := fun e => by subst e; cases hi
      simp only [y, Data.set_regs, Function.update_of_ne h1, Function.update_of_ne h2]
    refine ⟨y, t1 + 4, he1.seq he2, ?_,
      hrep1.supported hreg_y (fun _ _ => rfl) (he2.bounded hrep1.1),
      modifies_of_fib hmod_fib, ?_⟩
    · simp only [decode, Cslib.Algorithms.Lean.MinPQ.stepAlloc, hsh, y, Data.set_regs,
        Function.update_of_ne (by decide : outFlag ≠ outValReg),
        Function.update_of_ne (by decide : outFlag ≠ s0),
        Function.update_of_ne (by decide : outK ≠ outValReg),
        Function.update_of_ne (by decide : outK ≠ s0),
        Function.update_self, hfl_ne, hok_eq, ↓reduceIte]
      rfl
    · rw [potential_supported hreg_y]
      change t1 + 4 + FibonacciHeap.potential (x1.comap f42) ≤ 11 + potential x
      rw [Data.comap_extend f42_injective]
      change t1 + FibonacciHeap.potential y_fib ≤ 7 + FibonacciHeap.potential (x.comap f42)
        at hpot_fib
      unfold potential
      omega

private theorem allocHandleBranch_exec {n_max U V w base u v : ℕ}
    {s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x)
    (hsz : Cslib.Algorithms.Lean.MinPQ.size s.entries < n_max) :
    ∃ h freeList' fresh' x1,
      Cslib.Algorithms.Lean.MinPQ.allocHandle s = some (h, freeList', fresh') ∧
      s.entries h = none ∧
      (Cslib.Algorithms.Lean.MinPQ.AllocState.mk
        (Function.update s.entries h (some (u, v))) freeList' fresh').WellFormed ∧
      ExecWithin w allocHandleBranch x x1 5 ∧
      x1.Bounded w ∧
      x1.mem = x.mem ∧
      x1.regs argV = h.val ∧
      x1.regs freshReg = fresh' ∧
      x1.regs freeTopReg = freeList'.length ∧
      (∀ i : Fin rMinPQ, i ≠ argV → i ≠ freshReg → i ≠ freeTopReg → i ≠ s0 →
        x1.regs i = x.regs i) ∧
      (∀ (i : ℕ) (hi : i < freeList'.length),
        x.mem (base + FibonacciHeap.space n_max + n_max + (freeList'.length - 1 - i)) =
          (freeList'[i]).val) := by
  have hfit_stop := hrep.fits_stop
  have hz0 := hrep.zeroP_eq
  have ho1 := hrep.oneP_eq
  obtain ⟨hb, _, hwf, _, hfb, hfresh, htop, _, hfree⟩ := hrep
  obtain ⟨h, freeList', fresh', halloc, hh_none, hwf'⟩ :=
    Cslib.Algorithms.Lean.MinPQ.allocHandle_spec hwf hsz u v
  have halloc_eq := halloc
  rcases hfl : s.freeList with _ | ⟨hd, tl⟩
  · -- Bump-pointer case (`freeList = []`)
    have hfr_lt : s.fresh < n_max := by
      have hsum := hwf.2.2.2.2
      rw [hfl, List.length_nil, Nat.add_zero] at hsum
      omega
    simp only [Cslib.Algorithms.Lean.MinPQ.allocHandle, hfl, hfr_lt, ↓reduceDIte,
      Option.some.injEq, Prod.mk.injEq] at halloc
    obtain ⟨rfl, rfl, rfl⟩ := halloc
    have hc : (Cond.eq freeTopReg zeroP).Holds x := by
      simp only [Cond.Holds, htop, hfl, List.length_nil, hz0]
    let x1 := (x.set argV s.fresh).set freshReg (s.fresh + 1)
    have e1 : ExecWithin (B := .exact) w (.op (.copy argV freshReg)) x (x.set argV s.fresh) 1 := by
      simpa only [hfresh] using
        (ExecWithin.copy (B := .exact) (w := w) (x := x) (d := argV) (s := freshReg))
    have e2 : ExecWithin w (.op (.exactBin .add freshReg freshReg oneP))
        (x.set argV s.fresh) x1 1 := by
      have hfr1 : (x.set argV s.fresh).regs freshReg = s.fresh := by
        simp only [Data.set_regs, Function.update_of_ne (by decide : freshReg ≠ argV), hfresh]
      have ho1' : (x.set argV s.fresh).regs oneP = 1 := by
        simp only [Data.set_regs, Function.update_of_ne (by decide : oneP ≠ argV), ho1]
      simpa only [hfr1, ho1'] using
        FibonacciHeap.execWithin_exactAdd
          (x := x.set argV s.fresh) (d := freshReg) (i := freshReg) (j := oneP)
          (by rw [hfr1, ho1']; have := space_lower n_max; exact hfit_stop.of_le (by omega))
    have he : ExecWithin w allocHandleBranch x x1 5 := by
      unfold allocHandleBranch
      exact (ExecWithin.branch_pos hc (e1.seq e2)).mono (by omega)
    refine ⟨⟨s.fresh, hfr_lt⟩, [], s.fresh + 1, x1, halloc_eq, hh_none, hwf', he,
      he.bounded hb, rfl,
      by simp only [x1, Data.set_regs, Function.update_of_ne (by decide : argV ≠ freshReg),
        Function.update_self],
      by simp only [x1, Data.set_regs, Function.update_self],
      by simp only [x1, Data.set_regs, Function.update_of_ne (by decide : freeTopReg ≠ freshReg),
        Function.update_of_ne (by decide : freeTopReg ≠ argV), htop, hfl, List.length_nil],
      fun i h1 h2 _ _ => by simp only [x1, Data.set_regs, Function.update_of_ne h2,
        Function.update_of_ne h1],
      fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  · -- Free-stack pop case (`freeList = hd :: tl`)
    simp only [Cslib.Algorithms.Lean.MinPQ.allocHandle, hfl, Option.some.injEq,
      Prod.mk.injEq] at halloc
    obtain ⟨rfl, rfl, rfl⟩ := halloc
    have htop_eq : x.regs freeTopReg = tl.length + 1 := by
      rw [htop, hfl, List.length_cons]
    have hc : ¬(Cond.eq freeTopReg zeroP).Holds x := by
      simp only [Cond.Holds, htop_eq, hz0]; omega
    have htl_lt : tl.length < n_max := by
      have hsum := hwf.2.2.2.2
      have hfr_le := hwf.1
      rw [hfl, List.length_cons] at hsum
      omega
    have hm_top : x.mem (base + FibonacciHeap.space n_max + n_max + tl.length) = hd.val := by
      have h0 := hfree 0 (by simp only [hfl, List.length_cons]; omega)
      simpa only [hfl, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero,
        List.getElem_cons_zero] using h0
    let a1 := x.set freeTopReg tl.length
    let a2 := a1.set s0 (base + FibonacciHeap.space n_max + n_max + tl.length)
    let x1 := a2.set argV hd.val
    have e1 : ExecWithin w (.op (.exactBin .sub freeTopReg freeTopReg oneP)) x a1 1 := by
      simpa only [htop_eq, ho1, Nat.add_sub_cancel] using
        FibonacciHeap.execWithin_exactSub (x := x) (d := freeTopReg) (i := freeTopReg) (j := oneP)
          (by rw [htop_eq, ho1]; omega)
          (by rw [htop_eq, ho1, Nat.add_sub_cancel]; have := space_lower n_max;
              exact hfit_stop.of_le (by omega))
    have e2 : ExecWithin w (.op (.exactBin .add s0 freeBaseReg freeTopReg)) a1 a2 1 := by
      have ha1_fb : a1.regs freeBaseReg = base + FibonacciHeap.space n_max + n_max := by
        simp only [a1, Data.set_regs,
          Function.update_of_ne (by decide : freeBaseReg ≠ freeTopReg), hfb]
      have ha1_top : a1.regs freeTopReg = tl.length := by
        simp only [a1, Data.set_regs, Function.update_self]
      simpa only [ha1_fb, ha1_top] using
        FibonacciHeap.execWithin_exactAdd (x := a1) (d := s0) (i := freeBaseReg) (j := freeTopReg)
          (by rw [ha1_fb, ha1_top]; rw [space_eq_fib_add] at hfit_stop;
              exact hfit_stop.of_le (by omega))
    have e3 : ExecWithin (B := .exact) w (.op (.load argV s0)) a2 x1 1 := by
      simpa only [a2, a1, Data.set_mem, Data.set_regs, Function.update_self, hm_top] using
        (ExecWithin.load (B := .exact) (w := w) (x := a2) (d := argV) (a := s0))
    have he : ExecWithin w allocHandleBranch x x1 5 := by
      unfold allocHandleBranch
      exact ExecWithin.branch_neg hc (e1.seq (e2.seq e3))
    refine ⟨hd, tl, s.fresh, x1, halloc_eq, hh_none, hwf', he, he.bounded hb, rfl,
      by simp only [x1, Data.set_regs, Function.update_self],
      by simp only [x1, a2, a1, Data.set_regs,
        Function.update_of_ne (by decide : freshReg ≠ argV),
        Function.update_of_ne (by decide : freshReg ≠ s0),
        Function.update_of_ne (by decide : freshReg ≠ freeTopReg), hfresh],
      by simp only [x1, a2, a1, Data.set_regs,
        Function.update_of_ne (by decide : freeTopReg ≠ argV),
        Function.update_of_ne (by decide : freeTopReg ≠ s0), Function.update_self],
      fun i h1 _ h3 h4 => by simp only [x1, a2, a1, Data.set_regs,
        Function.update_of_ne h1, Function.update_of_ne h4, Function.update_of_ne h3],
      fun i hi => ?_⟩
    have hi' : i + 1 < s.freeList.length := by simp only [hfl, List.length_cons]; omega
    have hfi := hfree (i + 1) hi'
    have hidx : s.freeList.length - 1 - (i + 1) = tl.length - 1 - i := by
      simp only [hfl, List.length_cons]; omega
    have hget : (s.freeList[i + 1]'hi') = tl[i] := by simp only [hfl, List.getElem_cons_succ]
    rw [hidx, hget] at hfi
    exact hfi

theorem insertCode_exec {n_max U V w base u v : ℕ}
    {s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x)
    (hv : (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).valid s.entries (.insert u v))
    (hk_reg : x.regs argK = u) (hval_reg : x.regs inValReg = v) :
    ∃ y t, ExecWithin w insertCode x y t ∧
      decode (n_max := n_max) (U := U) (V := V) (.insert u v) y.regs =
        some (Cslib.Algorithms.Lean.MinPQ.stepAlloc s (.insert u v)).2 ∧
      AllocRep n_max U V w base (Cslib.Algorithms.Lean.MinPQ.stepAlloc s (.insert u v)).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      t + potential y ≤ 129 + potential x := by
  have hfit_stop := hrep.fits_stop
  have hvb := hrep.valBase_eq
  obtain ⟨hsz, hu_lt, hv_lt⟩ := hv
  obtain ⟨h, freeList', fresh', x1, halloc, hh_none, hwf', he_alloc, hb1, hm1,
    hx1_v, hx1_fresh, hx1_top, hx1_regs, hfree'⟩ :=
    allocHandleBranch_exec (u := u) (v := v) hrep hsz
  have hh_lt := h.isLt
  have ho_val := owns_val_addr (base := base) hh_lt
  have hx1_vb : x1.regs valBaseReg = base + FibonacciHeap.space n_max :=
    (hx1_regs valBaseReg (by decide) (by decide) (by decide) (by decide)).trans hvb
  have hx1_inVal : x1.regs inValReg = v :=
    (hx1_regs inValReg (by decide) (by decide) (by decide) (by decide)).trans hval_reg
  let x2 := (x1.set s0 (base + FibonacciHeap.space n_max + h.val)).write
    (base + FibonacciHeap.space n_max + h.val) v
  have ew1 : ExecWithin w (.op (.exactBin .add s0 valBaseReg argV)) x1
      (x1.set s0 (base + FibonacciHeap.space n_max + h.val)) 1 := by
    simpa only [hx1_vb, hx1_v] using
      FibonacciHeap.execWithin_exactAdd (x := x1) (d := s0) (i := valBaseReg) (j := argV)
        (by rw [hx1_vb, hx1_v]; rw [space_eq_fib_add] at hfit_stop;
            exact hfit_stop.of_le (by omega))
  have ew2 : ExecWithin (B := .exact) w (.op (.store s0 inValReg))
      (x1.set s0 (base + FibonacciHeap.space n_max + h.val)) x2 1 := by
    simpa only [Data.set_regs, Function.update_self,
      Function.update_of_ne (by decide : inValReg ≠ s0), hx1_inVal] using
      (ExecWithin.store (B := .exact) (w := w)
        (x := x1.set s0 (base + FibonacciHeap.space n_max + h.val)) (a := s0) (s := inValReg))
  have hb2 : x2.Bounded w := ew2.bounded (ew1.bounded hb1)
  have hreg2 : ∀ j : Fin rFib, FibonacciHeap.inputReg j = false →
      (x2.comap f42).regs j = (x.comap f42).regs j := fun j hj => by
    have hj_in : inputReg (f42 j) = false := inputReg_f42_of_false j hj
    change x2.regs (f42 j) = x.regs (f42 j)
    have h1 : f42 j ≠ argV := fun e => by rw [e] at hj_in; cases hj_in
    have h2 : f42 j ≠ freshReg := fun e => freshReg_notMem_range ⟨j, e⟩
    have h3 : f42 j ≠ freeTopReg := fun e => freeTopReg_notMem_range ⟨j, e⟩
    have h4 : f42 j ≠ s0 := fun e => by rw [e] at hj_in; cases hj_in
    simp only [x2, Data.write_regs, Data.set_regs, Function.update_of_ne h4]
    exact hx1_regs (f42 j) h1 h2 h3 h4
  have hmem2_fib : ∀ a ∈ (Block.mk base (FibonacciHeap.space n_max)).footprint,
      (x2.comap f42).mem a = (x.comap f42).mem a := fun a ha => by
    have hne : a ≠ base + FibonacciHeap.space n_max + h.val := fun e =>
      notMem_fib_footprint_of_ge (by omega) (e ▸ ha)
    simp only [x2, Data.comap, Data.write_mem, Data.set_mem, Function.update_of_ne hne, hm1]
  have hinv2 : FibonacciHeap.FibInv n_max U w base
      (Cslib.Algorithms.Lean.MinPQ.toIndexed s.entries) (x2.comap f42) :=
    FibonacciHeap.FibInv.supported hreg2 hmem2_fib (hb2.comap f42) hrep.2.1
  have hpot2 : potential x2 = potential x :=
    FibonacciHeap.potential_supported hreg2
  have hx2_v : (x2.comap f42).regs FibonacciHeap.argV = h.val := by
    change x2.regs argV = h.val
    simp only [x2, Data.write_regs, Data.set_regs,
      Function.update_of_ne (by decide : argV ≠ s0), hx1_v]
  have hx2_k : (x2.comap f42).regs FibonacciHeap.argK = u := by
    change x2.regs argK = u
    simp only [x2, Data.write_regs, Data.set_regs,
      Function.update_of_ne (by decide : argK ≠ s0)]
    exact (hx1_regs argK (by decide) (by decide) (by decide) (by decide)).trans hk_reg
  have hval_fib : Cslib.Algorithms.Lean.MinPQ.toIndexed s.entries h = none ∧ u ≤ U := by
    simp only [Cslib.Algorithms.Lean.MinPQ.toIndexed_apply, hh_none, Option.map_none, true_and]
    exact Nat.le_of_lt hu_lt
  obtain ⟨y_fib, t_fib, he_fib, hinv_fib, hmod_fib, hpot_fib⟩ :=
    FibonacciHeap.insertCode_exec h u hinv2 hval_fib hx2_v hx2_k
  let x3 := y_fib.extend f42 x2
  have he3 : ExecWithin w (FibonacciHeap.insertCode.rename f42) x2 x3 t_fib :=
    he_fib.rename f42_injective
  have hx3_v : x3.regs argV = h.val := by
    change (x3.comap f42).regs FibonacciHeap.argV = h.val
    rw [Data.comap_extend f42_injective]
    exact (he_fib.regs_eq (by decide)).trans hx2_v
  let y := x3.set outV h.val
  have he4 : ExecWithin (B := .exact) w (.op (.copy outV argV)) x3 y 1 := by
    simpa only [hx3_v] using
      (ExecWithin.copy (B := .exact) (w := w) (x := x3) (d := outV) (s := argV))
  have he : ExecWithin w insertCode x y (5 + 1 + 1 + t_fib + 1) := by
    unfold insertCode
    exact (he_alloc.seq (ew1.seq (ew2.seq (he3.seq he4)))).mono (by omega)
  have hby : y.Bounded w := he4.bounded (he3.bounded hb2)
  have hreg_y3 : ∀ i : Fin rMinPQ, inputReg i = false → y.regs i = x3.regs i := fun i hi => by
    have hne : i ≠ outV := fun e => by subst e; cases hi
    simp only [y, Data.set_regs, Function.update_of_ne hne]
  have hmem3_ge : ∀ a, base + FibonacciHeap.space n_max ≤ a → x3.mem a = x2.mem a :=
    fun a ha => hmod_fib a (notMem_fib_footprint_of_ge ha)
  have hmod_all : Modifies (Block.mk base (space n_max)).footprint x.mem y.mem := by
    have hm_x2 : Modifies (Block.mk base (space n_max)).footprint x.mem x2.mem := by
      change Modifies (Block.mk base (space n_max)).footprint x.mem
        (Function.update x1.mem (base + FibonacciHeap.space n_max + h.val) v)
      rw [hm1]
      exact Modifies.write_of_owns ho_val v
    exact FibonacciHeap.modifies_block_trans hm_x2 (modifies_of_fib hmod_fib)
  refine ⟨y, 5 + 1 + 1 + t_fib + 1, he, ?_, ?_, hmod_all, ?_⟩
  · simp only [decode, Cslib.Algorithms.Lean.MinPQ.stepAlloc, halloc, y, Data.set_regs,
      Function.update_self, hh_lt, ↓reduceDIte, Fin.eta]
    rfl
  · simp only [Cslib.Algorithms.Lean.MinPQ.stepAlloc, halloc]
    refine AllocRep.supported hreg_y3 (fun _ _ => rfl) hby ⟨he3.bounded hb2, ?_, hwf',
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only
      rw [Data.comap_extend f42_injective,
        Cslib.Algorithms.Lean.MinPQ.toIndexed_update_some s.entries h u v]
      exact hinv_fib
    · rw [Data.extend_regs_of_notMem y_fib x2 outerFrontierReg_notMem_range]
      simp only [x2, Data.write_regs, Data.set_regs,
        Function.update_of_ne (by decide : outerFrontierReg ≠ s0)]
      exact (hx1_regs outerFrontierReg (by decide) (by decide) (by decide) (by decide)).trans
        hrep.2.2.2.1
    · rw [Data.extend_regs_of_notMem y_fib x2 freeBaseReg_notMem_range]
      simp only [x2, Data.write_regs, Data.set_regs,
        Function.update_of_ne (by decide : freeBaseReg ≠ s0)]
      exact (hx1_regs freeBaseReg (by decide) (by decide) (by decide) (by decide)).trans
        hrep.2.2.2.2.1
    · rw [Data.extend_regs_of_notMem y_fib x2 freshReg_notMem_range]
      simp only [x2, Data.write_regs, Data.set_regs,
        Function.update_of_ne (by decide : freshReg ≠ s0), hx1_fresh]
    · rw [Data.extend_regs_of_notMem y_fib x2 freeTopReg_notMem_range]
      simp only [x2, Data.write_regs, Data.set_regs,
        Function.update_of_ne (by decide : freeTopReg ≠ s0), hx1_top]
    · intro h' u' v' hsh'
      rw [hmem3_ge _ (Nat.le_add_right _ _)]
      by_cases hh' : h' = h
      · subst hh'
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hsh'
        obtain ⟨rfl, rfl⟩ := hsh'
        exact ⟨hu_lt, hv_lt, by simp only [x2, Data.write_mem, Function.update_self]⟩
      · simp only [Function.update_of_ne hh'] at hsh'
        have hne_addr : base + FibonacciHeap.space n_max + h'.val ≠
            base + FibonacciHeap.space n_max + h.val := by
          have := Fin.val_ne_of_ne hh'; omega
        obtain ⟨hu', hv', hm'⟩ := hrep.2.2.2.2.2.2.2.1 h' u' v' hsh'
        exact ⟨hu', hv', by simp only [x2, Data.write_mem, Data.set_mem,
          Function.update_of_ne hne_addr, hm1, hm']⟩
    · intro i hi
      rw [hmem3_ge _ (by omega)]
      have hne_addr :
          base + FibonacciHeap.space n_max + n_max + (freeList'.length - 1 - i) ≠
          base + FibonacciHeap.space n_max + h.val := by omega
      simp only [x2, Data.write_mem, Data.set_mem, Function.update_of_ne hne_addr, hm1]
      exact hfree' i hi
  · rw [potential_supported hreg_y3]
    change 5 + 1 + 1 + t_fib + 1 + FibonacciHeap.potential (x3.comap f42) ≤ 129 + potential x
    rw [Data.comap_extend f42_injective]
    change t_fib + FibonacciHeap.potential y_fib ≤ 121 + FibonacciHeap.potential (x2.comap f42)
      at hpot_fib
    change FibonacciHeap.potential (x2.comap f42) = potential x at hpot2
    omega

theorem decreaseKeyCode_exec {n_max U V w base : ℕ}
    {s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (h : Fin n_max) (u' : ℕ) (hrep : AllocRep n_max U V w base s x)
    (hv : (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).valid s.entries (.decreaseKey h u'))
    (hv_reg : x.regs argV = h.val) (hk_reg : x.regs argK = u') :
    ∃ y t, ExecWithin w decreaseKeyCode x y t ∧
      decode (n_max := n_max) (U := U) (V := V) (.decreaseKey h u') y.regs =
        some (Cslib.Algorithms.Lean.MinPQ.stepAlloc s (.decreaseKey h u')).2 ∧
      AllocRep n_max U V w base (Cslib.Algorithms.Lean.MinPQ.stepAlloc s (.decreaseKey h u')).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      t + potential y ≤ 330 + potential x := by
  obtain ⟨hb, hfib, hwf, hfr, hfb, hfresh, htop, hval, hfree⟩ := hrep
  obtain ⟨u, v, hsh, hu'_le⟩ := hv
  obtain ⟨hu_lt, hv_lt, _⟩ := hval h u v hsh
  have hu'_lt : u' < U := Nat.lt_of_le_of_lt hu'_le hu_lt
  have hval_fib :
      (∃ k₀, Cslib.Algorithms.Lean.MinPQ.toIndexed s.entries h = some k₀ ∧ u' ≤ k₀) ∧ u' ≤ U := by
    refine ⟨⟨u, ?_, hu'_le⟩, Nat.le_of_lt hu'_lt⟩
    simp only [Cslib.Algorithms.Lean.MinPQ.toIndexed_apply, hsh, Option.map_some]
  obtain ⟨y_fib, t, he_fib, hinv_fib, hmod_fib, hpot_fib⟩ :=
    FibonacciHeap.decreaseKeyCode_exec h u' hfib hval_fib hv_reg hk_reg
  let y := y_fib.extend f42 x
  have he : ExecWithin w decreaseKeyCode x y t := he_fib.rename f42_injective
  have hmem_ge : ∀ a, base + FibonacciHeap.space n_max ≤ a → y.mem a = x.mem a :=
    fun a ha => hmod_fib a (notMem_fib_footprint_of_ge ha)
  have hwf' :=
    (Cslib.Algorithms.Lean.MinPQ.stepAlloc_refines_spec (U := U) (V := V) hwf
      (.decreaseKey h u') ⟨u, v, hsh, hu'_le⟩).2
  refine ⟨y, t, he, rfl, ?_, modifies_of_fib hmod_fib, ?_⟩
  · refine ⟨he.bounded hb, ?_, hwf',
      (Data.extend_regs_of_notMem y_fib x outerFrontierReg_notMem_range).trans hfr,
      (Data.extend_regs_of_notMem y_fib x freeBaseReg_notMem_range).trans hfb,
      by simp only [Cslib.Algorithms.Lean.MinPQ.stepAlloc, hsh];
         exact (Data.extend_regs_of_notMem y_fib x freshReg_notMem_range).trans hfresh,
      by simp only [Cslib.Algorithms.Lean.MinPQ.stepAlloc, hsh];
         exact (Data.extend_regs_of_notMem y_fib x freeTopReg_notMem_range).trans htop,
      ?_, ?_⟩
    · simp only [Cslib.Algorithms.Lean.MinPQ.stepAlloc, hsh]
      rw [Data.comap_extend f42_injective,
        Cslib.Algorithms.Lean.MinPQ.toIndexed_update_some s.entries h u' v]
      exact hinv_fib
    · intro h' u₁ v₁ hsh'
      simp only [Cslib.Algorithms.Lean.MinPQ.stepAlloc, hsh] at hsh'
      rw [hmem_ge _ (Nat.le_add_right _ _)]
      by_cases hh' : h' = h
      · subst hh'
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hsh'
        obtain ⟨rfl, rfl⟩ := hsh'
        exact ⟨hu'_lt, hv_lt, (hval h' u v hsh).2.2⟩
      · simp only [Function.update_of_ne hh'] at hsh'
        exact hval h' u₁ v₁ hsh'
    · intro i hi
      simp only [Cslib.Algorithms.Lean.MinPQ.stepAlloc, hsh] at hi ⊢
      rw [hmem_ge _ (by omega)]
      exact hfree i hi
  · unfold potential
    rw [Data.comap_extend f42_injective]
    exact hpot_fib

theorem extractMinCode_exec {n_max U V w base : ℕ}
    {s : Cslib.Algorithms.Lean.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x) :
    ∃ y t, ExecWithin w extractMinCode x y t ∧
      decode (n_max := n_max) (U := U) (V := V) .extractMin y.regs =
        some (Cslib.Algorithms.Lean.MinPQ.stepAlloc s .extractMin).2 ∧
      AllocRep n_max U V w base (Cslib.Algorithms.Lean.MinPQ.stepAlloc s .extractMin).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      t + potential y ≤
        418 * (Nat.log 2 (Cslib.Algorithms.Lean.MinPQ.size s.entries) + 1) + potential x := by
  have hfit_stop := hrep.fits_stop
  obtain ⟨hb, hfib, hwf, hfr, hfb, hfresh, htop, hval, hfree⟩ := hrep
  obtain ⟨y_fib, t1, he_fib, hdec_fib, hinv_fib, hmod_fib, hpot_fib⟩ :=
    FibonacciHeap.extractMinCode_exec hfib
  rw [Cslib.Algorithms.Lean.MinPQ.dom_toIndexed] at hpot_fib
  change t1 + FibonacciHeap.potential y_fib ≤
    410 * (Nat.log 2 (Cslib.Algorithms.Lean.MinPQ.size s.entries) + 1) +
      FibonacciHeap.potential (x.comap f42) at hpot_fib
  let x1 := y_fib.extend f42 x
  have he1 : ExecWithin w (FibonacciHeap.extractMinCode.rename f42) x x1 t1 :=
    he_fib.rename f42_injective
  have hb1 : x1.Bounded w := he1.bounded hb
  have hmem1_ge : ∀ a, base + FibonacciHeap.space n_max ≤ a → x1.mem a = x.mem a :=
    fun a ha => hmod_fib a (notMem_fib_footprint_of_ge ha)
  have hx1_z0 : x1.regs zeroP = 0 := by
    change (x1.comap f42).regs FibonacciHeap.zeroP = 0
    rw [Data.comap_extend f42_injective]
    exact hinv_fib.2.1.2.2.2.2.2.2.2.2.2.2.2.1
  have hx1_o1 : x1.regs oneP = 1 := by
    change (x1.comap f42).regs FibonacciHeap.oneP = 1
    rw [Data.comap_extend f42_injective]
    exact hinv_fib.2.1.2.2.2.2.2.2.2.2.2.2.2.2
  have hx1_vb : x1.regs valBaseReg = base + FibonacciHeap.space n_max := by
    change (x1.comap f42).regs FibonacciHeap.frontierReg = base + FibonacciHeap.space n_max
    rw [Data.comap_extend f42_injective]
    exact hinv_fib.2.1.2.1
  have hx1_fb : x1.regs freeBaseReg = base + FibonacciHeap.space n_max + n_max :=
    (Data.extend_regs_of_notMem y_fib x freeBaseReg_notMem_range).trans hfb
  have hx1_fresh : x1.regs freshReg = s.fresh :=
    (Data.extend_regs_of_notMem y_fib x freshReg_notMem_range).trans hfresh
  have hx1_top : x1.regs freeTopReg = s.freeList.length :=
    (Data.extend_regs_of_notMem y_fib x freeTopReg_notMem_range).trans htop
  have hx1_ofr : x1.regs outerFrontierReg = base + space n_max :=
    (Data.extend_regs_of_notMem y_fib x outerFrontierReg_notMem_range).trans hfr
  have hx1_fl : x1.regs outFlag = y_fib.regs FibonacciHeap.outFlag := by
    change (x1.comap f42).regs FibonacciHeap.outFlag = y_fib.regs FibonacciHeap.outFlag
    rw [Data.comap_extend f42_injective]
  have hx1_ov : x1.regs outV = y_fib.regs FibonacciHeap.outV := by
    change (x1.comap f42).regs FibonacciHeap.outV = y_fib.regs FibonacciHeap.outV
    rw [Data.comap_extend f42_injective]
  have hx1_ok : x1.regs outK = y_fib.regs FibonacciHeap.outK := by
    change (x1.comap f42).regs FibonacciHeap.outK = y_fib.regs FibonacciHeap.outK
    rw [Data.comap_extend f42_injective]
  have hwf' :=
    (Cslib.Algorithms.Lean.MinPQ.stepAlloc_refines_spec (U := U) (V := V) hwf .extractMin
      trivial).2
  rcases hfm : IndexedMinPQ.findMin (Cslib.Algorithms.Lean.MinPQ.toIndexed s.entries) with
    _ | ⟨h, u⟩
  · -- Empty queue (`findMin = none`)
    simp only [PQCode.decode, FibonacciHeap.code, IndexedMinPQ.spec, hfm] at hdec_fib hinv_fib
    have hfl0 : x1.regs outFlag = 0 := by
      rw [hx1_fl]
      by_contra hne
      simp only [hne, ↓reduceIte] at hdec_fib
      by_cases hlt : y_fib.regs FibonacciHeap.outV < n_max <;>
        simp only [hlt, ↓reduceDIte] at hdec_fib <;>
        nomatch hdec_fib
    have hc : (Cond.eq outFlag zeroP).Holds x1 := by simp only [Cond.Holds, hx1_z0, hfl0]
    let y := x1.set s0 0
    have he2 : ExecWithin (B := .exact) w
        (.branch (.eq outFlag zeroP) (.op (.copy s0 zeroP))
          (.seq (.op (.exactBin .add s0 valBaseReg outV)) <|
           .seq (.op (.load outValReg s0)) <|
           .seq (.op (.exactBin .add s0 freeBaseReg freeTopReg)) <|
           .seq (.op (.store s0 outV))
                (.op (.exactBin .add freeTopReg freeTopReg oneP)))) x1 y 2 :=
      ExecWithin.branch_pos hc (by simpa only [hx1_z0] using
        (ExecWithin.copy (B := .exact) (w := w) (x := x1) (d := s0) (s := zeroP)))
    have hreg_y : ∀ i : Fin rMinPQ, inputReg i = false → y.regs i = x1.regs i := fun i hi => by
      have hne : i ≠ s0 := fun e => by subst e; cases hi
      simp only [y, Data.set_regs, Function.update_of_ne hne]
    have hrep1 : AllocRep n_max U V w base s x1 :=
      ⟨hb1, by rw [Data.comap_extend f42_injective]; exact hinv_fib, hwf,
        hx1_ofr, hx1_fb, hx1_fresh, hx1_top,
        fun h' u' v' hsh' => ⟨(hval h' u' v' hsh').1, (hval h' u' v' hsh').2.1,
          (hmem1_ge _ (Nat.le_add_right _ _)).trans (hval h' u' v' hsh').2.2⟩,
        fun i hi => (hmem1_ge _ (by omega)).trans (hfree i hi)⟩
    refine ⟨y, t1 + 2, he1.seq he2, ?_, ?_, modifies_of_fib hmod_fib, ?_⟩
    · have hfm' : Cslib.Algorithms.Lean.MinPQ.findMin s.entries = none := by
        simp only [Cslib.Algorithms.Lean.MinPQ.findMin, hfm]
      simp only [decode, Cslib.Algorithms.Lean.MinPQ.stepAlloc, hfm', y, Data.set_regs,
        Function.update_of_ne (by decide : outFlag ≠ s0), hfl0, ↓reduceIte]
      rfl
    · have hfm' : Cslib.Algorithms.Lean.MinPQ.findMin s.entries = none := by
        simp only [Cslib.Algorithms.Lean.MinPQ.findMin, hfm]
      simp only [Cslib.Algorithms.Lean.MinPQ.stepAlloc, hfm']
      exact hrep1.supported hreg_y (fun _ _ => rfl) (he2.bounded hb1)
    · rw [potential_supported hreg_y]
      change t1 + 2 + FibonacciHeap.potential (x1.comap f42) ≤ _ + potential x
      rw [Data.comap_extend f42_injective]
      unfold potential
      omega
  · -- Non-empty queue (`findMin = some (h, u)`)
    obtain ⟨v, hsh, hfm', _⟩ := Cslib.Algorithms.Lean.MinPQ.findMin_eq_some_of_indexed hfm
    simp only [PQCode.decode, FibonacciHeap.code, IndexedMinPQ.spec, hfm] at hdec_fib hinv_fib
    have hfl_ne : x1.regs outFlag ≠ 0 := by
      rw [hx1_fl]
      intro h0
      simp only [h0, ↓reduceIte] at hdec_fib
      nomatch hdec_fib
    simp only [hx1_fl ▸ hfl_ne, ↓reduceIte] at hdec_fib
    have hlt_ov : y_fib.regs FibonacciHeap.outV < n_max := by
      by_contra hge
      simp only [hge, ↓reduceDIte] at hdec_fib
      nomatch hdec_fib
    simp only [hlt_ov, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq, Fin.ext_iff] at hdec_fib
    have hov_eq : x1.regs outV = h.val := hx1_ov.trans hdec_fib.1
    have hok_eq : x1.regs outK = u := hx1_ok.trans hdec_fib.2
    have hc : ¬(Cond.eq outFlag zeroP).Holds x1 := by simp only [Cond.Holds, hx1_z0]; exact hfl_ne
    have hh_lt := h.isLt
    have hsz_pos : 1 ≤ Cslib.Algorithms.Lean.MinPQ.size s.entries :=
      Finset.card_pos.mpr ⟨h, Cslib.Algorithms.Lean.MinPQ.mem_dom_iff.mpr ⟨u, v, hsh⟩⟩
    have hfl_lt : s.freeList.length < n_max := by
      have := hwf.1
      have := hwf.2.2.2.2
      omega
    have ho_free := owns_free_addr (base := base) hfl_lt
    let a1 := x1.set s0 (base + FibonacciHeap.space n_max + h.val)
    let a2 := a1.set outValReg v
    let a3 := a2.set s0 (base + FibonacciHeap.space n_max + n_max + s.freeList.length)
    let a4 := a3.write (base + FibonacciHeap.space n_max + n_max + s.freeList.length) h.val
    let y := a4.set freeTopReg (s.freeList.length + 1)
    have eb1 : ExecWithin w (.op (.exactBin .add s0 valBaseReg outV)) x1 a1 1 := by
      simpa only [hx1_vb, hov_eq] using
        FibonacciHeap.execWithin_exactAdd (x := x1) (d := s0) (i := valBaseReg) (j := outV)
          (by rw [hx1_vb, hov_eq]; rw [space_eq_fib_add] at hfit_stop;
              exact hfit_stop.of_le (by omega))
    have eb2 : ExecWithin (B := .exact) w (.op (.load outValReg s0)) a1 a2 1 := by
      have hm_v : x1.mem (base + FibonacciHeap.space n_max + h.val) = v :=
        (hmem1_ge _ (Nat.le_add_right _ _)).trans (hval h u v hsh).2.2
      simpa only [a1, Data.set_mem, Data.set_regs, Function.update_self, hm_v] using
        (ExecWithin.load (B := .exact) (w := w) (x := a1) (d := outValReg) (a := s0))
    have eb3 : ExecWithin w (.op (.exactBin .add s0 freeBaseReg freeTopReg)) a2 a3 1 := by
      have ha2_fb : a2.regs freeBaseReg = base + FibonacciHeap.space n_max + n_max := by
        simp only [a2, a1, Data.set_regs,
          Function.update_of_ne (by decide : freeBaseReg ≠ outValReg),
          Function.update_of_ne (by decide : freeBaseReg ≠ s0), hx1_fb]
      have ha2_top : a2.regs freeTopReg = s.freeList.length := by
        simp only [a2, a1, Data.set_regs,
          Function.update_of_ne (by decide : freeTopReg ≠ outValReg),
          Function.update_of_ne (by decide : freeTopReg ≠ s0), hx1_top]
      simpa only [ha2_fb, ha2_top] using
        FibonacciHeap.execWithin_exactAdd (x := a2) (d := s0) (i := freeBaseReg) (j := freeTopReg)
          (by rw [ha2_fb, ha2_top]; rw [space_eq_fib_add] at hfit_stop;
              exact hfit_stop.of_le (by omega))
    have eb4 : ExecWithin (B := .exact) w (.op (.store s0 outV)) a3 a4 1 := by
      have ha3_ov : a3.regs outV = h.val := by
        simp only [a3, a2, a1, Data.set_regs,
          Function.update_of_ne (by decide : outV ≠ s0),
          Function.update_of_ne (by decide : outV ≠ outValReg), hov_eq]
      simpa only [a3, Data.set_regs, Function.update_self, ha3_ov] using
        (ExecWithin.store (B := .exact) (w := w) (x := a3) (a := s0) (s := outV))
    have eb5 : ExecWithin w (.op (.exactBin .add freeTopReg freeTopReg oneP)) a4 y 1 := by
      have ha4_top : a4.regs freeTopReg = s.freeList.length := by
        simp only [a4, a3, a2, a1, Data.write_regs, Data.set_regs,
          Function.update_of_ne (by decide : freeTopReg ≠ s0),
          Function.update_of_ne (by decide : freeTopReg ≠ outValReg), hx1_top]
      have ha4_o1 : a4.regs oneP = 1 := by
        simp only [a4, a3, a2, a1, Data.write_regs, Data.set_regs,
          Function.update_of_ne (by decide : oneP ≠ s0),
          Function.update_of_ne (by decide : oneP ≠ outValReg), hx1_o1]
      simpa only [ha4_top, ha4_o1] using
        FibonacciHeap.execWithin_exactAdd (x := a4) (d := freeTopReg) (i := freeTopReg) (j := oneP)
          (by rw [ha4_top, ha4_o1]; have := space_lower n_max;
              exact hfit_stop.of_le (by omega))
    have he2 : ExecWithin (B := .exact) w
        (.branch (.eq outFlag zeroP) (.op (.copy s0 zeroP))
          (.seq (.op (.exactBin .add s0 valBaseReg outV)) <|
           .seq (.op (.load outValReg s0)) <|
           .seq (.op (.exactBin .add s0 freeBaseReg freeTopReg)) <|
           .seq (.op (.store s0 outV))
                (.op (.exactBin .add freeTopReg freeTopReg oneP)))) x1 y 7 :=
      ExecWithin.branch_neg hc (eb1.seq (eb2.seq (eb3.seq (eb4.seq eb5))))
    have hby : y.Bounded w := he2.bounded hb1
    have hreg_fib : ∀ j : Fin rFib, FibonacciHeap.inputReg j = false →
        (y.comap f42).regs j = (x1.comap f42).regs j := fun j hj => by
      have hj_in : inputReg (f42 j) = false := inputReg_f42_of_false j hj
      change y.regs (f42 j) = x1.regs (f42 j)
      have h1 : f42 j ≠ freeTopReg := fun e => freeTopReg_notMem_range ⟨j, e⟩
      have h2 : f42 j ≠ s0 := fun e => by rw [e] at hj_in; cases hj_in
      have h3 : f42 j ≠ outValReg := fun e => outValReg_notMem_range ⟨j, e⟩
      simp only [y, a4, a3, a2, a1, Data.set_regs, Data.write_regs,
        Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
    have hmem_fib : ∀ a ∈ (Block.mk base (FibonacciHeap.space n_max)).footprint,
        (y.comap f42).mem a = (x1.comap f42).mem a := fun a ha => by
      have hne : a ≠ base + FibonacciHeap.space n_max + n_max + s.freeList.length := fun e =>
        notMem_fib_footprint_of_ge (by omega) (e ▸ ha)
      simp only [y, a4, a3, a2, a1, Data.comap, Data.set_mem, Data.write_mem,
        Function.update_of_ne hne]
    have hmod_all : Modifies (Block.mk base (space n_max)).footprint x.mem y.mem := by
      have hm_y : Modifies (Block.mk base (space n_max)).footprint x1.mem y.mem :=
        Modifies.write_of_owns ho_free h.val
      exact FibonacciHeap.modifies_block_trans (modifies_of_fib hmod_fib) hm_y
    refine ⟨y, t1 + 7, he1.seq he2, ?_, ?_, hmod_all, ?_⟩
    · simp only [decode, Cslib.Algorithms.Lean.MinPQ.stepAlloc, hfm', y, a4, a3, a2, a1,
        Data.set_regs, Data.write_regs,
        Function.update_of_ne (by decide : outFlag ≠ freeTopReg),
        Function.update_of_ne (by decide : outFlag ≠ s0),
        Function.update_of_ne (by decide : outFlag ≠ outValReg),
        Function.update_of_ne (by decide : outV ≠ freeTopReg),
        Function.update_of_ne (by decide : outV ≠ s0),
        Function.update_of_ne (by decide : outV ≠ outValReg),
        Function.update_of_ne (by decide : outK ≠ freeTopReg),
        Function.update_of_ne (by decide : outK ≠ s0),
        Function.update_of_ne (by decide : outK ≠ outValReg),
        Function.update_of_ne (by decide : outValReg ≠ freeTopReg),
        Function.update_of_ne (by decide : outValReg ≠ s0),
        Function.update_self, hfl_ne, hov_eq, hok_eq, hh_lt, ↓reduceIte, ↓reduceDIte, Fin.eta]
      rfl
    · simp only [Cslib.Algorithms.Lean.MinPQ.stepAlloc, hfm'] at hwf' ⊢
      refine ⟨hby, ?_, hwf', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine FibonacciHeap.FibInv.supported hreg_fib hmem_fib (hby.comap f42) ?_
        dsimp only
        rw [Data.comap_extend f42_injective,
          Cslib.Algorithms.Lean.MinPQ.toIndexed_update_none s.entries h]
        exact hinv_fib
      · simp only [y, a4, a3, a2, a1, Data.set_regs, Data.write_regs,
          Function.update_of_ne (by decide : outerFrontierReg ≠ freeTopReg),
          Function.update_of_ne (by decide : outerFrontierReg ≠ s0),
          Function.update_of_ne (by decide : outerFrontierReg ≠ outValReg), hx1_ofr]
      · simp only [y, a4, a3, a2, a1, Data.set_regs, Data.write_regs,
          Function.update_of_ne (by decide : freeBaseReg ≠ freeTopReg),
          Function.update_of_ne (by decide : freeBaseReg ≠ s0),
          Function.update_of_ne (by decide : freeBaseReg ≠ outValReg), hx1_fb]
      · simp only [y, a4, a3, a2, a1, Data.set_regs, Data.write_regs,
          Function.update_of_ne (by decide : freshReg ≠ freeTopReg),
          Function.update_of_ne (by decide : freshReg ≠ s0),
          Function.update_of_ne (by decide : freshReg ≠ outValReg), hx1_fresh]
      · simp only [y, Data.set_regs, Function.update_self, List.length_cons]
      · intro h' u' v' hsh'
        by_cases hh' : h' = h
        · subst hh'; simp only [Function.update_self, reduceCtorEq] at hsh'
        · simp only [Function.update_of_ne hh'] at hsh'
          have hne_addr : base + FibonacciHeap.space n_max + h'.val ≠
              base + FibonacciHeap.space n_max + n_max + s.freeList.length := by
            have := h'.isLt; omega
          obtain ⟨hu', hv', hm'⟩ := hval h' u' v' hsh'
          refine ⟨hu', hv', ?_⟩
          simp only [y, a4, a3, a2, a1, Data.set_mem, Data.write_mem,
            Function.update_of_ne hne_addr]
          exact (hmem1_ge _ (Nat.le_add_right _ _)).trans hm'
      · intro i hi
        simp only [List.length_cons] at hi
        rcases i with _ | j
        · simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero,
            y, a4, a3, a2, a1, Data.set_mem, Data.write_mem, Function.update_self]
        · have hj : j < s.freeList.length := by omega
          have hidx : (h :: s.freeList).length - 1 - (j + 1) = s.freeList.length - 1 - j := by
            simp only [List.length_cons]; omega
          have hne_addr :
              base + FibonacciHeap.space n_max + n_max + (s.freeList.length - 1 - j) ≠
              base + FibonacciHeap.space n_max + n_max + s.freeList.length := by omega
          rw [hidx]
          simp only [List.getElem_cons_succ, y, a4, a3, a2, a1, Data.set_mem, Data.write_mem,
            Function.update_of_ne hne_addr]
          exact (hmem1_ge _ (by omega)).trans (hfree j hj)
    · have hp_y : potential y = FibonacciHeap.potential y_fib := by
        unfold potential
        rw [FibonacciHeap.potential_supported hreg_fib, Data.comap_extend f42_injective]
      rw [hp_y]
      unfold potential
      omega

/-! ## Unified dispatcher and `RelSubroutineDS` certificate -/

/-- Unified dispatcher `dispatchCode` implements all five `MinPQ` operations within
`charge n_max e o` amortized instructions over `Basis.exact`. -/
theorem dispatchCode_exec_raw {n_max U V w base : ℕ}
    {e : Cslib.Algorithms.Lean.MinPQ.State n_max} {x : Data rMinPQ}
    (o : Cslib.Algorithms.Lean.MinPQ.Op n_max) (hr : Rep n_max U V w base e x)
    (hv : (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).valid e o)
    (harg : rawArgMatch o x.regs) :
    ∃ y s' a m, Exec w dispatchCode x y m ∧
      (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).step e o s' a ∧
      decode (n_max := n_max) (U := U) (V := V) o y.regs = some a ∧
      Rep n_max U V w base s' y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      m + potential y ≤ charge n_max e o + potential x := by
  obtain ⟨s, rfl, hrep⟩ := hr
  have hz0 : x.regs zeroP = 0 := hrep.zeroP_eq
  obtain ⟨hstep_s, _⟩ :=
    Cslib.Algorithms.Lean.MinPQ.stepAlloc_refines_spec (U := U) (V := V) hrep.2.2.1 o hv
  cases o with
  | isEmpty =>
    obtain ⟨ht2, ht1, ht0⟩ := harg
    have c2 : (Cond.eq tag2 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht2
    have c1 : (Cond.eq tag1 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht1
    have c0 : (Cond.eq tag0 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht0
    obtain ⟨y, t, ⟨m, hm, he⟩, hdec, hrep_y, hmod, hpot⟩ := isEmptyCode_exec hrep
    refine ⟨y, _, _, m + 1 + 1 + 1,
      Exec.branch_pos c2 (Exec.branch_pos c1 (Exec.branch_pos c0 he)),
      hstep_s, hdec, ⟨_, rfl, hrep_y⟩, hmod, ?_⟩
    simp only [charge, tEmpty]
    omega
  | get h =>
    obtain ⟨ht2, ht1, ht0, hv_reg⟩ := harg
    have c2 : (Cond.eq tag2 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht2
    have c1 : (Cond.eq tag1 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht1
    have c0 : ¬(Cond.eq tag0 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht0
    obtain ⟨y, t, ⟨m, hm, he⟩, hdec, hrep_y, hmod, hpot⟩ := getCode_exec h hrep hv_reg
    refine ⟨y, _, _, m + 2 + 1 + 1,
      Exec.branch_pos c2 (Exec.branch_pos c1 (Exec.branch_neg c0 he)),
      hstep_s, hdec, ⟨_, rfl, hrep_y⟩, hmod, ?_⟩
    simp only [charge, tGet]
    omega
  | insert u v =>
    obtain ⟨ht2, ht1, ht0, hk_reg, hval_reg⟩ := harg
    have c2 : (Cond.eq tag2 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht2
    have c1 : ¬(Cond.eq tag1 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht1
    have c0 : (Cond.eq tag0 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht0
    obtain ⟨y, t, ⟨m, hm, he⟩, hdec, hrep_y, hmod, hpot⟩ :=
      insertCode_exec hrep hv hk_reg hval_reg
    refine ⟨y, _, _, m + 1 + 2 + 1,
      Exec.branch_pos c2 (Exec.branch_neg c1 (Exec.branch_pos c0 he)),
      hstep_s, hdec, ⟨_, rfl, hrep_y⟩, hmod, ?_⟩
    simp only [charge, tIns]
    omega
  | decreaseKey h u' =>
    obtain ⟨ht2, ht1, ht0, hv_reg, hk_reg⟩ := harg
    have c2 : (Cond.eq tag2 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht2
    have c1 : ¬(Cond.eq tag1 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht1
    have c0 : ¬(Cond.eq tag0 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact ht0
    obtain ⟨y, t, ⟨m, hm, he⟩, hdec, hrep_y, hmod, hpot⟩ :=
      decreaseKeyCode_exec h u' hrep hv hv_reg hk_reg
    refine ⟨y, _, _, m + 2 + 2 + 1,
      Exec.branch_pos c2 (Exec.branch_neg c1 (Exec.branch_neg c0 he)),
      hstep_s, hdec, ⟨_, rfl, hrep_y⟩, hmod, ?_⟩
    simp only [charge, tDec]
    omega
  | extractMin =>
    have c2 : ¬(Cond.eq tag2 zeroP).Holds x := by simp only [Cond.Holds, hz0]; exact harg
    obtain ⟨y, t, ⟨m, hm, he⟩, hdec, hrep_y, hmod, hpot⟩ := extractMinCode_exec hrep
    refine ⟨y, _, _, m + 2, Exec.branch_neg c2 he, hstep_s, hdec, ⟨_, rfl, hrep_y⟩, hmod, ?_⟩
    simp only [charge, tExt]
    omega

theorem dispatchCode_exec {n_max U V w base : ℕ}
    {e : Cslib.Algorithms.Lean.MinPQ.State n_max} {x : Data rMinPQ}
    (o : Cslib.Algorithms.Lean.MinPQ.Op n_max) (hr : Rep n_max U V w base e x)
    (hv : (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).valid e o)
    (harg : argMatch U o x.regs) :
    ∃ y s' a m, Exec w dispatchCode x y m ∧
      (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).step e o s' a ∧
      decode (n_max := n_max) (U := U) (V := V) o y.regs = some a ∧
      Rep n_max U V w base s' y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      m + potential y ≤ charge n_max e o + potential x := by
  obtain ⟨s, rfl, hrep⟩ := hr
  exact dispatchCode_exec_raw o ⟨s, rfl, hrep⟩ hv (rawArgMatch_of_argMatch hrep hv harg)

/-- Unified standalone and inline-subroutine relational certificate for the key–value
Fibonacci heap with handles over `Basis.exact`. -/
def relSubroutineDS {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V) :
    RelSubroutineDS subroutineCode (Cslib.Algorithms.Lean.MinPQ.spec n_max U V) w base ![n_max]
      (Cslib.Algorithms.Lean.MinPQ.empty n_max) where
  space := space n_max
  spanTime := 15
  setupTime := 18
  initPotential := 0
  charge := charge n_max
  rep := Rep n_max U V w base
  potential := potential
  encode := encode U
  argMatch := argMatch U
  decode := decode
  bounded := fun ⟨_, _, h⟩ => h.1
  arguments_fit o hv i _ := arguments_fit hS hU hV o hv i
  encode_matches := encode_matches
  rep_supported := Rep.supported
  potential_supported hreg _ _ := potential_supported hreg
  clear_nodup := by decide
  params_not_clear := by decide
  incCur_eval := incCur_eval
  span_exec := allocSpan_exec hS
  setup_exec := initSetup_exec
  step_exec := dispatchCode_exec

/-! ## Standalone `Basis.standard` `DynamicProgram` and `Stateful.RelAmortized` realizations -/

/-- Standalone `DynamicProgram` realization of the key–value Fibonacci heap over
`Basis.standard`. -/
def relDynamicProgram {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V) :
    DynamicProgram (Cslib.Algorithms.Lean.MinPQ.spec n_max U V) rMinPQ :=
  (relSubroutineDS (n_max := n_max) (U := U) (V := V) hS hU hV).toStandard.toDynamicProgram

/-- Standalone `RelDynamicCertificate` for the key–value Fibonacci heap over `Basis.standard`. -/
def relCertificate {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V) :
    RelDynamicCertificate (relDynamicProgram hS hU hV) w :=
  (relSubroutineDS hS hU hV).toStandard.toRelCertificate

/-- Standalone `Stateful.RelAmortized` certificate for the key–value Fibonacci heap over
`Basis.standard`, charging `+ 1` per operation for the trailing `halt` instruction. -/
theorem relAmortized {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V) :
    Stateful.RelAmortized (relCertificate hS hU hV).realization
      DynamicProgram.OperationTrace.instructions
      (fun _ x => potential x)
      (fun s o => charge n_max s o + 1) :=
  (relSubroutineDS hS hU hV).toStandard.toRelAmortized

/-- Adaptive-client amortized execution bound for any demonically admissible `MinPQ` client `p`
over `Basis.standard`. -/
theorem run_client_amortized {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V)
    {α : Type*} (p : (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).Client α)
    {s : Cslib.Algorithms.Lean.MinPQ.State n_max} {x : Data rMinPQ}
    (hr : Rep n_max U V w base s x)
    (hv : (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).DemonicValid s p) :
    ∃ a y traces s' tr,
      Stateful.Executes ((relDynamicProgram hS hU hV).ExecOp w) p x a y traces ∧
      (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).ClientRun s p a s' tr ∧
      Rep n_max U V w base s' y ∧
      traces.length = tr.length ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces + potential y ≤
        (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).totalCost
          (fun st o => charge n_max st o + 1) s tr + potential x :=
  (relSubroutineDS hS hU hV).toStandard.run_client_amortized p hr hv

/-! ## Standalone end-to-end `Basis.exact` flat-program operation-sequence theorems -/

/-- Compiled flat `Program .exact rMinPQ` for `O(1)` fresh zeroed-memory initialization. -/
def initFreshProg : Program .exact rMinPQ := subroutineCode.initFreshProg

/-- Compiled flat `Program .exact rMinPQ` for `O(n_max)` dirty-memory reusable initialization. -/
def initClearProg : Program .exact rMinPQ := subroutineCode.initClearProg

/-- Compiled flat `Program .exact rMinPQ` serving all five priority-queue operations. -/
def opProg : Program .exact rMinPQ := subroutineCode.opProg

/-- Initial register assignment supplying `n_max` in `nReg` (`R[0]`), `base` in `outerFrontierReg`
(`R[1]`), and `0` elsewhere. -/
def initRegs (n_max base : ℕ) : Fin rMinPQ → ℕ :=
  fun i => if i = nReg then n_max else if i = outerFrontierReg then base else 0

/-- Deliver operation `o`'s 3-bit tag into `tag2..tag0` (`R[17..19]`), handle/key arguments into
`argV, argK` (`R[20..21]`), and satellite value into `inValReg` (`R[46]`), leaving all other
registers unchanged. -/
def prepareRegs {n_max : ℕ} (o : Cslib.Algorithms.Lean.MinPQ.Op n_max)
    (regs : Fin rMinPQ → ℕ) : Fin rMinPQ → ℕ :=
  fun i =>
    if i = tag2 ∨ i = tag1 ∨ i = tag0 ∨ i = argV ∨ i = argK ∨ i = inValReg then
      rawEncode o i
    else
      regs i

/-- Count `isEmpty` and `get` queries in an operation sequence. -/
def numQueries {n_max : ℕ} : List (Cslib.Algorithms.Lean.MinPQ.Op n_max) → ℕ
  | [] => 0
  | .isEmpty :: ops | .get _ :: ops => 1 + numQueries ops
  | _ :: ops => numQueries ops

/-- Count `insert` operations in an operation sequence. -/
def numInserts {n_max : ℕ} : List (Cslib.Algorithms.Lean.MinPQ.Op n_max) → ℕ
  | [] => 0
  | .insert _ _ :: ops => 1 + numInserts ops
  | _ :: ops => numInserts ops

/-- Count `decreaseKey` operations in an operation sequence. -/
def numDecreaseKeys {n_max : ℕ} : List (Cslib.Algorithms.Lean.MinPQ.Op n_max) → ℕ
  | [] => 0
  | .decreaseKey _ _ :: ops => 1 + numDecreaseKeys ops
  | _ :: ops => numDecreaseKeys ops

/-- Count `extractMin` operations in an operation sequence. -/
def numExtractMins {n_max : ℕ} : List (Cslib.Algorithms.Lean.MinPQ.Op n_max) → ℕ
  | [] => 0
  | .extractMin :: ops => 1 + numExtractMins ops
  | _ :: ops => numExtractMins ops

/-- Sum of `Nat.log 2 (MinPQ.size s) + 1` over all `extractMin` steps along a relational
transcript `tr` starting from state `s`, where `MinPQ.size s` is the number of stored elements
immediately before each `extractMin`. -/
def extractLogSum {n_max U V : ℕ} :
    Cslib.Algorithms.Lean.MinPQ.State n_max →
      (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).Transcript → ℕ
  | _, [] => 0
  | s, e :: tr =>
    (match e.op with
     | .extractMin => Nat.log 2 (Cslib.Algorithms.Lean.MinPQ.size s) + 1
     | _ => 0) + extractLogSum e.nextState tr

theorem extractLogSum_le_numExtractMins {n_max U V : ℕ} :
    ∀ (tr : (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).Transcript)
      (s : Cslib.Algorithms.Lean.MinPQ.State n_max),
      extractLogSum s tr ≤ numExtractMins tr.ops * (Nat.log 2 n_max + 1)
  | [], _ => Nat.zero_le _
  | ⟨o, res, s₁⟩ :: tr, s => by
    have ih := extractLogSum_le_numExtractMins tr s₁
    have hlog : Nat.log 2 (Cslib.Algorithms.Lean.MinPQ.size s) ≤ Nat.log 2 n_max :=
      Nat.log_mono_right (Cslib.Algorithms.Lean.MinPQ.size_le s)
    cases o with
    | extractMin =>
      simp only [extractLogSum, Stateful.RelSpec.Transcript.ops_cons, numExtractMins,
        Nat.add_mul, Nat.one_mul]
      omega
    | _ =>
      simp only [extractLogSum, Stateful.RelSpec.Transcript.ops_cons, numExtractMins,
        Nat.zero_add]
      omega

/-- Sequential flat-program execution of `ops` by repeated calls to `opProg`: each call prepares
input registers via `prepareRegs`, runs `opProg` from `pc = 0` to `halt`, decodes a valid
`MinPQ.spec` transition `(s₁, a)`, modifies memory only within `[base, base + space n_max)`,
records the resulting transcript `tr`, and accumulates total instructions executed (including
each trailing `halt`). -/
inductive RunsOps {n_max U V : ℕ} (w base : ℕ) :
    Cslib.Algorithms.Lean.MinPQ.State n_max → Data rMinPQ →
      List (Cslib.Algorithms.Lean.MinPQ.Op n_max) →
      (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).Transcript →
      Cslib.Algorithms.Lean.MinPQ.State n_max → Data rMinPQ → ℕ → Prop
  | nil {s x} : RunsOps w base s x [] [] s x 0
  | cons {s s₁ s₂ x o a ops tr pc y z steps rest} :
      Runs w opProg ⟨0, ⟨prepareRegs o x.regs, x.mem⟩⟩ ⟨pc, y⟩ steps →
      (∃ out, step w opProg ⟨pc, y⟩ = .halt out) →
      (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).step s o s₁ a →
      decode (n_max := n_max) (U := U) (V := V) o y.regs = some a →
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem →
      RunsOps w base s₁ y ops tr s₂ z rest →
      RunsOps w base s x (o :: ops) (⟨o, a, s₁⟩ :: tr) s₂ z ((steps + 1) + rest)

private theorem step_program_halt {w : ℕ} (c : Code .exact rMinPQ) (out : Fin rMinPQ)
    (y : Data rMinPQ) : step w (c.program out) ⟨0 + c.size, y⟩ = .halt (y.regs out) :=
  step_halt (by
    simp only [Code.program, Nat.zero_add,
      List.getElem?_append_right (Code.length_assemble c 0).le,
      Code.length_assemble, Nat.sub_self, List.getElem?_cons_zero])

private theorem seq_runsOps {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V) :
    ∀ (ops : List (Cslib.Algorithms.Lean.MinPQ.Op n_max))
      {s : Cslib.Algorithms.Lean.MinPQ.State n_max} {x : Data rMinPQ},
      Rep n_max U V w base s x →
      (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).ValidOpSeq s ops →
      ∃ tr s_fin z total,
        RunsOps (U := U) (V := V) w base s x ops tr s_fin z total ∧
        tr.ops = ops ∧
        (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).ValidTranscript s tr s_fin ∧
        Rep n_max U V w base s_fin z ∧
        total + potential z ≤
          421 * (numQueries ops + numInserts ops + numDecreaseKeys ops +
            extractLogSum s tr) + potential x
  | [], s, x, hr, _ =>
    ⟨[], s, x, 0, .nil, rfl, .nil (D := Cslib.Algorithms.Lean.MinPQ.spec n_max U V) s, hr,
      by simp only [numQueries, numInserts, numDecreaseKeys, extractLogSum]; omega⟩
  | o :: ops, s, x, hr, ⟨hv_o, hv_rest⟩ => by
    let x' : Data rMinPQ := ⟨prepareRegs o x.regs, x.mem⟩
    have hbx : x.Bounded w := hr.choose_spec.2.1
    have henc_eq : encode U o = rawEncode o := encode_eq_rawEncode_of_rep hr hv_o
    have hb' : x'.Bounded w := by
      refine ⟨fun i => ?_, hbx.2⟩
      change Fits w (if _ then rawEncode o i else x.regs i)
      split_ifs
      · rw [← henc_eq]
        exact arguments_fit hS hU hV o hv_o i
      · exact hbx.1 i
    have hreg' : ∀ i, inputReg i = false → x'.regs i = x.regs i := fun i hi => by
      have hne : ¬(i = tag2 ∨ i = tag1 ∨ i = tag0 ∨ i = argV ∨ i = argK ∨ i = inValReg) := by
        rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact absurd hi (by decide)
      simp only [x', prepareRegs, hne, ↓reduceIte]
    have hr' : Rep n_max U V w base s x' := hr.supported hreg' (fun _ _ => rfl) hb'
    have hpot' : potential x' = potential x := potential_supported hreg'
    have harg' : rawArgMatch o x'.regs := by
      cases o with
      | isEmpty => exact ⟨rfl, rfl, rfl⟩
      | get _ => exact ⟨rfl, rfl, Nat.one_ne_zero, rfl⟩
      | insert _ _ => exact ⟨rfl, Nat.one_ne_zero, rfl, rfl, rfl⟩
      | decreaseKey _ _ => exact ⟨rfl, Nat.one_ne_zero, Nat.one_ne_zero, rfl, rfl⟩
      | extractMin => exact Nat.one_ne_zero
    obtain ⟨y, s₁, a, m, he_op, hstep, hdec, hr_y, hmod, hpot_m⟩ :=
      dispatchCode_exec_raw o hr' hv_o harg'
    rw [hpot'] at hpot_m
    have hruns : Runs w opProg ⟨0, x'⟩ ⟨0 + dispatchCode.size, y⟩ m :=
      he_op.runs (pc := 0) (p := opProg) (Program.Contains.self _).append_left
    have hhalt : step w opProg ⟨0 + dispatchCode.size, y⟩ = .halt (y.regs outFlag) :=
      step_program_halt dispatchCode outFlag y
    obtain ⟨tr, s_fin, z, rest, hrest, hops, htr, hr_z, hpot_rest⟩ :=
      seq_runsOps hS hU hV ops hr_y (hv_rest s₁ a hstep)
    refine ⟨⟨o, a, s₁⟩ :: tr, s_fin, z, (m + 1) + rest,
      .cons hruns ⟨_, hhalt⟩ hstep hdec hmod hrest,
      congrArg (o :: ·) hops, .cons ⟨o, a, s₁⟩ hv_o hstep htr, hr_z, ?_⟩
    cases o <;>
      simp only [charge, tEmpty, tGet, tIns, tDec, tExt,
        numQueries, numInserts, numDecreaseKeys, extractLogSum] at hpot_m ⊢ <;>
      omega

private theorem initRegs_bounded {n_max base w : ℕ} (hS : Fits w (base + space n_max))
    {mem₀ : ℕ → ℕ} (hmem : ∀ a, Fits w (mem₀ a)) :
    (⟨initRegs n_max base, mem₀⟩ : Data rMinPQ).Bounded w := by
  refine ⟨fun i => ?_, hmem⟩
  simp only [initRegs]
  split_ifs
  · exact hS.of_le (by have := space_lower n_max; omega)
  · exact hS.of_le (Nat.le_add_right base _)
  · exact hS.of_le (Nat.zero_le _)

/-- Standalone `Basis.exact` operation-sequence theorem with `O(1)` fresh initialization on zeroed
`[base, base + 11 * n_max + 1)` and per-extraction `O(log n + 1)` amortized cost in the current
number of stored elements `n = MinPQ.size s`. -/
theorem run_ops_exact_fresh {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V)
    {mem₀ : ℕ → ℕ} (hmem : ∀ a, Fits w (mem₀ a))
    (hzero : ∀ a ∈ (Block.mk base (space n_max)).footprint, mem₀ a = 0)
    (ops : List (Cslib.Algorithms.Lean.MinPQ.Op n_max))
    (hv : (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).ValidOpSeq
      (Cslib.Algorithms.Lean.MinPQ.empty n_max) ops) :
    ∃ pc₀ x₀ t_init tr s_fin z t_ops,
      Runs w initFreshProg ⟨0, ⟨initRegs n_max base, mem₀⟩⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w initFreshProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base (space n_max)).footprint mem₀ x₀.mem ∧
      RunsOps (U := U) (V := V) w base (Cslib.Algorithms.Lean.MinPQ.empty n_max) x₀ ops tr
        s_fin z t_ops ∧
      tr.ops = ops ∧
      (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).ValidTranscript
        (Cslib.Algorithms.Lean.MinPQ.empty n_max) tr s_fin ∧
      t_init + 1 ≤ 421 ∧
      t_ops ≤
        421 * (numQueries ops + numInserts ops + numDecreaseKeys ops +
          extractLogSum (Cslib.Algorithms.Lean.MinPQ.empty n_max) tr) ∧
      t_ops ≤
        421 * (numQueries ops + numInserts ops + numDecreaseKeys ops +
          numExtractMins ops * (Nat.log 2 n_max + 1)) := by
  let d₀ : Data rMinPQ := ⟨initRegs n_max base, mem₀⟩
  have hfr_eq : d₀.regs outerFrontierReg = base := by
    simp only [d₀, initRegs, show outerFrontierReg ≠ nReg by decide, ↓reduceIte]
  have hpar : ∀ j : Fin 1, d₀.regs (![nReg] j) = ![n_max] j := fun j => by
    fin_cases j; rfl
  obtain ⟨x₀, ⟨t_init, ht_init, he_init⟩, _, hr₀, hpot₀, hmod₀⟩ :=
    (relSubroutineDS hS hU hV).initFresh_exec (initRegs_bounded hS hmem) hfr_eq hpar hzero
  have hruns₀ : Runs w initFreshProg ⟨0, d₀⟩
      ⟨0 + subroutineCode.initFresh.size, x₀⟩ t_init :=
    he_init.runs (pc := 0) (p := initFreshProg) (Program.Contains.self _).append_left
  have hhalt₀ : step w initFreshProg ⟨0 + subroutineCode.initFresh.size, x₀⟩ =
      .halt (x₀.regs outFlag) :=
    step_program_halt subroutineCode.initFresh outFlag x₀
  obtain ⟨tr, s_fin, z, t_ops, hruns_ops, hops, htr, _, hbound⟩ :=
    seq_runsOps hS hU hV ops hr₀ hv
  have hlog_le := extractLogSum_le_numExtractMins tr (Cslib.Algorithms.Lean.MinPQ.empty n_max)
  rw [hops] at hlog_le
  refine ⟨_, x₀, t_init, tr, s_fin, z, t_ops, hruns₀, ⟨_, hhalt₀⟩, hmod₀, hruns_ops,
    hops, htr, ?_, ?_, ?_⟩
  · change t_init ≤ 33 at ht_init
    omega
  · change potential x₀ ≤ 0 at hpot₀
    omega
  · change potential x₀ ≤ 0 at hpot₀
    omega

/-- Standalone `Basis.exact` operation-sequence theorem with `O(n_max)` reusable initialization on
arbitrary `w`-bounded memory `mem₀` and per-extraction `O(log n + 1)` amortized cost in the current
number of stored elements `n = MinPQ.size s`. -/
theorem run_ops_exact_reusable {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V)
    {mem₀ : ℕ → ℕ} (hmem : ∀ a, Fits w (mem₀ a))
    (ops : List (Cslib.Algorithms.Lean.MinPQ.Op n_max))
    (hv : (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).ValidOpSeq
      (Cslib.Algorithms.Lean.MinPQ.empty n_max) ops) :
    ∃ pc₀ x₀ t_init tr s_fin z t_ops,
      Runs w initClearProg ⟨0, ⟨initRegs n_max base, mem₀⟩⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w initClearProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base (space n_max)).footprint mem₀ x₀.mem ∧
      RunsOps (U := U) (V := V) w base (Cslib.Algorithms.Lean.MinPQ.empty n_max) x₀ ops tr
        s_fin z t_ops ∧
      tr.ops = ops ∧
      (Cslib.Algorithms.Lean.MinPQ.spec n_max U V).ValidTranscript
        (Cslib.Algorithms.Lean.MinPQ.empty n_max) tr s_fin ∧
      t_init + 1 ≤ 421 * (n_max + 1) ∧
      t_ops ≤
        421 * (numQueries ops + numInserts ops + numDecreaseKeys ops +
          extractLogSum (Cslib.Algorithms.Lean.MinPQ.empty n_max) tr) ∧
      t_ops ≤
        421 * (numQueries ops + numInserts ops + numDecreaseKeys ops +
          numExtractMins ops * (Nat.log 2 n_max + 1)) := by
  let d₀ : Data rMinPQ := ⟨initRegs n_max base, mem₀⟩
  have hfr_eq : d₀.regs outerFrontierReg = base := by
    simp only [d₀, initRegs, show outerFrontierReg ≠ nReg by decide, ↓reduceIte]
  have hpar : ∀ j : Fin 1, d₀.regs (![nReg] j) = ![n_max] j := fun j => by
    fin_cases j; rfl
  obtain ⟨x₀, ⟨t_init, ht_init, he_init⟩, _, hr₀, hpot₀, hmod₀⟩ :=
    (relSubroutineDS hS hU hV).initClear_exec (initRegs_bounded hS hmem) hfr_eq hpar
  have hruns₀ : Runs w initClearProg ⟨0, d₀⟩
      ⟨0 + subroutineCode.initClear.size, x₀⟩ t_init :=
    he_init.runs (pc := 0) (p := initClearProg) (Program.Contains.self _).append_left
  have hhalt₀ : step w initClearProg ⟨0 + subroutineCode.initClear.size, x₀⟩ =
      .halt (x₀.regs outFlag) :=
    step_program_halt subroutineCode.initClear outFlag x₀
  obtain ⟨tr, s_fin, z, t_ops, hruns_ops, hops, htr, _, hbound⟩ :=
    seq_runsOps hS hU hV ops hr₀ hv
  have hlog_le := extractLogSum_le_numExtractMins tr (Cslib.Algorithms.Lean.MinPQ.empty n_max)
  rw [hops] at hlog_le
  refine ⟨_, x₀, t_init, tr, s_fin, z, t_ops, hruns₀, ⟨_, hhalt₀⟩, hmod₀, hruns_ops,
    hops, htr, ?_, ?_, ?_⟩
  · change t_init ≤ 33 + 4 * (11 * n_max + 1) + 6 at ht_init
    omega
  · change potential x₀ ≤ 0 at hpot₀
    omega
  · change potential x₀ ≤ 0 at hpot₀
    omega

end Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.MinPQ
