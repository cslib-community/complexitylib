/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.BoundedExec
public import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
public import CslibFrontier.Computability.WordRAM.Realization.Reindex
public import CslibFrontier.Tactic.Realize

/-!
# Resizable Word RAM machine model

This module formalizes the word-granular **Resizable Word RAM** machine model (`RData`, `RInstr`,
`RProgram`, `RCode`, and `RDemonicExec`), grounding the resizable word-prefix memory model of
[LiLiangYuZhou2023Succincter], [LiLiangYuZhou2024], and [KuszmaulLiangZhou2026] directly on
`Cslib.WordRAM` instructions.

A machine configuration `RData r` holds `r` registers (`regs : Fin r → ℕ`), word-addressed memory
(`mem : ℕ → ℕ`), and the `0`-indexed active word frontier (`frontier : ℕ`, `[0, frontier)`):

1. **Bounds-checked access (`evalResizable`)**: `Op.load d a` and `Op.store a s` require
   `x.regs a < x.frontier`, faulting (`none`) otherwise.
2. **Word-granular resizing (`RInstr.grow`, `RInstr.shrink`)**: `grow dst kReg` extends
   `[0, frontier)` to `[0, frontier + k)` when `Fits w (frontier + k)`, stores old `frontier` in
   `dst`, and initializes `[frontier, frontier + k)` demonically (`DemonicGrow`, matching
   [KuszmaulLiangZhou2026], Section 5.1, Footnote 10); `shrink kReg` contracts `[0, frontier)` by
   `k ≤ frontier` words and zeroes `[frontier - k, frontier)`.
3. **Direct `realize` bridge (`RDemonicExec.of_execBounded`, `RDemonicExec.of_realizesBounded`)**:
   any `ExecBounded w L c x.toData y T` with `L ≤ x.frontier` lifts directly to `RDemonicExec`, and
   `growZeroCode` erases demonic growth in `4 * k + 7` instructions.

## Main definitions

* `Cslib.WordRAM.Resizable.RData`, `Cslib.WordRAM.Resizable.RData.Bounded`: resizable machine data
  and its word/frontier boundedness invariant.
* `Cslib.WordRAM.Resizable.DemonicGrow`, `Cslib.WordRAM.Resizable.evalResizable`: demonic growth
  relation and bounds-checked data instruction evaluation.
* `Cslib.WordRAM.Resizable.RInstr`, `Cslib.WordRAM.Resizable.RProgram`,
  `Cslib.WordRAM.Resizable.RState`, `Cslib.WordRAM.Resizable.RCfg`,
  `Cslib.WordRAM.Resizable.RCode`: flat and structured Resizable Word RAM programs and states.
* `Cslib.WordRAM.Resizable.RDemonicExec`: big-step demonic execution tracking steps `T` and peak
  hardware word frontier `L_peak`.
* `Cslib.WordRAM.Resizable.growZeroCode`: exact-basis (`Basis.exact`) subroutine executing demonic
  `grow` followed by zero-fill (transferable via `RCode.mapSimulates`).

## Main results

* `Cslib.WordRAM.Resizable.clear_demonicGrow_eq`: clearing `[frontier, frontier + k)` after
  `DemonicGrow` recovers canonical zero-extended memory.
* `Cslib.WordRAM.Resizable.RDemonicExec.of_execBounded`,
  `Cslib.WordRAM.Resizable.RDemonicExec.of_realizesBounded`,
  `Cslib.WordRAM.Resizable.RDemonicExec.mapSimulates`: lifting `ExecBounded`/`RealizesBounded`
  programs and transporting bases.
* `Cslib.WordRAM.Resizable.growZeroCode_exec`: `growZeroCode` executes in `4 * k + 7` instructions
  with peak frontier `x.frontier + k` and zeroes demonically initialized words.

## References

* [Hagerup1998] Torben Hagerup, *Sorting and Searching on the Word RAM*, STACS 1998.
* [LiLiangYuZhou2023Succincter] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic
  "Succincter"*, FOCS 2023, pp. 1715–1733 (`arXiv:2309.12950v1`, Section 2.1).
* [LiLiangYuZhou2024] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic
  Dictionary with Subconstant Wasted Bits per Key*, SODA 2024 (`arXiv:2310.20536v1`, Section 3.2,
  PDF pp. 9–11 / printed pp. 8–10).
* [KuszmaulLiangZhou2026] William Kuszmaul, Jingxun Liang, and Renfei Zhou, *Succinct Dynamic
  Rank/Select: Bypassing the Tree-Structure Bottleneck*, SODA 2026 (`arXiv:2510.19175v1`,
  Section 5.1, PDF pp. 16–19 / printed pp. 15–18, and Footnote 10, PDF p. 18 / printed p. 17).
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.RealizesBounded

open Cslib.DataStructure

/-- Absorbed frontier-bounded `iterate₀` rule when every body issues at least one memory query. -/
theorem iterate₀ {δ : Type} {k l : ℕ} {σ : Type}
    (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → (δ × σ) → Memory.State → Prop}
    (h : RealizesBounded .exact body
      ((input.prodMap output).trans (Fin.appendEquiv k l).toEmbedding)
      output safe (fun _ _ => 0))
    (hquery : ∀ x s, 1 ≤ memoryCost (body x) s) :
    RealizesBounded .exact (fun d : (δ × σ) × ℕ => iterate body d.1.1 d.2 d.1.2)
      ((((input.prodMap output).trans (Fin.appendEquiv k l).toEmbedding).prodMap
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
          (Fin.appendEquiv (k + l) 1).toEmbedding) output
      (fun w d s => iterationSafe body safe w d.1.1 d.2 d.1.2 s) (fun _ _ => 0) :=
  (iterateRuntime input output h).mono_mul 1 fun ((d, a), fuel) s => by
    have := iterationWork_zero_le body hquery d fuel a s
    dsimp only
    omega

/-- Absorbed frontier-bounded `while₀` rule when every body issues at least one memory query. -/
theorem while₀ {δ σ : Type} {B : Basis} {k l : ℕ}
    (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ)) (cond : Cond (k + l))
    (cutoff : δ × σ → ℕ) {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    (h : RealizesBounded B body (appendWords input output) output safe (fun _ _ => 0))
    (hquery : ∀ x s, 1 ≤ memoryCost (body x) s) :
    RealizesBounded B (fun (d, a) => boundedWhile
      (fun d a => test cond ((appendWords input output) (d, a))) body d (cutoff (d, a)) a)
      (appendWords input output) output
      (fun w (d, a) s => whileSafe
        (fun d a => test cond ((appendWords input output) (d, a))) body safe w d
        (cutoff (d, a)) a s)
      (fun _ _ => 0) :=
  (whileBounded input output cond cutoff h).mono_mul 1 fun (d, a) s => by
    have := whileWork_zero_le (fun d a => test cond ((appendWords input output) (d, a))) body
      hquery d (cutoff (d, a)) a s
    dsimp only
    omega

end Cslib.WordRAM.Realization.RealizesBounded

namespace Cslib.WordRAM.Resizable

open Cslib.WordRAM Cslib.DataStructure

variable {B B' : Basis} {r : ℕ}

/-! ## Resizable machine data and demonic word growth -/

/-- Machine data of a word-granular Resizable Word RAM: `r` registers, word-addressed memory `mem`,
and the current number of allocated `w`-bit words `frontier` (the active prefix is
`[0, frontier)`). -/
@[ext]
structure RData (r : ℕ) where
  /-- Register file contents. -/
  regs : Fin r → ℕ
  /-- Word-addressed memory contents. -/
  mem : ℕ → ℕ
  /-- Number of currently allocated words `L`. -/
  frontier : ℕ

namespace RData

/-- Underlying fixed-memory `WordRAM.Data r` (registers and memory). -/
def toData (x : RData r) : Data r := ⟨x.regs, x.mem⟩

/-- Set register `i` to `v`. -/
def set (x : RData r) (i : Fin r) (v : ℕ) : RData r :=
  ⟨Function.update x.regs i v, x.mem, x.frontier⟩

/-- Write `v` to memory address `a`. -/
def write (x : RData r) (a v : ℕ) : RData r :=
  ⟨x.regs, Function.update x.mem a v, x.frontier⟩

/-- Set register `i` to `v` if `Fits w v`, and fault (`none`) otherwise. -/
def put (w : ℕ) (x : RData r) (i : Fin r) (v : ℕ) : Option (RData r) :=
  if Fits w v then some (x.set i v) else none

@[simp] theorem toData_regs (x : RData r) : x.toData.regs = x.regs := rfl
@[simp] theorem toData_mem (x : RData r) : x.toData.mem = x.mem := rfl
@[simp] theorem set_regs (x : RData r) (i : Fin r) (v : ℕ) :
    (x.set i v).regs = Function.update x.regs i v := rfl
@[simp] theorem set_mem (x : RData r) (i : Fin r) (v : ℕ) : (x.set i v).mem = x.mem := rfl
@[simp] theorem set_frontier (x : RData r) (i : Fin r) (v : ℕ) :
    (x.set i v).frontier = x.frontier := rfl
@[simp] theorem set_toData (x : RData r) (i : Fin r) (v : ℕ) :
    (x.set i v).toData = x.toData.set i v := rfl
@[simp] theorem write_regs (x : RData r) (a v : ℕ) : (x.write a v).regs = x.regs := rfl
@[simp] theorem write_mem (x : RData r) (a v : ℕ) :
    (x.write a v).mem = Function.update x.mem a v := rfl
@[simp] theorem write_frontier (x : RData r) (a v : ℕ) :
    (x.write a v).frontier = x.frontier := rfl
@[simp] theorem write_toData (x : RData r) (a v : ℕ) :
    (x.write a v).toData = x.toData.write a v := rfl

theorem put_of_fits {w : ℕ} {x : RData r} {i : Fin r} {v : ℕ} (h : Fits w v) :
    x.put w i v = some (x.set i v) := by simp [put, h]

/-- Word-boundedness and canonical frontier invariant at word width `w`: every register and memory
cell holds a `w`-bit word, `frontier` fits in a `w`-bit word, and all unallocated cells
`a ≥ frontier` hold `0`. -/
def Bounded (w : ℕ) (x : RData r) : Prop :=
  x.toData.Bounded w ∧ Fits w x.frontier ∧ (∀ a, x.frontier ≤ a → x.mem a = 0)

theorem Bounded.regs_fits {w : ℕ} {x : RData r} (hx : x.Bounded w) (i : Fin r) :
    Fits w (x.regs i) := hx.1.1 i
theorem Bounded.mem_fits {w : ℕ} {x : RData r} (hx : x.Bounded w) (a : ℕ) :
    Fits w (x.mem a) := hx.1.2 a
theorem Bounded.frontier_fits {w : ℕ} {x : RData r} (hx : x.Bounded w) :
    Fits w x.frontier := hx.2.1
theorem Bounded.zero_above {w : ℕ} {x : RData r} (hx : x.Bounded w) {a : ℕ}
    (ha : x.frontier ≤ a) : x.mem a = 0 := hx.2.2 a ha
theorem Bounded.set {w : ℕ} {x : RData r} (hx : x.Bounded w) {i : Fin r} {v : ℕ}
    (hv : Fits w v) : (x.set i v).Bounded w := ⟨hx.1.set hv, hx.2.1, hx.2.2⟩

theorem Bounded.write {w : ℕ} {x : RData r} (hx : x.Bounded w) {a v : ℕ}
    (ha : a < x.frontier) (hv : Fits w v) : (x.write a v).Bounded w := by
  refine ⟨⟨hx.1.1, fun b => ?_⟩, hx.2.1, fun b hb => ?_⟩
  · dsimp only [RData.write, RData.toData]
    by_cases hba : b = a
    · subst hba; simpa using hv
    · simpa [Function.update_of_ne hba] using hx.1.2 b
  · dsimp only [RData.write] at hb ⊢
    have hba : b ≠ a := by omega
    simpa [Function.update_of_ne hba] using hx.2.2 b hb

end RData

/-- Demonic word-granular growth of `[0, L)` by `k` words at word width `w`
([KuszmaulLiangZhou2026], Section 5.1): existing cells `a < L` retain their values, newly
allocated cells `a ∈ [L, L + k)` receive arbitrary `w`-bit words (`Fits w (mem' a)`), and
unallocated cells `a ≥ L + k` hold `0`. -/
def DemonicGrow (w L k : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  (∀ a < L, mem' a = mem a) ∧
    (∀ a, L ≤ a → a < L + k → Fits w (mem' a)) ∧
    (∀ a, L + k ≤ a → mem' a = 0)

/-- Zero-initializing the newly grown range `[L, L + k)` via `clear mem L k` is a particular
instance of `DemonicGrow` whenever `mem` is zero above `L`. -/
theorem demonicGrow_clear (w L k : ℕ) (mem : ℕ → ℕ) (hz : ∀ a, L ≤ a → mem a = 0) :
    DemonicGrow w L k mem (clear mem L k) := by
  refine ⟨fun a ha => ?_, fun a hlo hhi => ?_, fun a ha => ?_⟩
  · exact clear_of_not_owns (by simp only [Block.Owns]; omega)
  · rw [clear_of_owns ⟨hlo, hhi⟩]
    exact fits_zero w
  · rw [clear_of_not_owns (by simp only [Block.Owns]; omega)]
    exact hz a (by omega)

/-- Any memory `mem'` satisfying `DemonicGrow w x.frontier k x.mem mem'` preserves `RData.Bounded w`
when the new frontier `x.frontier + k` fits in `w` bits. -/
theorem RData.Bounded.grow {w : ℕ} {x : RData r} (hx : x.Bounded w) {dst : Fin r} {k : ℕ}
    {mem' : ℕ → ℕ} (hfit : Fits w (x.frontier + k))
    (hgrow : DemonicGrow w x.frontier k x.mem mem') :
    (⟨Function.update x.regs dst x.frontier, mem', x.frontier + k⟩ : RData r).Bounded w := by
  refine ⟨⟨?_, ?_⟩, hfit, hgrow.2.2⟩
  · intro i
    dsimp only [RData.toData]
    by_cases hid : i = dst
    · subst hid; simpa using hx.frontier_fits
    · simpa [Function.update_of_ne hid] using hx.regs_fits i
  · intro a
    dsimp only [RData.toData]
    by_cases hlt : a < x.frontier
    · rw [hgrow.1 a hlt]
      exact hx.mem_fits a
    · by_cases hmid : a < x.frontier + k
      · exact hgrow.2.1 a (by omega) hmid
      · rw [hgrow.2.2 a (by omega)]
        exact fits_zero w

/-- Shrinking the frontier by `k ≤ x.frontier` words and clearing `[x.frontier - k, x.frontier)`
preserves `RData.Bounded w`. -/
theorem RData.Bounded.shrink {w : ℕ} {x : RData r} (hx : x.Bounded w) {k : ℕ}
    (hk : k ≤ x.frontier) :
    (⟨x.regs, clear x.mem (x.frontier - k) k, x.frontier - k⟩ : RData r).Bounded w := by
  refine ⟨⟨hx.1.1, fun a => ?_⟩, hx.2.1.of_le (Nat.sub_le _ _), fun a ha => ?_⟩
  · dsimp only [RData.toData]
    by_cases hown : (Block.mk (x.frontier - k) k).Owns a
    · rw [clear_of_owns hown]
      exact fits_zero w
    · rw [clear_of_not_owns hown]
      exact hx.mem_fits a
  · dsimp only at ha ⊢
    by_cases hlt : a < x.frontier
    · exact clear_of_owns (by simp only [Block.Owns]; omega)
    · rw [clear_of_not_owns (by simp only [Block.Owns]; omega)]
      exact hx.zero_above (by omega)

/-- Updating a demonically grown memory with `clear mem' frontier k` recovers `x.mem` identically
whenever `x.Bounded w` holds (since `x.mem a = 0` for all `a ≥ x.frontier`). -/
theorem clear_demonicGrow_eq {w k : ℕ} {x : RData r} {mem' : ℕ → ℕ}
    (hx : x.Bounded w) (hdem : DemonicGrow w x.frontier k x.mem mem') :
    clear mem' x.frontier k = x.mem := by
  funext a
  by_cases ha_lt : a < x.frontier
  · rw [clear_of_not_owns (by simp only [Block.Owns]; omega), hdem.1 a ha_lt]
  · by_cases ha_in : a < x.frontier + k
    · have hown : (Block.mk x.frontier k).Owns a := by simp only [Block.Owns]; omega
      rw [clear_of_owns hown, hx.zero_above (by omega)]
    · rw [clear_of_not_owns (by simp only [Block.Owns]; omega),
        hdem.2.2 a (by omega), hx.zero_above (by omega)]

/-! ## Bounds-checked data instruction evaluation on `RData r` -/

/-- Evaluate a data instruction on `RData r` at word size `w`.
Unlike fixed-memory `Op.eval`, `load d a` and `store a s` require the accessed word address
`x.regs a` to lie strictly below `x.frontier` (`x.regs a < x.frontier`), faulting (`none`) on any
access at or above the current frontier. -/
def evalResizable (w : ℕ) : Op B r → RData r → Option (RData r)
  | .const d v, x => x.put w d v
  | .copy d s, x => some (x.set d (x.regs s))
  | .alu f d args, x => do
      let value ← B.interp w f (x.regs ∘ args)
      x.put w d value
  | .load d a, x =>
      if x.regs a < x.frontier then some (x.set d (x.mem (x.regs a))) else none
  | .store a s, x =>
      if x.regs a < x.frontier then some (x.write (x.regs a) (x.regs s)) else none

/-- Any data instruction whose fixed-memory `Op.eval` succeeds with `Op.BoundedAccess L x.toData`
for `L ≤ x.frontier` evaluates identically under `evalResizable` and preserves `x.frontier`. -/
theorem evalResizable_of_boundedAccess {w L : ℕ} {o : Op B r} {x : RData r} {y : Data r}
    (hb : o.BoundedAccess L x.toData) (hL : L ≤ x.frontier) (he : o.eval w x.toData = some y) :
    evalResizable w o x = some ⟨y.regs, y.mem, x.frontier⟩ := by
  cases o with
  | const d v =>
    dsimp only [Op.eval, RData.toData, Data.put, evalResizable, RData.put] at he ⊢
    split_ifs at he ⊢ with hf; injection he with hy; subst hy; rfl
  | copy d s => injection he with hy; subst hy; rfl
  | alu f d args =>
    dsimp only [Op.eval, RData.toData, evalResizable] at he ⊢
    cases h_interp : B.interp w f (x.regs ∘ args) with
    | none => simp [h_interp] at he
    | some v =>
      simp only [h_interp, bind, Option.bind, Data.put, RData.put] at he ⊢
      split_ifs at he ⊢ with hf; injection he with hy; subst hy; rfl
  | load d a =>
    dsimp only [Op.eval, RData.toData] at he; injection he with hy; subst hy
    have hlt : x.regs a < x.frontier := lt_of_lt_of_le hb hL
    simp [evalResizable, hlt, RData.set, Data.set]
  | store a s =>
    dsimp only [Op.eval, RData.toData] at he; injection he with hy; subst hy
    have hlt : x.regs a < x.frontier := lt_of_lt_of_le hb hL
    simp [evalResizable, hlt, RData.write, Data.write]

/-- `evalResizable` preserves `RData.Bounded w`. -/
theorem RData.Bounded.evalResizable {w : ℕ} {o : Op B r} {x y : RData r}
    (hx : x.Bounded w) (he : Resizable.evalResizable w o x = some y) : y.Bounded w := by
  cases o with
  | const d v =>
    dsimp only [Resizable.evalResizable, RData.put] at he
    split_ifs at he with hf; injection he with hy; subst hy; exact hx.set hf
  | copy d s => injection he with hy; subst hy; exact hx.set (hx.regs_fits s)
  | alu f d args =>
    dsimp only [Resizable.evalResizable] at he
    cases h_interp : B.interp w f (x.regs ∘ args) with
    | none => simp [h_interp] at he
    | some v =>
      simp only [h_interp, bind, Option.bind, RData.put] at he
      split_ifs at he with hf; injection he with hy; subst hy; exact hx.set hf
  | load d a =>
    dsimp only [Resizable.evalResizable] at he
    split_ifs at he with hlt; injection he with hy; subst hy; exact hx.set (hx.mem_fits _)
  | store a s =>
    dsimp only [Resizable.evalResizable] at he
    split_ifs at he with hlt; injection he with hy; subst hy; exact hx.write hlt (hx.regs_fits s)

/-- Basis simulation transports `evalResizable`. -/
theorem evalResizable_mapSimulates (φ : B.Simulates B') {w : ℕ} {o : Op B r} {x y : RData r}
    (he : evalResizable w o x = some y) : evalResizable w (o.mapSimulates φ) x = some y := by
  cases o with
  | const _ _ | copy _ _ | load _ _ | store _ _ => exact he
  | alu f d args =>
    dsimp only [evalResizable] at he
    obtain ⟨v, hv, hput⟩ := Option.bind_eq_some_iff.mp he
    dsimp only [Op.mapSimulates, evalResizable]
    have hv' : B'.interp w (φ.map f)
        (x.regs ∘ fun a => args (Fin.cast (φ.arity_map f) a)) = some v :=
      φ.eval_some w f (x.regs ∘ args) hv
    rw [hv']
    exact hput

/-! ## Flat and structured Resizable Word RAM programs -/

/-- Flat instructions of a word-granular Resizable Word RAM over basis `B` and `r` registers. -/
inductive RInstr (B : Basis) (r : ℕ) where
  /-- Execute a bounds-checked data instruction (`load`/`store` require `regs a < frontier`). -/
  | op (o : Op B r)
  /-- Jump unconditionally to instruction `t`. -/
  | jump (t : ℕ)
  /-- Jump to `t` if `c` holds, otherwise advance `pc` by `1`. -/
  | branch (c : Cond r) (t : ℕ)
  /-- Halt with the contents of register `i` as output. -/
  | halt (i : Fin r)
  /-- Sample uniformly from `[0, regs src]` into `dst`. -/
  | rand (dst src : Fin r)
  /-- Grow `[0, frontier)` by `regs kReg` words, storing the old `frontier` in `dst`. -/
  | grow (dst kReg : Fin r)
  /-- Shrink `[0, frontier)` by `regs kReg ≤ frontier` words. -/
  | shrink (kReg : Fin r)
  deriving DecidableEq

/-- A flat Resizable Word RAM program is a list of `RInstr B r` indexed by the program counter. -/
abbrev RProgram (B : Basis) (r : ℕ) := List (RInstr B r)

/-- Machine state of a flat Resizable Word RAM program: program counter and `RData r`. -/
@[ext]
structure RState (r : ℕ) where
  /-- Program counter. -/
  pc : ℕ
  /-- Registers, memory, and active word frontier. -/
  data : RData r

/-- Absorbing configuration for clocked execution of a flat Resizable Word RAM program. -/
inductive RCfg (r : ℕ) where
  /-- Active execution at state `s`. -/
  | running (s : RState r)
  /-- Halted with scalar output `v` and final resizable machine data `data`. -/
  | halted (v : ℕ) (data : RData r)
  /-- Faulted on an out-of-bounds memory access, overflow, invalid shrink, or invalid `pc`. -/
  | faulted

/-- `p` contains the subprogram `q` starting at instruction index `base`. -/
def RProgram.Contains (p : RProgram B r) (base : ℕ) (q : RProgram B r) : Prop :=
  ∃ pre post, p = pre ++ q ++ post ∧ pre.length = base

namespace RProgram.Contains

variable {p q q₁ q₂ : RProgram B r} {base : ℕ}

theorem self (p : RProgram B r) : p.Contains 0 p := ⟨[], [], by simp, rfl⟩
theorem append_left (h : p.Contains base (q₁ ++ q₂)) : p.Contains base q₁ :=
  let ⟨pre, post, hp, hl⟩ := h; ⟨pre, q₂ ++ post, by simp [hp], hl⟩
theorem append_right (h : p.Contains base (q₁ ++ q₂)) : p.Contains (base + q₁.length) q₂ :=
  let ⟨pre, post, hp, hl⟩ := h; ⟨pre ++ q₁, post, by simp [hp], by simp [hl]⟩
theorem cons_tail {i : RInstr B r} (h : p.Contains base (i :: q)) : p.Contains (base + 1) q :=
  append_right (q₁ := [i]) h
theorem getElem? (h : p.Contains base q) {k : ℕ} (hk : k < q.length) :
    p[base + k]? = q[k]? := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk]
theorem head {i : RInstr B r} (h : p.Contains base (i :: q)) : p[base]? = some i := by
  simpa using h.getElem? (k := 0) (by simp)

end RProgram.Contains

/-- Whether a flat resizable instruction inspects the ambient word width `w`. -/
def RInstr.ReadsWidth : RInstr B r → Prop
  | .op o => o.ReadsWidth | _ => False

/-- Map a basis simulation across a flat resizable instruction. -/
def RInstr.mapSimulates (φ : B.Simulates B') : RInstr B r → RInstr B' r
  | .op o => .op (o.mapSimulates φ) | .jump t => .jump t | .branch c t => .branch c t
  | .halt i => .halt i | .rand dst src => .rand dst src
  | .grow dst kReg => .grow dst kReg | .shrink kReg => .shrink kReg

/-- Structured programs of a Resizable Word RAM: bounds-checked data instructions, sequencing,
conditionals, while loops, uniform random sampling (`rand`), demonic word-granular `grow`, and
word-granular `shrink`. -/
inductive RCode (B : Basis) (r : ℕ) where
  /-- Bounds-checked data instruction. -/
  | op (o : Op B r)
  /-- Sequential composition. -/
  | seq (c₁ c₂ : RCode B r)
  /-- Conditional branch on register comparison `c`. -/
  | branch (c : Cond r) (pos neg : RCode B r)
  /-- While loop on register comparison `c`. -/
  | loop (c : Cond r) (body : RCode B r)
  /-- Uniform random sample from `[0, regs src]` into `dst`. -/
  | rand (dst src : Fin r)
  /-- Grow `[0, frontier)` by `regs kReg` words, storing the old `frontier` in `dst`. -/
  | grow (dst kReg : Fin r)
  /-- Shrink `[0, frontier)` by `regs kReg ≤ frontier` words. -/
  | shrink (kReg : Fin r)
  deriving DecidableEq

namespace RCode

/-- Embed a standard structured `WordRAM.Code B r` into `RCode B r`. -/
def ofCode : Code B r → RCode B r
  | .op o => .op o | .seq c₁ c₂ => .seq (ofCode c₁) (ofCode c₂)
  | .branch c pos neg => .branch c (ofCode pos) (ofCode neg)
  | .loop c body => .loop c (ofCode body) | .rand dst src => .rand dst src

/-- Compiled flat instruction count of a structured `RCode B r`. -/
@[simp] def size : RCode B r → ℕ
  | .seq c₁ c₂ => c₁.size + c₂.size | .branch _ pos neg => neg.size + pos.size + 2
  | .loop _ body => body.size + 3 | .op _ | .rand _ _ | .grow _ _ | .shrink _ => 1

/-- Assemble a structured `RCode B r` at instruction index `pc`. -/
def assemble : RCode B r → ℕ → RProgram B r
  | .op o, _ => [.op o]
  | .seq c₁ c₂, pc => c₁.assemble pc ++ c₂.assemble (pc + c₁.size)
  | .branch c pos neg, pc =>
    .branch c (pc + neg.size + 2) :: neg.assemble (pc + 1) ++
      .jump (pc + neg.size + pos.size + 2) :: pos.assemble (pc + neg.size + 2)
  | .loop c body, pc =>
    .branch c (pc + 2) :: .jump (pc + body.size + 3) :: body.assemble (pc + 2) ++ [.jump pc]
  | .rand dst src, _ => [.rand dst src]
  | .grow dst kReg, _ => [.grow dst kReg]
  | .shrink kReg, _ => [.shrink kReg]

/-- Assembling `c : RCode B r` at any base index produces `c.size` flat instructions. -/
@[simp] theorem length_assemble (c : RCode B r) (pc : ℕ) : (c.assemble pc).length = c.size := by
  induction c generalizing pc with
  | branch _ _ _ ihp ihn =>
    simp only [assemble, List.length_append, List.length_cons, ihp, ihn, size]; omega
  | _ => simp_all [assemble]

/-- Complete flat Resizable Word RAM program: `c.assemble 0` followed by `halt out`. -/
def program (c : RCode B r) (out : Fin r) : RProgram B r := c.assemble 0 ++ [.halt out]

/-- Whether a structured `RCode B r` inspects the ambient word width `w`. -/
def ReadsWidth : RCode B r → Prop
  | .op o => o.ReadsWidth | .seq c₁ c₂ => c₁.ReadsWidth ∨ c₂.ReadsWidth
  | .branch _ pos neg => pos.ReadsWidth ∨ neg.ReadsWidth | .loop _ body => body.ReadsWidth
  | .rand _ _ | .grow _ _ | .shrink _ => False

@[simp] theorem readsWidth_ofCode (c : Code B r) : (ofCode c).ReadsWidth ↔ c.ReadsWidth := by
  induction c <;> simp_all [ofCode, ReadsWidth, Code.ReadsWidth]

/-- Map a basis simulation across `RCode B r`. -/
def mapSimulates (φ : B.Simulates B') : RCode B r → RCode B' r
  | .op o => .op (o.mapSimulates φ) | .seq c₁ c₂ => .seq (c₁.mapSimulates φ) (c₂.mapSimulates φ)
  | .branch c pos neg => .branch c (pos.mapSimulates φ) (neg.mapSimulates φ)
  | .loop c body => .loop c (body.mapSimulates φ) | .rand dst src => .rand dst src
  | .grow dst kReg => .grow dst kReg | .shrink kReg => .shrink kReg

@[simp] theorem size_mapSimulates (φ : B.Simulates B') (c : RCode B r) :
    (c.mapSimulates φ).size = c.size := by induction c <;> simp_all [mapSimulates, size]

theorem mapSimulates_ofCode (φ : B.Simulates B') (c : Code B r) :
    (ofCode c).mapSimulates φ = ofCode (c.mapSimulates φ) := by
  induction c <;> simp_all [ofCode, mapSimulates, Code.mapSimulates]

theorem readsWidth_of_mapSimulates (φ : B.Simulates B') {c : RCode B r}
    (h : (c.mapSimulates φ).ReadsWidth) : c.ReadsWidth := by
  induction c with
  | op o => exact Op.readsWidth_of_mapSimulates φ h
  | seq _ _ ih₁ ih₂ => exact h.imp ih₁ ih₂
  | branch _ _ _ ihp ihn => exact h.imp ihp ihn
  | loop _ _ ih => exact ih h
  | rand _ _ | grow _ _ | shrink _ => exact h

end RCode

/-! ## Big-step demonic execution (`RDemonicExec`) -/

/-- Big-step demonic execution judgment `RDemonicExec w L_peak c x T P`: at word width `w`,
starting from `x : RData r`, the structured program `c : RCode B r` executes without faulting in at
most `T` instructions, keeps the active hardware word frontier `≤ L_peak` at every step, and
establishes postcondition `P y` on the resulting state `y : RData r` for **every** demonic choice
of newly grown memory words (`DemonicGrow`) on `grow` instructions. -/
inductive RDemonicExec (w L_peak : ℕ) : RCode B r → RData r → ℕ → (RData r → Prop) → Prop where
  | op {o : Op B r} {x y : RData r} {P : RData r → Prop} :
      x.frontier ≤ L_peak → evalResizable w o x = some y → P y → RDemonicExec w L_peak (.op o) x 1 P
  | grow {dst kReg : Fin r} {x : RData r} {P : RData r → Prop} :
      x.frontier + x.regs kReg ≤ L_peak → Fits w (x.frontier + x.regs kReg) →
      (∀ mem', DemonicGrow w x.frontier (x.regs kReg) x.mem mem' →
        P ⟨Function.update x.regs dst x.frontier, mem', x.frontier + x.regs kReg⟩) →
      RDemonicExec w L_peak (.grow dst kReg) x 1 P
  | shrink {kReg : Fin r} {x : RData r} {P : RData r → Prop} :
      x.frontier ≤ L_peak → x.regs kReg ≤ x.frontier →
      P ⟨x.regs, clear x.mem (x.frontier - x.regs kReg) (x.regs kReg), x.frontier - x.regs kReg⟩ →
      RDemonicExec w L_peak (.shrink kReg) x 1 P
  | rand {dst src : Fin r} {x : RData r} {P : RData r → Prop} :
      x.frontier ≤ L_peak → Fits w (x.regs src) → (∀ v ≤ x.regs src, P (x.set dst v)) →
      RDemonicExec w L_peak (.rand dst src) x 1 P
  | seq {c₁ c₂ : RCode B r} {x : RData r} {T₁ T₂ : ℕ} {Q P : RData r → Prop} :
      RDemonicExec w L_peak c₁ x T₁ Q → (∀ y, Q y → RDemonicExec w L_peak c₂ y T₂ P) →
      RDemonicExec w L_peak (.seq c₁ c₂) x (T₁ + T₂) P
  | branch_pos {c : Cond r} {pos neg : RCode B r} {x : RData r} {T : ℕ} {P : RData r → Prop} :
      c.Holds x.toData → RDemonicExec w L_peak pos x T P →
      RDemonicExec w L_peak (.branch c pos neg) x (T + 1) P
  | branch_neg {c : Cond r} {pos neg : RCode B r} {x : RData r} {T : ℕ} {P : RData r → Prop} :
      ¬c.Holds x.toData → RDemonicExec w L_peak neg x T P →
      RDemonicExec w L_peak (.branch c pos neg) x (T + 2) P
  | loop_exit {c : Cond r} {body : RCode B r} {x : RData r} {P : RData r → Prop} :
      x.frontier ≤ L_peak → ¬c.Holds x.toData → P x → RDemonicExec w L_peak (.loop c body) x 2 P
  | loop_iter {c : Cond r} {body : RCode B r} {x : RData r} {T₁ T₂ : ℕ} {Q P : RData r → Prop} :
      c.Holds x.toData → RDemonicExec w L_peak body x T₁ Q →
      (∀ y, Q y → RDemonicExec w L_peak (.loop c body) y T₂ P) →
      RDemonicExec w L_peak (.loop c body) x (T₁ + 2 + T₂) P
  | mono {c : RCode B r} {x : RData r} {T₁ T₂ : ℕ} {P Q : RData r → Prop} :
      RDemonicExec w L_peak c x T₁ P → T₁ ≤ T₂ → (∀ y, P y → Q y) → RDemonicExec w L_peak c x T₂ Q

namespace RDemonicExec

variable {w L_peak : ℕ} {x : RData r}

/-- Every `RDemonicExec` requires the entry hardware frontier to satisfy `x.frontier ≤ L_peak`. -/
theorem frontier_le {c : RCode B r} {T : ℕ} {P : RData r → Prop}
    (h : RDemonicExec w L_peak c x T P) : x.frontier ≤ L_peak := by
  induction h with
  | op hL _ _ | shrink hL _ _ | rand hL _ _ | loop_exit hL _ _ => exact hL
  | grow hL _ _ => omega
  | seq _ _ ih₁ _ => exact ih₁
  | branch_pos _ _ ih | branch_neg _ _ ih => exact ih
  | loop_iter _ _ _ ihb _ => exact ihb
  | mono _ _ _ ih => exact ih

/-- Enlarge the peak hardware frontier bound `L₁ ≤ L₂`. -/
theorem mono_peak {L₁ L₂ : ℕ} {c : RCode B r} {T : ℕ} {P : RData r → Prop}
    (hL : L₁ ≤ L₂) (h : RDemonicExec w L₁ c x T P) : RDemonicExec w L₂ c x T P := by
  induction h with
  | op hf he hp => exact .op (hf.trans hL) he hp
  | grow hf hfit hp => exact .grow (hf.trans hL) hfit hp
  | shrink hf hk hp => exact .shrink (hf.trans hL) hk hp
  | rand hf hfit hp => exact .rand (hf.trans hL) hfit hp
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_exit hf hc hp => exact .loop_exit (hf.trans hL) hc hp
  | loop_iter hc _ _ ihb ihl => exact .loop_iter hc ihb ihl
  | mono _ hT hPQ ih => exact .mono ih hT hPQ

/-- Deterministic sequential composition specialized to equality postcondition `· = y`. -/
theorem seq_eq {c₁ c₂ : RCode B r} {y : RData r} {T₁ T₂ : ℕ} {P : RData r → Prop}
    (h₁ : RDemonicExec w L_peak c₁ x T₁ (· = y))
    (h₂ : RDemonicExec w L_peak c₂ y T₂ P) :
    RDemonicExec w L_peak (.seq c₁ c₂) x (T₁ + T₂) P :=
  h₁.seq fun _ hy => hy ▸ h₂

theorem const {d : Fin r} {v : ℕ} (hL : x.frontier ≤ L_peak) (hv : Fits w v) :
    RDemonicExec (B := B) w L_peak (.op (.const d v)) x 1 (· = x.set d v) :=
  .op hL (RData.put_of_fits hv) rfl

theorem copy {d s : Fin r} (hL : x.frontier ≤ L_peak) :
    RDemonicExec (B := B) w L_peak (.op (.copy d s)) x 1 (· = x.set d (x.regs s)) :=
  .op hL rfl rfl

theorem load {d a : Fin r} (hL : x.frontier ≤ L_peak) (ha : x.regs a < x.frontier) :
    RDemonicExec (B := B) w L_peak (.op (.load d a)) x 1 (· = x.set d (x.mem (x.regs a))) :=
  .op hL (by simp [evalResizable, ha]) rfl

theorem store {a s : Fin r} (hL : x.frontier ≤ L_peak) (ha : x.regs a < x.frontier) :
    RDemonicExec (B := B) w L_peak (.op (.store a s)) x 1 (· = x.write (x.regs a) (x.regs s)) :=
  .op hL (by simp [evalResizable, ha]) rfl

theorem exactBin {f : BinOp} {d i j : Fin r} (hL : x.frontier ≤ L_peak) {v : ℕ}
    (hev : f.evalExact (x.regs i) (x.regs j) = some v) (hfit : Fits w v) :
    RDemonicExec (B := .exact) w L_peak (.op (.exactBin f d i j)) x 1 (· = x.set d v) := by
  refine .op hL ?_ rfl
  change (do let val ← f.evalExact (x.regs i) (x.regs j); x.put w d val) = some (x.set d v)
  rw [hev]
  exact RData.put_of_fits hfit

/-- Indexed deterministic loop rule for `RDemonicExec`. -/
theorem loop {cond : Cond r} {body : RCode B r} (xs : ℕ → RData r) (k T : ℕ)
    (hL_end : (xs k).frontier ≤ L_peak)
    (hc : ∀ i < k, cond.Holds (xs i).toData) (hk : ¬cond.Holds (xs k).toData)
    (hbody : ∀ i < k, RDemonicExec w L_peak body (xs i) T (· = xs (i + 1))) :
    RDemonicExec w L_peak (.loop cond body) (xs 0) (k * (T + 2) + 2) (· = xs k) := by
  induction k generalizing xs with
  | zero =>
    rw [Nat.zero_mul, Nat.zero_add]
    exact .loop_exit hL_end hk rfl
  | succ k ih =>
    have hstep := RDemonicExec.loop_iter (hc 0 (by omega)) (hbody 0 (by omega)) fun y hy => by
      subst hy
      exact ih (fun i => xs (i + 1)) hL_end (fun i hi => hc (i + 1) (by omega)) hk
        (fun i hi => hbody (i + 1) (by omega))
    exact hstep.mono (by rw [Nat.succ_mul]; omega) fun _ h => h

/-- Transport `RDemonicExec` along any defined-evaluation basis simulation `φ : B.Simulates B'`. -/
theorem mapSimulates (φ : B.Simulates B') {c : RCode B r} {T : ℕ} {P : RData r → Prop}
    (h : RDemonicExec w L_peak c x T P) : RDemonicExec w L_peak (c.mapSimulates φ) x T P := by
  induction h with
  | op hL he hp => exact .op hL (evalResizable_mapSimulates φ he) hp
  | grow hL hfit hp => exact .grow hL hfit hp
  | shrink hL hk hp => exact .shrink hL hk hp
  | rand hL hfit hp => exact .rand hL hfit hp
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_exit hL hc hp => exact .loop_exit hL hc hp
  | loop_iter hc _ _ ihb ihl => exact .loop_iter hc ihb ihl
  | mono _ hT hPQ ih => exact .mono ih hT hPQ

/-- Lift any frontier-bounded structured execution `ExecBoundedExact w L c x.toData y n` with
`L ≤ x.frontier ≤ L_peak` directly to `RDemonicExec` on `RCode.ofCode c`. -/
theorem of_execBoundedExact {L n : ℕ} {c : Code B r} {y : Data r}
    (hL_peak : x.frontier ≤ L_peak) (hL : L ≤ x.frontier)
    (h : ExecBoundedExact w L c x.toData y n) :
    RDemonicExec w L_peak (RCode.ofCode c) x n (· = ⟨y.regs, y.mem, x.frontier⟩) := by
  generalize hx0 : x.toData = x₀ at h
  induction h generalizing x with
  | op hb he => subst hx0; exact .op hL_peak (evalResizable_of_boundedAccess hb hL he) rfl
  | seq _ _ ih₁ ih₂ => subst hx0; exact (ih₁ hL_peak hL rfl).seq_eq (ih₂ hL_peak hL rfl)
  | branch_pos hc _ ih => subst hx0; exact .branch_pos hc (ih hL_peak hL rfl)
  | branch_neg hc _ ih => subst hx0; exact .branch_neg hc (ih hL_peak hL rfl)
  | loop_exit hc => subst hx0; exact .loop_exit hL_peak hc (by cases x; rfl)
  | @loop_iter _ _ _ y _ m n hc _ _ ihb ihl =>
    subst hx0
    refine (RDemonicExec.loop_iter (T₂ := n) hc (ihb hL_peak hL rfl) ?_).mono
      (by omega) fun _ h => h
    rintro _ rfl
    exact ihl (x := ⟨y.regs, y.mem, x.frontier⟩) hL_peak hL rfl

/-- **Main `ExecBounded` → `RDemonicExec` bridge (`RDemonicExec.of_execBounded`).**
Every `ExecBounded w L c x.toData y T` whose address bound `L` lies at or below `x.frontier` lifts
directly to `RDemonicExec w L_peak (RCode.ofCode c) x T` with unchanged hardware `frontier`. -/
theorem of_execBounded {L T : ℕ} {c : Code B r} {y : Data r}
    (hL_peak : x.frontier ≤ L_peak) (hL : L ≤ x.frontier)
    (h : ExecBounded w L c x.toData y T) :
    RDemonicExec w L_peak (RCode.ofCode c) x T (· = ⟨y.regs, y.mem, x.frontier⟩) := by
  obtain ⟨n, hn, hex⟩ := h
  exact (of_execBoundedExact hL_peak hL hex).mono hn fun _ hy => hy

/-- Lift any register-only `ExecWithin` execution directly to `RDemonicExec`. -/
theorem of_execWithin_regOnly {T : ℕ} {c : Code B r} {y : Data r}
    (hL_peak : x.frontier ≤ L_peak) (hc : IsRegOnlyCode c)
    (h : ExecWithin w c x.toData y T) :
    RDemonicExec w L_peak (RCode.ofCode c) x T (· = ⟨y.regs, y.mem, x.frontier⟩) :=
  of_execBounded hL_peak (Nat.zero_le _) (ExecBounded.of_execWithin_regOnly hc h)

/-- **Direct `RealizesBounded` → `RDemonicExec` bridge (`RDemonicExec.of_realizesBounded`).**
Any `Memory.Prog` client certified by `RealizesBounded` whose post-state frontier stays
`≤ x.frontier` (for example, any non-allocating segment using only `Memory.read`, `Memory.write`,
arithmetic glue, conditionals, `iterate`, and `boundedWhile` when `x.regs frontier ≤ x.frontier`)
executes directly on the Resizable Word RAM via `RCode.ofCode`. -/
theorem of_realizesBounded {k l n C : ℕ} {δ α : Type}
    {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}
    {emit : ∀ {r : ℕ}, Fin r → (Fin k → Fin r) → (Fin (l + n + 1) → Fin r) → Code B r}
    (hspec : Realization.Realizes.SpecBounded B p input output safe work n C emit)
    (frontier : Fin r) (src : Fin k → Fin r) (tmp : Fin (l + n + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier)
    (d : δ) (hx : x.Bounded w) (hL_peak : x.frontier ≤ L_peak)
    (hin : x.regs ∘ src = input d)
    (hsafe : safe w d (Realization.memoryState frontier x.toData))
    (hv : (Memory.spec w).ValidHistory (Realization.memoryState frontier x.toData)
      ((Memory.spec w).clientHistory (Realization.memoryState frontier x.toData) (p d)))
    (hnoalloc : ((Memory.spec w).clientState
      (Realization.memoryState frontier x.toData) (p d)).frontier ≤ x.frontier) :
    ∃ y : Data r,
      RDemonicExec w L_peak (RCode.ofCode (emit frontier src tmp)) x
        (C * (Realization.memoryCost (p d) (Realization.memoryState frontier x.toData) +
          work d (Realization.memoryState frontier x.toData) + 1))
        (· = ⟨y.regs, y.mem, x.frontier⟩) ∧
      Realization.memoryState frontier y =
        (Memory.spec w).clientState (Realization.memoryState frontier x.toData) (p d) ∧
      (∀ i : Fin l, y.regs (tmp (Fin.castAdd (n + 1) i)) =
        output ((Memory.spec w).clientResult (Realization.memoryState frontier x.toData) (p d)) i) ∧
      ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  obtain ⟨_, hrun⟩ := hspec frontier src tmp hi hd hf hs
  obtain ⟨y, hy, hm, hout, hframe⟩ := hrun w d x.toData hx.1 hin hsafe hv
  have hy_fr : y.regs frontier ≤ x.frontier := by
    have hm_fr := congrArg Memory.State.frontier hm
    change y.regs frontier =
      ((Memory.spec w).clientState (Realization.memoryState frontier x.toData) (p d)).frontier
      at hm_fr
    rw [hm_fr]
    exact hnoalloc
  exact ⟨y, of_execBounded hL_peak hy_fr hy, hm, hout, hframe⟩

end RDemonicExec

/-! ## Basis-generic zeroed growth (`growZeroCode`) -/

/-- Exact-basis zero-fill loop clearing `[regs cur, regs stop)` in `4 * (stop - cur) + 2`
instructions. -/
def zeroFillExact (cur stop zero one : Fin r) : Code .exact r :=
  .loop (.lt cur stop) (.seq (.op (.store cur zero)) (.op (.exactBin .add cur cur one)))

/-- Frontier-bounded execution of `zeroFillExact` below `x.regs stop`. -/
theorem zeroFillExact_execBounded {w : ℕ} {cur stop zero one : Fin r} {x : Data r}
    (hcs : cur ≠ stop) (hcz : cur ≠ zero) (hco : cur ≠ one)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hle : x.regs cur ≤ x.regs stop) (hw : Fits w (x.regs stop)) :
    ExecBounded w (x.regs stop) (zeroFillExact cur stop zero one) x
      ⟨Function.update x.regs cur (x.regs stop),
        clear x.mem (x.regs cur) (x.regs stop - x.regs cur)⟩
      (4 * (x.regs stop - x.regs cur) + 2) := by
  set b := x.regs cur with hb
  set k := x.regs stop - b
  let xs : ℕ → Data r := fun i =>
    ⟨Function.update x.regs cur (b + i), clear x.mem b i⟩
  have hstop (i : ℕ) : (xs i).regs stop = x.regs stop := by
    simp [xs, Function.update_of_ne hcs.symm]
  have hcur (i : ℕ) : (xs i).regs cur = b + i := by simp [xs]
  have hbody (i : ℕ) (hi : i < k) :
      ExecBounded w (x.regs stop)
        (.seq (.op (.store cur zero)) (.op (.exactBin .add cur cur one)))
        (xs i) (xs (i + 1)) 2 := by
    have hz : (xs i).regs zero = 0 := by simp [xs, Function.update_of_ne hcz.symm, h0]
    have ho : (xs i).regs one = 1 := by simp [xs, Function.update_of_ne hco.symm, h1]
    have hlt_stop : (xs i).regs cur < x.regs stop := by rw [hcur]; omega
    let x_st := (xs i).write ((xs i).regs cur) ((xs i).regs zero)
    have hfit_next : Fits w (b + i + 1) := hw.of_le (by omega)
    have he_add : ExecBounded w (x.regs stop) (.op (.exactBin .add cur cur one)) x_st
        (x_st.set cur (b + i + 1)) 1 := by
      have hxst_cur : x_st.regs cur = b + i := hcur i
      have hxst_one : x_st.regs one = 1 := ho
      refine ExecBounded.op trivial ?_
      rw [Op.eval_exactBin, hxst_cur, hxst_one]
      exact Data.put_of_fits hfit_next
    have htarget : x_st.set cur (b + i + 1) = xs (i + 1) := by
      ext r'
      · simp only [x_st, Data.set, Data.write, xs]
        by_cases hr : r' = cur
        · subst hr; simp [Nat.add_assoc]
        · simp [Function.update_of_ne hr]
      · simp only [x_st, Data.set, Data.write, hcur, hz]
        simp [xs, clear_succ]
    rw [htarget] at he_add
    exact (ExecBounded.store hlt_stop).seq he_add
  have hloop := ExecBounded.loop (cond := .lt cur stop) xs k 2
    (fun i hi => by simp only [Cond.Holds, hcur, hstop]; omega)
    (by simp only [Cond.Holds, hcur, hstop]; omega) hbody
  have hbk : b + k = x.regs stop := by omega
  have hx0 : xs 0 = x := by ext r' <;> simp [xs, hb]
  have hxk : xs k = ⟨Function.update x.regs cur (x.regs stop), clear x.mem b k⟩ := by
    simp only [xs, hbk]
  rw [hx0, hxk] at hloop
  exact hloop.mono (by omega)

/-- Exact-basis (`Basis.exact`) subroutine that executes demonic `grow result count` and then
zeroes `[frontier, frontier + count)` via `zeroFillExact` in `4 * count + 7` instructions.
Use `.mapSimulates Basis.Simulates.exactStandard` to obtain the `Basis.standard` program. -/
def growZeroCode (count result cur stop zero one : Fin r) : RCode .exact r :=
  .seq (.op (.const zero 0)) <|
  .seq (.op (.const one 1)) <|
  .seq (.grow result count) <|
  .seq (.op (.copy cur result)) <|
  .seq (.op (.exactBin .add stop result count)) <|
       (RCode.ofCode (zeroFillExact cur stop zero one))

theorem growZeroCode_not_readsWidth (count result cur stop zero one : Fin r) :
    ¬(growZeroCode count result cur stop zero one).ReadsWidth := by
  simp [growZeroCode, zeroFillExact, RCode.ReadsWidth, Code.ReadsWidth, Op.ReadsWidth, Op.exactBin]

/-- **Demonic-safe zeroed growth (`growZeroCode_exec`).**
Starting from any `x : RData r` satisfying `x.Bounded w`, `growZeroCode` executes in `4 * k + 7`
instructions with peak frontier `≤ L_peak` under **demonic** `DemonicGrow`, erases every
demonically initialized word in `[x.frontier, x.frontier + k)`, and deterministically produces the
canonical zero-extended memory `x.mem` with new frontier `x.frontier + k`. -/
theorem growZeroCode_exec {w L_peak : ℕ} {count result cur stop zero one : Fin r} {x : RData r}
    (hx : x.Bounded w)
    (hd : [count, result, cur, stop, zero, one].Nodup)
    (h1 : Fits w 1)
    (hL_peak : x.frontier + x.regs count ≤ L_peak)
    (hw : Fits w (x.frontier + x.regs count)) :
    let f := x.frontier
    let k := x.regs count
    RDemonicExec w L_peak (growZeroCode count result cur stop zero one) x (4 * k + 7)
      (· = ⟨Function.update (Function.update (Function.update (Function.update (Function.update
          x.regs zero 0) one 1) result f) cur f) stop (f + k) |> fun regs =>
            Function.update regs cur (f + k),
        x.mem, f + k⟩) := by
  intro f k
  have hL0 : x.frontier ≤ L_peak := by omega
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hcr, hcc, hcs, hcz, hco⟩, ⟨hrc, hrs, hrz, hro⟩, ⟨hcs', hcz', hco'⟩,
    ⟨hsz, hso⟩, hzo, -⟩ := hd
  set x₁ := x.set zero 0
  set x₂ := x₁.set one 1
  have e₁ : RDemonicExec (B := .exact) w L_peak (.op (.const zero 0)) x 1 (· = x₁) :=
    RDemonicExec.const hL0 (fits_zero w)
  have e₂ : RDemonicExec (B := .exact) w L_peak (.op (.const one 1)) x₁ 1 (· = x₂) :=
    RDemonicExec.const hL0 h1
  have hx₂_k : x₂.regs count = k := by
    simp [x₂, x₁, Function.update_of_ne hco, Function.update_of_ne hcz, k]
  have e_grow : RDemonicExec (B := .exact) w L_peak (.grow result count) x₂ 1 fun x₃ =>
      ∃ mem', DemonicGrow w f k x.mem mem' ∧
        x₃ = ⟨Function.update x₂.regs result f, mem', f + k⟩ := by
    refine RDemonicExec.grow (by rw [hx₂_k]; exact hL_peak) (by rw [hx₂_k]; exact hw)
      fun mem' hdem => ?_
    rw [hx₂_k] at hdem ⊢
    exact ⟨mem', hdem, rfl⟩
  refine (e₁.seq_eq (e₂.seq_eq (e_grow.seq (T₂ := 4 * k + 4) fun x₃ hx₃ => ?_))).mono
    (by omega) fun _ h => h
  obtain ⟨mem', hdem, rfl⟩ := hx₃
  set x₃ : RData r := ⟨Function.update x₂.regs result f, mem', f + k⟩
  set x₄ := x₃.set cur (x₃.regs result)
  set x₅ := x₄.set stop (f + k)
  have hx₃_res : x₃.regs result = f := by simp [x₃]
  have e₄ : RDemonicExec (B := .exact) w L_peak (.op (.copy cur result)) x₃ 1 (· = x₄) :=
    RDemonicExec.copy hL_peak
  have hx₄_res : x₄.regs result = f := by
    simp [x₄, Function.update_of_ne hrc, hx₃_res]
  have hx₄_cnt : x₄.regs count = k := by
    simp [x₄, x₃, Function.update_of_ne hcc, Function.update_of_ne hcr, hx₂_k]
  have e₅ : RDemonicExec (B := .exact) w L_peak (.op (.exactBin .add stop result count)) x₄ 1
      (· = x₅) :=
    RDemonicExec.exactBin hL_peak (by simp [BinOp.evalExact, hx₄_res, hx₄_cnt]) hw
  have hx₅_cur : x₅.regs cur = f := by
    simp [x₅, x₄, Function.update_of_ne hcs', hx₃_res]
  have hx₅_stop : x₅.regs stop = f + k := by simp [x₅]
  have hx₅_zero : x₅.regs zero = 0 := by
    simp [x₅, x₄, x₃, x₂, x₁, Function.update_of_ne (Ne.symm hsz),
      Function.update_of_ne (Ne.symm hcz'), Function.update_of_ne (Ne.symm hrz), hzo]
  have hx₅_one : x₅.regs one = 1 := by
    simp [x₅, x₄, x₃, x₂, Function.update_of_ne (Ne.symm hso),
      Function.update_of_ne (Ne.symm hco'), Function.update_of_ne (Ne.symm hro)]
  have ezf_bdd := zeroFillExact_execBounded (w := w) (x := x₅.toData) hcs' hcz' hco'
    hx₅_zero hx₅_one (by rw [RData.toData_regs, hx₅_cur, hx₅_stop]; omega)
    (by rw [RData.toData_regs, hx₅_stop]; exact hw)
  have ezf := RDemonicExec.of_execBounded (x := x₅) hL_peak
    (by simp [x₅, x₄, x₃, RData.toData_regs]) ezf_bdd
  refine (e₄.seq_eq (e₅.seq_eq ezf)).mono (by rw [RData.toData_regs, hx₅_stop, hx₅_cur]; omega) ?_
  rintro _ rfl
  ext a
  · simp [x₅, x₄, x₃, x₂, x₁, RData.set]
  · simp only [RData.toData_mem, RData.toData_regs, hx₅_cur, hx₅_stop, Nat.add_sub_cancel_left]
    exact congrFun (clear_demonicGrow_eq hx hdem) a
  · rfl

end Cslib.WordRAM.Resizable

public meta section

namespace Cslib.WordRAM

open Lean Meta Elab Tactic Cslib.WordRAM.Realization in
/-- Map a `Realizes` proof-combinator constant to its `RealizesBounded` counterpart. -/
def mapRealizesConst (c : Name) : Option Name :=
  [(``Realizes.consequence, ``RealizesBounded.consequence),
   (``Realizes.consequence_valid, ``RealizesBounded.consequence_valid),
   (``Realizes.congr, ``RealizesBounded.congr), (``Realizes.reindex, ``RealizesBounded.reindex),
   (``Realizes.mono_mul, ``RealizesBounded.mono_mul), (``Realizes.pure₀, ``RealizesBounded.pure₀),
   (``Realizes.bind₀_of_run, ``RealizesBounded.bind₀_of_run),
   (``Realizes.read, ``RealizesBounded.read), (``Realizes.write, ``RealizesBounded.write),
   (``Realizes.alloc, ``RealizesBounded.alloc),
   (``Realizes.allocDirty, ``RealizesBounded.allocDirty),
   (``Realizes.branch₀, ``RealizesBounded.branch₀),
   (``Realizes.iterate₀, ``RealizesBounded.iterate₀),
   (``Realizes.while₀, ``RealizesBounded.while₀)].lookup c

open Lean Meta Elab Tactic Cslib.WordRAM.Realization in
/-- Translate the `Realizes` proof spine to `RealizesBounded` without touching client terms. -/
partial def translateRealizesProof (shadowMap : Std.HashMap FVarId FVarId) (e : Expr) :
    Expr :=
  let toBounded (t : Expr) : Expr := mkAppN (.const ``RealizesBounded []) t.getAppArgs
  match e with
  | .fvar fid => shadowMap[fid]?.map .fvar |>.getD e
  | .lam n t b bi => .lam n t (translateRealizesProof shadowMap b) bi
  | .mdata md b => .mdata md (translateRealizesProof shadowMap b)
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``id && args.size == 2 && args[0]!.isAppOfArity ``Realizes 10 then
      mkApp2 fn (toBounded args[0]!) (translateRealizesProof shadowMap args[1]!)
    else if fn.isConstOf ``Eq.mp && args.size == 4 && args[0]!.isAppOfArity ``Realizes 10 &&
        args[1]!.isAppOfArity ``Realizes 10 then
      let hEq := if args[2]!.isAppOfArity ``congrArg 6 then
        let cArgs := args[2]!.getAppArgs
        match cArgs[4]! with
        | .lam nm sTy body bi =>
          if body.isAppOfArity ``Realizes 10 then
            mkAppN args[2]!.getAppFn (cArgs.set! 4 (.lam nm sTy (toBounded body) bi))
          else args[2]!
        | _ => args[2]!
      else args[2]!
      mkApp4 fn (toBounded args[0]!) (toBounded args[1]!) hEq
        (translateRealizesProof shadowMap args[3]!)
    else match fn with
      | .const c us =>
        match mapRealizesConst c with
        | some c' => mkAppN (.const c' us) (args.map (translateRealizesProof shadowMap))
        | none => e
      | _ => e
  | _ => e

open Lean Meta Elab Tactic Cslib.WordRAM.Realization in
/-- Extend `realize` to `RealizesBounded` goals without editing
`CslibFrontier/Tactic/Realize.lean`. -/
elab_rules : tactic | `(tactic| realize) => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← whnfR (← goal.getType))
  unless target.isAppOfArity ``RealizesBounded 10 do
    throwUnsupportedSyntax
  let args := target.getAppArgs
  let mut shadowMap : Std.HashMap FVarId FVarId := {}
  let mut shadowIds : Array FVarId := #[]
  let mut rawRealizesIds : Array FVarId := #[]
  let mut gWork := goal
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars (← whnfR decl.type)
    if ty.isAppOfArity ``Realizes 10 then
      rawRealizesIds := rawRealizesIds.push decl.fvarId
    else if ty.isAppOfArity ``RealizesBounded 10 then
      let val ← mkAppM ``RealizesBounded.toRealizes #[decl.toExpr]
      gWork ← gWork.assert (decl.userName.appendAfter "_realizes") (← inferType val) val
      let (fid, gNext) ← gWork.intro1P
      gWork := gNext
      shadowMap := shadowMap.insert fid decl.fvarId
      shadowIds := shadowIds.push fid
  gWork.withContext do
    let mAux ← mkFreshExprMVar (mkAppN (mkConst ``Realizes []) args)
    let mut mGoal := mAux.mvarId!
    for rId in rawRealizesIds.reverse do
      mGoal ← try mGoal.clear rId catch _ => pure mGoal
    setGoals [mGoal]
    evalTactic (← `(tactic| realize))
    let mut cleanGoals : Array MVarId := #[]
    for rg in (← getGoals) do
      let mut cg := rg
      for sfid in shadowIds.reverse do
        cg ← try cg.clear sfid catch _ => pure cg
      cleanGoals := cleanGoals.push cg
    let prfBounded := translateRealizesProof shadowMap (← instantiateMVars mAux)
    check prfBounded
    unless ← isDefEq (← inferType prfBounded) target do
      throwError "realize: translated proof does not match RealizesBounded goal"
    gWork.assign prfBounded
    setGoals cleanGoals.toList

end Cslib.WordRAM
