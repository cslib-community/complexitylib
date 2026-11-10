/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.BoundedExec
public import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic

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
2. **Single-word resizing primitives (`RInstr.grow`, `RInstr.shrink`)**: `grow dst` extends
   `[0, frontier)` by `1` word to `[0, frontier + 1)` when `Fits w (frontier + 1)`, stores old
   `frontier` in `dst`, and initializes cell `frontier` demonically (`DemonicGrow w frontier 1`,
   matching [KuszmaulLiangZhou2026], Section 5.1, PDF pp. 16–17 / printed pp. 15–16 and
   Footnote 10, PDF p. 18 / printed p. 17); `shrink` contracts `[0, frontier)` by `1` word when
   `1 ≤ frontier` and zeroes cell `frontier - 1`. Multi-word resizing (`growDirtyCode`,
   `growZeroCode`, `shrinkCode`) is provided as derived `RCode` subroutines costing `Θ(k + 1)`
   instructions.
3. **Direct `realize` bridge (`RDemonicExec.of_execBounded`, `RDemonicExec.of_realizesBounded`)**:
   any `ExecBounded w L c x.toData y T` with `L ≤ x.frontier` lifts directly to `RDemonicExec`.

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
* `Cslib.WordRAM.Resizable.growDirtyCode`, `Cslib.WordRAM.Resizable.growZeroCode`,
  `Cslib.WordRAM.Resizable.shrinkCode`: derived exact-basis (`Basis.exact`) `RCode` subroutines for
  `Θ(k + 1)`-step demonic growth, zero-initialized growth, and multi-word shrinking.

## Main results

* `Cslib.WordRAM.Resizable.clear_demonicGrow_eq`: clearing `[frontier, frontier + k)` after
  `DemonicGrow` recovers canonical zero-extended memory.
* `Cslib.WordRAM.Resizable.RDemonicExec.of_execBounded`,
  `Cslib.WordRAM.Resizable.RDemonicExec.of_realizesBounded`,
  `Cslib.WordRAM.Resizable.RDemonicExec.mapSimulates`: lifting `ExecBounded`/`RealizesBounded`
  programs and transporting bases.
* `Cslib.WordRAM.Resizable.growDirtyCode_exec`, `Cslib.WordRAM.Resizable.growZeroCode_exec`,
  `Cslib.WordRAM.Resizable.shrinkCode_exec`: `Θ(k + 1)`-step execution certificates for the derived
  bulk resize subroutines.

## References

* [Hagerup1998] Torben Hagerup, *Sorting and Searching on the Word RAM*, STACS 1998.
* [RamanRao2003] Rajeev Raman and Satti Srinivasa Rao, *Succinct Dynamic Dictionaries and Trees*,
  ICALP 2003, LNCS 2719, pp. 357–368, Section 1.1.
* [LiLiangYuZhou2023Succincter] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic
  "Succincter"*, FOCS 2023, pp. 1715–1733 (`arXiv:2309.12950v1`, Section 2.1, PDF pp. 6–7 /
  printed pp. 5–6).
* [LiLiangYuZhou2024] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic
  Dictionary with Subconstant Wasted Bits per Key*, SODA 2024 (`arXiv:2310.20536v1`, Section 3.2,
  PDF pp. 9–10 / printed pp. 8–9).
* [KuszmaulLiangZhou2026] William Kuszmaul, Jingxun Liang, and Renfei Zhou, *Succinct Dynamic
  Rank/Select: Bypassing the Tree-Structure Bottleneck*, SODA 2026 (`arXiv:2510.19175v1`,
  Section 5.1, PDF pp. 16–20 / printed pp. 15–19; Theorem 5.2(6) and Footnote 10, PDF p. 18 /
  printed p. 17).
-/

@[expose] public section

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
def write (x : RData r) (a v : ℕ) : RData r := ⟨x.regs, Function.update x.mem a v, x.frontier⟩
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
@[simp] theorem write_frontier (x : RData r) (a v : ℕ) : (x.write a v).frontier = x.frontier := rfl
@[simp] theorem write_toData (x : RData r) (a v : ℕ) :
    (x.write a v).toData = x.toData.write a v := rfl
theorem put_of_fits {w : ℕ} {x : RData r} {i : Fin r} {v : ℕ} (h : Fits w v) :
    x.put w i v = some (x.set i v) := by simp [put, h]

/-- Word-boundedness and canonical frontier invariant at word width `w`: every register, memory
cell, and `frontier` fits in `w` bits, and all unallocated cells `a ≥ frontier` hold `0`. -/
def Bounded (w : ℕ) (x : RData r) : Prop :=
  x.toData.Bounded w ∧ Fits w x.frontier ∧ (∀ a, x.frontier ≤ a → x.mem a = 0)

theorem Bounded.regs_fits {w : ℕ} {x : RData r} (hx : x.Bounded w) (i : Fin r) :
    Fits w (x.regs i) := hx.1.1 i
theorem Bounded.mem_fits {w : ℕ} {x : RData r} (hx : x.Bounded w) (a : ℕ) :
    Fits w (x.mem a) := hx.1.2 a
theorem Bounded.frontier_fits {w : ℕ} {x : RData r} (hx : x.Bounded w) : Fits w x.frontier := hx.2.1
theorem Bounded.zero_above {w : ℕ} {x : RData r} (hx : x.Bounded w) {a : ℕ} (ha : x.frontier ≤ a) :
    x.mem a = 0 := hx.2.2 a ha
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
    simpa [Function.update_of_ne (by omega : b ≠ a)] using hx.2.2 b hb

end RData

/-- Demonic word-granular growth of `[0, L)` by `k` words at word width `w`
([KuszmaulLiangZhou2026], Section 5.1): cells `a < L` retain their values, cells `a ∈ [L, L + k)`
receive arbitrary `w`-bit words (`Fits w (mem' a)`), and cells `a ≥ L + k` hold `0`. -/
def DemonicGrow (w L k : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  (∀ a < L, mem' a = mem a) ∧ (∀ a, L ≤ a → a < L + k → Fits w (mem' a)) ∧
    (∀ a, L + k ≤ a → mem' a = 0)

/-- Zero-word growth is the identity transition on any memory zeroed above `L`. -/
theorem DemonicGrow.zero (w L : ℕ) {mem : ℕ → ℕ} (hz : ∀ a, L ≤ a → mem a = 0) :
    DemonicGrow w L 0 mem mem := ⟨fun _ _ => rfl, fun _ hlo hhi => absurd hhi (by omega), hz⟩

/-- Composing a `k`-word demonic growth from `L` with a `1`-word demonic growth from `L + k`. -/
theorem DemonicGrow.trans_one {w L k : ℕ} {mem₀ mem₁ mem₂ : ℕ → ℕ}
    (h₁ : DemonicGrow w L k mem₀ mem₁) (h₂ : DemonicGrow w (L + k) 1 mem₁ mem₂) :
    DemonicGrow w L (k + 1) mem₀ mem₂ := by
  refine ⟨fun a ha => (h₂.1 a (by omega)).trans (h₁.1 a ha), fun a hlo hhi => ?_,
    fun a ha => h₂.2.2 a (by omega)⟩
  by_cases hlt : a < L + k
  · rw [h₂.1 a hlt]; exact h₁.2.1 a hlo hlt
  · exact h₂.2.1 a (by omega) (by omega)

/-- Zero-initializing `[L, L + k)` via `clear mem L k` satisfies `DemonicGrow` when zero above. -/
theorem demonicGrow_clear (w L k : ℕ) (mem : ℕ → ℕ) (hz : ∀ a, L ≤ a → mem a = 0) :
    DemonicGrow w L k mem (clear mem L k) := by
  refine ⟨fun a ha => clear_of_not_owns (by simp only [Block.Owns]; omega), fun a hlo hhi => ?_,
    fun a ha => ?_⟩
  · rw [clear_of_owns ⟨hlo, hhi⟩]; exact fits_zero w
  · rw [clear_of_not_owns (by simp only [Block.Owns]; omega)]; exact hz a (by omega)

/-- `DemonicGrow w x.frontier k` preserves `RData.Bounded w` when `Fits w (x.frontier + k)`. -/
theorem RData.Bounded.grow {w : ℕ} {x : RData r} (hx : x.Bounded w) {dst : Fin r} {k : ℕ}
    {mem' : ℕ → ℕ} (hfit : Fits w (x.frontier + k))
    (hgrow : DemonicGrow w x.frontier k x.mem mem') :
    (⟨Function.update x.regs dst x.frontier, mem', x.frontier + k⟩ : RData r).Bounded w := by
  refine ⟨⟨fun i => ?_, fun a => ?_⟩, hfit, hgrow.2.2⟩
  · dsimp only [RData.toData]
    by_cases hid : i = dst
    · subst hid; simpa using hx.frontier_fits
    · simpa [Function.update_of_ne hid] using hx.regs_fits i
  · dsimp only [RData.toData]
    by_cases hlt : a < x.frontier
    · rw [hgrow.1 a hlt]; exact hx.mem_fits a
    · by_cases hmid : a < x.frontier + k
      · exact hgrow.2.1 a (by omega) hmid
      · rw [hgrow.2.2 a (by omega)]; exact fits_zero w

/-- Shrinking by `k ≤ x.frontier` words and clearing `[frontier - k, frontier)` keeps `Bounded`. -/
theorem RData.Bounded.shrink {w : ℕ} {x : RData r} (hx : x.Bounded w) {k : ℕ}
    (hk : k ≤ x.frontier) :
    (⟨x.regs, clear x.mem (x.frontier - k) k, x.frontier - k⟩ : RData r).Bounded w := by
  refine ⟨⟨hx.1.1, fun a => ?_⟩, hx.2.1.of_le (Nat.sub_le _ _), fun a ha => ?_⟩
  · dsimp only [RData.toData]
    by_cases hown : (Block.mk (x.frontier - k) k).Owns a
    · rw [clear_of_owns hown]; exact fits_zero w
    · rw [clear_of_not_owns hown]; exact hx.mem_fits a
  · dsimp only at ha ⊢
    by_cases hlt : a < x.frontier
    · exact clear_of_owns (by simp only [Block.Owns]; omega)
    · rw [clear_of_not_owns (by simp only [Block.Owns]; omega)]; exact hx.zero_above (by omega)

/-- Clearing `[frontier, frontier + k)` after `DemonicGrow` recovers `x.mem` when `x.Bounded w`. -/
theorem clear_demonicGrow_eq {w k : ℕ} {x : RData r} {mem' : ℕ → ℕ}
    (hx : x.Bounded w) (hdem : DemonicGrow w x.frontier k x.mem mem') :
    clear mem' x.frontier k = x.mem := by
  funext a
  by_cases ha_lt : a < x.frontier
  · rw [clear_of_not_owns (by simp only [Block.Owns]; omega), hdem.1 a ha_lt]
  · by_cases ha_in : a < x.frontier + k
    · rw [clear_of_owns (by simp only [Block.Owns]; omega), hx.zero_above (by omega)]
    · rw [clear_of_not_owns (by simp only [Block.Owns]; omega),
        hdem.2.2 a (by omega), hx.zero_above (by omega)]

/-! ## Bounds-checked data instruction evaluation on `RData r` -/

/-- Evaluate a data instruction on `RData r` at word size `w`, faulting when `load`/`store` accesses
an address `x.regs a ≥ x.frontier`. -/
def evalResizable (w : ℕ) : Op B r → RData r → Option (RData r)
  | .const d v, x => x.put w d v
  | .copy d s, x => some (x.set d (x.regs s))
  | .alu f d args, x => do let value ← B.interp w f (x.regs ∘ args); x.put w d value
  | .load d a, x => if x.regs a < x.frontier then some (x.set d (x.mem (x.regs a))) else none
  | .store a s, x => if x.regs a < x.frontier then some (x.write (x.regs a) (x.regs s)) else none

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
  /-- Grow `[0, frontier)` by `1` word to `[0, frontier + 1)`, storing old `frontier` in `dst`. -/
  | grow (dst : Fin r)
  /-- Shrink `[0, frontier)` by `1` word (`1 ≤ frontier`), zeroing cell `frontier - 1`. -/
  | shrink
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
  | .grow dst => .grow dst | .shrink => .shrink

/-- Structured programs of a Resizable Word RAM: bounds-checked data instructions, sequencing,
conditionals, while loops, uniform random sampling (`rand`), single-word demonic `grow`, and
single-word `shrink`. -/
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
  /-- Grow `[0, frontier)` by `1` word to `[0, frontier + 1)`, storing old `frontier` in `dst`. -/
  | grow (dst : Fin r)
  /-- Shrink `[0, frontier)` by `1` word (`1 ≤ frontier`), zeroing cell `frontier - 1`. -/
  | shrink
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
  | .loop _ body => body.size + 3 | .op _ | .rand _ _ | .grow _ | .shrink => 1

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
  | .grow dst, _ => [.grow dst]
  | .shrink, _ => [.shrink]

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
  | .rand _ _ | .grow _ | .shrink => False

@[simp] theorem readsWidth_ofCode (c : Code B r) : (ofCode c).ReadsWidth ↔ c.ReadsWidth := by
  induction c <;> simp_all [ofCode, ReadsWidth, Code.ReadsWidth]

/-- Map a basis simulation across `RCode B r`. -/
def mapSimulates (φ : B.Simulates B') : RCode B r → RCode B' r
  | .op o => .op (o.mapSimulates φ) | .seq c₁ c₂ => .seq (c₁.mapSimulates φ) (c₂.mapSimulates φ)
  | .branch c pos neg => .branch c (pos.mapSimulates φ) (neg.mapSimulates φ)
  | .loop c body => .loop c (body.mapSimulates φ) | .rand dst src => .rand dst src
  | .grow dst => .grow dst | .shrink => .shrink

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
  | rand _ _ | grow _ | shrink => exact h

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
  | grow {dst : Fin r} {x : RData r} {P : RData r → Prop} :
      x.frontier + 1 ≤ L_peak → Fits w (x.frontier + 1) →
      (∀ mem', DemonicGrow w x.frontier 1 x.mem mem' →
        P ⟨Function.update x.regs dst x.frontier, mem', x.frontier + 1⟩) →
      RDemonicExec w L_peak (.grow dst) x 1 P
  | shrink {x : RData r} {P : RData r → Prop} :
      x.frontier ≤ L_peak → 1 ≤ x.frontier →
      P ⟨x.regs, clear x.mem (x.frontier - 1) 1, x.frontier - 1⟩ →
      RDemonicExec w L_peak .shrink x 1 P
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
    RDemonicExec (B := B) w L_peak (.op (.copy d s)) x 1 (· = x.set d (x.regs s)) := .op hL rfl rfl
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
  rw [hev]; exact RData.put_of_fits hfit

/-- Indexed deterministic loop rule for `RDemonicExec`. -/
theorem loop {cond : Cond r} {body : RCode B r} (xs : ℕ → RData r) (k T : ℕ)
    (hL_end : (xs k).frontier ≤ L_peak)
    (hc : ∀ i < k, cond.Holds (xs i).toData) (hk : ¬cond.Holds (xs k).toData)
    (hbody : ∀ i < k, RDemonicExec w L_peak body (xs i) T (· = xs (i + 1))) :
    RDemonicExec w L_peak (.loop cond body) (xs 0) (k * (T + 2) + 2) (· = xs k) := by
  induction k generalizing xs with
  | zero => rw [Nat.zero_mul, Nat.zero_add]; exact .loop_exit hL_end hk rfl
  | succ k ih =>
    refine (RDemonicExec.loop_iter (hc 0 (by omega)) (hbody 0 (by omega)) fun y hy => ?_).mono
      (by rw [Nat.succ_mul]; omega) fun _ h => h
    subst hy; exact ih (fun i => xs (i + 1)) hL_end (fun i hi => hc (i + 1) (by omega)) hk
      (fun i hi => hbody (i + 1) (by omega))

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

/-- Indexed relational loop rule for `RDemonicExec`. -/
theorem loop_rel {cond : Cond r} {body : RCode B r} (P : ℕ → RData r → Prop) (k T : ℕ)
    (hc : ∀ i < k, ∀ z, P i z → cond.Holds z.toData)
    (hk : ∀ z, P k z → z.frontier ≤ L_peak ∧ ¬cond.Holds z.toData)
    (hbody : ∀ i < k, ∀ z, P i z → RDemonicExec w L_peak body z T (P (i + 1)))
    {x₀ : RData r} (hx₀ : P 0 x₀) :
    RDemonicExec w L_peak (.loop cond body) x₀ (k * (T + 2) + 2) (P k) := by
  induction k generalizing P x₀ with
  | zero => obtain ⟨hL, hnc⟩ := hk x₀ hx₀; simpa using RDemonicExec.loop_exit hL hnc hx₀
  | succ k ih =>
    refine (RDemonicExec.loop_iter (hc 0 (by omega) x₀ hx₀) (hbody 0 (by omega) x₀ hx₀)
      fun y hy => ih (fun i => P (i + 1)) (fun i hi => hc (i + 1) (by omega)) hk
        (fun i hi => hbody (i + 1) (by omega)) hy).mono (by rw [Nat.succ_mul]; omega) fun _ h => h

end RDemonicExec

/-! ## Derived `Θ(k + 1)` bulk resize subroutines (`growDirtyCode`, `growZeroCode`, `shrinkCode`) -/

private theorem write_zero_demonicGrow_one {w L : ℕ} {mem mem' : ℕ → ℕ}
    (hz : ∀ a, L ≤ a → mem a = 0) (hg : DemonicGrow w L 1 mem mem') :
    Function.update mem' L 0 = mem := by
  funext a; by_cases ha : a = L
  · subst ha; simp [hz L le_rfl]
  · rw [Function.update_of_ne ha]; rcases lt_trichotomy a L with hlt | rfl | hgt
    · exact hg.1 a hlt
    · exact absurd rfl ha
    · rw [hg.2.2 a (by omega), hz a (by omega)]

private theorem clear_shrink_step {m : ℕ → ℕ} {f i : ℕ} (hi : i < f) :
    clear (clear m (f - i) i) (f - i - 1) 1 = clear m (f - (i + 1)) (i + 1) := by
  funext a; by_cases h1 : (Block.mk (f - i - 1) 1).Owns a
  · rw [clear_of_owns h1, clear_of_owns (by simp only [Block.Owns] at h1 ⊢; omega)]
  · rw [clear_of_not_owns h1]; by_cases h2 : (Block.mk (f - i) i).Owns a
    · rw [clear_of_owns h2, clear_of_owns (by simp only [Block.Owns] at h2 ⊢; omega)]
    · rw [clear_of_not_owns h2, clear_of_not_owns (by simp only [Block.Owns] at h1 h2 ⊢; omega)]

/-- Derived exact-basis (`Basis.exact`) subroutine looping single-word `.grow` `regs count` times in
`4 * count + 5` instructions, storing the old `frontier` in `result` when `0 < regs count`. -/
def growDirtyCode (count result cur idx zero one : Fin r) : RCode .exact r :=
  .seq (.op (.const zero 0)) <| .seq (.op (.const one 1)) <|
  .branch (.lt zero count)
    (.seq (.grow result) <| .seq (.op (.const idx 1)) <|
      .loop (.lt idx count) (.seq (.grow cur) (.op (.exactBin .add idx idx one))))
    (.op (.copy zero zero))

theorem growDirtyCode_not_readsWidth (count result cur idx zero one : Fin r) :
    ¬(growDirtyCode count result cur idx zero one).ReadsWidth := by
  simp [growDirtyCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin]

/-- **Derived `Θ(k + 1)` demonic growth (`growDirtyCode_exec`).** -/
theorem growDirtyCode_exec {w L_peak : ℕ} {count result cur idx zero one : Fin r} {x : RData r}
    (hx : x.Bounded w) (hd : [count, result, cur, idx, zero, one].Nodup) (h1 : Fits w 1)
    (hL_peak : x.frontier + x.regs count ≤ L_peak) (hw : Fits w (x.frontier + x.regs count)) :
    let f := x.frontier; let k := x.regs count
    RDemonicExec w L_peak (growDirtyCode count result cur idx zero one) x (4 * k + 5) fun y =>
      y.Bounded w ∧ DemonicGrow w f k x.mem y.mem ∧ y.frontier = f + k ∧
        y.regs result = (if k = 0 then x.regs result else f) ∧
        ∀ j, j ≠ result → j ≠ cur → j ≠ idx → j ≠ zero → j ≠ one → y.regs j = x.regs j := by
  intro f k; have hL0 : f ≤ L_peak := by omega
  have hfk : Fits w k := hx.regs_fits count
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hcr, hcc, hci, hcz, hco⟩, ⟨hrc, hri, hrz, hro⟩, ⟨hci', hcz', hco'⟩,
    ⟨hiz, hio⟩, hzo, -⟩ := hd
  refine (RDemonicExec.const hL0 (fits_zero w)).seq_eq
    ((RDemonicExec.const hL0 h1).seq_eq ?_) |>.mono (T₂ := 4 * k + 5) ?_ fun _ h => h
  swap; · omega
  set x₂ := (x.set zero 0).set one 1
  have hx₂_k : x₂.regs count = k := by
    simp [x₂, Function.update_of_ne hco, Function.update_of_ne hcz, k]
  have hx₂_z : x₂.regs zero = 0 := by simp [x₂, Function.update_of_ne hzo.symm]
  by_cases hk0 : k = 0
  · refine (RDemonicExec.branch_neg (T := 1) (by simp [Cond.Holds, hx₂_z, hx₂_k, hk0])
      (RDemonicExec.copy hL0)).mono (by omega) ?_
    rintro _ rfl
    refine ⟨((hx.set (fits_zero w)).set h1).set (fits_zero w), ?_, by simp [x₂, f, hk0],
      by simp [x₂, hk0, Function.update_of_ne hrz.symm, Function.update_of_ne hro.symm],
      fun j _ _ _ hjz hjo => by simp [x₂, RData.set, Function.update_of_ne hjz,
        Function.update_of_ne hjo]⟩
    simpa [hk0] using DemonicGrow.zero w f hx.zero_above
  · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
    refine (RDemonicExec.branch_pos (T := 4 * k + 1) (by simp [Cond.Holds, hx₂_z, hx₂_k, hpos])
      ?_).mono (by omega) fun _ h => h
    let P (i : ℕ) (z : RData r) : Prop :=
      z.Bounded w ∧ DemonicGrow w f (i + 1) x.mem z.mem ∧ z.frontier = f + (i + 1) ∧
        z.regs zero = 0 ∧ z.regs one = 1 ∧ z.regs count = k ∧ z.regs result = f ∧
        z.regs idx = i + 1 ∧
        ∀ j, j ≠ result → j ≠ cur → j ≠ idx → j ≠ zero → j ≠ one → z.regs j = x.regs j
    have eg₁ : RDemonicExec (B := .exact) w L_peak
        (.seq (.grow result) (.op (.const idx 1))) x₂ 2 (P 0) := by
      refine (RDemonicExec.grow (by dsimp [x₂]; omega) (hw.of_le (by dsimp [x₂]; omega))
        fun m₁ hm₁ => ⟨m₁, hm₁, rfl⟩).seq fun x₃ ⟨m₁, hm₁, h3⟩ => ?_
      subst h3
      refine (RDemonicExec.const (by dsimp [x₂]; omega) h1).mono le_rfl ?_
      rintro _ rfl
      refine ⟨(((hx.set (fits_zero w)).set h1).grow (hw.of_le (by omega)) hm₁).set h1, hm₁, rfl,
        by simp [x₂, RData.set, Function.update_of_ne hiz.symm, Function.update_of_ne hrz,
          Function.update_of_ne hzo.symm],
        by simp [x₂, RData.set, Function.update_of_ne hio.symm, Function.update_of_ne hro],
        by simp [RData.set, Function.update_of_ne hci.symm, Function.update_of_ne hcr.symm, hx₂_k],
        by simp [RData.set, Function.update_of_ne hri], by simp [RData.set],
        fun j hjr _ hji hjz hjo => by simp [x₂, RData.set, Function.update_of_ne hjr,
          Function.update_of_ne hji, Function.update_of_ne hjz, Function.update_of_ne hjo]⟩
    refine (eg₁.seq fun x₄ hx₄ => RDemonicExec.loop_rel P (k - 1) 2
      (fun i hi z hz => by simp only [Cond.Holds, hz.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.1]; omega)
      (fun z hz => ⟨by rw [hz.2.2.1]; omega,
        by simp only [Cond.Holds, hz.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.1]; omega⟩)
      (fun i hi z hz => ?_) hx₄).mono (by omega) fun y hy => ?_
    · obtain ⟨hzb, hzg, hzfr, hzz, hzo', hzk, hzr, hzi, hzrem⟩ := hz
      refine (RDemonicExec.grow (by rw [hzfr]; omega) (hw.of_le (by rw [hzfr]; omega))
        fun m' hm' => ⟨m', hm', rfl⟩).seq fun z₁ ⟨m', hm', h1_eq⟩ => ?_
      subst h1_eq
      have hfit_i : Fits w (i + 1 + 1) := hfk.of_le (by omega)
      refine (RDemonicExec.exactBin (v := i + 1 + 1) (by rw [hzfr]; omega)
        (by simp [BinOp.evalExact, Function.update_of_ne hci'.symm,
          Function.update_of_ne hco', hzi, hzo']) hfit_i).mono le_rfl ?_
      rintro _ rfl
      have hgm : DemonicGrow w f (i + 1 + 1) x.mem m' := hzg.trans_one (hzfr ▸ hm')
      refine ⟨(hzb.grow (hw.of_le (by rw [hzfr]; omega)) hm').set hfit_i, hgm, by omega,
        by simp [RData.set, Function.update_of_ne hiz.symm, Function.update_of_ne hcz', hzz],
        by simp [RData.set, Function.update_of_ne hio.symm, Function.update_of_ne hco', hzo'],
        by simp [RData.set, Function.update_of_ne hci.symm, Function.update_of_ne hcc.symm, hzk],
        by simp [RData.set, Function.update_of_ne hri, Function.update_of_ne hrc, hzr],
        by simp [RData.set],
        fun j hjr hjc hji hjz hjo => by simp [RData.set, Function.update_of_ne hjc,
          Function.update_of_ne hji, hzrem j hjr hjc hji hjz hjo]⟩
    · obtain ⟨hyb, hyg, hyfr, -, -, -, hyr, -, hyrem⟩ := hy
      have hk1 : k - 1 + 1 = k := by omega
      rw [hk1] at hyg hyfr
      exact ⟨hyb, hyg, hyfr, by simp [hk0, hyr], hyrem⟩

/-- Deterministic post-state of `growZeroCode`. -/
def growZeroPost (count result cur idx zero one : Fin r) (x : RData r) : RData r :=
  ⟨Function.update (Function.update (Function.update (Function.update (Function.update
      x.regs zero 0) one 1) result (if x.regs count = 0 then x.regs result else x.frontier))
      idx (x.regs count)) cur 0,
   x.mem, x.frontier + x.regs count⟩

/-- Derived exact-basis (`Basis.exact`) subroutine growing by `regs count` words via 1-word `.grow`
and immediately zeroing each newly grown word in `5 * count + 6` instructions. -/
def growZeroCode (count result cur idx zero one : Fin r) : RCode .exact r :=
  .seq (.op (.const zero 0)) <| .seq (.op (.const one 1)) <| .seq (.op (.const idx 0)) <|
  .branch (.lt zero count)
    (.seq (.grow result) <| .seq (.op (.store result zero)) <| .seq (.op (.const idx 1)) <|
     .seq (.loop (.lt idx count)
       (.seq (.grow cur) <| .seq (.op (.store cur zero)) (.op (.exactBin .add idx idx one)))) <|
          (.op (.const cur 0)))
    (.op (.const cur 0))

theorem growZeroCode_not_readsWidth (count result cur idx zero one : Fin r) :
    ¬(growZeroCode count result cur idx zero one).ReadsWidth := by
  simp [growZeroCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin]

/-- **Derived `Θ(k + 1)` zero-initialized growth (`growZeroCode_exec`).** -/
theorem growZeroCode_exec {w L_peak : ℕ} {count result cur idx zero one : Fin r} {x : RData r}
    (hx : x.Bounded w) (hd : [count, result, cur, idx, zero, one].Nodup) (h1 : Fits w 1)
    (hL_peak : x.frontier + x.regs count ≤ L_peak) (hw : Fits w (x.frontier + x.regs count)) :
    RDemonicExec w L_peak (growZeroCode count result cur idx zero one) x (5 * x.regs count + 6)
      (· = growZeroPost count result cur idx zero one x) := by
  set f := x.frontier; set k := x.regs count; have hL0 : f ≤ L_peak := by omega
  have hfk : Fits w k := hx.regs_fits count
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hcr, hcc, hci, hcz, hco⟩, ⟨hrc, hri, hrz, hro⟩, ⟨hci', hcz', hco'⟩,
    ⟨hiz, hio⟩, hzo, -⟩ := hd
  refine ((RDemonicExec.const hL0 (fits_zero w)).seq_eq <| (RDemonicExec.const hL0 h1).seq_eq <|
    (RDemonicExec.const hL0 (fits_zero w)).seq_eq ?_).mono (T₂ := 5 * k + 6) ?_ fun _ h => h
  swap; · omega
  set x₃ := ((x.set zero 0).set one 1).set idx 0
  have hx₃_k : x₃.regs count = k := by
    simp [x₃, Function.update_of_ne hci.symm, Function.update_of_ne hco,
      Function.update_of_ne hcz, k]
  have hx₃_z : x₃.regs zero = 0 := by
    simp [x₃, Function.update_of_ne hiz.symm, Function.update_of_ne hzo.symm]
  by_cases hk0 : k = 0
  · refine (RDemonicExec.branch_neg (T := 1) (by simp [Cond.Holds, hx₃_z, hx₃_k, hk0])
      (RDemonicExec.const hL0 (fits_zero w))).mono (by omega) ?_
    rintro _ rfl; ext j
    · by_cases hjc : j = cur
      · subst hjc; simp [growZeroPost]
      · by_cases hji : j = idx
        · subst hji; simp [x₃, growZeroPost, hk0, Function.update_of_ne hci']
        · by_cases hjr : j = result
          · subst hjr; simp [x₃, growZeroPost, hk0, Function.update_of_ne hrc,
              Function.update_of_ne hri, Function.update_of_ne hro, Function.update_of_ne hrz]
          · simp [x₃, growZeroPost, RData.set, Function.update_of_ne hjc, Function.update_of_ne hji,
              Function.update_of_ne hjr]
    · rfl
    · simp [x₃, growZeroPost, f, k, hk0]
  · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
    refine (RDemonicExec.branch_pos (T := 5 * k + 2) (by simp [Cond.Holds, hx₃_z, hx₃_k, hpos])
      ?_).mono (by omega) fun _ h => h
    let baseRegs := Function.update (Function.update (Function.update x.regs zero 0) one 1) result f
    let xs (i : ℕ) : RData r :=
      ⟨Function.update (if i = 0 then baseRegs else Function.update baseRegs cur (f + i))
         idx (i + 1), x.mem, f + (i + 1)⟩
    have eg₀ : RDemonicExec (B := .exact) w L_peak
        (.seq (.grow result) (.seq (.op (.store result zero)) (.op (.const idx 1)))) x₃ 3
        (· = xs 0) := by
      refine (RDemonicExec.grow (by dsimp [x₃]; omega) (hw.of_le (by dsimp [x₃]; omega))
        fun m₁ hm₁ => ⟨m₁, hm₁, rfl⟩).seq fun x₄ ⟨m₁, hm₁, h4⟩ => ?_
      subst h4
      refine ((RDemonicExec.store (by dsimp [x₃]; omega) (by simp [x₃, f])).seq_eq
        (RDemonicExec.const (by dsimp [x₃]; omega) h1)).mono le_rfl ?_
      rintro _ rfl; ext j
      · by_cases hji : j = idx
        · subst hji; simp [xs, RData.set, RData.write]
        · by_cases hjr : j = result
          · subst hjr; simp [xs, baseRegs, RData.set, RData.write, Function.update_of_ne hji]
          · simp [xs, baseRegs, x₃, RData.set, RData.write, Function.update_of_ne hji,
              Function.update_of_ne hjr]
      · simp only [xs, RData.set, RData.write, Function.update_self,
          Function.update_of_ne hrz, hx₃_z]
        exact congrFun (write_zero_demonicGrow_one hx.zero_above hm₁) j
      · rfl
    have hloop := RDemonicExec.loop (L_peak := L_peak) (cond := .lt idx count) xs (k - 1) 3
      (by simp only [xs]; omega)
      (fun i hi => by
        have hcnt : (xs i).regs count = k := by
          by_cases hi0 : i = 0 <;> simp [xs, baseRegs, hi0, Function.update_of_ne hci.symm,
            Function.update_of_ne hcc.symm, Function.update_of_ne hcr.symm,
            Function.update_of_ne hco, Function.update_of_ne hcz, k]
        simp only [Cond.Holds, RData.toData_regs, hcnt, xs, Function.update_self]; omega)
      (by
        have hcnt : (xs (k - 1)).regs count = k := by
          by_cases hi0 : k - 1 = 0 <;> simp [xs, baseRegs, hi0, Function.update_of_ne hci.symm,
            Function.update_of_ne hcc.symm, Function.update_of_ne hcr.symm,
            Function.update_of_ne hco, Function.update_of_ne hcz, k]
        simp only [Cond.Holds, RData.toData_regs, hcnt, xs, Function.update_self]; omega)
      fun i hi => by
        have hz_i : (xs i).regs zero = 0 := by
          by_cases hi0 : i = 0 <;> simp [xs, baseRegs, hi0, Function.update_of_ne hiz,
            Function.update_of_ne hcz', Function.update_of_ne hrz, Function.update_of_ne hzo.symm]
        have ho_i : (xs i).regs one = 1 := by
          by_cases hi0 : i = 0 <;> simp [xs, baseRegs, hi0, Function.update_of_ne hio,
            Function.update_of_ne hco', Function.update_of_ne hro]
        refine (RDemonicExec.grow (by simp only [xs]; omega) (hw.of_le (by simp only [xs]; omega))
          fun m' hm' => ⟨m', hm', rfl⟩).seq fun z₁ ⟨m', hm', h1_eq⟩ => ?_
        subst h1_eq
        refine ((RDemonicExec.store (by simp only [xs]; omega) (by simp [xs])).seq_eq
          (RDemonicExec.exactBin (v := i + 1 + 1) (by simp only [xs]; omega)
            (by simp [BinOp.evalExact, RData.write, Function.update_of_ne hci'.symm,
              Function.update_of_ne hco', xs, ho_i]) (hfk.of_le (by omega)))).mono le_rfl ?_
        rintro _ rfl; ext j
        · by_cases hji : j = idx
          · subst hji; simp [xs, RData.set, RData.write]
          · by_cases hjc : j = cur
            · subst hjc; simp [xs, RData.set, RData.write, Function.update_of_ne hji]
            · by_cases hi0 : i = 0 <;> simp [xs, RData.set, RData.write, hi0,
                Function.update_of_ne hji, Function.update_of_ne hjc]
        · simp only [xs, RData.set, RData.write, Function.update_self,
            Function.update_of_ne hcz', hz_i]
          exact congrFun (write_zero_demonicGrow_one (fun a ha => hx.zero_above (by omega)) hm') j
        · simp only [xs]; omega
    refine (eg₀.seq_eq (hloop.seq_eq (RDemonicExec.const (by simp only [xs]; omega)
      (fits_zero w)))).mono (by omega) ?_
    rintro _ rfl; have hk1 : k - 1 + 1 = k := by omega
    ext j
    · by_cases hjc : j = cur
      · subst hjc; simp [growZeroPost, RData.set]
      · by_cases hji : j = idx
        · subst hji; simp [xs, growZeroPost, RData.set, hk1, Function.update_of_ne hjc]
        · by_cases hj0 : k - 1 = 0 <;> simp [xs, baseRegs, growZeroPost, RData.set, hj0, hk0,
            Function.update_of_ne hjc, Function.update_of_ne hji, f, k]
    · rfl
    · simp [xs, growZeroPost, hk1, f, k]

/-- Deterministic post-state of `shrinkCode`. -/
def shrinkPost (count idx zero one : Fin r) (x : RData r) : RData r :=
  ⟨Function.update (Function.update (Function.update x.regs zero 0) one 1) idx (x.regs count),
   clear x.mem (x.frontier - x.regs count) (x.regs count), x.frontier - x.regs count⟩

/-- Derived exact-basis (`Basis.exact`) subroutine looping single-word `.shrink` `regs count` times
in `4 * count + 5` instructions (`regs count ≤ frontier`). -/
def shrinkCode (count idx zero one : Fin r) : RCode .exact r :=
  .seq (.op (.const zero 0)) <| .seq (.op (.const one 1)) <| .seq (.op (.const idx 0)) <|
  .loop (.lt idx count) (.seq .shrink (.op (.exactBin .add idx idx one)))

theorem shrinkCode_not_readsWidth (count idx zero one : Fin r) :
    ¬(shrinkCode count idx zero one).ReadsWidth := by
  simp [shrinkCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin]

/-- **Derived `Θ(k + 1)` multi-word shrink (`shrinkCode_exec`).** -/
theorem shrinkCode_exec {w L_peak : ℕ} {count idx zero one : Fin r} {x : RData r}
    (hx : x.Bounded w) (hd : [count, idx, zero, one].Nodup) (h1 : Fits w 1)
    (hL_peak : x.frontier ≤ L_peak) (hk_le : x.regs count ≤ x.frontier) :
    RDemonicExec w L_peak (shrinkCode count idx zero one) x (4 * x.regs count + 5)
      (· = shrinkPost count idx zero one x) := by
  set f := x.frontier; set k := x.regs count; have hfk : Fits w k := hx.regs_fits count
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hci, hcz, hco⟩, ⟨hiz, hio⟩, hzo, -⟩ := hd
  let baseRegs := Function.update (Function.update x.regs zero 0) one 1
  let xs (i : ℕ) : RData r :=
    ⟨Function.update baseRegs idx i, clear x.mem (f - i) i, f - i⟩
  have hloop := RDemonicExec.loop (L_peak := L_peak) (cond := .lt idx count) xs k 2
    (by simp only [xs]; omega)
    (fun i hi => by
      simp [Cond.Holds, xs, baseRegs, Function.update_of_ne hci.symm,
        Function.update_of_ne hco, Function.update_of_ne hcz, k, hi])
    (by simp [Cond.Holds, xs, baseRegs, Function.update_of_ne hci.symm,
      Function.update_of_ne hco, Function.update_of_ne hcz, k])
    fun i hi => by
      refine (RDemonicExec.shrink (by simp only [xs]; omega) (by simp only [xs]; omega) rfl).seq_eq
        ((RDemonicExec.exactBin (v := i + 1) (by dsimp only; omega)
          (by simp [BinOp.evalExact, xs, baseRegs, Function.update_of_ne hio.symm])
          (hfk.of_le (by omega))).mono le_rfl ?_)
      rintro _ rfl; ext j
      · simp [xs, RData.set]
      · exact congrFun (clear_shrink_step (by omega)) j
      · dsimp only [xs, RData.set]; omega
  refine ((RDemonicExec.const hL_peak (fits_zero w)).seq_eq <|
    (RDemonicExec.const hL_peak h1).seq_eq <|
    (RDemonicExec.const hL_peak (fits_zero w)).seq_eq ?_).mono (by omega) ?_
  · convert hloop using 2; ext j
    · simp [xs, baseRegs, RData.set]
    · simp [xs, clear]
    · rfl
  · rintro _ rfl; rfl

end Cslib.WordRAM.Resizable
