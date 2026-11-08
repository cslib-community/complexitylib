/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.GhostLoop
public import Complexity.Computability.WordRAM.Glue.Basic
public import Complexity.Computability.WordRAM.MapOp
public import Complexity.Computability.WordRAM.RegisterCopy
public import Complexity.Computability.WordRAM.Subroutine

/-!
# Frontier-bounded structured word-RAM executions

`Cslib.WordRAM.Exec` and `Cslib.WordRAM.ExecWithin` evaluate memory loads and stores on an
unbounded cell array `ℕ → ℕ` without checking an allocation frontier. On the Resizable Word RAM,
by contrast, `load` and `store` succeed only at addresses strictly below the current hardware
word frontier `frontier`.

This module refines `Exec` and `ExecWithin` to `ExecBoundedExact` and `ExecBounded`, recording on
every `load d a` and `store a s` that the accessed word address `x.regs a` lies strictly below an
explicit address bound `L`. Pairing `Realization.Realizes` with the frontier-bounded realization
judgment `Realization.RealizesBounded` allows every non-allocating `Memory.Prog` client compiled by
`realize` to lift directly to the Resizable Word RAM (`RDemonicExec.of_execBounded`) without
duplicating the compiler or modifying `Complexity/Tactic/Realize.lean`.

## Main definitions

* `Cslib.WordRAM.IsRegOnlyOp`, `Cslib.WordRAM.IsRegOnlyCode`: predicates for data instructions and
  structured programs that perform no memory accesses (`load` or `store`) and no `rand` sampling.
* `Cslib.WordRAM.Op.BoundedAccess`: side condition requiring `x.regs a < L` on `load` and `store`.
* `Cslib.WordRAM.ExecBoundedExact`, `Cslib.WordRAM.ExecBounded`: exact-step and bounded-step
  structured executions whose memory accesses stay strictly below `L`.

## Main results

* `Cslib.WordRAM.ExecBounded.toExecWithin`: forget the address bound `L` back to `ExecWithin`.
* `Cslib.WordRAM.ExecBounded.mono_bound`: enlarge the address bound `L₁ ≤ L₂`.
* `Cslib.WordRAM.ExecBounded.of_execWithin_regOnly`: lift any register-only `ExecWithin` execution
  to `ExecBounded` at an arbitrary bound `L`.
* `Cslib.WordRAM.ExecBounded.mapSimulates`: transport frontier-bounded executions along any
  defined-evaluation basis simulation `Basis.Simulates`.
* `Cslib.WordRAM.SubroutineCode.zeroFillCode_execBounded`: frontier-bounded execution of
  `SubroutineCode.zeroFillCode`.

## References

* [Hagerup1998] Torben Hagerup, *Sorting and Searching on the Word RAM*, STACS 1998 (standard
  word-RAM register and memory instruction semantics).
* [KuszmaulLiangZhou2026] William Kuszmaul, Jingxun Liang, and Renfei Zhou, *Succinct Dynamic
  Rank/Select: Bypassing the Tree-Structure Bottleneck*, SODA 2026 (`arXiv:2510.19175v1`,
  Section 5.1, PDF p. 16 / printed p. 15: memory accesses restricted to the active word prefix).
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B B' : Basis} {r : ℕ}

/-! ## Register-only instructions and bounded memory access -/

/-- Whether a data instruction accesses only registers (neither `load` nor `store`). -/
def IsRegOnlyOp : Op B r → Prop
  | .const _ _ | .copy _ _ | .alu _ _ _ => True
  | .load _ _ | .store _ _ => False

instance decidableIsRegOnlyOp (o : Op B r) : Decidable (IsRegOnlyOp o) := by
  cases o <;> unfold IsRegOnlyOp <;> infer_instance

/-- Whether a structured `Code B r` uses only register instructions (no `load`, `store`, or
`rand`). -/
def IsRegOnlyCode : Code B r → Prop
  | .op o => IsRegOnlyOp o
  | .seq c₁ c₂ => IsRegOnlyCode c₁ ∧ IsRegOnlyCode c₂
  | .branch _ pos neg => IsRegOnlyCode pos ∧ IsRegOnlyCode neg
  | .loop _ body => IsRegOnlyCode body
  | .rand _ _ => False

instance decidableIsRegOnlyCode : (c : Code B r) → Decidable (IsRegOnlyCode c)
  | .op o => inferInstanceAs (Decidable (IsRegOnlyOp o))
  | .seq c₁ c₂ =>
    have := decidableIsRegOnlyCode c₁
    have := decidableIsRegOnlyCode c₂
    inferInstanceAs (Decidable (_ ∧ _))
  | .branch _ pos neg =>
    have := decidableIsRegOnlyCode pos
    have := decidableIsRegOnlyCode neg
    inferInstanceAs (Decidable (_ ∧ _))
  | .loop _ body => decidableIsRegOnlyCode body
  | .rand _ _ => isFalse id

/-- Every `Code.IsGlue` fragment is register-only. -/
theorem Code.IsGlue.isRegOnlyCode {c : Code B r} (h : c.IsGlue) : IsRegOnlyCode c := by
  induction c with
  | op o => cases o <;> simp_all [Code.IsGlue, IsRegOnlyCode, IsRegOnlyOp]
  | seq _ _ iha ihb | branch _ _ _ iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | loop | rand => exact h.elim

/-- `copyBank` uses only register-copy instructions. -/
theorem copyBank_isRegOnlyCode {k : ℕ} (src dst : Fin k → Fin r) (idle : Fin r) :
    IsRegOnlyCode (copyBank (B := B) src dst idle) := by
  induction k with
  | zero => trivial
  | succ _ ih => exact ⟨trivial, ih _ _⟩

/-- Data instruction `o` accesses only memory addresses strictly below `L` when evaluated at `x`. -/
def Op.BoundedAccess (L : ℕ) : Op B r → Data r → Prop
  | .const _ _, _ | .copy _ _, _ | .alu _ _ _, _ => True
  | .load _ a, x | .store a _, x => x.regs a < L

instance decidableBoundedAccess (L : ℕ) (o : Op B r) (x : Data r) :
    Decidable (o.BoundedAccess L x) := by
  cases o <;> unfold Op.BoundedAccess <;> infer_instance

theorem Op.BoundedAccess.mono {L₁ L₂ : ℕ} {o : Op B r} {x : Data r}
    (hL : L₁ ≤ L₂) (h : o.BoundedAccess L₁ x) : o.BoundedAccess L₂ x := by
  cases o <;> simp only [Op.BoundedAccess] at h ⊢ <;> omega

theorem Op.BoundedAccess.of_isRegOnly {L : ℕ} {o : Op B r} {x : Data r}
    (ho : IsRegOnlyOp o) : o.BoundedAccess L x := by
  cases o <;> simp_all [IsRegOnlyOp, Op.BoundedAccess]

theorem Op.boundedAccess_mapSimulates_iff (ψ : B.Simulates B') (L : ℕ) (o : Op B r) (x : Data r) :
    (o.mapSimulates ψ).BoundedAccess L x ↔ o.BoundedAccess L x := by
  cases o <;> rfl

/-! ## Exact and bounded executions with address bound `L` -/

/-- `ExecBoundedExact w L c x y n`: at word size `w`, the structured program `c` leads from data
`x` to data `y` in `n` instructions, and every `load` or `store` accesses an address `< L`. -/
inductive ExecBoundedExact (w L : ℕ) : Code B r → Data r → Data r → ℕ → Prop where
  /-- A data instruction whose memory access (if any) is `< L` takes `1` instruction. -/
  | op {o : Op B r} {x y : Data r} :
      o.BoundedAccess L x → o.eval w x = some y → ExecBoundedExact w L (.op o) x y 1
  /-- Sequencing adds the instruction counts. -/
  | seq {c₁ c₂ : Code B r} {x y z : Data r} {m n : ℕ} :
      ExecBoundedExact w L c₁ x y m → ExecBoundedExact w L c₂ y z n →
      ExecBoundedExact w L (.seq c₁ c₂) x z (m + n)
  /-- Positive branch of a conditional adds `1` instruction. -/
  | branch_pos {c : Cond r} {pos neg : Code B r} {x y : Data r} {n : ℕ} :
      c.Holds x → ExecBoundedExact w L pos x y n →
      ExecBoundedExact w L (.branch c pos neg) x y (n + 1)
  /-- Negative branch of a conditional adds `2` instructions. -/
  | branch_neg {c : Cond r} {pos neg : Code B r} {x y : Data r} {n : ℕ} :
      ¬c.Holds x → ExecBoundedExact w L neg x y n →
      ExecBoundedExact w L (.branch c pos neg) x y (n + 2)
  /-- Exiting a while loop takes `2` instructions. -/
  | loop_exit {c : Cond r} {body : Code B r} {x : Data r} :
      ¬c.Holds x → ExecBoundedExact w L (.loop c body) x x 2
  /-- One iteration of a while loop followed by the rest adds `m + n + 2` instructions. -/
  | loop_iter {c : Cond r} {body : Code B r} {x y z : Data r} {m n : ℕ} :
      c.Holds x → ExecBoundedExact w L body x y m →
      ExecBoundedExact w L (.loop c body) y z n →
      ExecBoundedExact w L (.loop c body) x z (m + n + 2)

/-- `ExecBounded w L c x y T`: at word size `w`, the structured program `c` leads from data `x`
to data `y` within `T` instructions while every `load` or `store` accesses an address `< L`. -/
def ExecBounded (w L : ℕ) (c : Code B r) (x y : Data r) (T : ℕ) : Prop :=
  ∃ n ≤ T, ExecBoundedExact w L c x y n

namespace ExecBoundedExact

variable {w L L₁ L₂ n : ℕ} {c : Code B r} {x y : Data r}

/-- Forget the address bound `L` to obtain an ordinary `Exec`. -/
theorem toExec (h : ExecBoundedExact w L c x y n) : Exec w c x y n := by
  induction h with
  | op _ ho => exact .op ho
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_exit hc => exact .loop_exit hc
  | loop_iter hc _ _ ihb ihl => exact .loop_iter hc ihb ihl

/-- Enlarge the address bound `L₁ ≤ L₂`. -/
theorem mono_bound (hL : L₁ ≤ L₂) (h : ExecBoundedExact w L₁ c x y n) :
    ExecBoundedExact w L₂ c x y n := by
  induction h with
  | op hb ho => exact .op (hb.mono hL) ho
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_exit hc => exact .loop_exit hc
  | loop_iter hc _ _ ihb ihl => exact .loop_iter hc ihb ihl

/-- Lift any register-only `Exec` to `ExecBoundedExact` at an arbitrary bound `L`. -/
theorem of_exec_regOnly (hc : IsRegOnlyCode c) (h : Exec w c x y n) :
    ExecBoundedExact w L c x y n := by
  induction h with
  | op ho => exact .op (.of_isRegOnly hc) ho
  | seq _ _ ih₁ ih₂ => exact .seq (ih₁ hc.1) (ih₂ hc.2)
  | branch_pos hcond _ ih => exact .branch_pos hcond (ih hc.1)
  | branch_neg hcond _ ih => exact .branch_neg hcond (ih hc.2)
  | loop_exit hcond => exact .loop_exit hcond
  | loop_iter hcond _ _ ihb ihl => exact .loop_iter hcond (ihb hc) (ihl hc)

/-- Transport `ExecBoundedExact` along a defined-evaluation basis simulation. -/
theorem mapSimulates (ψ : B.Simulates B') (h : ExecBoundedExact w L c x y n) :
    ExecBoundedExact w L (c.mapSimulates ψ) x y n := by
  induction h with
  | op hb ho =>
    exact .op ((Op.boundedAccess_mapSimulates_iff ψ L _ _).mpr hb)
      (Op.eval_mapSimulates_of_some ψ ho)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_exit hc => exact .loop_exit hc
  | loop_iter hc _ _ ihb ihl => exact .loop_iter hc ihb ihl

/-- Every exact execution within `n` instructions is a bounded execution within `n`. -/
theorem within (h : ExecBoundedExact w L c x y n) : ExecBounded w L c x y n :=
  ⟨n, le_rfl, h⟩

/-- Word-boundedness is preserved along `ExecBoundedExact`. -/
theorem bounded (h : ExecBoundedExact w L c x y n) (hx : x.Bounded w) : y.Bounded w :=
  h.toExec.bounded hx

/-- Unwritten registers keep their values along `ExecBoundedExact`. -/
theorem regs_eq {reg : Fin r} (h : ExecBoundedExact w L c x y n) (hp : c.Preserves reg) :
    y.regs reg = x.regs reg :=
  h.toExec.regs_eq hp

/-- A frontier-bounded structured execution is a run of any containing flat program. -/
theorem runs {p : Program B r} {pc : ℕ} (h : ExecBoundedExact w L c x y n)
    (hp : p.Contains pc (c.assemble pc)) : Runs w p ⟨pc, x⟩ ⟨pc + c.size, y⟩ n :=
  h.toExec.runs hp

/-- A frontier-bounded structured execution followed by `halt out` is a halting run. -/
theorem executes (h : ExecBoundedExact w L c x y n) (out : Fin r) :
    Executes w (c.program out) ⟨0, x⟩ (y.regs out) (n + 1) :=
  h.toExec.executes out

end ExecBoundedExact

namespace ExecBounded

variable {w L L₁ L₂ T T₁ T₂ : ℕ} {c c₁ c₂ pos neg body : Code B r} {cond : Cond r}
  {x y z : Data r} {d i j a s : Fin r}

/-- Forget the address bound `L` to obtain `ExecWithin`. -/
theorem toExecWithin (h : ExecBounded w L c x y T) : ExecWithin w c x y T :=
  let ⟨n, hn, he⟩ := h
  ⟨n, hn, he.toExec⟩

instance instCoeOutExec (w L : ℕ) (c : Code B r) (x y : Data r) (n : ℕ) :
    CoeOut (ExecBoundedExact w L c x y n) (Exec w c x y n) :=
  ⟨ExecBoundedExact.toExec⟩

instance instCoeOutExecWithin (w L : ℕ) (c : Code B r) (x y : Data r) (T : ℕ) :
    CoeOut (ExecBounded w L c x y T) (ExecWithin w c x y T) :=
  ⟨ExecBounded.toExecWithin⟩

/-- Enlarge the instruction budget `T ≤ T₂`. -/
theorem mono (h : ExecBounded w L c x y T) (hT : T ≤ T₂) : ExecBounded w L c x y T₂ :=
  let ⟨n, hn, he⟩ := h
  ⟨n, hn.trans hT, he⟩

/-- Enlarge the address bound `L₁ ≤ L₂`. -/
theorem mono_bound (hL : L₁ ≤ L₂) (h : ExecBounded w L₁ c x y T) :
    ExecBounded w L₂ c x y T :=
  let ⟨n, hn, he⟩ := h
  ⟨n, hn, he.mono_bound hL⟩

/-- Lift any register-only `ExecWithin` execution to `ExecBounded` at an arbitrary bound `L`. -/
theorem of_execWithin_regOnly (hc : IsRegOnlyCode c) (h : ExecWithin w c x y T) :
    ExecBounded w L c x y T :=
  let ⟨n, hn, he⟩ := h
  ⟨n, hn, ExecBoundedExact.of_exec_regOnly hc he⟩

/-- Word-boundedness is preserved along `ExecBounded`. -/
theorem bounded (h : ExecBounded w L c x y T) (hx : x.Bounded w) : y.Bounded w :=
  h.toExecWithin.bounded hx

/-- Unwritten registers keep their values along `ExecBounded`. -/
theorem regs_eq {reg : Fin r} (h : ExecBounded w L c x y T) (hp : c.Preserves reg) :
    y.regs reg = x.regs reg :=
  h.toExecWithin.regs_eq hp

/-- Transport `ExecBounded` along a defined-evaluation basis simulation. -/
theorem mapSimulates (ψ : B.Simulates B') (h : ExecBounded w L c x y T) :
    ExecBounded w L (c.mapSimulates ψ) x y T :=
  let ⟨n, hn, he⟩ := h
  ⟨n, hn, he.mapSimulates ψ⟩

/-- Single data instruction with bounded access. -/
theorem op {o : Op B r} (hb : o.BoundedAccess L x) (ho : o.eval w x = some y) :
    ExecBounded w L (.op o) x y 1 :=
  (ExecBoundedExact.op hb ho).within

/-- Constant load into register `d`. -/
theorem const {v : ℕ} (h : Fits w v) :
    ExecBounded (B := B) w L (.op (.const d v)) x (x.set d v) 1 :=
  op trivial (Data.put_of_fits h)

/-- ALU operation into register `d`. -/
theorem alu {f : B.Op} {args : Fin (B.Arity f) → Fin r} {v : ℕ}
    (hf : B.interp w f (x.regs ∘ args) = some v) (h : Fits w v) :
    ExecBounded w L (.op (.alu f d args)) x (x.set d v) 1 :=
  op trivial (by rw [Op.eval_alu, hf]; exact Data.put_of_fits h)

/-- Register copy into register `d`. -/
theorem copy : ExecBounded (B := B) w L (.op (.copy d s)) x (x.set d (x.regs s)) 1 :=
  op trivial rfl

/-- Memory load from an address `x.regs a < L`. -/
theorem load (ha : x.regs a < L) :
    ExecBounded (B := B) w L (.op (.load d a)) x (x.set d (x.mem (x.regs a))) 1 :=
  op ha rfl

/-- Memory store to an address `x.regs a < L`. -/
theorem store (ha : x.regs a < L) :
    ExecBounded (B := B) w L (.op (.store a s)) x (x.write (x.regs a) (x.regs s)) 1 :=
  op ha rfl

/-- Standard binary operation into register `d`. -/
theorem bin {f : BinOp} (h : Fits w (f.eval (x.regs i) (x.regs j))) :
    ExecBounded w L (.op (.bin f d i j)) x (x.set d (f.eval (x.regs i) (x.regs j))) 1 :=
  op trivial (Data.put_of_fits h)

/-- Word-width read into register `d`. -/
theorem width : ExecBounded w L (.op (.width d)) x (x.set d w) 1 :=
  op trivial (Op.eval_width w d x)

/-- Sequential composition of frontier-bounded executions. -/
theorem seq (h₁ : ExecBounded w L c₁ x y T₁) (h₂ : ExecBounded w L c₂ y z T₂) :
    ExecBounded w L (.seq c₁ c₂) x z (T₁ + T₂) :=
  let ⟨m, hm, he₁⟩ := h₁
  let ⟨n, hn, he₂⟩ := h₂
  ⟨m + n, Nat.add_le_add hm hn, .seq he₁ he₂⟩

/-- Positive branch of a conditional. -/
theorem branch_pos (hc : cond.Holds x) (h : ExecBounded w L pos x y T) :
    ExecBounded w L (.branch cond pos neg) x y (T + 1) :=
  let ⟨n, hn, he⟩ := h
  ⟨n + 1, Nat.add_le_add_right hn 1, .branch_pos hc he⟩

/-- Negative branch of a conditional. -/
theorem branch_neg (hc : ¬cond.Holds x) (h : ExecBounded w L neg x y T) :
    ExecBounded w L (.branch cond pos neg) x y (T + 2) :=
  let ⟨n, hn, he⟩ := h
  ⟨n + 2, Nat.add_le_add_right hn 2, .branch_neg hc he⟩

/-- Conditional with a shared bound on both alternatives. -/
theorem branch (hpos : cond.Holds x → ExecBounded w L pos x y T)
    (hneg : ¬cond.Holds x → ExecBounded w L neg x y T) :
    ExecBounded w L (.branch cond pos neg) x y (T + 2) := by
  by_cases hc : cond.Holds x
  · exact (branch_pos hc (hpos hc)).mono (by omega)
  · exact branch_neg hc (hneg hc)

/-- Exiting a loop when the condition fails takes at most `2` instructions. -/
theorem loop_exit (hc : ¬cond.Holds x) : ExecBounded w L (.loop cond body) x x 2 :=
  (ExecBoundedExact.loop_exit hc).within

/-- One loop iteration followed by the rest adds `T₁ + 2` instructions to the bound. -/
theorem loop_iter (hc : cond.Holds x) (h₁ : ExecBounded w L body x y T₁)
    (h₂ : ExecBounded w L (.loop cond body) y z T₂) :
    ExecBounded w L (.loop cond body) x z (T₁ + T₂ + 2) :=
  let ⟨m, hm, he₁⟩ := h₁
  let ⟨n, hn, he₂⟩ := h₂
  ⟨m + n + 2, by omega, .loop_iter hc he₁ he₂⟩

/-- Loop through explicit states `xs 0, …, xs k` under address bound `L`. -/
theorem loop (xs : ℕ → Data r) (k T : ℕ) (hc : ∀ i < k, cond.Holds (xs i))
    (hk : ¬cond.Holds (xs k)) (hbody : ∀ i < k, ExecBounded w L body (xs i) (xs (i + 1)) T) :
    ExecBounded w L (.loop cond body) (xs 0) (xs k) (k * (T + 2) + 2) := by
  induction k generalizing xs with
  | zero => simpa using loop_exit hk
  | succ k ih =>
    have hstep := loop_iter (hc 0 (by omega)) (hbody 0 (by omega))
      (ih (fun i => xs (i + 1)) (fun i hi => hc (i + 1) (by omega)) hk
        (fun i hi => hbody (i + 1) (by omega)))
    exact hstep.mono (by rw [Nat.succ_mul]; omega)

/-- Frontier-bounded counterpart of `ExecWithin.loop_invariant_state_additive`. -/
theorem loop_invariant_state_additive {σ : Type*} {code : Code B r} {C D : ℕ}
    (I : ℕ → σ → Data r → Prop) (next : σ → σ) (charge : σ → ℕ)
    (hexit : ∀ s x, I 0 s x → ¬cond.Holds x)
    (hbody : ∀ n s x, I (n + 1) s x →
      cond.Holds x ∧ ∃ y, ExecBounded w L code x y (C * (charge s + 1) + D) ∧
        I n (next s) y)
    {n : ℕ} {s : σ} {x : Data r} (hx : I n s x) :
    ∃ y, ExecBounded w L (.loop cond code) x y
        (C * iterationSum next charge n s + (C + D + 2) * n + 2) ∧
      I 0 ((next^[n]) s) y := by
  induction n generalizing s x with
  | zero =>
    refine ⟨x, (loop_exit (hexit s x hx)).mono ?_, hx⟩
    simp [iterationSum]
  | succ n ih =>
    obtain ⟨hc, u, hu, hI⟩ := hbody n s x hx
    obtain ⟨y, hy, hIy⟩ := ih hI
    refine ⟨y, (loop_iter hc hu hy).mono ?_, ?_⟩
    · simp only [iterationSum, Nat.mul_add, Nat.add_mul, Nat.mul_one]
      omega
    · simpa only [Function.iterate_succ_apply] using hIy

end ExecBounded

/-- `copyBank` executes within `k + 1` instructions under any address bound `L`. -/
theorem copyBank_execBounded {k : ℕ} (src dst : Fin k → Fin r) (idle : Fin r)
    (hi : Function.Injective dst) (hd : ∀ i j, src i ≠ dst j) (w L : ℕ) (x : Data r) :
    ∃ y, ExecBounded w L (copyBank (B := B) src dst idle) x y (k + 1) ∧
      y.mem = x.mem ∧ (∀ i, y.regs (dst i) = x.regs (src i)) ∧
      ∀ j, (∀ i, dst i ≠ j) → y.regs j = x.regs j := by
  obtain ⟨y, hy, hm, hout, hframe⟩ := copyBank_exec src dst idle hi hd w x
  exact ⟨y, ExecBounded.of_execWithin_regOnly (copyBank_isRegOnlyCode src dst idle) hy,
    hm, hout, hframe⟩

/-- Frontier-bounded execution of `P.zeroFillCode` clearing `[base, base + space)` with all
stores strictly below `base + space`. -/
theorem SubroutineCode.zeroFillCode_execBounded {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init) {w base space : ℕ} {params : Fin k_init → ℕ}
    (hclear : [P.curReg, P.zeroReg, P.oneReg, P.baseReg, P.frontierReg].Nodup)
    (hparams : ∀ j, P.initParams j ∉ [P.curReg, P.zeroReg, P.oneReg])
    (hinc_reg : IsRegOnlyOp P.incCur)
    (hinc : ∀ {x : Data r_ds}, x.regs P.oneReg = 1 → Fits w (x.regs P.curReg + 1) →
      P.incCur.eval w x = some (x.set P.curReg (x.regs P.curReg + 1)))
    {x₁ : Data r_ds}
    (hx₁ : x₁.Bounded w) (hb₁ : x₁.regs P.baseReg = base)
    (hfr₁ : x₁.regs P.frontierReg = base + space)
    (hpar₁ : ∀ j, x₁.regs (P.initParams j) = params j) :
    ∃ x₂, ExecBounded w (base + space) P.zeroFillCode x₁ x₂ (4 * space + 6) ∧
      x₂.Bounded w ∧
      x₂.regs P.baseReg = base ∧
      x₂.regs P.frontierReg = base + space ∧
      (∀ j, x₂.regs (P.initParams j) = params j) ∧
      (∀ a ∈ (Block.mk base space).footprint, x₂.mem a = 0) ∧
      Modifies (Block.mk base space).footprint x₁.mem x₂.mem := by
  have hfit0 : Fits w 0 := (hx₁.1 P.baseReg).of_le (Nat.zero_le _)
  have hfit_stop : Fits w (base + space) := hfr₁ ▸ hx₁.1 P.frontierReg
  obtain ⟨hcur_not, hzero_not, hone_not, hbase_ne_fr, _⟩ :=
    (List.nodup_cons.mp hclear).imp_right fun h =>
      (List.nodup_cons.mp h).imp_right fun h =>
        (List.nodup_cons.mp h).imp_right List.nodup_cons.mp
  have hcur_ne_zero : P.curReg ≠ P.zeroReg := fun h => hcur_not (by simp [h])
  have hcur_ne_one : P.curReg ≠ P.oneReg := fun h => hcur_not (by simp [h])
  have hcur_ne_base : P.curReg ≠ P.baseReg := fun h => hcur_not (by simp [h])
  have hcur_ne_fr : P.curReg ≠ P.frontierReg := fun h => hcur_not (by simp [h])
  have hzero_ne_one : P.zeroReg ≠ P.oneReg := fun h => hzero_not (by simp [h])
  have hzero_ne_base : P.zeroReg ≠ P.baseReg := fun h => hzero_not (by simp [h])
  have hzero_ne_fr : P.zeroReg ≠ P.frontierReg := fun h => hzero_not (by simp [h])
  have hone_ne_base : P.oneReg ≠ P.baseReg := fun h => hone_not (by simp [h])
  have hone_ne_fr : P.oneReg ≠ P.frontierReg := fun h => hone_not (by simp [h])
  by_cases hsp : 0 < space
  · have hc_pos : (Cond.lt P.baseReg P.frontierReg).Holds x₁ := by
      simp only [Cond.Holds, hb₁, hfr₁]; omega
    have hfit1 : Fits w 1 := hfit_stop.of_le (by omega)
    let x_z := x₁.set P.zeroReg 0
    let x_o := x_z.set P.oneReg 1
    let x_c := x_o.set P.curReg (x_o.regs P.baseReg)
    have hxc_base : x_c.regs P.baseReg = base := by
      simp [x_c, x_o, x_z, Data.set, Function.update_of_ne hcur_ne_base.symm,
        Function.update_of_ne hone_ne_base.symm, Function.update_of_ne hzero_ne_base.symm, hb₁]
    have hxc_fr : x_c.regs P.frontierReg = base + space := by
      simp [x_c, x_o, x_z, Data.set, Function.update_of_ne hcur_ne_fr.symm,
        Function.update_of_ne hone_ne_fr.symm, Function.update_of_ne hzero_ne_fr.symm, hfr₁]
    have hxc_zero : x_c.regs P.zeroReg = 0 := by
      simp [x_c, x_o, x_z, Data.set, Function.update_of_ne hcur_ne_zero.symm,
        Function.update_of_ne hzero_ne_one]
    have hxc_one : x_c.regs P.oneReg = 1 := by
      simp [x_c, x_o, x_z, Data.set, Function.update_of_ne hcur_ne_one.symm]
    have hxc_cur : x_c.regs P.curReg = base := by
      simp [x_c, x_o, x_z, Data.set, Function.update_of_ne hone_ne_base.symm,
        Function.update_of_ne hzero_ne_base.symm, hb₁]
    let xs : ℕ → Data r_ds := fun i =>
      ⟨Function.update x_c.regs P.curReg (base + i), clear x₁.mem base i⟩
    have hxs0 : xs 0 = x_c := by
      ext r'
      · by_cases hr : r' = P.curReg
        · subst hr; simp [xs, hxc_cur]
        · simp [xs, Function.update_of_ne hr, x_c, x_o, x_z, Data.set]
      · simp [xs, x_c, x_o, x_z, Data.set]
    have hloop_cond : ∀ i < space, (Cond.lt P.curReg P.frontierReg).Holds (xs i) := by
      intro i hi
      simp only [Cond.Holds, xs, Function.update_self,
        Function.update_of_ne hcur_ne_fr.symm, hxc_fr]
      omega
    have hloop_exit : ¬(Cond.lt P.curReg P.frontierReg).Holds (xs space) := by
      simp only [Cond.Holds, xs, Function.update_self,
        Function.update_of_ne hcur_ne_fr.symm, hxc_fr]
      omega
    have hloop_body : ∀ i < space,
        ExecBounded w (base + space) (.seq (.op (.store P.curReg P.zeroReg)) (.op P.incCur))
          (xs i) (xs (i + 1)) 2 := by
      intro i hi
      have hsi_zero : (xs i).regs P.zeroReg = 0 := by
        simp [xs, Function.update_of_ne hcur_ne_zero.symm, hxc_zero]
      have hsi_one : (xs i).regs P.oneReg = 1 := by
        simp [xs, Function.update_of_ne hcur_ne_one.symm, hxc_one]
      have hsi_cur : (xs i).regs P.curReg = base + i := by simp [xs]
      let x_st := (xs i).write ((xs i).regs P.curReg) ((xs i).regs P.zeroReg)
      have hst_one : x_st.regs P.oneReg = 1 := hsi_one
      have hst_fit : Fits w (x_st.regs P.curReg + 1) := by
        change Fits w ((xs i).regs P.curReg + 1)
        rw [hsi_cur]
        exact hfit_stop.of_le (by omega)
      have he_inc : ExecBounded w (base + space) (.op P.incCur) x_st
          (x_st.set P.curReg (x_st.regs P.curReg + 1)) 1 :=
        ExecBounded.op (.of_isRegOnly hinc_reg) (hinc hst_one hst_fit)
      have htarget : x_st.set P.curReg (x_st.regs P.curReg + 1) = xs (i + 1) := by
        ext r'
        · simp only [x_st, Data.set, Data.write, xs, hsi_cur]
          by_cases hr : r' = P.curReg
          · subst hr; simp [Nat.add_assoc]
          · simp [Function.update_of_ne hr]
        · simp only [x_st, Data.set, Data.write, hsi_cur, hsi_zero]
          simp [xs, clear_succ]
      rw [htarget] at he_inc
      exact (ExecBounded.store (by rw [hsi_cur]; omega)).seq he_inc
    have hloop : ExecBounded w (base + space)
        (.loop (.lt P.curReg P.frontierReg) (.seq (.op (.store P.curReg P.zeroReg)) (.op P.incCur)))
        x_c (xs space) (space * (2 + 2) + 2) := by
      simpa [hxs0] using ExecBounded.loop xs space 2 hloop_cond hloop_exit hloop_body
    have hseq : ExecBounded w (base + space)
        (.seq (.op (.const P.zeroReg 0)) <|
         .seq (.op (.const P.oneReg 1)) <|
         .seq (.op (.copy P.curReg P.baseReg)) <|
         .loop (.lt P.curReg P.frontierReg)
           (.seq (.op (.store P.curReg P.zeroReg)) (.op P.incCur)))
        x₁ (xs space) (1 + (1 + (1 + (space * (2 + 2) + 2)))) :=
      (ExecBounded.const hfit0).seq
        ((ExecBounded.const hfit1).seq (ExecBounded.copy.seq hloop))
    have hbranch : ExecBounded w (base + space) P.zeroFillCode x₁ (xs space) (4 * space + 6) :=
      (ExecBounded.branch_pos hc_pos hseq).mono (by omega)
    refine ⟨xs space, hbranch, hbranch.bounded hx₁, ?_, ?_, ?_, ?_, ?_⟩
    · simp [xs, Function.update_of_ne hcur_ne_base.symm, hxc_base]
    · simp [xs, Function.update_of_ne hcur_ne_fr.symm, hxc_fr]
    · intro j
      have hne_cur : P.initParams j ≠ P.curReg := fun h => hparams j (by simp [h])
      have hne_one : P.initParams j ≠ P.oneReg := fun h => hparams j (by simp [h])
      have hne_zero : P.initParams j ≠ P.zeroReg := fun h => hparams j (by simp [h])
      simp [xs, x_c, x_o, x_z, Data.set, Function.update_of_ne hne_cur,
        Function.update_of_ne hne_one, Function.update_of_ne hne_zero, hpar₁ j]
    · intro a ha
      exact clear_of_owns (Block.mem_footprint.mp ha)
    · intro a ha
      exact clear_of_not_owns fun h => ha (Block.mem_footprint.mpr h)
  · have hsp0 : space = 0 := by omega
    subst hsp0
    have hc_neg : ¬(Cond.lt P.baseReg P.frontierReg).Holds x₁ := by
      simp [Cond.Holds, hb₁, hfr₁]
    have hbranch : ExecBounded w (base + 0) P.zeroFillCode x₁ (x₁.set P.zeroReg 0)
        (4 * 0 + 6) :=
      (ExecBounded.branch_neg hc_neg (ExecBounded.const hfit0)).mono (by omega)
    refine ⟨x₁.set P.zeroReg 0, hbranch, hbranch.bounded hx₁, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Data.set, Function.update_of_ne hzero_ne_base.symm, hb₁]
    · simp [Data.set, Function.update_of_ne hzero_ne_fr.symm, hfr₁]
    · intro j
      have hne_zero : P.initParams j ≠ P.zeroReg := fun h => hparams j (by simp [h])
      simp [Data.set, Function.update_of_ne hne_zero, hpar₁ j]
    · intro a ha
      simp [Block.footprint] at ha
    · intro _ _
      rfl

end Cslib.WordRAM
