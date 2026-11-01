/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Basic
public import Complexity.Computability.WordRAM.Subroutine

/-!
# Native memory-query realizations

The native query arguments are already in the caller's live register environment. Loads and
stores reuse the basis-generic execution rules. Allocation uses exact arithmetic and the
existing generic zero-fill subroutine; it changes the full memory abstraction exactly as the
memory oracle specifies. Argument computation, binds and the final halt are charged by the
surrounding realization rules rather than hidden in these primitives.

## Main results

* `Realizes.read`, `Realizes.write`: one-instruction memory operations with live-register frames.
* `Realizes.allocDirty`: exact two-instruction bump allocation, including zero-width empty blocks.
* `Realizes.alloc`: zeroed allocation via the existing basis-generic zero-fill code.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.Realizes

open Cslib.DataStructure

variable {B : Basis} {δ : Type} {k : ℕ}

local notation "word" => Equiv.toEmbedding (Equiv.symm (Equiv.funUnique (Fin 1) ℕ))
local notation "unitWords" => Equiv.toEmbedding (Equiv.ofUnique Unit (Fin 0 → ℕ))

/-- A read returns a word without changing the frontier or any memory cell. Its address is a
live word; memory admissibility additionally states that the address is allocated. -/
theorem read (input : δ ↪ (Fin k → ℕ)) (i : Fin k) :
    Realizes B (fun d => Memory.read (input d i)) input word
      (fun _ _ _ => True) (fun _ _ => 0) := by
  refine ⟨0, 1, fun _ src tmp => .op (.load (tmp 0) (src i)), ?_⟩
  intro r frontier src tmp hi hd hf hs
  refine ⟨by simp [Code.ReadsWidth, Op.ReadsWidth], ?_⟩
  intro w d x hx hin hsafe hv
  have harg : x.regs (src i) = input d i := congrFun hin i
  let y := x.set (tmp 0) (x.mem (input d i))
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · have he := ExecWithin.load (B := B) (w := w) (d := tmp 0) (a := src i) (x := x)
    rw [harg] at he
    exact he.mono (by change 1 ≤ 1 * (1 + 0 + 1); omega)
  · apply Memory.State.ext
    · rfl
    · change (x.set (tmp 0) _).regs frontier = x.regs frontier
      simp [Data.set, Function.update_of_ne (hf 0).symm]
  · intro j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    change (x.set (tmp 0) _).regs (tmp 0) = x.mem (input d i)
    simp [Data.set]
  · intro j hj htmp
    exact Function.update_of_ne (htmp 0).symm _ _

/-- A store returns unit, updates precisely the selected memory cell and preserves all registers.
The value and allocated-address hypotheses remain in the existing memory valid-history premise. -/
theorem write (input : δ ↪ (Fin k → ℕ)) (i j : Fin k) :
    Realizes B (fun d => Memory.write (input d i) (input d j)) input unitWords
      (fun _ _ _ => True) (fun _ _ => 0) := by
  refine ⟨0, 1, fun _ src _ => .op (.store (src i) (src j)), ?_⟩
  intro r frontier src tmp hi hd hf hs
  refine ⟨by simp [Code.ReadsWidth, Op.ReadsWidth], ?_⟩
  intro w d x hx hin hsafe hv
  have hi' : x.regs (src i) = input d i := congrFun hin i
  have hj' : x.regs (src j) = input d j := congrFun hin j
  let y := x.write (input d i) (input d j)
  refine ⟨y, ?_, ?_, ?_, fun _ _ _ => rfl⟩
  · have he := ExecWithin.store (B := B) (w := w) (a := src i) (s := src j) (x := x)
    rw [hi', hj'] at he
    exact he.mono (by change 1 ≤ 1 * (1 + 0 + 1); omega)
  · rfl
  · exact fun i => Fin.elim0 i

/-- Dirty allocation returns the old frontier and adds the count exactly, without touching memory.
No constant `1` is materialized, so a zero-width empty allocation is included. -/
theorem allocDirty (input : δ ↪ (Fin k → ℕ)) (i : Fin k) :
    Realizes .exact (fun d => Memory.allocDirty (input d i)) input word
      (fun _ _ _ => True) (fun _ _ => 0) := by
  refine ⟨0, 1, fun frontier src tmp =>
    .seq (.op (.copy (tmp 0) frontier)) (.op (.exactBin .add frontier frontier (src i))), ?_⟩
  intro r frontier src tmp hi hd hf hs
  refine ⟨by simp [Code.ReadsWidth, Op.ReadsWidth, Op.exactBin, Basis.exact], ?_⟩
  intro w d x hx hin hsafe hv
  have harg : x.regs (src i) = input d i := congrFun hin i
  have hfit : Fits w (x.regs frontier + input d i) := hv.1
  let a := x.set (tmp 0) (x.regs frontier)
  let y := a.set frontier (x.regs frontier + input d i)
  have ha : a.regs frontier = x.regs frontier :=
    Function.update_of_ne (hf 0).symm _ _
  have hai : a.regs (src i) = input d i :=
    (Function.update_of_ne (hd i 0) _ _).trans harg
  have hcopy : ExecWithin (B := .exact) w (.op (.copy (tmp 0) frontier)) x a 1 :=
    ExecWithin.copy
  have hadd : ExecWithin w (.op (.exactBin .add frontier frontier (src i))) a y 1 := by
    apply ExecWithin.op
    rw [Op.eval_exactBin, ha, hai]
    exact Data.put_of_fits hfit
  refine ⟨y, (hcopy.seq hadd).mono (by change 1 + 1 ≤ 1 * (1 + 0 + 1); omega), ?_, ?_, ?_⟩
  · apply Memory.State.ext
    · rfl
    · change (a.set frontier _).regs frontier = x.regs frontier + input d i
      simp [Data.set]
  · intro j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    change y.regs (tmp 0) = x.regs frontier
    simp [y, a, Data.set, Function.update_of_ne (hf 0)]
  · intro j hj htmp
    simp [y, a, Data.set, Function.update_of_ne hj,
      Function.update_of_ne (htmp 0).symm]

private def clearPackage {r : ℕ} (frontier base cur zero one : Fin r) :
    SubroutineCode .exact r 0 where
  allocSpan := .op (.copy base base)
  initSetup := .op (.copy base base)
  code := .op (.copy base base)
  frontierReg := frontier
  baseReg := base
  initParams := Fin.elim0
  curReg := cur
  zeroReg := zero
  oneReg := one
  incCur := .exactBin .add cur cur one
  input := fun _ => false
  output := base

/-- Zeroed allocation realizes the full oracle memory update on arbitrary old scratch contents.
The reused clear code materializes `1` only in the positive-size branch. -/
theorem alloc (input : δ ↪ (Fin k → ℕ)) (i : Fin k) :
    Realizes .exact (fun d => Memory.alloc (input d i)) input word
      (fun _ _ _ => True) (fun _ _ => 0) := by
  refine ⟨2, 4, fun frontier src tmp =>
    .seq (.op (.copy (tmp 0) frontier)) <|
      .seq (.op (.exactBin .add frontier frontier (src i)))
        (clearPackage frontier (tmp 0) (tmp 1) (tmp 2) (tmp 3)).zeroFillCode, ?_⟩
  intro r frontier src tmp hi hd hf hs
  refine ⟨by simp [Code.ReadsWidth, Op.ReadsWidth, Op.exactBin, Basis.exact,
    clearPackage, SubroutineCode.zeroFillCode], ?_⟩
  intro w d x hx hin hsafe hv
  have harg : x.regs (src i) = input d i := congrFun hin i
  have hfit : Fits w (x.regs frontier + input d i) := hv.1
  let a := x.set (tmp 0) (x.regs frontier)
  let b := a.set frontier (x.regs frontier + input d i)
  let P := clearPackage frontier (tmp 0) (tmp 1) (tmp 2) (tmp 3)
  have ha : a.regs frontier = x.regs frontier := Function.update_of_ne (hf 0).symm _ _
  have hai : a.regs (src i) = input d i :=
    (Function.update_of_ne (hd i 0) _ _).trans harg
  have hcopy : ExecWithin (B := .exact) w (.op (.copy (tmp 0) frontier)) x a 1 :=
    ExecWithin.copy
  have hadd : ExecWithin w (.op (.exactBin .add frontier frontier (src i))) a b 1 := by
    apply ExecWithin.op
    rw [Op.eval_exactBin, ha, hai]
    exact Data.put_of_fits hfit
  have hclear : [P.curReg, P.zeroReg, P.oneReg, P.baseReg, P.frontierReg].Nodup := by
    simp [P, clearPackage, hi.eq_iff, hf]
  have hinc {z : Data r} (hz : z.regs P.oneReg = 1) (hfit : Fits w (z.regs P.curReg + 1)) :
      P.incCur.eval w z = some (z.set P.curReg (z.regs P.curReg + 1)) := by
    change z.regs (tmp 3) = 1 at hz
    change Fits w (z.regs (tmp 1) + 1) at hfit
    change (Op.exactBin .add (tmp 1) (tmp 1) (tmp 3)).eval w z =
      some (z.set (tmp 1) (z.regs (tmp 1) + 1))
    rw [Op.eval_exactBin, hz]
    exact Data.put_of_fits hfit
  have hbbase : b.regs P.baseReg = x.regs frontier := by
    simp [P, clearPackage, b, a, Data.set, Function.update_of_ne (hf 0)]
  have hbfront : b.regs P.frontierReg = x.regs frontier + input d i := by
    simp [P, clearPackage, b, Data.set]
  obtain ⟨y, hy, hby, hbase, hfront, _, hzero, hmod⟩ :=
    P.zeroFillCode_exec (params := Fin.elim0) hclear (fun j => Fin.elim0 j) hinc
      ((hcopy.seq hadd).bounded hx)
      hbbase hbfront (fun j => Fin.elim0 j)
  have hmem : y.mem = clear x.mem (x.regs frontier) (input d i) := by
    funext addr
    by_cases ha : (Block.mk (x.regs frontier) (input d i)).Owns addr
    · rw [clear_of_owns ha]
      exact hzero addr (Block.mem_footprint.mpr ha)
    · rw [clear_of_not_owns ha]
      exact hmod addr (fun h => ha (Block.mem_footprint.mp h))
  have hwhole := hcopy.seq (hadd.seq hy)
  refine ⟨y, hwhole.mono (by change 1 + (1 + (4 * input d i + 6)) ≤
    4 * ((input d i + 1) + 0 + 1); omega), ?_, ?_, ?_⟩
  · apply Memory.State.ext
    · exact hmem
    · exact hfront
  · intro j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    exact hbase
  · intro j hj htmp
    apply hwhole.regs_eq
    simp [Code.Preserves, Op.dest, Op.exactBin, P, clearPackage,
      SubroutineCode.zeroFillCode, Ne.symm hj, htmp]

end Cslib.WordRAM.Realization.Realizes
