/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Cell
public import Complexity.Algorithms.WordRAM.ThreeSum.Memory

/-!
# Native matrix-building loop for Convolution-3SUM

This is a fixed native word-RAM program for one tripartite instance. Its parameters are supplied
in registers. Every row/column calculation, index calculation, guarded input read, store and loop
instruction is charged. The three matrices follow the input in disjoint blocks.

The construction directly adapts Anthropic's `convFillBody` and its prefix invariant at
[`formal-math@16a5ce4`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/Convolution/Fill.lean).
The graph builder does not invoke an Exact Triangle solver.

## Main definitions

* `Fill.body`: one matrix cell and the loop-counter increment.
* `Fill.program`: initialize counters and fill all three matrices.

## Main results

* `Fill.exec`: the complete matrix builder with charged time and memory correctness.

## References

* [V. Vassilevska Williams and R. Williams, *Finding, minimizing, and counting weighted
  subgraphs*][VassilevskaWilliamsWilliams2013]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Fill

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Register holding the number of cells in each matrix. -/
abbrev area : Fin 28 := 20
/-- Loop increment. -/
abbrev one : Fin 28 := 21

/-- Write all three weights at the current cell and advance the counter. -/
def body : Code .standard 28 := ram[
  ⟪Cell.step⟫; Cell.cell ← Cell.cell + one ]

/-- Initialize the counter and matrix area, then write each row-major cell. -/
def program : Code .standard 28 :=
  .seq (ram[ Cell.cell ← #0; one ← #1; area ← Cell.side * Cell.side ])
    (.loop (.lt Cell.cell area) body)

/-- Fill three disjoint matrices within `131t² + 5` native instructions, excluding the halt.
All matrix addresses and the one-past-end addresses fit target words. The signed index bound
and both signs of the filler fit the source width. The program keeps its input and parameters. -/
theorem exec {w : ℕ} (A : Args) (x : Data 28)
    (ht : x.regs Cell.side = A.t) (hs : x.regs Cell.inst = A.s)
    (hab : x.regs Cell.matAB = A.ab) (hbc : x.regs Cell.matBC = A.bc)
    (hac : x.regs Cell.matAC = A.ac) (hlen : x.regs Cell.len = A.N)
    (hbase : x.regs Cell.base = A.base) (hf : x.regs Cell.filler = encode A.filler)
    (hmem : ∀ i < A.N, x.mem (A.base + i) = encode (A.values i))
    (hidx : GenericRAM.Signed.Fits w ((2 * (A.t * A.t) + A.s + 1 : ℕ) : ℤ))
    (hF : GenericRAM.Signed.Fits w A.filler) (hnF : GenericRAM.Signed.Fits w (-A.filler))
    (hμ : ∀ i < A.N, GenericRAM.Signed.Fits w (A.values i))
    (haddr : Fits (w + 2) (A.base + A.N))
    (habfit : Fits (w + 2) (A.ab + A.t * A.t))
    (hbcfit : Fits (w + 2) (A.bc + A.t * A.t))
    (hacfit : Fits (w + 2) (A.ac + A.t * A.t))
    (hbelow : A.base + A.N ≤ A.ab)
    (hABBC : A.ab + A.t * A.t ≤ A.bc) (hBCAC : A.bc + A.t * A.t ≤ A.ac) :
    ∃ y, ExecWithin (w + 2) program x y (131 * (A.t * A.t) + 5) ∧
      y.mem = A.filled x.mem (A.t * A.t) ∧
      y.regs Cell.side = A.t ∧ y.regs Cell.inst = A.s ∧
      y.regs Cell.matAB = A.ab ∧ y.regs Cell.matBC = A.bc ∧ y.regs Cell.matAC = A.ac ∧
      y.regs Cell.len = A.N ∧ y.regs Cell.base = A.base ∧
      y.regs Cell.filler = encode A.filler := by
  let P (i : Fin 28) : Prop := i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨
    (15 ≤ i.val ∧ i.val ≤ 19)
  let I (y : Data 28) : Prop :=
    (∀ i, P i → y.regs i = x.regs i) ∧ y.regs one = 1 ∧
    y.regs area = A.t * A.t ∧ y.regs Cell.cell ≤ A.t * A.t ∧
    y.mem = A.filled x.mem (y.regs Cell.cell)
  have hbody (y : Data 28) (hy : I y) (hc : (Cond.lt Cell.cell area).Holds y) :
      ∃ z, ExecWithin (w + 2) body y z 129 ∧ I z ∧
        A.t * A.t - z.regs Cell.cell < A.t * A.t - y.regs Cell.cell := by
    obtain ⟨hr, ho, ha, hq, hm⟩ := hy
    have hlt : y.regs Cell.cell < A.t * A.t := by simpa only [Cond.holds_lt, ha] using hc
    have hinput : ∀ i < A.N, y.mem (A.base + i) = encode (A.values i) := by
      intro i hi
      rw [hm, A.input_filled x.mem _ hbelow (by omega) (by omega) hi]
      exact hmem i hi
    obtain ⟨z, he, hzmem, hzf, hzreg⟩ := Cell.exec_step y rfl
      ((hr Cell.side (by decide)).trans ht) ((hr Cell.inst (by decide)).trans hs)
      ((hr Cell.matAB (by decide)).trans hab) ((hr Cell.matBC (by decide)).trans hbc)
      ((hr Cell.matAC (by decide)).trans hac) ((hr Cell.len (by decide)).trans hlen)
      ((hr Cell.base (by decide)).trans hbase) ((hr Cell.filler (by decide)).trans hf)
      hinput hlt hidx hF hnF hμ haddr (habfit.of_le (by omega))
      (hbcfit.of_le (by omega)) (hacfit.of_le (by omega)) hbelow (by omega)
    have hzc : z.regs Cell.cell = y.regs Cell.cell := hzreg Cell.cell (by decide)
    have hzo : z.regs one = 1 := (hzreg one (by decide)).trans ho
    have hza : z.regs area = A.t * A.t := (hzreg area (by decide)).trans ha
    have hzr (i : Fin 28) (hi : P i) : z.regs i = x.regs i := by
      by_cases hif : i = Cell.filler
      · subst i
        exact hzf.trans (hr _ hi)
      · have hiv : i.val ≠ 12 := fun hv => hif (Fin.ext hv)
        exact (hzreg i (by dsimp only [P] at hi; omega)).trans (hr i hi)
    have hmemory : z.mem = A.filled x.mem (y.regs Cell.cell + 1) := by
      rw [A.filled_succ x.mem hABBC hBCAC hlt, ← hm]
      simpa only [Args.valueAB, Args.valueBC, Args.valueAC] using hzmem
    have hinc : Fits (w + 2) (z.regs Cell.cell + z.regs one) :=
      hacfit.of_le (by rw [hzc, hzo]; omega)
    refine ⟨z.set Cell.cell (y.regs Cell.cell + 1), ?_, ?_, ?_⟩
    · have hi := (ExecWithin.bin (f := BinOp.add)
        (x := z) (d := Cell.cell) (i := Cell.cell) (j := one) hinc)
      simpa only [body, BinOp.eval, hzc, hzo] using he.seq hi
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        have hne : i ≠ Cell.cell := by
          intro h
          have hv := congrArg Fin.val h
          change i.val = 14 at hv
          dsimp only [P] at hi
          omega
        simpa only [Data.set_regs, Function.update_of_ne hne] using hzr i hi
      · simpa +decide only [Data.set_regs, Function.update_apply, one, Cell.cell,
          ↓reduceIte] using hzo
      · simpa +decide only [Data.set_regs, Function.update_apply, area, Cell.cell,
          ↓reduceIte] using hza
      · simpa only [Data.set_regs, Function.update_self] using Nat.succ_le_of_lt hlt
      · simpa only [Data.set_mem, Data.set_regs, Function.update_self] using hmemory
    · simp only [Data.set_regs, Function.update_self]
      omega
  have h1 : Fits (w + 2) 1 := (show Fits 2 1 from by decide).mono (by omega)
  have harea : Fits (w + 2) (A.t * A.t) := hacfit.of_le (by omega)
  let x₀ := ((x.set Cell.cell 0).set one 1).set area (A.t * A.t)
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hic : i ≠ Cell.cell := by
        intro h
        have hv := congrArg Fin.val h
        change i.val = 14 at hv
        dsimp only [P] at hi
        omega
      have hio : i ≠ one := by
        intro h
        have hv := congrArg Fin.val h
        change i.val = 21 at hv
        dsimp only [P] at hi
        omega
      have hia : i ≠ area := by
        intro h
        have hv := congrArg Fin.val h
        change i.val = 20 at hv
        dsimp only [P] at hi
        omega
      simp only [x₀, Data.set_regs, Function.update_of_ne hia, Function.update_of_ne hio,
        Function.update_of_ne hic]
    · simp +decide [x₀, one, area, Cell.cell]
    · simp [x₀]
    · simp +decide [x₀, one, area, Cell.cell]
    · simp +decide [x₀, one, area, Cell.cell]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => A.t * A.t - y.regs Cell.cell) hbody hx₀
  obtain ⟨hr, ho, ha, hq, hm⟩ := hy
  have hend : y.regs Cell.cell = A.t * A.t := by
    simp only [Cond.holds_lt, ha] at hc
    omega
  refine ⟨y, ?_, by simpa only [hend] using hm,
    (hr Cell.side (by decide)).trans ht, (hr Cell.inst (by decide)).trans hs,
    (hr Cell.matAB (by decide)).trans hab, (hr Cell.matBC (by decide)).trans hbc,
    (hr Cell.matAC (by decide)).trans hac, (hr Cell.len (by decide)).trans hlen,
    (hr Cell.base (by decide)).trans hbase, (hr Cell.filler (by decide)).trans hf⟩
  have hinit : ExecWithin (w + 2)
      (ram[ Cell.cell ← #0; one ← #1; area ← Cell.side * Cell.side ]) x x₀ 3 := by
    ram_eval [x₀, ht, h1, harea, Cell.cell, Cell.side, one, area, Fin.mk.injEq]
  have hall := hinit.seq he
  convert hall using 1
  · rfl
  · simp +decide only [x₀, Data.set_regs, Function.update_apply, Cell.cell, one, area,
      ↓reduceIte, Nat.sub_zero]
    omega

end Cslib.Algorithms.WordRAM.ThreeSum.Fill
