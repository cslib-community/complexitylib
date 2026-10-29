/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Powers
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Ready

/-!
# Native headers, powers and evaluator pointers

## Main results

* `PrunedQuery.exec_initialize`: load both actual headers, compute the encoding-array length,
  derive every evaluator pointer, and establish the ordinary register calling convention.

The prefix uses `4L+27` instructions, including its power loop. Its continuation is the existing
structured sequence rule, so composing it with evaluation gives the original fixed program.
This continuation lemma is an internal implementation API for the complete initialized-run
theorems in `Pruned.Flat` and `Pruned.Width`.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Initialization derives all pointers from the two ordinary scalar headers. Its output
assertion contains no execution or fit fields; the charged native composition is proved here. -/
theorem exec_initialize {w L Q : ℕ} (x : Data registers) (hL : x.mem 1 = L)
    (hQ : x.mem 2 = Q) (hfit : Fits w (addressBound L Q)) :
    ∃ y, y.mem = x.mem ∧ KernelRegs L (scratchBase L Q) 3 (3 + 10 ^ L) y ∧
      y.regs queryCount = Q ∧ y.regs queries = 3 + 2 * 10 ^ L ∧
      y.regs output = outputBase L Q ∧ y.regs epoch = 0 ∧
      ∀ (tail : Code .standard registers) z T, ExecWithin w tail y z T →
        ExecWithin w (ram[ ⟪header⟫; ⟪powers⟫; ⟪parameters⟫; ⟪locate⟫; ⟪tail⟫ ])
          x z (4 * L + 27 + T) := by
  have hp : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hscalar : L + Q + 10 ^ L + 16 ≤ addressBound L Q := by
    unfold addressBound
    nlinarith only [hp]
  have h1 : Fits w 1 := hfit.of_le (by omega)
  have h2 : Fits w 2 := hfit.of_le (by omega)
  have h3 : Fits w 3 := hfit.of_le (by omega)
  let h := (((x.set address 1).set inputDepth L).set address 2).set queryCount Q
  have hheader : ExecWithin w header x h 4 := by
    ram_eval [header, h, hL, hQ, h1, h2, address, inputDepth, queryCount, Fin.mk.injEq]
  have hdepth : h.regs inputDepth = L := by simp +decide [h, address, inputDepth, queryCount]
  obtain ⟨p, hpower, hpmem, hpL, hspan, _, hnil, hone, _, hten, hnine, hfour, _⟩ :=
    exec_powers h hdepth hfit
  have hpQ : p.regs queryCount = Q :=
    (hpower.regs_eq (by decide : powers.Preserves queryCount)).trans (by simp [h])
  let u := ((((((p.set arrayA 3).set arrayB (3 + 10 ^ L)).set queries (3 + 10 ^ L + 10 ^ L)).set
    output (3 + 10 ^ L + 10 ^ L + Q)).set scratch (3 + 10 ^ L + 10 ^ L + Q + Q)).set epoch 0)
  have hB : Fits w (3 + 10 ^ L) := hfit.of_le (by omega)
  have hqueries : Fits w (3 + 10 ^ L + 10 ^ L) :=
    hfit.of_le (by unfold addressBound; nlinarith only [hp])
  have hout : Fits w (3 + 10 ^ L + 10 ^ L + Q) :=
    hfit.of_le (by unfold addressBound; nlinarith only [hp])
  have hs : Fits w (3 + 10 ^ L + 10 ^ L + Q + Q) :=
    hfit.of_le (by unfold addressBound; nlinarith only [hp])
  have hparameters : ExecWithin w parameters p u 6 := by
    ram_eval [parameters, u, hspan, hpQ, h3, hB, hqueries, hout, hs, arrayA, arrayB, queries,
      output, scratch, epoch, span, queryCount, Fin.mk.injEq]
  have unchanged (i : Fin registers) (hi : parameters.Preserves i) : u.regs i = p.regs i :=
    hparameters.regs_eq hi
  have huL : u.regs inputDepth = L := (unchanged _ (by decide)).trans hpL
  have huspan : u.regs span = 10 ^ L := (unchanged _ (by decide)).trans hspan
  have hu1 : u.regs one = 1 := (unchanged _ (by decide)).trans hone
  have hu4 : u.regs frameWidth = 4 := (unchanged _ (by decide)).trans hfour
  have hus : u.regs scratch = scratchBase L Q := by
    simp +decide [u, scratch, epoch, scratchBase, outputBase, two_mul, Nat.add_assoc]
  obtain ⟨y, hlocate, hymem, hyf, hyl, hyv, hys, _⟩ := exec_locate u hu1 hu4
    (hfit.of_le (by
      rw [hus, huL, huspan]
      unfold scratchBase outputBase addressBound
      have hm : L ≤ L * 10 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
      nlinarith only [hp, hm]))
  have hyconstant (i : Fin registers) (hi : locate.Preserves i)
      (hi' : parameters.Preserves i) : y.regs i = p.regs i :=
    (hlocate.regs_eq hi).trans (unchanged i hi')
  have hregs : KernelRegs L (scratchBase L Q) 3 (3 + 10 ^ L) y := by
    constructor
    · exact (hyconstant _ (by decide) (by decide)).trans hpL
    · exact (hyconstant _ (by decide) (by decide)).trans hspan
    · exact (hlocate.regs_eq (by decide : locate.Preserves arrayA)).trans (by
        simp +decide [u, arrayA, arrayB, queries, output, scratch, epoch])
    · exact (hlocate.regs_eq (by decide : locate.Preserves arrayB)).trans (by
        simp +decide [u, arrayA, arrayB, queries, output, scratch, epoch])
    · exact hyf.trans hus
    · simpa only [hus, huL] using hyl
    · simpa only [hus, huL, huspan] using hyv
    · simpa only [hus, huL, huspan] using hys
    · exact (hyconstant _ (by decide) (by decide)).trans hnil
    · exact (hyconstant _ (by decide) (by decide)).trans hone
    · exact (hyconstant _ (by decide) (by decide)).trans hten
    · exact (hyconstant _ (by decide) (by decide)).trans hnine
    · exact (hyconstant _ (by decide) (by decide)).trans hfour
  refine ⟨y, ?_, hregs, ?_, ?_, ?_, ?_, ?_⟩
  · exact hymem.trans (show u.mem = p.mem from rfl) |>.trans hpmem
  · exact (hyconstant _ (by decide) (by decide)).trans hpQ
  · exact (hlocate.regs_eq (by decide : locate.Preserves queries)).trans (by
      simp +decide [u, queries, output, scratch, epoch, two_mul, Nat.add_assoc])
  · exact (hlocate.regs_eq (by decide : locate.Preserves output)).trans (by
      simp +decide [u, output, scratch, epoch, outputBase, two_mul, Nat.add_assoc])
  · exact (hlocate.regs_eq (by decide : locate.Preserves epoch)).trans (by simp [u])
  · intro tail z T htail
    exact (hheader.seq (hpower.seq (hparameters.seq (hlocate.seq htail)))).mono (by omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
