/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Child

/-!
# Actual empty-child transitions

## Main results

* `PrunedQuery.exec_node_emptyChild`: compute an empty child by real native scanning,
  advance the parent term, and preserve its request list and partial values.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- An empty-child transition may change the temporary child list, shared stamps and the
parent frame. Its first three frame words are also explicitly preserved below. -/
def emptyChildWrites (L f d : ℕ) : Finset ℕ :=
  (Block.mk (f + 4 * (L + 1) + (d + 1) * 10 ^ L) (10 ^ L)).footprint ∪
  (Block.mk (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) (10 ^ L)).footprint ∪
  (Block.mk (f + 4 * d) 4).footprint

/-- The program itself observes its computed zero child count and skips the recursive push.
Every scan, comparison, increment and stored counter is charged. -/
theorem exec_node_emptyChild {w L f a0 b0 d N k : ℕ} (x : Data registers)
    (hregs : KernelRegs L f a0 b0 x) (hd : x.regs level = d) (hdL : d < L)
    (hm : x.regs mode = 1)
    (hN : x.mem (f + 4 * d) = N) (hcap : N ≤ 10 ^ L)
    (hterm : x.mem (f + 4 * d + 3) = k) (hk : k < 10)
    (input : ℕ → ℕ)
    (hinput : ∀ i < N, x.mem (f + 4 * (L + 1) + d * 10 ^ L + i) = input i)
    (hcodes : ∀ i < N, input i < 10 ^ L)
    (hmarks : ∀ q < 10 ^ L,
      x.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) ≤ x.regs epoch)
    (hempty : scanSet true k input N = ∅)
    (hw : Fits w (8 * f + 64 * (L + 1) * 10 ^ L + x.regs epoch + 128)) :
    ∃ y, ExecWithin w step x y (20 * N + 33) ∧ KernelRegs L f a0 b0 y ∧
      y.regs level = d ∧ y.regs mode = 1 ∧ y.regs active = x.regs active ∧
      y.regs epoch = x.regs epoch + 1 ∧
      ScanMemory y.mem (f + 4 * (L + 1) + (d + 1) * 10 ^ L)
        (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) (x.regs epoch + 1) (10 ^ L) ∅ ∧
      (∀ j < 3, y.mem (f + 4 * d + j) = x.mem (f + 4 * d + j)) ∧
      y.mem (f + 4 * d + 3) = k + 1 ∧
      Modifies (emptyChildWrites L f d) x.mem y.mem := by
  have hpow : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hL : L + 1 ≤ (L + 1) * 10 ^ L := by nlinarith only [hpow]
  obtain ⟨v, hstep, _, hvf, hvl, _, _, _, hvt, hva, hve,
      hv0, hv1, hv4, _, hvc, htable, hscanMod⟩ :=
    exec_loadScanChild x hregs hd hdL hm hN hcap hterm hk input hinput hcodes hmarks hw
  rw [hempty] at hvc htable
  simp only [Finset.card_empty] at hvc
  obtain ⟨y, hy, _, hym, hmem, _⟩ := exec_advance v hv1 hv4
    (hw.of_le (by rw [hvt]; omega)) (hw.of_le (by rw [hvf]; nlinarith only [hL, hdL]))
  have hskip : ExecWithin w
      (ram[ if nil < childCount then [ ⟪push⟫ ] else [ ⟪advance⟫ ] ]) v y 7 :=
    hy.branch_neg (by simp only [Cond.holds_lt, hv0, hvc, lt_self_iff_false, not_false_eq_true])
  have he : ExecWithin w step x y (20 * N + 33) := (hstep hskip).mono (by omega)
  have hmem' : y.mem = Function.update v.mem (f + 4 * d + 3) (k + 1) := by
    simpa only [hvf, hvt] using hmem
  have hframe : Modifies (Block.mk (f + 4 * d) 4).footprint v.mem y.mem := by
    rw [hmem']
    exact Modifies.write_of_owns (by constructor <;> omega) _
  obtain ⟨hymem, hymod, hbelow⟩ := postScan_memory htable hscanMod hframe (by omega)
  refine ⟨y, he, hregs.of_step he,
    (hy.regs_eq (by decide : advance.Preserves level)).trans hvl, hym,
    (hy.regs_eq (by decide : advance.Preserves active)).trans hva,
    (hy.regs_eq (by decide : advance.Preserves epoch)).trans hve,
    hymem, ?_, by simp only [hmem', Function.update_self], hymod⟩
  intro j hj
  rw [hmem', Function.update_of_ne (by omega : f + 4 * d + j ≠ f + 4 * d + 3)]
  exact hbelow _ (by omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
