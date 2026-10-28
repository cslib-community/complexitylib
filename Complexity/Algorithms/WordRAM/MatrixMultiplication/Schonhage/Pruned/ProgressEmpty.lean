/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Progress

/-!
# Skipping a computed empty child

## Main results

* `PrunedQuery.exec_progress_empty`: native scanning and its computed zero count advance the
  partial-sum invariant without a recursive call or a value store.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

private theorem notMem_emptyChildWrites_values {L f d q : ℕ} (hd : d < L)
    (hq : q < 10 ^ L) :
    f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L + q ∉ emptyChildWrites L f d := by
  simp only [emptyChildWrites, Finset.mem_union, Block.mem_footprint, Block.Owns]
  have hm := Nat.mul_le_mul_right (10 ^ L) (by omega : d + 1 ≤ L + 1)
  have hnext : d * 10 ^ L + q < (d + 1) * 10 ^ L := by nlinarith only [hq]
  have hbound := hnext.trans_le hm
  have hsep : (d + 1) * 10 ^ L + 10 ^ L ≤ (L + 1) * 10 ^ L := by
    have := Nat.mul_le_mul_right (10 ^ L) (by omega : d + 2 ≤ L + 1)
    nlinarith only [this]
  rw [show 2 * (L + 1) * 10 ^ L = (L + 1) * 10 ^ L + (L + 1) * 10 ^ L by ring]
  omega

/-- The proof selects the empty mathematical case, and the actual native scan proves that
the machine takes its zero-count branch. Every directory update and loop test is charged. -/
theorem exec_progress_empty {w L f a0 b0 n d p E : ℕ}
    (S : Finset (OutStr (n + 1))) (a b : Leaf (n + 1) → ℤ) (x y : Data registers)
    (hx : NodeReady L f a0 b0 (n + 1) d p E S x) (k : Fin 10)
    (hy : NodeProgress L f a0 b0 n d p E S a b x k.val y)
    (hempty : childSet S (Encoding.termDigits k) = ∅)
    (hfit : Fits w (nodeBudget L f a0 b0 E (n + 1))) :
    ∃ z, ExecWithin w step y z (20 * S.card + 33) ∧
      NodeProgress L f a0 b0 n d p E S a b x (k.val + 1) z := by
  have hd : d < L := by have := hx.depth_add; omega
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (10 : ℕ))
    (by have := hx.depth_add; omega : n + 1 ≤ L)
  let input := fun i => y.mem (f + 4 * (L + 1) + d * 10 ^ L + i)
  have hcodes : ∀ i < S.card, input i < 10 ^ L := by
    intro i hi
    exact (hy.requests i hi ▸ hx.read_lt hi).trans_le hpow
  have hscan : scanSet true k.val input S.card = ∅ := by
    rw [hy.scan_eq hx k, hempty, Finset.image_empty]
  have hE := hy.epoch_child_le k.isLt
  obtain ⟨z, hz, hregs, hlevel, hmode, hactive, hepoch, htable, hfirst, hterm, hframe⟩ :=
    exec_node_emptyChild (N := S.card) (k := k.val) y hy.regs hy.level_eq hd hy.mode_eq
      (hy.frame 0) hx.card_le (hy.frame 3) k.isLt input (fun _ _ => rfl) hcodes
      hy.timestamps hscan (hfit.of_le (by unfold nodeBudget; omega))
  have hmod : Modifies (nodeWrites L f d) y.mem z.mem :=
    fun c hc => hframe c (fun h => hc (emptyChildWrites_subset_nodeWrites hd h))
  refine ⟨z, hz, ⟨hregs, hlevel, hmode, hactive.trans hy.active_eq, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩⟩
  · intro j
    change z.mem (f + 4 * d + j.val) = ![S.card, p, 10 ^ d, k.val + 1] j
    fin_cases j
    · exact (hfirst 0 (by decide)).trans (hy.frame 0)
    · exact (hfirst 1 (by decide)).trans (hy.frame 1)
    · exact (hfirst 2 (by decide)).trans (hy.frame 2)
    · exact hterm
  · intro i hi
    exact (hmod _ (notMem_nodeWrites_list hd.le (hi.trans_le hx.card_le))).trans
      (hy.requests i hi)
  · intro q hq
    have hqbound := (queryIndex q).isLt.trans_le hpow
    rw [hframe _ (notMem_emptyChildWrites_values hd hqbound), hy.values q hq,
      partialValue_succ]
    have hc : Pruned.childResult a b S (Encoding.termDigits k) (Fin.tail q) = 0 := by
      simp [Pruned.childResult, hempty]
    simp only [hc, ite_self, add_zero]
  · rw [hepoch]
    exact hy.epoch_le.trans (Nat.le_succ _)
  · rw [hepoch]
    have he := hy.epoch_upper
    nlinarith only [he]
  · intro q hq
    rw [hepoch]
    exact htable.stamp_le q hq
  · simpa only [Finset.union_self] using hy.footprint.trans hmod

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
