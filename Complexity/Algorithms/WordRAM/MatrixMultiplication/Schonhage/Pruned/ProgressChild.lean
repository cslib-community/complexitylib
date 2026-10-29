/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Progress

/-!
# Child entry established by the native dispatch

## Main results

* `PrunedQuery.exec_progress_child`: an actual nonempty scan and push establishes the next
  induction assertion, with its computed set and prefix.

The finite nonemptiness test is a proof case split. The machine uses the count it computes by
scanning the parent's actual list; that count, its contents and the fresh directory are proved
at the same returned state as the execution.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- A pushed child's strided input cells are the existing `sliceAt`, rather than a supplied
child array. Both preceding native phases preserve the original source block below `f`. -/
theorem NodeProgress.child_source {L f a0 b0 n d p E base : ℕ}
    {S : Finset (OutStr (n + 1))} {a b c : Leaf (n + 1) → ℤ}
    {x y u : Data registers} (hx : NodeReady L f a0 b0 (n + 1) d p E S x) (k : Fin 10)
    (hy : NodeProgress L f a0 b0 n d p E S a b x k.val y)
    (hpush : Modifies (childWrites L f d) y.mem u.mem) (hbase : base + 10 ^ L ≤ f)
    (hc : ∀ v, x.mem (base + p + 10 ^ d * (Encoding.leafIndex v).val) =
      Signed.encode (c v)) (v : Leaf n) :
    u.mem (base + (p + k.val * 10 ^ d) + 10 ^ (d + 1) * (Encoding.leafIndex v).val) =
      Signed.encode (sliceAt c (Encoding.termDigits k) v) := by
  have hd : d < L := by have := hx.depth_add; omega
  let t := Encoding.termDigits k
  have haddr : base + (p + k.val * 10 ^ d) + 10 ^ (d + 1) * (Encoding.leafIndex v).val =
      base + p + 10 ^ d * (Encoding.leafIndex (Fin.cons t v)).val := by
    rw [leafIndex_cons, show Encoding.termDigits.symm t = k from
      Encoding.termDigits.symm_apply_apply k, pow_succ]
    ring
  rw [haddr]
  have hbefore := hx.source_before hbase (Fin.cons t v)
  have hnot := notMem_nodeWrites_before hd.le hbefore
  rw [hpush _ (fun h => hnot (childWrites_subset_nodeWrites hd h)), hy.footprint _ hnot]
  exact hc (Fin.cons t v)

/-- The computed child state satisfies the concrete node-entry assertion and has a budget
derived from the original parent parameters. No child execution is assumed here. -/
theorem exec_progress_child {w L f a0 b0 n d p E : ℕ}
    (S : Finset (OutStr (n + 1))) (a b : Leaf (n + 1) → ℤ) (x y : Data registers)
    (hx : NodeReady L f a0 b0 (n + 1) d p E S x) (k : Fin 10)
    (hy : NodeProgress L f a0 b0 n d p E S a b x k.val y)
    (hne : (childSet S (Encoding.termDigits k)).Nonempty)
    (hfit : Fits w (nodeBudget L f a0 b0 E (n + 1))) :
    ∃ z, ExecWithin w step y z (20 * S.card + 42) ∧
      NodeReady L f a0 b0 n (d + 1) (p + k.val * 10 ^ d) (y.regs epoch + 1)
        (childSet S (Encoding.termDigits k)) z ∧
      Modifies (childWrites L f d) y.mem z.mem ∧
      Fits w (nodeBudget L f a0 b0 (y.regs epoch + 1) n) := by
  have hd : d < L := by have := hx.depth_add; omega
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (10 : ℕ))
    (by have := hx.depth_add; omega : n + 1 ≤ L)
  let input := fun i => y.mem (f + 4 * (L + 1) + d * 10 ^ L + i)
  have hcodes : ∀ i < S.card, input i < 10 ^ L := by
    intro i hi
    exact (hy.requests i hi ▸ hx.read_lt hi).trans_le hpow
  have hscan := hy.scan_eq hx k
  have hnonempty : (scanSet true k.val input S.card).Nonempty := by
    rw [hscan]
    exact hne.image _
  have hE := hy.epoch_child_le k.isLt
  obtain ⟨z, hz, hregs, hlevel, hmode, hactive, hepoch, hrequests, hcount, hpref,
      hstride, hterm, hframe⟩ := exec_node_child (N := S.card) (p := p) (k := k.val) y
    hy.regs hy.level_eq hd hy.mode_eq (hy.frame 0) hx.card_le (hy.frame 1) hx.prefix_lt
    (hy.frame 2) (hy.frame 3) k.isLt input (fun _ _ => rfl) hcodes hy.timestamps
    hnonempty (hfit.of_le (by unfold nodeBudget; omega))
  have hset : ScanMemory z.mem (f + 4 * (L + 1) + (d + 1) * 10 ^ L)
      (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) (y.regs epoch + 1) (10 ^ L)
      ((childSet S (Encoding.termDigits k)).image (fun q => (queryIndex q).val)) := by
    simpa only [input, hscan] using hrequests
  refine ⟨z, hz, ⟨hregs, ?_, ?_, hlevel, hmode, hactive.trans hy.active_eq, hepoch,
    ?_, hset⟩, hframe, hfit.of_le (nodeBudget_child_le hE)⟩
  · have := hx.depth_add
    omega
  · have hp := hx.prefix_lt
    have hk := k.isLt
    rw [pow_succ]
    nlinarith only [hp, hk]
  · intro j
    change z.mem (f + 4 * (d + 1) + j.val) =
      ![(childSet S (Encoding.termDigits k)).card, p + k.val * 10 ^ d, 10 ^ (d + 1), 0] j
    fin_cases j
    · change z.mem (f + 4 * (d + 1)) = (childSet S (Encoding.termDigits k)).card
      simpa only [input, hscan, card_image_queryIndex] using hcount
    · exact hpref
    · exact hstride
    · exact hterm

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
