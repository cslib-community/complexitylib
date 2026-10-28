/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Ready
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.NodeFrame

/-!
# Stored partial sums between native child calls

## Main definitions

* `PrunedQuery.NodeProgress`: the actual dispatch cursor, frame, directory and partial values.

## Main results

* `PrunedQuery.exec_ready_enter`: native entry establishes the zero-term invariant.

This is an invariant of the existing finite controller. It contains ordinary register and memory
equalities, not assumed executions or resource bounds. The timestamp directory is shared by all
nodes, so the parent retains its list but does not retain a stale membership-marker assertion.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Progress after `k` of the ten actual child dispatches. The initial state is kept only to
express the concrete spatial frame and preservation of its occupied request list. -/
structure NodeProgress (L f a0 b0 n d p E : ℕ) (S : Finset (OutStr (n + 1)))
    (a b : Leaf (n + 1) → ℤ) (x : Data registers) (k : ℕ) (y : Data registers) : Prop where
  /-- The constants and workspace pointers are unchanged. -/
  regs : KernelRegs L f a0 b0 y
  /-- The cursor is at this internal node. -/
  level_eq : y.regs level = d
  /-- The next controller step dispatches the stored term. -/
  mode_eq : y.regs mode = 1
  /-- A dispatching node is active. -/
  active_eq : y.regs active = 1
  /-- The first three frame words survive all child returns. -/
  frame : (Block.mk (f + 4 * d) 4).Realizes y.mem ![S.card, p, 10 ^ d, k]
  /-- The parent's requests remain in the actual original row. -/
  requests : ∀ i < S.card,
    y.mem (f + 4 * (L + 1) + d * 10 ^ L + i) =
      x.mem (f + 4 * (L + 1) + d * 10 ^ L + i)
  /-- Every requested accumulator holds the completed prefix of terms. -/
  values : ∀ q ∈ S,
    y.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L + (queryIndex q).val) =
      encode (partialValue a b S q k)
  /-- Native scans only increase the generation. -/
  epoch_le : E ≤ y.regs epoch
  /-- Each completed term pays for its scan and its possible descendant calls. -/
  epoch_upper : y.regs epoch ≤ E + k * (1 + epochAllowance n)
  /-- All directory cells admit a further fresh generation. -/
  timestamps : ∀ q < 10 ^ L,
    y.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) ≤ y.regs epoch
  /-- Only the explicit descendant workspace may have changed. -/
  footprint : Modifies (nodeWrites L f d) x.mem y.mem

/-- The native scan's quotient image is the existing mathematical child set, even though
the shared timestamp directory no longer marks the parent's membership. -/
theorem NodeProgress.scan_eq {L f a0 b0 n d p E k : ℕ} {S : Finset (OutStr (n + 1))}
    {a b : Leaf (n + 1) → ℤ} {x y : Data registers}
    (hx : NodeReady L f a0 b0 (n + 1) d p E S x)
    (hy : NodeProgress L f a0 b0 n d p E S a b x k y) (t : Fin 10) :
    scanSet true t.val (fun i => y.mem (f + 4 * (L + 1) + d * 10 ^ L + i)) S.card =
      (childSet S (Encoding.termDigits t)).image (fun q => (queryIndex q).val) := by
  rw [scanSet_child]
  have he : (Finset.range S.card).image
      (fun i => y.mem (f + 4 * (L + 1) + d * 10 ^ L + i)) =
        (Finset.range S.card).image
          (fun i => x.mem (f + 4 * (L + 1) + d * 10 ^ L + i)) :=
    Finset.image_congr (fun i hi => hy.requests i (Finset.mem_range.mp hi))
  rw [he, hx.image_read, childCodes_eq_image]

/-- Before a dispatch, the original scalar budget covers the fresh scan and every possible
descendant generation for that term. -/
theorem NodeProgress.epoch_child_le {L f a0 b0 n d p E k : ℕ}
    {S : Finset (OutStr (n + 1))} {a b : Leaf (n + 1) → ℤ} {x y : Data registers}
    (hy : NodeProgress L f a0 b0 n d p E S a b x k y) (hk : k < 10) :
    y.regs epoch + 1 + epochAllowance n ≤ E + epochAllowance (n + 1) := by
  have hp := mul_epochAllowance_le (n := n) (by omega : k + 1 ≤ 10)
  nlinarith only [hy.epoch_upper, hp]

/-- Entry performs the actual frame loads, clear loop and term store. The same returned state
has zero partial sums and the original request list, including when that list is empty. -/
theorem exec_ready_enter {w L f a0 b0 n d p E : ℕ} (S : Finset (OutStr (n + 1)))
    (a b : Leaf (n + 1) → ℤ) (x : Data registers)
    (hx : NodeReady L f a0 b0 (n + 1) d p E S x)
    (hfit : Fits w (nodeBudget L f a0 b0 E (n + 1))) :
    ∃ y, ExecWithin w step x y (7 * S.card + 28) ∧
      NodeProgress L f a0 b0 n d p E S a b x 0 y := by
  have hd : d < L := by have := hx.depth_add; omega
  have hpow : (10 : ℕ) ^ (n + 1) ≤ 10 ^ L :=
    Nat.pow_le_pow_right (by decide) (by have := hx.depth_add; omega)
  let input := fun i => x.mem (f + 4 * (L + 1) + d * 10 ^ L + i)
  have hcodes : ∀ i < S.card, input i < 10 ^ L :=
    fun i hi => (hx.read_lt hi).trans_le hpow
  obtain ⟨y, hy, hregs, hlevel, hmode, hE, hactive, hmem, hread, hframe⟩ :=
    exec_node_enter (N := S.card) x hx.regs hx.level_eq hd hx.mode_eq (hx.frame 0) hx.card_le
      input (fun _ _ => rfl) hcodes (hfit.of_le (by unfold nodeBudget; omega))
  have hrow (j : ℕ) (hj : j < 4) :
      ¬(Block.mk (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L)
        (10 ^ L)).Owns (f + 4 * d + j) := by
    dsimp only [Block.Owns]
    omega
  have hstamp (q : ℕ) :
      ¬(Block.mk (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L)
        (10 ^ L)).Owns (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) := by
    dsimp only [Block.Owns]
    have hm := Nat.mul_le_mul_right (10 ^ L) (by omega : d + 1 ≤ L + 1)
    rintro ⟨_, hlt⟩
    nlinarith only [hm, hlt]
  refine ⟨y, hy, ⟨hregs, hlevel, hmode, hactive.trans hx.active_eq, ?_, hread, ?_,
    ?_, ?_, ?_, hframe⟩⟩
  · intro j
    change y.mem (f + 4 * d + j.val) = ![S.card, p, 10 ^ d, 0] j
    rw [hmem]
    fin_cases j
    · change Function.update (_ : ℕ → ℕ) (f + 4 * d + 3) 0 (f + 4 * d + 0) = S.card
      rw [Function.update_of_ne (by omega), zeroQueryPrefix_outside hcodes (hrow 0 (by decide))]
      exact hx.frame 0
    · change Function.update (_ : ℕ → ℕ) (f + 4 * d + 3) 0 (f + 4 * d + 1) = p
      rw [Function.update_of_ne (by omega), zeroQueryPrefix_outside hcodes (hrow 1 (by decide))]
      exact hx.frame 1
    · change Function.update (_ : ℕ → ℕ) (f + 4 * d + 3) 0 (f + 4 * d + 2) = 10 ^ d
      rw [Function.update_of_ne (by omega), zeroQueryPrefix_outside hcodes (hrow 2 (by decide))]
      exact hx.frame 2
    · exact Function.update_self _ _ _
  · intro q hq
    obtain ⟨i, hi, hqi⟩ := hx.exists_read hq
    have hval : f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L +
        (queryIndex q).val ≠ f + 4 * d + 3 := by omega
    rw [hmem, Function.update_of_ne hval, partialValue_zero, show encode 0 = 0 from rfl]
    rw [← hqi]
    exact zeroQueryPrefix_at hi
  · rw [hE, hx.epoch_eq]
  · simp only [Nat.zero_mul, Nat.add_zero, hE, hx.epoch_eq, le_refl]
  · intro q hq
    rw [hmem, Function.update_of_ne (by omega), zeroQueryPrefix_outside hcodes (hstamp q),
      hE, hx.epoch_eq]
    exact hx.requests.stamp_le q hq

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
