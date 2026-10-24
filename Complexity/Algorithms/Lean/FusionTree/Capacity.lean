/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.FusionTree.Tree
import Mathlib.Tactic.Ring

/-!
# Word-size-dependent fusion-tree capacity

A power-of-two branching factor leaves explicit slack for checked arithmetic. Above width
512, `16B⁵ ≤ w`; below that threshold the branching factor is two. In both regimes the
constructed tree has height at most `14 (1 + log_w n)`, with one constant for all widths.
These are arithmetic and tree-height bounds, not an instruction-count certificate.

## Main definitions

* `branching`: the chosen capacity, always at least two.

## Main results

* `branching_capacity`: quantitative room for packed sketches at large widths.
* `height_build_branching_le`: the desired word-logarithmic height bound.
* `packed_width_le`: both packed-comparison products fit a physical word.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.FusionTree

/-- Below width 512, binary branching suffices up to a uniform constant. At larger widths,
the exponent leaves four bits of slack for the fifth-power capacity bound. -/
def branching (w : ℕ) : ℕ :=
  if 9 ≤ Nat.log 2 w then 2 ^ ((Nat.log 2 w - 4) / 5) else 2

/-- The fusion-tree branching factor `branching w` is always at least `2`. -/
theorem two_le_branching (w : ℕ) : 2 ≤ branching w := by
  unfold branching
  split
  · rename_i hw
    have hk : 1 ≤ (Nat.log 2 w - 4) / 5 := by omega
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
  · exact le_rfl

/-- Large-width nodes have slack for compression and both rank multiplications. -/
theorem branching_capacity {w : ℕ} (hw : 9 ≤ Nat.log 2 w) :
    16 * branching w ^ 5 ≤ w := by
  have hw0 : w ≠ 0 := by intro he; simp [he] at hw
  rw [branching, ite_eq_left hw, ← pow_mul, show 16 = 2 ^ 4 by decide, ← pow_add]
  exact (Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.pow_log_le_self 2 hw0)

/-- One comparison of bases works uniformly in the small- and large-width regimes. -/
private theorem word_le_branching_pow (w : ℕ) : w ≤ branching w ^ 14 := by
  have hupper := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) w).le
  unfold branching
  split
  · rename_i hw
    rw [← pow_mul]
    apply hupper.trans
    apply Nat.pow_le_pow_right (by decide)
    have hdiv := Nat.div_add_mod (Nat.log 2 w - 4) 5
    have hmod := Nat.mod_lt (Nat.log 2 w - 4) (by decide : 0 < 5)
    omega
  · rename_i hw
    exact hupper.trans (Nat.pow_le_pow_right (by decide) (by omega))

/-- A single constant bounds the constructed tree's word-logarithmic height, including empty
and singleton inputs. Predecessor runtime still requires a constant-time node implementation. -/
theorem height_build_branching_le {w : ℕ} (hw : 2 ≤ w) (xs : List ℕ) :
    (Tree.build (branching w) xs).height ≤ 14 * (Nat.log w xs.length + 1) := by
  apply (Tree.height_build_le _ _).trans
  apply (Nat.clog_le_iff_le_pow (show 1 < branching w by have := two_le_branching w; omega)).mpr
  calc
    xs.length ≤ w ^ (Nat.log w xs.length + 1) :=
      (Nat.lt_pow_succ_log_self hw xs.length).le
    _ ≤ (branching w ^ 14) ^ (Nat.log w xs.length + 1) :=
      Nat.pow_le_pow_left (word_le_branching_pow w) _
    _ = branching w ^ (14 * (Nat.log w xs.length + 1)) := (pow_mul _ _ _).symm

/-- At large widths, a node with at most `B` keys and at most `B` relevant bits has enough
room for fields of width `2r⁴+1` and the complete count product. -/
theorem packed_width_le {w n r : ℕ} (hw : 9 ≤ Nat.log 2 w)
    (hn : n ≤ branching w) (hr : r ≤ branching w) :
    2 * ((2 * r ^ 4 + 1) * n) ≤ w := by
  have hB := two_le_branching w
  have hp : 0 < branching w ^ 4 := Nat.pow_pos (by omega)
  have hr' := Nat.pow_le_pow_left hr 4
  have hcoef : 2 * r ^ 4 + 1 ≤ 3 * branching w ^ 4 := by omega
  calc
    2 * ((2 * r ^ 4 + 1) * n) ≤ 2 * ((3 * branching w ^ 4) * branching w) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul hcoef hn)
    _ = 6 * branching w ^ 5 := by ring
    _ ≤ 16 * branching w ^ 5 := Nat.mul_le_mul_right _ (by decide)
    _ ≤ w := branching_capacity hw

/-- The same packed-width slack puts the entire compressed window in a single product limb. -/
theorem compression_window_le {w n r : ℕ} (hw : 9 ≤ Nat.log 2 w)
    (hn0 : 0 < n) (hn : n ≤ branching w) (hr : r ≤ branching w) :
    2 * r ^ 4 + (w - 2 * (w / 2)) ≤ w / 2 := by
  have hpacked := packed_width_le hw hn hr
  have hm := Nat.mul_le_mul_left (2 * r ^ 4 + 1) (show 1 ≤ n by omega)
  simp only [mul_one] at hm
  omega

end Cslib.Algorithms.Lean.FusionTree
