/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.CompositionDepth
public import CslibFrontier.Foundations.Data.List.BalancedFold
import Mathlib.Tactic.Ring

/-!
# Combining circuits along a balanced tree

A circuit `op` reading two blocks of `r` inputs and producing `r` outputs combines circuits with `r`
outputs: `op.comp (C.append D)` runs `C` and `D` side by side and feeds their outputs to `op`.
Combining a list of `k` circuits in this way along a balanced binary tree (`Circuit.balanced`, by
`List.balancedFold`) computes the balanced fold of their values under the function of `op`
(`Circuit.eval_balanced`). It uses `k - 1` copies of `op` (`Circuit.size_balanced`) and adds at most
`⌈log₂ k⌉` times the depth of `op` to the depth of the deepest circuit
(`Circuit.depth_balanced_le`). This is how a binary operation, such as the minimum, is computed on
`k` arguments in logarithmic depth, and `Formula.balanced` is its analogue for formulas.

For an empty list the supplied fallback circuit is returned; the nonempty size formula does
not charge the fallback. Appending circuits duplicates their programs, even on shared inputs.

## Main definitions

* `Cslib.Circuits.Circuit.balanced`: circuits combined along a balanced binary tree.

## Main results

* `Cslib.Circuits.Circuit.eval_balanced`: it computes the balanced fold of their values.
* `Cslib.Circuits.Circuit.size_balanced`: its size, for a nonempty list.
* `Cslib.Circuits.Circuit.size_balanced_le`: a uniform bound including the empty fallback.
* `Cslib.Circuits.Circuit.depth_balanced_le`: its depth.

## References

This construction uses the balanced list folds of
`CslibFrontier.Foundations.Data.List.BalancedFold`.
-/

@[expose] public section

namespace Cslib.Circuits.Circuit

variable {σ : Signature} {n r : ℕ} {U : Type*}

/-- The circuits of `l` combined by `op` along a balanced binary tree, or `unit` if `l` is empty:
two circuits `C` and `D` are combined into `op.comp (C.append D)`. -/
def balanced (op : Circuit σ (r + r) r) (unit : Circuit σ n r) (l : List (Circuit σ n r)) :
    Circuit σ n r :=
  l.balancedFold (fun C D => op.comp (C.append D)) unit fun C => C

/-- Circuits combined by `op` along a balanced tree compute the balanced fold of their values under
the function of `op`. -/
theorem eval_balanced (I : Interpretation σ U) (op : Circuit σ (r + r) r) (unit : Circuit σ n r)
    (l : List (Circuit σ n r)) (x : Fin n → U) :
    (balanced op unit l).eval I x =
      l.balancedFold (fun u v => op.eval I (Fin.append u v)) (unit.eval I x)
        fun C => C.eval I x :=
  List.balancedFold_hom (fun C : Circuit σ n r => C.eval I x)
    (op' := fun u v => op.eval I (Fin.append u v)) (fun C D => by rw [eval_comp, eval_append]) l

/-- A nonempty list of `k` circuits combined along a balanced tree uses `k - 1` copies of `op`. -/
theorem size_balanced (op : Circuit σ (r + r) r) (unit : Circuit σ n r)
    {l : List (Circuit σ n r)} (hl : l ≠ []) :
    (balanced op unit l).size = (l.map size).sum + (l.length - 1) * op.size := by
  refine List.balancedFold_induction
    (p := fun l (C : Circuit σ n r) =>
      l ≠ [] → C.size = (l.map size).sum + (l.length - 1) * op.size)
    (fun h => absurd rfl h) (fun C _ => by simp) (fun l₁ l₂ C D h₁ h₂ hC hD _ => ?_) l hl
  obtain ⟨a, ha⟩ : ∃ a, l₁.length = a + 1 :=
    ⟨l₁.length - 1, by have := List.length_pos_iff.2 h₁; omega⟩
  obtain ⟨b, hb⟩ : ∃ b, l₂.length = b + 1 :=
    ⟨l₂.length - 1, by have := List.length_pos_iff.2 h₂; omega⟩
  rw [size_comp, size_append, hC h₁, hD h₂, List.map_append, List.sum_append, List.length_append,
    ha, hb, Nat.add_sub_cancel, Nat.add_sub_cancel, show a + 1 + (b + 1) - 1 = a + b + 1 by omega]
  ring

/-- A uniform gate bound also covering the empty fallback and an unused expensive operator. -/
theorem size_balanced_le (op : Circuit σ (r + r) r) (unit : Circuit σ n r)
    (l : List (Circuit σ n r)) :
    (balanced op unit l).size ≤ unit.size + (l.map size).sum + l.length * op.size := by
  by_cases hl : l = []
  · simp [hl, balanced]
  · rw [size_balanced op unit hl]
    have := Nat.mul_le_mul_right op.size (Nat.sub_le l.length 1)
    omega

/-- **Depth of a balanced tree of circuits.** If every circuit of a list of `k` circuits has depth
at most `D`, then combining them by `op` along a balanced tree gives depth at most
`D + depth op * ⌈log₂ k⌉`. -/
theorem depth_balanced_le (op : Circuit σ (r + r) r) (unit : Circuit σ n r)
    {l : List (Circuit σ n r)} {D : ℕ} (hl : ∀ C ∈ l, C.depth ≤ D)
    (hunit : l = [] → unit.depth ≤ D) :
    (balanced op unit l).depth ≤ D + op.depth * Nat.clog 2 l.length :=
  List.apply_balancedFold_le depth (fun C D' => (depth_comp_le _ _).trans
    ((Nat.add_comm _ _).trans_le (Nat.add_le_add_right (depth_append_le C D') _))) hl hunit

end Cslib.Circuits.Circuit
