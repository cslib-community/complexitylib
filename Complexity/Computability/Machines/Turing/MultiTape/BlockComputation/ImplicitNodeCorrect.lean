/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ImplicitNode
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.EncodedTree

/-!
# Implicit node tags agree with the existing Boolean tree

Classification reports the kind of the existing `encodedTree` node reached by the typed path.
The proof reuses the descending-tree lookup theorem, including uniform-height source padding
and rejection of paths beyond the horizon.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ImplicitNode

open Cslib.TreeEval.Ary

/-- Native raw-path classification agrees with the existing encoded tree's node tag. -/
theorem classify_eq_nodeAt {k q s : ℕ} {Q : Type}
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ) (path : List (Fin (k * 3 + 1))) :
    classify k (σ, q, path.map Fin.val) =
      kind ((encodedTree (MultiTapePTM.ofDeterministic M) w b
        (scheduleOfNat k q σ) e).nodeAt path) := by
  have hall : (path.map Fin.val).all (fun j => decide (j < k * 3 + 1)) = true := by
    apply List.all_eq_true.mpr
    intro j hj
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hj
    exact decide_eq_true p.isLt
  have hv : ImplicitPath.valid k (σ, q, path.map Fin.val) =
      decide (path.length ≤ q) := by
    simp only [ImplicitPath.valid, List.length_map, hall, Bool.and_true]
  rw [encodedTree, tree, Descending.nodeAt_tree]
  simp only [classify, hv, List.length_map, decide_eq_true_eq, Descending.lookup]
  by_cases hlt : path.length < q
  · have hle : path.length ≤ q := hlt.le
    have hne : path.length ≠ q := by omega
    simp only [hlt, hle, hne, ↓reduceIte, kind]
  · by_cases heq : path.length = q
    · simp [heq, kind]
    · have hle : ¬path.length ≤ q := by omega
      simp only [hlt, hle, heq, ↓reduceIte, kind]

end Turing.MultiTapePTM.BlockComputation.ImplicitNode
