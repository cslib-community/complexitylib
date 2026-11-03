/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayAssignments
public import Complexity.Computability.TreeEval.Ary.Packed.AssignmentLabelsCorrect

/-!
# Packed assignment labels in block-gate child order

The native assignment reader reconstructs the same previous/provider words as the Boolean
block gate receives after unpacking its row-major interpolation assignment. The preceding
control is child zero; the provider at tape `h` and port `δ` is the successor of the product
index `(h, δ)`. All child words are retained for canonical checking, including unused providers.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Assignments

open Cslib.BitString Cslib.TreeEval.Ary.Packed

/-- The native word family is exactly the packed gate decoder's child family, reordered into
previous control and work-tape providers as in the existing interval gate. -/
theorem labels_eq_unpackBits {k r m b : ℕ} (hb : b ≤ r * m) (hm : 0 < m)
    (counter : ℕ) :
    let words := fun child : Fin (k * 3 + 1) =>
      List.ofFn (unpackBits hb (blocksEquiv (fun q : Fin ((k * 3 + 1) * r) =>
        (⟨gridDigit (2 ^ m) counter q, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ m))) child))
    labels k ((2 ^ m) ^ ((k * 3 + 1) * r), counter, r * m, b) =
      (words 0, fun h δ => words (Fin.succ (finProdFinEquiv (h, δ)))) := by
  apply Prod.ext
  · exact AssignmentLabels.label_eq_ofFn_unpackBits hb hm counter (0 : Fin (k * 3 + 1))
  · funext h δ
    have hindex : 1 + 3 * h.val + δ.val =
        (Fin.succ (finProdFinEquiv (h, δ)) : Fin (k * 3 + 1)).val := by
      simp only [Fin.val_succ, finProdFinEquiv_apply_val]
      omega
    change AssignmentLabels.label (_, _, _, _, 1 + 3 * h.val + δ.val) = _
    rw [hindex]
    exact AssignmentLabels.label_eq_ofFn_unpackBits hb hm counter
      (Fin.succ (finProdFinEquiv (h, δ)) : Fin (k * 3 + 1))

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Assignments
