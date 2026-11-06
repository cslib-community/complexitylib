/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.Exec
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.InputLayout
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Resources

/-!
# Sparse work summed over a native query batch

All wanted outputs of the same inner dimension have the same alpha-controlled query
allowance. The actual batch adds six instructions per request and one final loop exit.
Preparation remains outside this allowance and is charged once by the initialized client.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch

open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The native batch allowance scales with the number of wanted outputs, including duplicates,
and sparse alpha counts. There is no dense encoding-span scan per wanted query. -/
theorem queryTime_eq_alpha {L m t : ℕ} (qs : List (OutStr L))
    (hη : ∀ η ∈ qs, (innerSetO η).card = m) :
    queryTime m t qs = qs.length *
      (258 * (L + 1) * (∑ d ∈ Finset.range (t + 1), alpha m d) + 34) + 2 := by
  induction qs with
  | nil => simp [queryTime]
  | cons η qs ih =>
    have hhead := BoxQuery.queryTime_eq_alpha t η (hη η (by simp))
    have htail := ih (by intro η h; exact hη η (by simp [h]))
    simp only [queryTime, List.map_cons, List.sum_cons] at htail ⊢
    rw [hhead]
    simp only [List.length_cons]
    nlinarith

/-- Shared construction is charged once for the entire wanted batch. Its table term
retains the existing beta bound, separately from every sparse query charge. -/
theorem preparationTime_le (L m t : ℕ) (hm : m ≤ L) (ht : t ≤ m) :
    preparationTime L m t ≤ 4 * L + 21 + 64 * (L + 1) ^ 2 * 10 ^ L +
      328 * (m + 1) * (∑ d ∈ Finset.Icc t m, beta L m d) + 20 := by
  have h := BoxQuery.preparationTime_le L m t hm ht
  unfold preparationTime
  omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch
