/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Tournament

/-!
# Superquadratic sensitivity separation: recursive children

This file counts the child positions read by a single row clause: the `r` target children of its own
row together with one labeled gate child for each out-neighbour. These two sets are disjoint because
tournaments are loopless, so the clause of row `i` reads `r + d` children, where `d` is the
outdegree of `i`.

## Main definitions

* `rowChildren`: the child positions `(j, c)` read by the clause of row `i`.

## Main results

* `rowChildren_card`: the clause of row `i` reads `r + d` children, where `d` is the outdegree of
  `i`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/RecursiveChildren.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

open scoped Classical in
/-- Child positions used by a row clause, including its targets and outgoing gates. -/
def rowChildren {k r : ℕ} (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (i : Fin k) : Finset (Fin k × Fin r) :=
  Finset.univ.image (fun c => (i, c)) ∪
    (Finset.univ.filter (T.Adj i)).image (fun j => (j, label i j))

open scoped Classical in
/-- The target positions `(i, c)` of row `i` are disjoint from its gate positions `(j, label i j)`
for the out-neighbours `j` of `i`. -/
private theorem rowChildren_disjoint {k r : ℕ} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (i : Fin k) :
    Disjoint (Finset.univ.image fun c => (i, c))
      ((Finset.univ.filter (T.Adj i)).image fun j => (j, label i j)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hq
  have hji : j = i := congrArg Prod.fst he
  exact T.loopless i (hji ▸ (Finset.mem_filter.mp hj).2)

open scoped Classical in
/-- The clause of row `i` reads exactly `r + d` child positions, where `d` is the outdegree of `i`.
-/
theorem rowChildren_card {k r : ℕ} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (i : Fin k) :
    (rowChildren T label i).card = r + (Finset.univ.filter (T.Adj i)).card := by
  rw [rowChildren, Finset.card_union_of_disjoint (rowChildren_disjoint T label i)]
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  simp

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
