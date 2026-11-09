/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Tournament
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Superquadratic sensitivity separation: tournament cyclic

Constructs the cyclic tournament on `Fin (2 * a + 1)`, with an edge `i → j` exactly when the cyclic
difference `(j - i).val` lies between `1` and `a`. Every vertex has outdegree `a`, so taking
`a = M ^ 2` gives a regular tournament on `2 * M ^ 2 + 1` vertices, as required by the recursive
construction.

## Main definitions

* `cyclicTournament`: the cyclic tournament on `Fin (2 * a + 1)`.
* `regularCyclicTournament`: the cyclic tournament on `2 * M ^ 2 + 1` vertices, viewed as a regular
  tournament.

## Main results

* `cyclicTournament_outdegree`: every vertex of `cyclicTournament a` has outdegree `a`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/TournamentCyclic.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- Orient the odd cyclic graph by the first half of the nonzero cyclic differences. -/
def cyclicTournament (a : ℕ) : Tournament (2 * a + 1) where
  Adj i j := 0 < (j-i).val ∧ (j-i).val ≤ a
  loopless i := by simp
  edge_compl := by
    intro i j hij
    have hδ : j-i ≠ 0 := sub_ne_zero.mpr hij.symm
    have hp : 0 < (j-i).val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hδ)
    have hb := (j-i).isLt
    have hn : (i-j).val = 2 * a + 1-(j-i).val := by
      rw [← neg_sub j i, Fin.val_neg, ite_eq_right hδ]
    change (0 < (j-i).val ∧ (j-i).val ≤ a) ↔ ¬ (0 < (i-j).val ∧ (i-j).val ≤ a)
    rw [hn]
    omega

open scoped Classical in
/-- Every vertex of `cyclicTournament a` has exactly `a` outgoing neighbors. -/
theorem cyclicTournament_outdegree (a : ℕ) (i : Fin (2 * a + 1)) :
    (Finset.univ.filter ((cyclicTournament a).Adj i)).card = a := by
  let z : Fin (2 * a + 1) := 0
  let b : Fin (2 * a + 1) := ⟨a, by omega⟩
  have he : (Finset.Ioc z b).card =
      (Finset.univ.filter ((cyclicTournament a).Adj i)).card :=
    Finset.card_equiv (Equiv.addLeft i) (by
      intro x
      simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_univ, true_and]
      change (0 < x.val ∧ x.val ≤ a) ↔
        (0 < ((i + x)-i).val ∧ ((i + x)-i).val ≤ a)
      rw [add_sub_cancel_left])
  rw [← he, Fin.card_Ioc]
  change a - 0 = a
  exact Nat.sub_zero a

/-- The cyclic tournament on `2 * M ^ 2 + 1` vertices has outdegree `M ^ 2`. -/
def regularCyclicTournament (M : ℕ) : RegularTournament M where
  toTournament := cyclicTournament (M ^ 2)
  outdegree := cyclicTournament_outdegree (M ^ 2)

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
