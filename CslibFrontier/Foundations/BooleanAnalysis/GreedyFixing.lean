/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fibers
public import CslibFrontier.Foundations.Combinatorics.PessimisticEstimator
import CslibFrontier.Foundations.BooleanAnalysis.Decomposition
import Mathlib.Tactic.Linarith

/-!
# Greedy fixing of coordinates by conditional expectations

The method of conditional expectations on the cube `ι → Bool`. A state is a point `x` together
with a set `sel` of coordinates that have been fixed; the conditional expectation of `f` given
the fixed coordinates is `projectionAverage f sel x`, the average of `f` over the coordinates
outside `sel`. Fixing a free coordinate to `false` and to `true` splits this average into two
halves (`Cslib.BitString.projectionAverage_fixCoord_false_add_true`), so the larger of the two
is at least the current average. Fixing the coordinates one at a time, each to the value of
larger conditional expectation, therefore ends at a point where `f` is at least its mean
(`Cslib.BitString.expect_le_greedy_fixCoord`)
[Alon and Spencer, Chapter 16][AlonSpencer2016]
[Williamson and Shmoys, Section 5.2][WilliamsonShmoys2011].

This is the exact form of the method, the instance of `Cslib.PessimisticEstimator.greedy` in
which the estimate is the conditional expectation itself
(`Cslib.PessimisticEstimator.greedy_spec_of_add_le`). Clients for which the conditional
expectation is expensive use a pessimistic estimator instead, as Johnson's algorithm does in
`CslibFrontier.Logics.Propositional.CNF.Johnson`.

## Main definitions

* `Cslib.BitString.fixCoord`: fix one coordinate of a point and mark it as fixed.

## Main results

* `Cslib.BitString.projectionAverage_fixCoord_false_add_true`: fixing a free coordinate splits
  the conditional expectation into two halves.
* `Cslib.BitString.expect_le_greedy_fixCoord`: greedy fixing by conditional expectations reaches
  a point where `f` is at least its mean.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Chapter 16][AlonSpencer2016]
* [D. P. Williamson, D. B. Shmoys, *The Design of Approximation Algorithms*,
  Section 5.2][WilliamsonShmoys2011]
-/

public section

namespace Cslib.BitString

open Finset Function PessimisticEstimator
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fix coordinate `i` of the point `s.1` to `b` and add `i` to the fixed coordinates `s.2`. -/
@[expose] def fixCoord (i : ι) (b : Bool) (s : (ι → Bool) × (ι → Bool)) :
    (ι → Bool) × (ι → Bool) :=
  (update s.1 i b, update s.2 i true)

/-- Fixing a free coordinate `i` to `false` and to `true` splits the conditional expectation of
`f` given the fixed coordinates `sel` into two halves. -/
theorem projectionAverage_fixCoord_false_add_true (f : (ι → Bool) → ℝ) {i : ι}
    (x sel : ι → Bool) (hi : sel i = false) :
    projectionAverage f (update sel i true) (update x i false) +
        projectionAverage f (update sel i true) (update x i true) =
      2 * projectionAverage f sel x := by
  unfold projectionAverage
  rw [← expect_add_distrib, ← expect_update_false_add_update_true (i := i)]
  refine expect_congr rfl fun y _ => ?_
  have key (b : Bool) : resample (update sel i true) y (update x i b) =
      resample sel (update y i b) x := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [resample, hi]
    · simp [resample, Set.piecewise, update_of_ne hj]
  rw [key, key]

/-- **Greedy fixing by conditional expectations.** Starting from any point with no fixed
coordinates, fix the coordinates of a list without repetitions that covers every coordinate one
at a time, each to the value of larger conditional expectation of `f` (minimizing its negation).
The resulting point is one where `f` is at least its mean. -/
theorem expect_le_greedy_fixCoord (f : (ι → Bool) → ℝ) (coords : List ι) (hnd : coords.Nodup)
    (hcov : ∀ i, i ∈ coords) (x : ι → Bool) :
    𝔼 y, f y ≤ f (greedy fixCoord (fun s => -projectionAverage f s.2 s.1) coords
      (x, fun _ => false)).1 := by
  set Φ : (ι → Bool) × (ι → Bool) → ℝ := fun s => -projectionAverage f s.2 s.1
  let Inv : List ι → (ι → Bool) × (ι → Bool) → Prop := fun rs s =>
    rs.Nodup ∧ ∀ i, s.2 i = !decide (i ∈ rs)
  have hbranch : ∀ r rs s b, Inv (r :: rs) s → Inv rs (fixCoord r b s) := by
    rintro r rs ⟨x, sel⟩ b ⟨hnd, hsel⟩
    refine ⟨(List.nodup_cons.1 hnd).2, fun i => ?_⟩
    by_cases hi : i = r
    · subst hi
      simp [fixCoord, (List.nodup_cons.1 hnd).1]
    · simpa [fixCoord, update_of_ne hi, hi] using hsel i
  have havg : ∀ r rs s, Inv (r :: rs) s →
      Φ (fixCoord r true s) + Φ (fixCoord r false s) ≤ Φ s + Φ s := by
    rintro r rs ⟨x, sel⟩ ⟨-, hsel⟩
    have h := projectionAverage_fixCoord_false_add_true f x sel (i := r) (by simpa using hsel r)
    simp only [Φ, fixCoord]
    linarith
  have hinit : Inv coords (x, fun _ => false) := ⟨hnd, fun i => by simp [hcov i]⟩
  obtain ⟨⟨-, hend⟩, hle⟩ := greedy_spec_of_add_le fixCoord Φ Inv hbranch havg coords _ hinit
  set e := greedy fixCoord Φ coords (x, fun _ => false)
  have hsel : e.2 = fun _ => true := funext fun i => by simp [hend i]
  have h0 : Φ (x, fun _ => false) = -𝔼 y, f y := by
    simp only [Φ, projectionAverage, resample_false]
  have h1 : Φ e = -f e.1 := by
    simp only [Φ, projectionAverage, hsel, resample_true, expect_const univ_nonempty]
  linarith

end Cslib.BitString
