/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product
import CslibFrontier.Probability.PMF.Expect

/-!
# Resampling one coordinate of a product distribution

Holding one coordinate of an independent product fixed is overwriting it after sampling
(`pi_update_pure`). Consequently an average over the product may first draw the whole tuple and
then redraw one coordinate independently (`sum_pi_mul_update`). This is the step that fixes all
coordinates but one in coordinate-wise averaging arguments.

## Main results

* `Cslib.Probability.PMF.pi_update_pure`: fixing a coordinate is overwriting it.
* `Cslib.Probability.PMF.sum_pi_mul_update`: an average over a product equals the average with one
  coordinate redrawn independently.
-/

public section

namespace Cslib.Probability.PMF

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}

/-- Fixing a coordinate of an independent product to `v` is the same as overwriting it with `v`
after sampling. -/
theorem pi_update_pure [∀ i, Finite (α i)] (p : ∀ i, PMF (α i)) (i : ι) (v : α i) :
    pi (Function.update p i (PMF.pure v)) = (pi p).map fun y => Function.update y i v := by
  let overwrite : ∀ j, α j → α j := Function.update (fun j => id) i fun _ => v
  have hlaw : (fun j => (p j).map (overwrite j)) = Function.update p i (PMF.pure v) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [overwrite, Function.update_self]
      exact PMF.map_const (p j) v
    · simp [overwrite, hj, PMF.map_id]
  have hmap : (fun (y : ∀ j, α j) j => overwrite j (y j)) = fun y => Function.update y i v := by
    funext y j
    by_cases hj : j = i
    · subst hj
      simp [overwrite]
    · simp [overwrite, hj]
  rw [← hlaw, pi_map, hmap]

/-- **Resampling a coordinate.** Averaging `F` over an independent product is the same as drawing
a tuple and then redrawing coordinate `i` independently from its own law. -/
theorem sum_pi_mul_update [∀ i, Fintype (α i)] (p : ∀ i, PMF (α i)) (i : ι)
    (F : (∀ j, α j) → ℝ) :
    ∑ y, (pi p y).toReal * F y =
      ∑ y, (pi p y).toReal * ∑ v, (p i v).toReal * F (Function.update y i v) := by
  conv_lhs => rw [← pi_bind_update p i]
  rw [sum_bind_mul]
  simp only [pi_update_pure, sum_map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

end Cslib.Probability.PMF
