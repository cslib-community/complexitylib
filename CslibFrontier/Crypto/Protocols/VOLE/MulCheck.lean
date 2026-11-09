/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.VOLE.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Roots

/-!
# Soundness of the VOLE multiplication check

For authenticated values `x`, `y`, `z`, the receiver checks that
`w_x * w_y - w_z * delta = a * delta + b`. The sender may choose arbitrary coefficients
`a`, `b`, rather than the honest `voleMulCrossTerm` and `voleMulConstTerm`. If `x * y ≠ z`,
the check is a nonzero quadratic in the secret key `delta`, hence accepts at at most two keys.

## Main results

* `card_filter_voleMulCheck_le_two`: a false multiplication has at most two accepting keys.
* `toOuterMeasure_voleMulCheck_le`: a fixed false claim passes with probability at most `2 / |F|`.
* `toOuterMeasure_voleMulCheck_bind_le`: the same bound for arbitrary randomized sender state,
  sampled before the independent uniform key. The state determines values, masks and coefficients.

These are original root-count consequences of `voleMulCheck_sub_eq`, not security of an entire
VOLE-based ZK protocol. There is no efficiency claim. In particular, the sender cannot choose its
coefficients after seeing the receiver's key or tags. Over a field with two elements the bound is
one, and false claims can indeed pass at every key.
-/

public section

namespace Cslib.Crypto.Protocols.VOLE

open Probability Polynomial
open scoped ENNReal

universe u

variable {F : Type u} [Field F]

/-- A false multiplication check with arbitrary fixed affine coefficients accepts at at most
two secret keys. Values, masks and coefficients are all fixed before varying the key. -/
theorem card_filter_voleMulCheck_le_two [Fintype F] [DecidableEq F]
    {x y z : F} (v_x v_y v_z a b : F) (hfalse : x * y ≠ z) :
    (Finset.univ.filter fun delta : F =>
      (x * delta + v_x) * (y * delta + v_y) - (z * delta + v_z) * delta =
        a * delta + b).card ≤ 2 := by
  let p : Polynomial F := C (x * y - z) * X ^ 2 +
    C (voleMulCrossTerm x v_x y v_y v_z - a) * X + C (voleMulConstTerm v_x v_y - b)
  have hp : p ≠ 0 := by
    intro h
    have hd := natDegree_quadratic (b := voleMulCrossTerm x v_x y v_y v_z - a)
      (c := voleMulConstTerm v_x v_y - b) (sub_ne_zero.mpr hfalse)
    change p.natDegree = 2 at hd
    simp [h] at hd
  have hsub : (Finset.univ.filter fun delta : F =>
      (x * delta + v_x) * (y * delta + v_y) - (z * delta + v_z) * delta =
        a * delta + b) ⊆ p.roots.toFinset := by
    intro delta hdelta
    have hc := (Finset.mem_filter.mp hdelta).2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot]
    have hid := voleMulCheck_sub_eq (x := x) (y := y) (z := z)
      (v_x := v_x) (v_y := v_y) (v_z := v_z) (delta := delta) rfl rfl rfl
    simp only [p, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    linear_combination hid.symm + hc
  exact (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' p).trans natDegree_quadratic_le))

/-- A false multiplication with arbitrary fixed affine coefficients passes the check under a
uniform secret key with probability at most `2 / |F|`. -/
theorem toOuterMeasure_voleMulCheck_le [Fintype F]
    {x y z : F} (v_x v_y v_z a b : F) (hfalse : x * y ≠ z) :
    (PMF.uniformOfFintype F).toOuterMeasure
      {delta | (x * delta + v_x) * (y * delta + v_y) - (z * delta + v_z) * delta =
        a * delta + b} ≤ 2 / (Fintype.card F : ℝ≥0∞) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype, div_eq_mul_inv]
  gcongr
  exact_mod_cast card_filter_voleMulCheck_le_two v_x v_y v_z a b hfalse

/-- Soundness for an arbitrary randomized sender. Its state `s` determines the values, masks,
and claimed affine coefficients before an independent uniform key is sampled. The bad event
includes the failed multiplication constraint, so no assumption on the sender's support is needed.
This experiment gives the sender no receiver key or tags before fixing its claim. -/
theorem toOuterMeasure_voleMulCheck_bind_le [Fintype F] {S : Type u} (sender : PMF S)
    (x y z v_x v_y v_z a b : S → F) :
    (do
      let s ← sender
      let delta ← PMF.uniformOfFintype F
      return (s, delta)).toOuterMeasure
      {r | x r.1 * y r.1 ≠ z r.1 ∧
        (x r.1 * r.2 + v_x r.1) * (y r.1 * r.2 + v_y r.1) -
          (z r.1 * r.2 + v_z r.1) * r.2 = a r.1 * r.2 + b r.1} ≤
        2 / (Fintype.card F : ℝ≥0∞) := by
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.toOuterMeasure_bind_apply]
  refine PMF.tsum_mul_le_of_forall_le sender fun s => ?_
  change ((PMF.uniformOfFintype F).map (fun delta => (s, delta))).toOuterMeasure _ ≤ _
  rw [PMF.toOuterMeasure_map_apply]
  by_cases hfalse : x s * y s ≠ z s
  · refine le_trans (MeasureTheory.measure_mono ?_)
      (toOuterMeasure_voleMulCheck_le (v_x s) (v_y s) (v_z s) (a s) (b s) hfalse)
    intro delta hdelta
    exact hdelta.2
  · simp [hfalse]

end Cslib.Crypto.Protocols.VOLE
