/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Product
import Complexity.Probability.PMF.Bind

/-!
# Guessing after finite leakage

A finite observation multiplies the largest input mass by at most the number of possible
observations. The guessing strategy may be randomized and its output type may be infinite.

## Main results

* `Cslib.Probability.PMF.bind_le_card_mul_of_fiber_subsingleton`: the finite-leakage bound.
* `Cslib.Probability.PMF.tsum_mul_apply_le_card_mul`: guessing a sample from a hint with finitely
  many values, for sources on any type.
* `Cslib.Probability.PMF.uniform_bind_le_div_of_coordinate_subsingleton`: its independent
  uniform-coordinate specialization.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

/-- A randomized test after finite leakage succeeds with probability at most the number of
observations times the largest source mass, when each observation and test output identifies
at most one successful source value. -/
theorem bind_le_card_mul_of_fiber_subsingleton {X Y Z : Type*} [Finite X] [Fintype Y]
    (source : PMF X) (leak : X → Y) (kernel : Y → PMF Z) (event : X → Z → Prop)
    [∀ x z, Decidable (event x z)] {mass : ℝ≥0∞} (hmass : ∀ x, source x ≤ mass)
    (hunique : ∀ y z, Set.Subsingleton {x | leak x = y ∧ event x z}) :
    (source.bind fun x => (kernel (leak x)).map fun z => decide (event x z)) true ≤
      Fintype.card Y * mass := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  have hrow (y : Y) :
      (∑ x : X, if leak x = y then
        ((kernel y).map fun z => decide (event x z)) true else 0) ≤ 1 := by
    have hexpr (x : X) :
        (if leak x = y then ((kernel y).map fun z => decide (event x z)) true else 0) =
          ∑' z, if leak x = y ∧ event x z then kernel y z else 0 := by
      by_cases hx : leak x = y <;> simp [hx, PMF.map_apply]
    simp_rw [hexpr]
    rw [← tsum_fintype (L := .unconditional X), tsum_comm]
    simp only [tsum_fintype]
    calc
      _ ≤ ∑' z, kernel y z := by
        apply tsum_le_tsum
        intro z
        calc
          _ = ∑ x ∈ Finset.univ.filter (fun x => leak x = y ∧ event x z), kernel y z := by
            simp only [Finset.sum_filter]
          _ ≤ 1 * kernel y z := by
            rw [Finset.sum_const]
            simp only [nsmul_eq_mul]
            gcongr
            exact_mod_cast Finset.card_le_one.mpr (fun a ha b hb =>
              hunique y z (by simpa using ha) (by simpa using hb))
          _ = kernel y z := one_mul _
      _ = 1 := (kernel y).tsum_coe
  rw [PMF.bind_apply, tsum_fintype]
  calc
    _ ≤ ∑ x : X, mass * ((kernel (leak x)).map fun z => decide (event x z)) true := by
      gcongr with x
      exact hmass x
    _ = mass * ∑ y : Y, ∑ x : X, if leak x = y then
        ((kernel y).map fun z => decide (event x z)) true else 0 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      simp
    _ ≤ mass * ∑ _y : Y, (1 : ℝ≥0∞) := by
      gcongr with y
      exact hrow y
    _ = Fintype.card Y * mass := by simp [mul_comm]

/-- A guess that depends on a sample only through a hint taking values in a finite set `T` equals
the sample with probability at most `T.card` times the largest source mass. Unlike
`bind_le_card_mul_of_fiber_subsingleton`, the source may live on an infinite type. -/
theorem tsum_mul_apply_le_card_mul {X : Type*} (source : PMF X) {mass : ℝ≥0∞}
    (hmass : ∀ x, source x ≤ mass) {Y : Type*} (hint : X → Y) (T : Finset Y)
    (hT : ∀ x, hint x ∈ T) (guess : Y → PMF X) :
    ∑' x, source x * guess (hint x) x ≤ T.card * mass := by
  calc ∑' x, source x * guess (hint x) x
      ≤ ∑' x, mass * ∑ t ∈ T, guess t x :=
        tsum_le_tsum fun x => mul_le_mul' (hmass x)
          (Finset.single_le_sum (f := fun t => guess t x) (fun _ _ => zero_le) (hT x))
    _ = T.card * mass := by
        rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
        simp only [PMF.tsum_coe, Finset.sum_const, nsmul_eq_mul, mul_one, mul_comm]

/-- A coordinate of independent uniform inputs cannot be predicted from their coordinatewise
finite observations except with probability `|Y| / |X|`. The successful event may depend on all
coordinates and on an arbitrary randomized output, but fixes that coordinate once the other
coordinates and output are fixed. -/
theorem uniform_bind_le_div_of_coordinate_subsingleton
    {ι X Y Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X] [Fintype Y]
    (observe : X → Y) (kernel : (ι → Y) → PMF Z) (event : (ι → X) → Z → Prop)
    [∀ values z, Decidable (event values z)] (j : ι)
    (hunique : ∀ (values : ι → X) z,
      Set.Subsingleton {x | event (Function.update values j x) z}) :
    ((uniformOfFintype (ι → X)).bind fun values =>
      (kernel (observe ∘ values)).map fun z => decide (event values z)) true ≤
        Fintype.card Y / Fintype.card X := by
  classical
  rw [← uniformOfFintype_update (γ := X) j]
  simp only [PMF.bind_bind, PMF.bind_map]
  rw [PMF.bind_comm]
  apply bind_apply_le_on_support
  intro values _
  have hobs (x : X) : observe ∘ Function.update values j x =
      Function.update (observe ∘ values) j (observe x) := by
    funext i
    by_cases hi : i = j <;> simp [hi, Function.comp_def]
  dsimp only [Function.comp_apply]
  simp only [hobs]
  exact (bind_le_card_mul_of_fiber_subsingleton (uniformOfFintype X) observe
    (fun y => kernel (Function.update (observe ∘ values) j y))
    (fun x z => event (Function.update values j x) z)
    (fun x => (uniformOfFintype_apply x).le)
    (fun _ z a ha b hb => hunique values z ha.2 hb.2)).trans_eq (div_eq_mul_inv _ _).symm

end Cslib.Probability.PMF
