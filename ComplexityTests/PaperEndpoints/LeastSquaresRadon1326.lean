/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.RadonGeometry
public import Complexity.Statistics.LeastSquares.NonRange
import Mathlib.Tactic

/-! The general Radon localization theorem applied to the exact six-point source instance. -/

namespace LeastSquaresRadon1326

open Cslib.LeastSquares Matrix

/-- The real coordinates of the preserved exact six-point construction. -/
@[expose] public def point (i : Fin 6) : ℝ × ℝ := ((NonRange.point i).1, (NonRange.point i).2)
private def qlift (i : Fin 6) : Fin 4 → ℚ :=
  ![(NonRange.point i).1 * (NonRange.point i).2, (NonRange.point i).1, (NonRange.point i).2, 1]
private def qgram (s : Finset (Fin 6)) : Matrix s s ℚ :=
  fun i j => qlift i ⬝ᵥ qlift j

-- All 57 subsets of size at most four, including the empty subset, have independent rows.
private theorem determinants : ∀ s : Finset (Fin 6), s.card ≤ 4 → (qgram s).det ≠ 0 := by
  decide +kernel

private theorem cast_lift (i : Fin 6) (k : Fin 4) :
    (qlift i k : ℝ) = Geometry.lift point i k := by
  fin_cases k <;> simp [qlift, Geometry.lift, point]

private theorem general_position : Geometry.LiftedGeneralPosition point := by
  intro s hs
  let L : (Fin 4 → ℝ) →ₗ[ℝ] (s → ℝ) :=
    { toFun := fun v j => v ⬝ᵥ Geometry.lift point j
      map_add' := by intro v w; ext j; exact add_dotProduct _ _ _
      map_smul' := by intro a v; ext j; simp [smul_dotProduct] }
  apply LinearIndependent.of_comp L
  have hdet : ((Rat.castHom ℝ).mapMatrix (qgram s)).det ≠ 0 := by
    rw [← RingHom.map_det]
    change ((qgram s).det : ℝ) ≠ 0
    exact_mod_cast determinants s hs
  have he : ((Rat.castHom ℝ).mapMatrix (qgram s)) =
      fun i j : s => Geometry.lift point i ⬝ᵥ Geometry.lift point j := by
    ext i j
    change ((qlift i ⬝ᵥ qlift j : ℚ) : ℝ) = _
    simp only [dotProduct]
    push_cast
    simp only [cast_lift]
  rw [he] at hdet
  exact linearIndependent_rows_of_det_ne_zero hdet

private theorem scatter_cast (s : Finset (Fin 6)) :
    Geometry.scatter point s = (NonRange.scatter s : ℝ) := by
  unfold Geometry.scatter NonRange.scatter
  push_cast
  rfl

private theorem minimum : Geometry.UniqueMinimum point NonRange.retained := by
  intro s hs hne
  rw [scatter_cast, scatter_cast]
  exact_mod_cast NonRange.nonrange_optimum.2.2.2.1 s hs hne

private theorem nonrange : ¬ Geometry.IsRange point NonRange.retained := by
  rintro ⟨c, hc, hd⟩
  apply NonRange.not_range
  refine ⟨c, ?_⟩
  have he (i : Fin 6) : Geometry.lift point i ⬝ᵥ c = NonRange.planeValue c i := by
    simp [Geometry.lift, point, NonRange.planeValue, dotProduct, Fin.sum_univ_succ]
    ring
  intro i
  constructor
  · intro hi
    exact (he i) ▸ hc i hi
  · intro hi
    by_contra hn
    have hpos := hd i hn
    rw [he] at hpos
    linarith

/-- The paper's six-point optimum instantiates the full general localization theorem. -/
public theorem localized_six_point :
    ∃ W : Geometry.FiveWitness point NonRange.retained, ∃ D : Finset (Fin 6),
    Disjoint NonRange.retained D ∧ (D.card = 2 ∨ D.card = 3) ∧
      (∀ k, W.index k ∈ NonRange.retained ∪ D) ∧
      (∀ T ⊆ NonRange.retained ∪ D, T.card = NonRange.retained.card → T ≠ NonRange.retained →
        Geometry.scatter point NonRange.retained < Geometry.scatter point T) ∧
      ¬ Geometry.IsRangeOn point (NonRange.retained ∪ D) NonRange.retained :=
  minimum.local_witness point NonRange.retained general_position nonrange

-- Its explicit omitted Radon pair is strictly anti-monotone over the reals.
example : ((point 0).1 - (point 3).1) * ((point 0).2 - (point 3).2) = -961/625 := by
  norm_num [point, NonRange.point]

end LeastSquaresRadon1326
