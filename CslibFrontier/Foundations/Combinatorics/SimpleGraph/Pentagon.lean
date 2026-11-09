/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/LovaszTheta.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.LovaszTheta
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Shannon capacity of the pentagon

The five-cycle `C₅ = SimpleGraph.cycleGraph 5` has independence number `2`, but its strong square
has the independent set `{(i, 2i mod 5)}` of size `5` [Shannon1956], so `Θ(C₅) ≥ √5`. Shannon left
the exact value open; Lovász proved `Θ(C₅) = √5` with the *umbrella* orthonormal representation in
`ℝ³` [Lovasz1979Shannon]: the unit vectors
`u i = (5^(-1/4), r cos (2πi/5), r sin (2πi/5))`, `r² = 1 - 1/√5`,
make `⟪u i, u j⟫ = 1/√5 + r² cos (2π(i - j)/5)` vanish when `i - j ≡ ±2 (mod 5)`, because
`cos (4π/5) = -cos (π/5) = -(1 + √5)/4`. With the handle `c = (1, 0, 0)`, `⟪c, u i⟫² = 1/√5`, so
`ϑ(C₅) ≤ √5`. This is the three-dimensional construction of Knuth's notes for odd cycles with
`n = 5` [Knuth1994, §22], up to the relabelling `i ↦ 3i` that maps `C₅` onto its complement.

## Main definitions

* `SimpleGraph.pentagonUmbrella`: Lovász's umbrella, an orthonormal representation of `C₅` in `ℝ³`.

## Main results

* `SimpleGraph.shannonCapacity_cycleGraph_five`: `Θ(C₅) = √5`.
* `SimpleGraph.tendsto_indepNum_strongPow_cycleGraph_five`: `α(C₅ᵏ)^(1/k) → √5`.
* `SimpleGraph.lovaszTheta_cycleGraph_five`: `ϑ(C₅) = √5`.
* `SimpleGraph.indepNum_cycleGraph_five`: `α(C₅) = 2`, so `α(C₅) < Θ(C₅)`.

## References

* [D. E. Knuth, *The sandwich theorem*][Knuth1994]
* [L. Lovász, *On the Shannon capacity of a graph*][Lovasz1979Shannon]
* [C. E. Shannon, *The zero error capacity of a noisy channel*][Shannon1956]
-/

public section

open Filter Topology Real
open scoped RealInnerProductSpace

namespace SimpleGraph

/-- `{(i, 2i mod 5)}` is an independent set of size `5` in the strong square of `C₅`. -/
theorem five_le_indepNum_strongPow_two_cycleGraph_five :
    5 ≤ ((cycleGraph 5).strongPow 2).indepNum := by
  classical
  have hf : Function.Injective (fun i : Fin 5 => ![i, 2 * i]) := by decide
  have hind : ((cycleGraph 5).strongPow 2).IsIndepSet
      (Finset.univ.image fun i : Fin 5 => ![i, 2 * i] : Finset (Fin 2 → Fin 5)) := by
    have : ∀ i j : Fin 5, i ≠ j → ¬((cycleGraph 5).strongPow 2).Adj ![i, 2 * i] ![j, 2 * j] := by
      decide
    intro x hx y hy hxy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact this i j fun h => hxy (h ▸ rfl)
  have := hind.card_le_indepNum
  rwa [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at this

theorem sqrt_five_le_shannonCapacity_cycleGraph_five : √5 ≤ (cycleGraph 5).shannonCapacity := by
  refine le_trans ?_ (rpow_indepNum_strongPow_le_shannonCapacity (G := cycleGraph 5) 1)
  have h5 : (5 : ℝ) ≤ (((cycleGraph 5).strongPow (1 + 1)).indepNum : ℝ) := by
    exact_mod_cast five_le_indepNum_strongPow_two_cycleGraph_five
  rw [Real.sqrt_eq_rpow, show ((((1 : ℕ) : ℝ) + 1)⁻¹ : ℝ) = 1 / 2 by norm_num]
  exact Real.rpow_le_rpow (by norm_num) h5 (by norm_num)

private theorem cos_four_pi_div_five : cos (4 * π / 5) = -cos (π / 5) := by
  rw [show 4 * π / 5 = π - π / 5 by ring, cos_pi_sub]

private theorem cos_six_pi_div_five : cos (6 * π / 5) = -cos (π / 5) := by
  rw [show 6 * π / 5 = π / 5 + π by ring, cos_add_pi]

/-- Lovász's **umbrella**: the orthonormal representation of `C₅` in `ℝ³` whose vectors make the
angle with the handle `(1, 0, 0)` for which nonadjacent vectors are orthogonal. -/
noncomputable def pentagonUmbrella (i : Fin 5) : EuclideanSpace ℝ (Fin 3) :=
  !₂[√(√5)⁻¹, √(1 - (√5)⁻¹) * cos (2 * π * (i : ℕ) / 5),
    √(1 - (√5)⁻¹) * sin (2 * π * (i : ℕ) / 5)]

theorem inner_pentagonUmbrella (i j : Fin 5) :
    ⟪pentagonUmbrella i, pentagonUmbrella j⟫ =
      (√5)⁻¹ + (1 - (√5)⁻¹) * cos (2 * π * (i : ℕ) / 5 - 2 * π * (j : ℕ) / 5) := by
  have h₁ : (√(√5))⁻¹ ^ 2 = (√5)⁻¹ := by rw [inv_pow, Real.sq_sqrt (by positivity)]
  have h₂ : √(1 - (√5)⁻¹) * √(1 - (√5)⁻¹) = 1 - (√5)⁻¹ :=
    Real.mul_self_sqrt (sub_nonneg.2 (inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by norm_num))))
  rw [cos_sub]
  simp only [pentagonUmbrella, PiLp.inner_apply, Fin.sum_univ_three, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, RCLike.inner_apply, conj_trivial, Real.sqrt_inv]
  linear_combination h₁ + (cos (2 * π * (i : ℕ) / 5) * cos (2 * π * (j : ℕ) / 5) +
    sin (2 * π * (i : ℕ) / 5) * sin (2 * π * (j : ℕ) / 5)) * h₂

theorem norm_pentagonUmbrella (i : Fin 5) : ‖pentagonUmbrella i‖ = 1 := by
  have h := inner_pentagonUmbrella i i
  rw [sub_self, cos_zero, mul_one, add_sub_cancel, real_inner_self_eq_norm_sq] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

theorem inner_pentagonUmbrella_eq_zero {i j : Fin 5} (hij : i ≠ j)
    (hadj : ¬(cycleGraph 5).Adj i j) : ⟪pentagonUmbrella i, pentagonUmbrella j⟫ = 0 := by
  have key : (i : ℕ) = j + 2 ∨ (j : ℕ) = i + 2 ∨ (i : ℕ) = j + 3 ∨ (j : ℕ) = i + 3 := by
    revert i j
    decide
  have hc : cos (2 * π * (i : ℕ) / 5 - 2 * π * (j : ℕ) / 5) = -cos (π / 5) := by
    rcases key with h | h | h | h <;> rw [h] <;> push_cast
    · rw [show 2 * π * ((j : ℕ) + 2 : ℝ) / 5 - 2 * π * (j : ℕ) / 5 = 4 * π / 5 by ring,
        cos_four_pi_div_five]
    · rw [show 2 * π * (i : ℕ) / 5 - 2 * π * ((i : ℕ) + 2 : ℝ) / 5 = -(4 * π / 5) by ring,
        cos_neg, cos_four_pi_div_five]
    · rw [show 2 * π * ((j : ℕ) + 3 : ℝ) / 5 - 2 * π * (j : ℕ) / 5 = 6 * π / 5 by ring,
        cos_six_pi_div_five]
    · rw [show 2 * π * (i : ℕ) / 5 - 2 * π * ((i : ℕ) + 3 : ℝ) / 5 = -(6 * π / 5) by ring,
        cos_neg, cos_six_pi_div_five]
  rw [inner_pentagonUmbrella, hc, cos_pi_div_five]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5pos : 0 < √5 := by positivity
  field_simp
  linear_combination -h5

theorem isOrthonormalRepresentation_pentagonUmbrella :
    (cycleGraph 5).IsOrthonormalRepresentation pentagonUmbrella :=
  ⟨norm_pentagonUmbrella, fun _ _ => inner_pentagonUmbrella_eq_zero⟩

/-- The umbrella with handle `(1, 0, 0)` gives `ϑ(C₅) ≤ √5`. -/
theorem lovaszTheta_cycleGraph_five_le : (cycleGraph 5).lovaszTheta ≤ √5 := by
  refine lovaszTheta_le_of_rep isOrthonormalRepresentation_pentagonUmbrella
    (c := EuclideanSpace.single 0 1) (by simp) (by positivity) fun i => ?_
  rw [EuclideanSpace.inner_single_left]
  have h5pos : 0 < √5 := by positivity
  simp [pentagonUmbrella, h5pos.ne']

/-- **Lovász's theorem**: the Shannon capacity of the pentagon is `√5`. -/
theorem shannonCapacity_cycleGraph_five : (cycleGraph 5).shannonCapacity = √5 :=
  le_antisymm (shannonCapacity_le_lovaszTheta.trans lovaszTheta_cycleGraph_five_le)
    sqrt_five_le_shannonCapacity_cycleGraph_five

/-- The limit form of `Θ(C₅) = √5`: `α(C₅ᵏ)^(1/k) → √5`. -/
theorem tendsto_indepNum_strongPow_cycleGraph_five :
    Tendsto (fun k : ℕ => (((cycleGraph 5).strongPow (k + 1)).indepNum : ℝ) ^ ((k + 1 : ℝ)⁻¹))
      atTop (𝓝 √5) :=
  shannonCapacity_cycleGraph_five ▸ (cycleGraph 5).tendsto_shannonCapacity

theorem lovaszTheta_cycleGraph_five : (cycleGraph 5).lovaszTheta = √5 :=
  le_antisymm lovaszTheta_cycleGraph_five_le
    (sqrt_five_le_shannonCapacity_cycleGraph_five.trans shannonCapacity_le_lovaszTheta)

/-- `α(C₅) = 2`: the upper bound follows from `α(C₅) ≤ ϑ(C₅) = √5 < 3`. -/
theorem indepNum_cycleGraph_five : (cycleGraph 5).indepNum = 2 := by
  refine le_antisymm ?_ ?_
  · have h := indepNum_le_lovaszTheta.trans lovaszTheta_cycleGraph_five_le
    have h3 : √5 < 3 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have : (cycleGraph 5).indepNum < 3 := by exact_mod_cast h.trans_lt h3
    omega
  · have hind : (cycleGraph 5).IsIndepSet ({0, 2} : Finset (Fin 5)) := by
      have : ∀ x ∈ ({0, 2} : Finset (Fin 5)), ∀ y ∈ ({0, 2} : Finset (Fin 5)), x ≠ y →
          ¬(cycleGraph 5).Adj x y := by decide
      exact fun x hx y hy => this x hx y hy
    simpa using hind.card_le_indepNum

end SimpleGraph
