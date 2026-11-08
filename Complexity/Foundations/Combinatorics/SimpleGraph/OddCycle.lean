/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/LovaszTheta.lean`)

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.SimpleGraph.LovaszTheta
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The Lovász theta function of odd cycles

For odd `n ≥ 3`, put `c = cos (π / n)`. Lovász computed the theta function of the cycle `Cₙ`
and of its complement [Lovasz1979]:
`ϑ(Cₙ) = n c / (1 + c)` and `ϑ(Cₙᶜ) = (1 + c) / c`. We follow the elementary proof in Knuth's notes
[Knuth1994, §22], which needs no semidefinite duality:

* an *umbrella* in `ℝ³` (Knuth's (22.2)–(22.5)) is an orthonormal representation of `Cₙᶜ` with
  handle value `c / (1 + c)`, so `ϑ(Cₙᶜ) ≤ (1 + c) / c`;
* a *Fourier* representation of `Cₙ` with weights `β k = (1 + cos (2πk/n) / c) / n` (Knuth's
  (22.6)–(22.9), with the frequencies reindexed) has handle value `β 0 = (1 + c) / (n c)`, so
  `ϑ(Cₙ) ≤ n c / (1 + c)`;
* the product of the two bounds is `n`, while `n ≤ ϑ(G) ϑ(Gᶜ)` holds for every graph
  (`SimpleGraph.natCard_le_lovaszTheta_mul_lovaszTheta_compl`), so both bounds are equalities.

Our Fourier vectors use the frequencies `2πk/n` and have `2n` real coordinates; Knuth uses the
angle `π(n - 1)/n` and `2n - 1` coordinates. The two choices differ by a permutation of the
frequencies (and one coordinate that is identically zero), so the Gram matrices agree.

For `n = 3` the formula gives `ϑ(K₃) = 1`, and for `n = 5` it gives `√5`, recovering
`SimpleGraph.lovaszTheta_cycleGraph_five`. For odd `n ≥ 7` it gives the upper bound
`Θ(Cₙ) ≤ ϑ(Cₙ)`, for instance `Θ(C₇) ≤ ϑ(C₇) ≈ 3.32`. The exact value of `Θ(C₇)` is open.

## Main definitions

* `SimpleGraph.oddCycleComplUmbrella`: the umbrella representation of `Cₙᶜ` in `ℝ³`.
* `SimpleGraph.oddCycleWeight`, `SimpleGraph.oddCycleFourier`: the Fourier representation of `Cₙ`.

## Main results

* `SimpleGraph.lovaszTheta_cycleGraph_of_odd`: `ϑ(Cₙ) = n cos (π/n) / (1 + cos (π/n))`.
* `SimpleGraph.lovaszTheta_compl_cycleGraph_of_odd`: `ϑ(Cₙᶜ) = (1 + cos (π/n)) / cos (π/n)`.
* `SimpleGraph.lovaszTheta_cycleGraph_mul_compl_of_odd`: `ϑ(Cₙ) ϑ(Cₙᶜ) = n`.
* `SimpleGraph.shannonCapacity_cycleGraph_le_of_odd`: `Θ(Cₙ) ≤ n cos (π/n) / (1 + cos (π/n))`.
* `SimpleGraph.sum_range_cos_two_pi_mul_div`: `∑_{k < n} cos (2πjk/n)` is `n` if `n ∣ j` and `0`
  otherwise.

## References

* [D. E. Knuth, *The sandwich theorem*][Knuth1994]
* [L. Lovász, *On the Shannon capacity of a graph*][Lovasz1979]
-/

public section

open Finset Real
open scoped RealInnerProductSpace

namespace SimpleGraph

/-- Adjacency in `Cₙ` in terms of the values of the vertices. -/
theorem cycleGraph_adj_iff_val {n : ℕ} {u v : Fin n} (hne : u ≠ v) :
    (cycleGraph n).Adj u v ↔
      (u : ℕ) = v + 1 ∨ (v : ℕ) = u + 1 ∨ (u : ℕ) + 1 = v + n ∨ (v : ℕ) + 1 = u + n := by
  have hne' : (u : ℕ) ≠ v := fun h => hne (Fin.ext h)
  have hu := u.isLt
  have hv := v.isLt
  rw [cycleGraph_adj']
  rcases lt_or_gt_of_ne hne' with h | h
  · have h1 : ((u - v : Fin n) : ℕ) = n + u - v := Fin.coe_sub_iff_lt.2 h
    have h2 : ((v - u : Fin n) : ℕ) = v - u := Fin.coe_sub_iff_le.2 h.le
    rw [h1, h2]
    omega
  · have h1 : ((u - v : Fin n) : ℕ) = u - v := Fin.coe_sub_iff_le.2 h.le
    have h2 : ((v - u : Fin n) : ℕ) = n + v - u := Fin.coe_sub_iff_lt.2 h
    rw [h1, h2]
    omega

private theorem cos_pi_div_pos {n : ℕ} (hn : 3 ≤ n) : 0 < cos (π / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply cos_pos_of_mem_Ioo
  constructor
  · have : 0 < π / n := div_pos pi_pos hn'
    linarith [pi_pos]
  · rw [div_lt_div_iff₀ hn' two_pos]
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pi_pos]

/-! ### The umbrella for the complement of an odd cycle -/

/-- The umbrella representation of `Cₙᶜ` in `ℝ³` [Knuth1994, §22, (22.2)]: unit vectors whose
azimuths around the handle `(1, 0, 0)` advance by `π - π/n`. -/
noncomputable def oddCycleComplUmbrella (n : ℕ) (v : Fin n) : EuclideanSpace ℝ (Fin 3) :=
  !₂[√(cos (π / n) / (1 + cos (π / n))),
    √(1 / (1 + cos (π / n))) * cos ((π - π / n) * (v : ℕ)),
    √(1 / (1 + cos (π / n))) * sin ((π - π / n) * (v : ℕ))]

theorem inner_oddCycleComplUmbrella {n : ℕ} (hn : 3 ≤ n) (u v : Fin n) :
    ⟪oddCycleComplUmbrella n u, oddCycleComplUmbrella n v⟫ =
      cos (π / n) / (1 + cos (π / n)) +
        1 / (1 + cos (π / n)) * cos ((π - π / n) * (u : ℕ) - (π - π / n) * (v : ℕ)) := by
  have hc := cos_pi_div_pos hn
  have h₁ : √(cos (π / n) / (1 + cos (π / n))) * √(cos (π / n) / (1 + cos (π / n))) =
      cos (π / n) / (1 + cos (π / n)) := Real.mul_self_sqrt (by positivity)
  have h₂ : √(1 / (1 + cos (π / n))) * √(1 / (1 + cos (π / n))) = 1 / (1 + cos (π / n)) :=
    Real.mul_self_sqrt (by positivity)
  rw [cos_sub]
  simp only [oddCycleComplUmbrella, PiLp.inner_apply, Fin.sum_univ_three, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, RCLike.inner_apply, conj_trivial]
  linear_combination h₁ + (cos ((π - π / n) * (u : ℕ)) * cos ((π - π / n) * (v : ℕ)) +
    sin ((π - π / n) * (u : ℕ)) * sin ((π - π / n) * (v : ℕ))) * h₂

theorem norm_oddCycleComplUmbrella {n : ℕ} (hn : 3 ≤ n) (v : Fin n) :
    ‖oddCycleComplUmbrella n v‖ = 1 := by
  have hc := cos_pi_div_pos hn
  have h : ‖oddCycleComplUmbrella n v‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_oddCycleComplUmbrella hn, sub_self, cos_zero]
    field_simp
    ring
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

private theorem cos_oddCycle_step {m : ℕ} {u v : Fin (2 * m + 1)}
    (h : (u : ℕ) = v + 1 ∨ (v : ℕ) = u + 1 ∨ (u : ℕ) + 1 = v + (2 * m + 1) ∨
      (v : ℕ) + 1 = u + (2 * m + 1)) :
    cos ((π - π / ((2 * m + 1 : ℕ) : ℝ)) * (u : ℕ) - (π - π / ((2 * m + 1 : ℕ) : ℝ)) * (v : ℕ)) =
      -cos (π / ((2 * m + 1 : ℕ) : ℝ)) := by
  set N : ℝ := ((2 * m + 1 : ℕ) : ℝ) with hN
  have hN0 : N ≠ 0 := by rw [hN]; positivity
  have hNm : N = 2 * m + 1 := by rw [hN]; push_cast; ring
  rcases h with h | h | h | h
  · have hu : ((u : ℕ) : ℝ) = (v : ℕ) + 1 := by exact_mod_cast h
    rw [hu, show (π - π / N) * ((v : ℕ) + 1) - (π - π / N) * (v : ℕ) = π - π / N by ring,
      cos_pi_sub]
  · have hv : ((v : ℕ) : ℝ) = (u : ℕ) + 1 := by exact_mod_cast h
    rw [hv, show (π - π / N) * (u : ℕ) - (π - π / N) * ((u : ℕ) + 1) = -(π - π / N) by ring,
      cos_neg, cos_pi_sub]
  · have hu : ((u : ℕ) : ℝ) = (v : ℕ) + N - 1 := by
      rw [hNm]; have : ((u : ℕ) : ℝ) + 1 = (v : ℕ) + (2 * m + 1) := by exact_mod_cast h
      linarith
    have : (π - π / N) * (u : ℕ) - (π - π / N) * (v : ℕ) = m * (2 * π) - (π - π / N) := by
      rw [hu]; field_simp; rw [hNm]; ring
    rw [this, cos_nat_mul_two_pi_sub, cos_pi_sub]
  · have hv : ((v : ℕ) : ℝ) = (u : ℕ) + N - 1 := by
      rw [hNm]; have : ((v : ℕ) : ℝ) + 1 = (u : ℕ) + (2 * m + 1) := by exact_mod_cast h
      linarith
    have : (π - π / N) * (u : ℕ) - (π - π / N) * (v : ℕ) = -(m * (2 * π) - (π - π / N)) := by
      rw [hv]; field_simp; rw [hNm]; ring
    rw [this, cos_neg, cos_nat_mul_two_pi_sub, cos_pi_sub]

theorem inner_oddCycleComplUmbrella_eq_zero {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) {u v : Fin n}
    (hne : u ≠ v) (hadj : ¬(cycleGraph n)ᶜ.Adj u v) :
    ⟪oddCycleComplUmbrella n u, oddCycleComplUmbrella n v⟫ = 0 := by
  obtain ⟨m, rfl⟩ := hodd
  have hc := cos_pi_div_pos hn
  have hA : (cycleGraph (2 * m + 1)).Adj u v := by
    rw [compl_adj] at hadj
    by_contra h
    exact hadj ⟨hne, h⟩
  rw [inner_oddCycleComplUmbrella hn,
    cos_oddCycle_step ((cycleGraph_adj_iff_val hne).1 hA)]
  field_simp
  ring

theorem isOrthonormalRepresentation_oddCycleComplUmbrella {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) :
    (cycleGraph n)ᶜ.IsOrthonormalRepresentation (oddCycleComplUmbrella n) :=
  ⟨norm_oddCycleComplUmbrella hn, fun _ _ => inner_oddCycleComplUmbrella_eq_zero hodd hn⟩

theorem lovaszTheta_compl_cycleGraph_le {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) :
    (cycleGraph n)ᶜ.lovaszTheta ≤ (1 + cos (π / n)) / cos (π / n) := by
  have hc := cos_pi_div_pos hn
  refine lovaszTheta_le_of_rep (isOrthonormalRepresentation_oddCycleComplUmbrella hodd hn)
    (c := EuclideanSpace.single 0 1) (by simp) (by positivity) fun v => ?_
  rw [EuclideanSpace.inner_single_left]
  simp only [oddCycleComplUmbrella, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero,
    map_one, one_mul]
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  rfl

/-! ### A discrete Fourier sum -/

/-- `∑_{k < n} cos (2π j k / n)` is `n` if `n ∣ j` and `0` otherwise. -/
theorem sum_range_cos_two_pi_mul_div {n : ℕ} (hn : 0 < n) (j : ℤ) :
    ∑ k ∈ range n, cos (2 * π * j / n * k) = if (n : ℤ) ∣ j then (n : ℝ) else 0 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    have : ∀ k ∈ range n, cos (2 * π * ((n * q : ℤ) : ℝ) / n * k) = 1 := by
      intro k _
      rw [show 2 * π * ((n * q : ℤ) : ℝ) / n * k = ((q * k : ℤ) : ℝ) * (2 * π) by
        push_cast; field_simp]
      exact cos_int_mul_two_pi _
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul, mul_one]
  · have h := Real.sum_cos n (a := 2 * π * j / n) ?_ 0
    · simp only [add_zero] at h
      rw [h, show (n : ℝ) * (2 * π * j / n) / 2 = (j : ℝ) * π by field_simp, sin_int_mul_pi,
        zero_mul, zero_div]
    · intro k hk
      apply hd
      refine ⟨k, ?_⟩
      have : (j : ℝ) = n * k := by
        field_simp at hk
        exact hk
      exact_mod_cast this

/-- The squared Fourier weights `β k = (1 + cos (2πk/n) / cos (π/n)) / n` of the representation
`SimpleGraph.oddCycleFourier`; they are nonnegative for odd `n ≥ 3`. -/
noncomputable def oddCycleWeight (n k : ℕ) : ℝ :=
  (1 + cos (2 * π * k / n) / cos (π / n)) / n

private theorem cos_two_pi_mul_div_ge {n k : ℕ} (hodd : Odd n) (hn : 3 ≤ n) (hk : k < n) :
    -cos (π / n) ≤ cos (2 * π * k / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have key : ∀ i : ℕ, 2 * i + 1 ≤ n → -cos (π / n) ≤ cos (2 * π * i / n) := by
    intro i hi
    have hi' : (2 * i + 1 : ℝ) ≤ n := by exact_mod_cast hi
    rw [← cos_pi_sub]
    apply cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · have : 0 < π / n := div_pos pi_pos hn'
      linarith
    · have : π - π / n = π * (n - 1) / n := by field_simp
      rw [this]
      apply div_le_div_of_nonneg_right _ hn'.le
      nlinarith [pi_pos]
  obtain ⟨m, rfl⟩ := hodd
  by_cases h : 2 * k + 1 ≤ 2 * m + 1
  · exact key k h
  · have h2 : 2 * (2 * m + 1 - k) + 1 ≤ 2 * m + 1 := by omega
    have := key _ h2
    have hc : cos (2 * π * ((2 * m + 1 - k : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) =
        cos (2 * π * k / ((2 * m + 1 : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hk.le, show 2 * π * (((2 * m + 1 : ℕ) : ℝ) - k) / ((2 * m + 1 : ℕ) : ℝ) =
        2 * π - 2 * π * k / ((2 * m + 1 : ℕ) : ℝ) by field_simp, cos_two_pi_sub]
    linarith

theorem oddCycleWeight_nonneg {n k : ℕ} (hodd : Odd n) (hn : 3 ≤ n) (hk : k < n) :
    0 ≤ oddCycleWeight n k := by
  have hc := cos_pi_div_pos hn
  have h := cos_two_pi_mul_div_ge hodd hn hk
  unfold oddCycleWeight
  apply div_nonneg _ (Nat.cast_nonneg _)
  rw [show 1 + cos (2 * π * k / n) / cos (π / n) =
    (cos (π / n) + cos (2 * π * k / n)) / cos (π / n) by field_simp]
  apply div_nonneg _ hc.le
  linarith

/-- The Fourier orthonormal representation of `Cₙ`: coordinates `(k, 0)` and `(k, 1)` are
`√(β k) cos (2πkv/n)` and `√(β k) sin (2πkv/n)`. -/
noncomputable def oddCycleFourier (n : ℕ) (v : Fin n) : EuclideanSpace ℝ (Fin n × Fin 2) :=
  WithLp.toLp 2 fun p => √(oddCycleWeight n p.1) *
    ![cos (2 * π * (p.1 : ℕ) / n * (v : ℕ)), sin (2 * π * (p.1 : ℕ) / n * (v : ℕ))] p.2

theorem inner_oddCycleFourier {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) (u v : Fin n) :
    ⟪oddCycleFourier n u, oddCycleFourier n v⟫ =
      ∑ k ∈ range n, oddCycleWeight n k * cos (2 * π * (((u : ℕ) : ℤ) - (v : ℕ) : ℤ) / n * k) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type,
    ← Fin.sum_univ_eq_sum_range (fun k => oddCycleWeight n k *
      cos (2 * π * (((u : ℕ) : ℤ) - (v : ℕ) : ℤ) / n * k))]
  refine sum_congr rfl fun k _ => ?_
  have hw := Real.mul_self_sqrt (oddCycleWeight_nonneg hodd hn k.isLt)
  have ha : 2 * π * ((((u : ℕ) : ℤ) - (v : ℕ) : ℤ) : ℝ) / n * (k : ℕ) =
      2 * π * (k : ℕ) / n * (u : ℕ) - 2 * π * (k : ℕ) / n * (v : ℕ) := by
    push_cast
    ring
  rw [ha, cos_sub]
  simp only [oddCycleFourier, Fin.sum_univ_two, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, RCLike.inner_apply, conj_trivial]
  linear_combination (cos (2 * π * (k : ℕ) / n * (u : ℕ)) * cos (2 * π * (k : ℕ) / n * (v : ℕ)) +
    sin (2 * π * (k : ℕ) / n * (u : ℕ)) * sin (2 * π * (k : ℕ) / n * (v : ℕ))) * hw

theorem sum_oddCycleWeight_mul_cos {n : ℕ} (hn : 3 ≤ n) (j : ℤ) :
    ∑ k ∈ range n, oddCycleWeight n k * cos (2 * π * j / n * k) =
      ((if (n : ℤ) ∣ j then (n : ℝ) else 0) + ((if (n : ℤ) ∣ j + 1 then (n : ℝ) else 0) +
        (if (n : ℤ) ∣ j - 1 then (n : ℝ) else 0)) / (2 * cos (π / n))) / n := by
  have hc := cos_pi_div_pos hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [← sum_range_cos_two_pi_mul_div (by omega) j,
    ← sum_range_cos_two_pi_mul_div (by omega) (j + 1),
    ← sum_range_cos_two_pi_mul_div (by omega) (j - 1), ← sum_add_distrib, sum_div,
    ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun k _ => ?_
  have h1 : cos (2 * π * ((j + 1 : ℤ) : ℝ) / n * k) = cos (2 * π * j / n * k + 2 * π * k / n) := by
    congr 1
    push_cast
    ring
  have h2 : cos (2 * π * ((j - 1 : ℤ) : ℝ) / n * k) = cos (2 * π * j / n * k - 2 * π * k / n) := by
    congr 1
    push_cast
    ring
  rw [h1, h2, cos_add, cos_sub]
  unfold oddCycleWeight
  field_simp
  ring

private theorem not_dvd_of_abs_lt {n : ℕ} {x : ℤ} (h0 : x ≠ 0) (h1 : -(n : ℤ) < x)
    (h2 : x < n) : ¬(n : ℤ) ∣ x :=
  fun hd => h0 (Int.eq_zero_of_abs_lt_dvd hd (abs_lt.2 ⟨h1, h2⟩))

theorem inner_oddCycleFourier_self {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) (v : Fin n) :
    ⟪oddCycleFourier n v, oddCycleFourier n v⟫ = 1 := by
  have hc := cos_pi_div_pos hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [inner_oddCycleFourier hodd hn, sum_oddCycleWeight_mul_cos hn, sub_self, zero_add, zero_sub,
    ite_eq_left (dvd_zero _), ite_eq_right (not_dvd_of_abs_lt one_ne_zero (by omega) (by omega)),
    ite_eq_right (not_dvd_of_abs_lt (by omega) (by omega) (by omega))]
  field_simp
  ring

theorem norm_oddCycleFourier {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) (v : Fin n) :
    ‖oddCycleFourier n v‖ = 1 := by
  have h : ‖oddCycleFourier n v‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_oddCycleFourier_self hodd hn]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

theorem inner_oddCycleFourier_eq_zero {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) {u v : Fin n}
    (hne : u ≠ v) (hadj : ¬(cycleGraph n).Adj u v) :
    ⟪oddCycleFourier n u, oddCycleFourier n v⟫ = 0 := by
  have hne' : (u : ℕ) ≠ v := fun h => hne (Fin.ext h)
  have hval := (cycleGraph_adj_iff_val hne).not.1 hadj
  have hu := u.isLt
  have hv := v.isLt
  rw [inner_oddCycleFourier hodd hn, sum_oddCycleWeight_mul_cos hn,
    ite_eq_right (not_dvd_of_abs_lt (by omega) (by omega) (by omega)),
    ite_eq_right (not_dvd_of_abs_lt (by omega) (by omega) (by omega)),
    ite_eq_right (not_dvd_of_abs_lt (by omega) (by omega) (by omega))]
  simp

theorem isOrthonormalRepresentation_oddCycleFourier {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) :
    (cycleGraph n).IsOrthonormalRepresentation (oddCycleFourier n) :=
  ⟨norm_oddCycleFourier hodd hn, fun _ _ => inner_oddCycleFourier_eq_zero hodd hn⟩

theorem lovaszTheta_cycleGraph_le {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) :
    (cycleGraph n).lovaszTheta ≤ n * cos (π / n) / (1 + cos (π / n)) := by
  have hc := cos_pi_div_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have : NeZero n := ⟨by omega⟩
  refine lovaszTheta_le_of_rep (isOrthonormalRepresentation_oddCycleFourier hodd hn)
    (c := EuclideanSpace.single (0, 0) 1) (by simp) (by positivity) fun v => ?_
  rw [EuclideanSpace.inner_single_left]
  simp only [oddCycleFourier, PiLp.toLp_apply, Matrix.cons_val_zero, Fin.val_zero,
    Nat.cast_zero, mul_zero, zero_mul, zero_div, cos_zero, map_one, one_mul, mul_one]
  rw [Real.sq_sqrt (oddCycleWeight_nonneg hodd hn (by omega))]
  unfold oddCycleWeight
  rw [Nat.cast_zero, mul_zero, zero_div, cos_zero]
  field_simp
  linarith

private theorem lovaszTheta_cycleGraph_aux {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) :
    (cycleGraph n).lovaszTheta = n * cos (π / n) / (1 + cos (π / n)) ∧
      (cycleGraph n)ᶜ.lovaszTheta = (1 + cos (π / n)) / cos (π / n) := by
  have hc := cos_pi_div_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hprod := natCard_le_lovaszTheta_mul_lovaszTheta_compl (G := cycleGraph n)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hprod
  have hA := lovaszTheta_cycleGraph_le hodd hn
  have hB := lovaszTheta_compl_cycleGraph_le hodd hn
  have hApos : 0 < (cycleGraph n).lovaszTheta := lovaszTheta_pos
  have hBpos : 0 < (cycleGraph n)ᶜ.lovaszTheta := lovaszTheta_pos
  have ha : 0 < n * cos (π / n) / (1 + cos (π / n)) := by positivity
  have hb : 0 < (1 + cos (π / n)) / cos (π / n) := by positivity
  have hab : n * cos (π / n) / (1 + cos (π / n)) * ((1 + cos (π / n)) / cos (π / n)) = n := by
    field_simp
  constructor
  · refine le_antisymm hA (le_of_not_gt fun h => ?_)
    nlinarith [mul_lt_mul_of_pos_right h hBpos, mul_le_mul_of_nonneg_left hB ha.le]
  · refine le_antisymm hB (le_of_not_gt fun h => ?_)
    nlinarith [mul_lt_mul_of_pos_left h hApos, mul_le_mul_of_nonneg_right hA hb.le]

/-- **Lovász's theorem for odd cycles**: `ϑ(Cₙ) = n cos (π/n) / (1 + cos (π/n))` for odd
`n ≥ 3` [Knuth1994, §22, (22.11)]. -/
theorem lovaszTheta_cycleGraph_of_odd {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) :
    (cycleGraph n).lovaszTheta = n * cos (π / n) / (1 + cos (π / n)) :=
  (lovaszTheta_cycleGraph_aux hodd hn).1

/-- `ϑ(Cₙᶜ) = (1 + cos (π/n)) / cos (π/n)` for odd `n ≥ 3` [Knuth1994, §22, (22.12)]. -/
theorem lovaszTheta_compl_cycleGraph_of_odd {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) :
    (cycleGraph n)ᶜ.lovaszTheta = (1 + cos (π / n)) / cos (π / n) :=
  (lovaszTheta_cycleGraph_aux hodd hn).2

/-- Odd cycles attain `ϑ(G) ϑ(Gᶜ) = |V|` [Knuth1994, §23]. -/
theorem lovaszTheta_cycleGraph_mul_compl_of_odd {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) :
    (cycleGraph n).lovaszTheta * (cycleGraph n)ᶜ.lovaszTheta = n := by
  have hc := cos_pi_div_pos hn
  rw [lovaszTheta_cycleGraph_of_odd hodd hn, lovaszTheta_compl_cycleGraph_of_odd hodd hn]
  field_simp

/-- Lovász's upper bound on the Shannon capacity of an odd cycle. -/
theorem shannonCapacity_cycleGraph_le_of_odd {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) :
    (cycleGraph n).shannonCapacity ≤ n * cos (π / n) / (1 + cos (π / n)) :=
  lovaszTheta_cycleGraph_of_odd hodd hn ▸ shannonCapacity_le_lovaszTheta

end SimpleGraph
