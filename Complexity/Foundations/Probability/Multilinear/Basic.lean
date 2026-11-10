/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.Finset.Expect
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Complexity.Foundations.MeasureTheory.Integral.Pi
import Complexity.Foundations.MeasureTheory.Integral.PiUpdate
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Formal multilinear polynomials of independent random variables

A *formal multilinear polynomial* in the variables indexed by a finite type `ι` is given by its
coefficients `c : Finset ι → ℝ`, and it evaluates to `F(z) = ∑_S c S ∏_{i ∈ S} z i`
(`multilinearEval`) [O'Donnell, Definition 11.63][ODonnell2014]. Its *influence* on `i` is
`Inf_i[F] = ∑_{S ∋ i} c S ^ 2` (`multilinearInfluence`). Splitting off the monomials that contain
`i` writes `F(z) = E_i F(z) + z i · D_i F(z)`, where neither `E_i F` (`multilinearExpectCoeff`) nor
`D_i F` (`multilinearDerivCoeff`) depends on `z i` (`multilinearEval_update`).

When the variables are independent with mean `0`, second moment `1` and finite fourth moments
(each lies in `L⁴`, the integrability hypothesis used throughout), the monomials are orthonormal and
`E[F(z)²] = ∑_S c S ^ 2` (`integral_multilinearEval_sq`)
[O'Donnell, Remark 11.64][ODonnell2014]. This is proved by induction on the coordinates that `F`
mentions, integrating out one coordinate at a time.

## Main definitions

* `ProbabilityTheory.multilinearEval`: the evaluation `F(z) = ∑_S c S ∏_{i ∈ S} z i`.
* `ProbabilityTheory.multilinearInfluence`: `Inf_i[F] = ∑_{S ∋ i} c S ^ 2`.
* `ProbabilityTheory.multilinearExpectCoeff`, `ProbabilityTheory.multilinearDerivCoeff`: the
  coefficients of `E_i F` and `D_i F`.

## Main results

* `ProbabilityTheory.multilinearEval_update`: `F(update z i x) = E_i F(z) + x · D_i F(z)`.
* `ProbabilityTheory.multilinearInfluence_eq_sum_multilinearDerivCoeff_sq`:
  `Inf_i[F] = ∑_S (D_i F)^(S) ^ 2`.
* `ProbabilityTheory.sum_multilinearInfluence`: `∑_i Inf_i[F] = ∑_S |S| c S ^ 2`.
* `ProbabilityTheory.memLp_multilinearEval`: `F(z) ∈ Lᵖ` when every variable is in `Lᵖ`.
* `ProbabilityTheory.integral_multilinearEval_sq`: `E[F(z)²] = ∑_S c S ^ 2`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 11.6.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Definitions and algebra -/

/-- The value `F(z) = ∑_S c S ∏_{i ∈ S} z i` of the formal multilinear polynomial with
coefficients `c` at `z` [O'Donnell, Definition 11.63][ODonnell2014]. -/
noncomputable def multilinearEval (c : Finset ι → ℝ) (z : ι → ℝ) : ℝ :=
  ∑ S, c S * ∏ i ∈ S, z i

/-- The influence `Inf_i[F] = ∑_{S ∋ i} c S ^ 2` of coordinate `i` on the formal multilinear
polynomial with coefficients `c` [O'Donnell, Section 11.6][ODonnell2014]. -/
noncomputable def multilinearInfluence (c : Finset ι → ℝ) (i : ι) : ℝ :=
  ∑ S with i ∈ S, c S ^ 2

omit [DecidableEq ι] in
theorem multilinearEval_def (c : Finset ι → ℝ) (z : ι → ℝ) :
    multilinearEval c z = ∑ S, c S * ∏ i ∈ S, z i := by
  rw [multilinearEval]

theorem multilinearInfluence_def (c : Finset ι → ℝ) (i : ι) :
    multilinearInfluence c i = ∑ S with i ∈ S, c S ^ 2 := by
  rw [multilinearInfluence]

/-- The coefficients of `E_i F`, the part of `F` made of the monomials that do not contain `i`. -/
def multilinearExpectCoeff (c : Finset ι → ℝ) (i : ι) (S : Finset ι) : ℝ :=
  if i ∈ S then 0 else c S

/-- The coefficients of `D_i F`, the polynomial with `F = E_i F + z i · D_i F`: the coefficient of
`S ∌ i` is `c (insert i S)`. -/
def multilinearDerivCoeff (c : Finset ι → ℝ) (i : ι) (S : Finset ι) : ℝ :=
  if i ∈ S then 0 else c (insert i S)

/-- Splitting a sum over sets by whether they contain `i`. -/
private theorem sum_eq_sum_ite_notMem_add (i : ι) (g : Finset ι → ℝ) :
    ∑ S, g S = ∑ S, (if i ∈ S then 0 else g S) + ∑ S, (if i ∈ S then 0 else g (insert i S)) := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun S => i ∈ S),
    sum_filter_mem_eq_sum_filter_notMem i g, sum_filter, sum_filter, add_comm]
  congr 1 <;> refine sum_congr rfl fun S _ => ?_ <;> split_ifs <;> rfl

omit [Fintype ι] in
theorem multilinearExpectCoeff_of_mem (c : Finset ι → ℝ) {i : ι} {S : Finset ι} (h : i ∈ S) :
    multilinearExpectCoeff c i S = 0 := by
  simp [multilinearExpectCoeff, h]

omit [Fintype ι] in
theorem multilinearDerivCoeff_of_mem (c : Finset ι → ℝ) {i : ι} {S : Finset ι} (h : i ∈ S) :
    multilinearDerivCoeff c i S = 0 := by
  simp [multilinearDerivCoeff, h]

/-- `F(z) = E_i F(z) + z i · D_i F(z)`. -/
theorem multilinearEval_eq_add_mul (c : Finset ι → ℝ) (i : ι) (z : ι → ℝ) :
    multilinearEval c z =
      multilinearEval (multilinearExpectCoeff c i) z +
        z i * multilinearEval (multilinearDerivCoeff c i) z := by
  rw [multilinearEval, sum_eq_sum_ite_notMem_add i, multilinearEval, multilinearEval, mul_sum]
  congr 1 <;> refine sum_congr rfl fun S _ => ?_ <;>
    simp only [multilinearExpectCoeff, multilinearDerivCoeff] <;> split_ifs with h
  · simp
  · rfl
  · simp
  · rw [prod_insert h]; ring

/-- A polynomial without monomials containing `i` does not depend on `z i`. -/
theorem multilinearEval_update_of_forall_mem {c : Finset ι → ℝ} {i : ι}
    (hc : ∀ S, i ∈ S → c S = 0) (z : ι → ℝ) (x : ℝ) :
    multilinearEval c (Function.update z i x) = multilinearEval c z := by
  refine sum_congr rfl fun S _ => ?_
  by_cases h : i ∈ S
  · rw [hc S h, zero_mul, zero_mul]
  · congr 1
    refine prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (by rintro rfl; exact h hj)]

/-- Setting coordinate `i` to `x`: `F(update z i x) = E_i F(z) + x · D_i F(z)`. -/
theorem multilinearEval_update (c : Finset ι → ℝ) (i : ι) (z : ι → ℝ) (x : ℝ) :
    multilinearEval c (Function.update z i x) =
      multilinearEval (multilinearExpectCoeff c i) z +
        x * multilinearEval (multilinearDerivCoeff c i) z := by
  rw [multilinearEval_eq_add_mul c i,
    multilinearEval_update_of_forall_mem (fun _ => multilinearExpectCoeff_of_mem c),
    multilinearEval_update_of_forall_mem (fun _ => multilinearDerivCoeff_of_mem c),
    Function.update_self]

/-- The squared coefficients of `F` split between `E_i F` and `D_i F`. -/
theorem sum_sq_eq_sum_multilinearExpectCoeff_sq_add (c : Finset ι → ℝ) (i : ι) :
    ∑ S, c S ^ 2 =
      ∑ S, multilinearExpectCoeff c i S ^ 2 + ∑ S, multilinearDerivCoeff c i S ^ 2 := by
  rw [sum_eq_sum_ite_notMem_add i]
  congr 1 <;> refine sum_congr rfl fun S _ => ?_ <;>
    simp only [multilinearExpectCoeff, multilinearDerivCoeff] <;> split_ifs <;> simp

/-- `Inf_i[F] = E[(D_i F)²]` in coefficient form: `Inf_i[F] = ∑_S (D_i F)^(S) ^ 2`. -/
theorem multilinearInfluence_eq_sum_multilinearDerivCoeff_sq (c : Finset ι → ℝ) (i : ι) :
    multilinearInfluence c i = ∑ S, multilinearDerivCoeff c i S ^ 2 := by
  rw [multilinearInfluence, sum_filter_mem_eq_sum_filter_notMem i, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  simp only [multilinearDerivCoeff]; split_ifs <;> simp

theorem multilinearInfluence_nonneg (c : Finset ι → ℝ) (i : ι) : 0 ≤ multilinearInfluence c i :=
  sum_nonneg fun _ _ => sq_nonneg _

/-- The total influence is the degree-weighted Fourier weight:
`∑_i Inf_i[F] = ∑_S |S| c S ^ 2`. -/
theorem sum_multilinearInfluence (c : Finset ι → ℝ) :
    ∑ i, multilinearInfluence c i = ∑ S, (#S : ℝ) * c S ^ 2 := by
  simp only [multilinearInfluence, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  rw [Fintype.sum_ite_mem, sum_const, nsmul_eq_mul]

omit [Fintype ι] in
/-- If `F` has degree at most `k`, so does `E_i F`. -/
theorem multilinearExpectCoeff_eq_zero_of_card_lt {c : Finset ι → ℝ} {k : ℕ}
    (hc : ∀ S, k < #S → c S = 0) (i : ι) (S : Finset ι) (hS : k < #S) :
    multilinearExpectCoeff c i S = 0 := by
  unfold multilinearExpectCoeff; split_ifs; exacts [rfl, hc S hS]

omit [Fintype ι] in
/-- If `F` has degree at most `k + 1`, then `D_i F` has degree at most `k`. -/
theorem multilinearDerivCoeff_eq_zero_of_card_lt {c : Finset ι → ℝ} {k : ℕ}
    (hc : ∀ S, k + 1 < #S → c S = 0) (i : ι) (S : Finset ι) (hS : k < #S) :
    multilinearDerivCoeff c i S = 0 := by
  unfold multilinearDerivCoeff; split_ifs with h
  · rfl
  · exact hc _ (by rw [card_insert_of_notMem h]; omega)

omit [Fintype ι] in
/-- If `F` is constant, then `D_i F = 0`. -/
theorem multilinearDerivCoeff_eq_zero_of_degree_zero {c : Finset ι → ℝ}
    (hc : ∀ S, 0 < #S → c S = 0) (i : ι) : multilinearDerivCoeff c i = 0 := funext fun S => by
  unfold multilinearDerivCoeff; split_ifs
  · rfl
  · exact hc _ (card_pos.2 (insert_nonempty i S))

omit [DecidableEq ι] in
@[simp] theorem multilinearEval_zero (z : ι → ℝ) : multilinearEval (0 : Finset ι → ℝ) z = 0 := by
  simp [multilinearEval]

/-! ### Integrability -/

omit [DecidableEq ι] in
@[fun_prop]
theorem continuous_multilinearEval (c : Finset ι → ℝ) : Continuous (multilinearEval c) := by
  unfold multilinearEval; fun_prop

omit [DecidableEq ι] in
/-- If every variable is in `Lᵖ` for a natural exponent `p ≥ 1`, then so is `F(z)`. -/
theorem memLp_multilinearEval (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] {p : ℕ}
    (hp : p ≠ 0) (hμ : ∀ i, MemLp id p (μ i)) (c : Finset ι → ℝ) :
    MemLp (multilinearEval c) p (Measure.pi μ) := by
  refine memLp_finsetSum (μ := Measure.pi μ) (p := p)
    (f := fun S z => c S * ∏ i ∈ S, z i) _ fun S _ => ?_
  refine MemLp.const_mul ?_ (c S)
  refine (integrable_norm_rpow_iff (by fun_prop) (by exact_mod_cast hp) (by simp)).1 ?_
  have h := Integrable.finset_prod_pi (μ := μ) S (f := fun _ t => |t| ^ p)
    fun i _ => by simpa using (hμ i).integrable_norm_pow hp
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Real.norm_eq_abs, abs_prod, ENNReal.toReal_natCast, Real.rpow_natCast, prod_pow]

omit [DecidableEq ι] in
/-- If every variable is in `L⁴`, then `|F(z)| ^ j` is integrable for `j ≤ 4`. -/
theorem integrable_abs_multilinearEval_pow (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, MemLp id 4 (μ i)) (c : Finset ι → ℝ) {j : ℕ} (hj : j ≤ 4) :
    Integrable (fun z => |multilinearEval c z| ^ j) (Measure.pi μ) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  have h := ((memLp_multilinearEval μ (p := 4) (by norm_num) (by exact_mod_cast hμ) c).mono_exponent
    (p := (j : ℝ≥0∞)) (by exact_mod_cast hj)).integrable_norm_pow hj0.ne'
  simpa using h

omit [DecidableEq ι] in
/-- If every variable is in `L⁴`, then `F(z) ^ j` is integrable for `j ≤ 4`. -/
theorem integrable_multilinearEval_pow (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, MemLp id 4 (μ i)) (c : Finset ι → ℝ) {j : ℕ} (hj : j ≤ 4) :
    Integrable (fun z => multilinearEval c z ^ j) (Measure.pi μ) :=
  (integrable_abs_multilinearEval_pow μ hμ c hj).mono'
    ((continuous_multilinearEval c).pow j).aestronglyMeasurable
    (ae_of_all _ fun z => by simp)

/-! ### The `L²` identity -/

omit [DecidableEq ι] in
/-- A polynomial without nonconstant monomials is the constant `c ∅`. -/
theorem multilinearEval_of_forall_nonempty {c : Finset ι → ℝ}
    (hc : ∀ S : Finset ι, S.Nonempty → c S = 0) (z : ι → ℝ) : multilinearEval c z = c ∅ := by
  rw [multilinearEval, sum_eq_single ∅ (fun S _ hS => by
    rw [hc S (nonempty_iff_ne_empty.2 hS), zero_mul]) (by simp)]
  simp

omit [Fintype ι] in
/-- If `F` only mentions the variables in `insert i T`, then `E_i F` only mentions those in `T`. -/
theorem multilinearExpectCoeff_eq_zero_of_not_subset {c : Finset ι → ℝ} {i : ι} {T : Finset ι}
    (hc : ∀ S, ¬ S ⊆ insert i T → c S = 0) (S : Finset ι) (hS : ¬ S ⊆ T) :
    multilinearExpectCoeff c i S = 0 := by
  unfold multilinearExpectCoeff
  split_ifs with h
  · rfl
  · exact hc S (by rwa [subset_insert_iff_of_notMem h])

omit [Fintype ι] in
/-- If `F` only mentions the variables in `insert i T`, then `D_i F` only mentions those in `T`. -/
theorem multilinearDerivCoeff_eq_zero_of_not_subset {c : Finset ι → ℝ} {i : ι} {T : Finset ι}
    (hc : ∀ S, ¬ S ⊆ insert i T → c S = 0) (S : Finset ι) (hS : ¬ S ⊆ T) :
    multilinearDerivCoeff c i S = 0 := by
  unfold multilinearDerivCoeff
  split_ifs with h
  · rfl
  · exact hc _ (by rwa [insert_subset_insert_iff h])

/-- `E[(e + z d)²] = e² + d²` for `z` with mean `0` and second moment `1`. -/
theorem integral_add_mul_sq {m : Measure ℝ} [IsProbabilityMeasure m] (hm : MemLp id 2 m)
    (h1 : ∫ z, z ∂m = 0) (h2 : ∫ z, z ^ 2 ∂m = 1) (e d : ℝ) :
    ∫ z, (e + z * d) ^ 2 ∂m = e ^ 2 + d ^ 2 := by
  have hz : Integrable (fun z : ℝ => z) m := hm.integrable one_le_two
  have hz2 : Integrable (fun z : ℝ => z ^ 2) m := by
    simpa using hm.integrable_norm_pow two_ne_zero
  have : (fun z => (e + z * d) ^ 2) = fun z => e ^ 2 + ((2 * e * d) * z + d ^ 2 * z ^ 2) := by
    funext z; ring
  rw [this, integral_add (f := fun _ => e ^ 2) (g := fun z => 2 * e * d * z + d ^ 2 * z ^ 2)
      (integrable_const _) ((hz.const_mul _).add (hz2.const_mul _)),
    integral_add (f := fun z => 2 * e * d * z) (g := fun z => d ^ 2 * z ^ 2) (hz.const_mul _)
      (hz2.const_mul _), integral_const_mul, integral_const_mul, h1, h2]
  simp

omit [DecidableEq ι] in
private theorem integral_multilinearEval_sq_aux (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, MemLp id 4 (μ i)) (h1 : ∀ i, ∫ z, z ∂μ i = 0)
    (h2 : ∀ i, ∫ z, z ^ 2 ∂μ i = 1) (T : Finset ι) :
    ∀ c : Finset ι → ℝ, (∀ S, ¬ S ⊆ T → c S = 0) →
      ∫ z, multilinearEval c z ^ 2 ∂Measure.pi μ = ∑ S, c S ^ 2 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro c hc
    have hS : ∑ S, c S ^ 2 = c ∅ ^ 2 := sum_eq_single ∅
      (fun S _ hS => by rw [hc S (by simpa [subset_empty] using hS)]; simp) (by simp)
    simp [multilinearEval_of_forall_nonempty fun S hS => hc S (by
      simpa [subset_empty, nonempty_iff_ne_empty] using hS), hS]
  | insert a T _ ih =>
    intro c hc
    have h4 (c' : Finset ι → ℝ) := integrable_multilinearEval_pow μ hμ c' (j := 2) (by norm_num)
    rw [← integral_integral_update μ (h4 c) a]
    simp_rw [multilinearEval_update c a,
      integral_add_mul_sq ((hμ a).mono_exponent (by norm_num)) (h1 a) (h2 a)]
    rw [integral_add (h4 _) (h4 _), ih _ (multilinearExpectCoeff_eq_zero_of_not_subset hc),
      ih _ (multilinearDerivCoeff_eq_zero_of_not_subset hc),
      sum_sq_eq_sum_multilinearExpectCoeff_sq_add c a]

omit [DecidableEq ι] in
/-- **Orthonormality of monomials** [O'Donnell, Remark 11.64][ODonnell2014]. If the variables are
independent with mean `0` and second moment `1`, then `E[F(z)²] = ∑_S c S ^ 2`. The variables are
assumed to lie in `L⁴`, as in all applications here. -/
theorem integral_multilinearEval_sq (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, MemLp id 4 (μ i)) (h1 : ∀ i, ∫ z, z ∂μ i = 0) (h2 : ∀ i, ∫ z, z ^ 2 ∂μ i = 1)
    (c : Finset ι → ℝ) :
    ∫ z, multilinearEval c z ^ 2 ∂Measure.pi μ = ∑ S, c S ^ 2 :=
  integral_multilinearEval_sq_aux μ hμ h1 h2 univ c fun S hS => absurd (subset_univ S) hS

end ProbabilityTheory
