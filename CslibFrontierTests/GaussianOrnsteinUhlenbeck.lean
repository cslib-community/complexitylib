/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/
import CslibFrontier.Foundations.Probability.Gaussian.OrnsteinUhlenbeck
import Mathlib.Analysis.PSeries

/-! # Tests for the Ornstein–Uhlenbeck operator

* The Hermite differential equation for `H_2 = X² - 1`, and the eigenvalue identity
  `x h_1' - h_1'' = h_1`.
* Integration by parts with its value: `E[(x f' - f'') g] = 1` for `f = g = id`, for the
  coordinate of `Unit → ℝ`, and for `f = g = z₀` on `Fin 2 → ℝ`.
* The `L²` operator on `f = h_β`: `L h_β = |β| h_β` in Hermite coordinates; it is the left
  derivative at `ρ = 1` of `ρ ↦ U_ρ h_β`, and every left derivative is `L h_β`; in exponential
  time, `-L h_β` is the right derivative at `t = 0`.
* Proposition 11.27 for `h_β`: the derivative at `|ρ| < 1` has Hermite coordinate
  `|β| ρ ^ (|β| - 1)` at `β`; at `ρ = 1/2` it is `2 L U_{1/2} h_β = 2 U_{1/2} L h_β`; and
  `L U_{1/2} h_β = U_{1/2} L h_β`.
* Exercise 11.18: `f = ∑ n, (n + 1)⁻¹ h_n` is in `L²(γ)` but not in the domain of `L`, so
  `ρ ↦ U_ρ f` has no left derivative at `ρ = 1`; by Exercise 11.18(c), `U_{1/2} f` is in the
  domain, and `ρ ↦ U_ρ f` is still differentiable at `ρ = 1/2`.
-/

namespace CslibFrontierTests.GaussianOrnsteinUhlenbeck

open MeasureTheory ProbabilityTheory Polynomial Filter Topology

/-! ### The differential form -/

-- `X H_2' - H_2'' = 2 H_2` for `H_2 = X² - 1`.
example : X * derivative (X ^ 2 - 1 : ℤ[X]) - derivative (derivative (X ^ 2 - 1 : ℤ[X])) =
    2 * (X ^ 2 - 1) := by
  have h2 : hermite 2 = X ^ 2 - 1 := by
    rw [hermite_succ_succ, hermite_one, hermite_zero, C_1]
    ring
  have h := X_mul_derivative_hermite_sub 2
  rw [h2] at h
  exact_mod_cast h

-- `x h_1' x - h_1'' x = h_1 x = x`.
example (x : ℝ) :
    x * deriv (normalizedHermite 1) x - deriv (deriv (normalizedHermite 1)) x = x := by
  simpa using mul_deriv_normalizedHermite_sub 1 x

/-! ### Integration by parts -/

-- Integration by parts for `f = g = id`: `E[(x · 1 - 0) x] = E[1 · 1] = 1`.
example : ∫ x, (x * deriv id x - deriv (deriv id) x) * id x ∂gaussianReal 0 1 = 1 := by
  have hid : deriv (id : ℝ → ℝ) = fun _ => 1 := funext fun _ => deriv_id _
  rw [integral_mul_deriv_sub_deriv_deriv_mul_gaussianReal ?_ differentiable_id ?_ ?_ ?_ ?_]
  · simp [hid]
  · rw [hid]; exact differentiable_const _
  · rw [hid]; simpa using (memLp_id_gaussianReal 1).integrable (le_refl _) |>.congr (by rfl)
  · rw [hid]; simpa [← sq] using (memLp_id_gaussianReal 2).integrable_sq
  · rw [hid]; simp
  · rw [hid]; simp

-- Integration by parts in `n` dimensions for `f = g = (z ↦ z ())` on `Unit → ℝ`:
-- `E[z () · z ()] = E[1 · 1] = 1`.
example : ∫ z : Unit → ℝ, (∑ i, (z i * deriv (fun t => (Function.update z i t) ()) (z i) -
        deriv (deriv fun t => (Function.update z i t) ()) (z i))) * z ()
        ∂Measure.pi (fun _ : Unit => gaussianReal 0 1) = 1 := by
  have hu : ∀ (i : Unit) (z : Unit → ℝ), (fun t => (Function.update z i t) ()) = id := by
    intro i z
    funext t
    simp [Subsingleton.elim i ()]
  have hid : deriv (id : ℝ → ℝ) = fun _ => 1 := funext fun _ => deriv_id _
  have he := measurePreserving_eval (fun _ : Unit => gaussianReal 0 1) ()
  have hsq : Integrable (fun z : Unit → ℝ => z () * z ())
      (Measure.pi fun _ : Unit => gaussianReal 0 1) := by
    simpa [Function.comp_def, sq] using
      he.integrable_comp_of_integrable (memLp_id_gaussianReal 2).integrable_sq
  rw [integral_sum_mul_deriv_update_sub_mul_pi_gaussianReal (ι := Unit) (f := fun z => z ())
    (g := fun z => z ()) ?_ ?_ ?_ ?_ ?_ ?_] <;>
    simp only [hu, hid, deriv_const', zero_mul, mul_one, one_mul]
  · simp
  · exact fun _ _ => differentiable_const _
  · exact fun _ _ => differentiable_id
  · exact fun _ => he.integrable_comp_of_integrable ((memLp_id_gaussianReal 1).integrable le_rfl)
  · intro i
    obtain rfl := Subsingleton.elim i ()
    exact hsq
  · exact fun _ => integrable_zero _ _ _
  · exact fun _ => integrable_const _

/-- Along coordinate `i`, the line through `z` of `z ↦ z 0` on `Fin 2 → ℝ` has derivative `1` if
`i = 0` and `0` otherwise. -/
theorem deriv_update_zero (z : Fin 2 → ℝ) (i : Fin 2) :
    deriv (fun t => Function.update z i t 0) = fun _ => if i = 0 then 1 else 0 := by
  fin_cases i
  · funext t
    simp
  · funext t
    simp

-- Integration by parts on `Fin 2 → ℝ` for `f = g = z₀`: `E[z₀ · z₀] = 1 + 0`.
example : ∫ z : Fin 2 → ℝ, (∑ i, (z i * deriv (fun t => (Function.update z i t) 0) (z i) -
        deriv (deriv fun t => (Function.update z i t) 0) (z i))) * z 0
        ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1) = 1 := by
  have he := measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) 0
  have h1 : Integrable (fun z : Fin 2 → ℝ => z 0) (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
    he.integrable_comp_of_integrable ((memLp_id_gaussianReal 1).integrable le_rfl)
  have h2 : Integrable (fun z : Fin 2 → ℝ => z 0 * z 0)
      (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
    simpa [Function.comp_def, sq] using
      he.integrable_comp_of_integrable (memLp_id_gaussianReal 2).integrable_sq
  rw [integral_sum_mul_deriv_update_sub_mul_pi_gaussianReal (f := fun z => z 0)
    (g := fun z => z 0) ?_ ?_ ?_ ?_ ?_ ?_] <;>
    try simp only [deriv_update_zero, deriv_const', zero_mul]
  · simp
  · exact fun _ _ => differentiable_const _
  · intro i z
    fin_cases i
    · simp
    · simp
  · intro i
    fin_cases i
    · simpa using h1
    · simp
  · intro i
    fin_cases i
    · simpa using h2
    · simp
  · exact fun _ => integrable_zero _ _ _
  · intro i
    fin_cases i <;> simp

/-! ### The operator `L` on `h_β` -/

section MultiHermite

variable {ι : Type*} [Fintype ι]

/-- `h_β` is in the domain of `L`. -/
theorem memOrnsteinUhlenbeckDomain_multiHermite (β : ι → ℕ) :
    MemOrnsteinUhlenbeckDomain (multiHermite β) := by
  refine memOrnsteinUhlenbeckDomain_iff.2 ⟨memLp_multiHermite β, ?_⟩
  have e : (fun α : ι → ℕ => ((∑ i, α i : ℕ) : ℝ) ^ 2 * hermiteCoeff (multiHermite β) α ^ 2) =
      fun α => if α = β then ((∑ i, β i : ℕ) : ℝ) ^ 2 else 0 := by
    funext α
    rw [hermiteCoeff_multiHermite]
    by_cases h : α = β
    · subst h
      simp
    · simp [h, Ne.symm h]
  rw [e]
  exact (hasSum_ite_eq β _).summable

/-- The `L²` classes of `U_ρ h_β` for `|ρ| ≤ 1`, extended by `0`. -/
noncomputable def noiseClass (β : ι → ℕ) (ρ : ℝ) :
    Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  if hρ : |ρ| ≤ 1 then
    ((memLp_multiHermite β).gaussianNoiseOp hρ one_le_two).toLp (gaussianNoiseOp ρ (multiHermite β))
  else 0

/-- `noiseClass β ρ` is an `L²` class of `U_ρ h_β` for `|ρ| ≤ 1`. -/
theorem noiseClass_ae (β : ι → ℕ) (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    noiseClass β ρ =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1]
      gaussianNoiseOp ρ (multiHermite β) := by
  simp only [noiseClass, hρ, dite_true]
  exact MemLp.coeFn_toLp _

-- `L h_β = |β| h_β`, in Hermite coordinates.
example (β α : ι → ℕ) :
    (hermiteBasis ι).repr (ornsteinUhlenbeck (multiHermite β)) α =
      if β = α then ((∑ i, β i : ℕ) : ℝ) else 0 := by
  rw [hermiteBasis_repr_ornsteinUhlenbeck (memOrnsteinUhlenbeckDomain_multiHermite β),
    hermiteCoeff_multiHermite]
  by_cases h : β = α
  · subst h
    simp
  · simp [h]

-- `L h_β` is the left derivative at `ρ = 1` of `ρ ↦ U_ρ h_β`, and every left derivative is
-- `L h_β`.
example (β : ι → ℕ) :
    HasDerivWithinAt (noiseClass β) (ornsteinUhlenbeck (multiHermite β)) (Set.Iic 1) 1 :=
  hasDerivWithinAt_gaussianNoiseOp (memOrnsteinUhlenbeckDomain_multiHermite β) (noiseClass_ae β)

example (β : ι → ℕ) {g : Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)}
    (hg : HasDerivWithinAt (noiseClass β) g (Set.Iic 1) 1) :
    g = ornsteinUhlenbeck (multiHermite β) :=
  eq_ornsteinUhlenbeck_of_hasDerivWithinAt (memLp_multiHermite β) (noiseClass_ae β) hg

-- In exponential time, `-L h_β` is the right derivative of `t ↦ U_{e^{-t}} h_β` at `t = 0`.
example (β : ι → ℕ) :
    HasDerivWithinAt (fun t => noiseClass β (Real.exp (-t)))
      (-ornsteinUhlenbeck (multiHermite β)) (Set.Ici 0) 0 :=
  hasDerivWithinAt_gaussianNoiseOp_exp_neg_zero (memOrnsteinUhlenbeckDomain_multiHermite β)
    (noiseClass_ae β)

-- Proposition 11.27 for `h_β`: any derivative of `ρ ↦ U_ρ h_β` at `|ρ| < 1` has Hermite
-- coordinate `|β| ρ ^ (|β| - 1)` at `β` and `0` elsewhere.
example (β α : ι → ℕ) {ρ : ℝ} (hρ : |ρ| < 1)
    {g : Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)} (hg : HasDerivAt (noiseClass β) g ρ) :
    (hermiteBasis ι).repr g α =
      if β = α then ((∑ i, β i : ℕ) : ℝ) * ρ ^ (∑ i, β i - 1) else 0 := by
  rw [hg.unique (hasDerivAt_gaussianNoiseOp (memLp_multiHermite β) (noiseClass_ae β) hρ),
    hermiteBasis_repr_tsum_smul (memℓp_mul_pow_mul_hermiteCoeff (memLp_multiHermite β) hρ),
    hermiteCoeff_multiHermite]
  by_cases h : β = α
  · subst h
    simp
  · simp [h]

-- `(d/dρ) U_ρ h_β = ρ⁻¹ L U_ρ h_β` at `ρ = 1/2`.
example (β : ι → ℕ) :
    HasDerivAt (noiseClass β)
      ((1 / 2 : ℝ)⁻¹ • ornsteinUhlenbeck (gaussianNoiseOp (1 / 2) (multiHermite β))) (1 / 2) :=
  hasDerivAt_gaussianNoiseOp_eq_inv_smul_ornsteinUhlenbeck (memLp_multiHermite β)
    (noiseClass_ae β) (by norm_num [abs_of_pos]) (by norm_num)

-- `(d/dρ) U_ρ h_β = ρ⁻¹ U_ρ L h_β` at `ρ = 1/2`.
example (β : ι → ℕ) :
    HasDerivAt (noiseClass β) ((1 / 2 : ℝ)⁻¹ •
      ((Lp.memLp (ornsteinUhlenbeck (multiHermite β))).gaussianNoiseOp
        (by norm_num [abs_of_pos]) one_le_two).toLp
      (gaussianNoiseOp (1 / 2) ⇑(ornsteinUhlenbeck (multiHermite β)))) (1 / 2) :=
  hasDerivAt_gaussianNoiseOp_eq_inv_smul_gaussianNoiseOp
    (memOrnsteinUhlenbeckDomain_multiHermite β) (noiseClass_ae β) (by norm_num [abs_of_pos])
    (by norm_num)

-- `L U_{1/2} h_β` has Hermite coefficient `|β| (1/2) ^ |β|` at `β`.
example (β : ι → ℕ) :
    hermiteCoeff ⇑(ornsteinUhlenbeck (gaussianNoiseOp (1 / 2) (multiHermite β))) β =
      ((∑ i, β i : ℕ) : ℝ) * (1 / 2) ^ (∑ i, β i) := by
  rw [hermiteCoeff_ornsteinUhlenbeck ((memOrnsteinUhlenbeckDomain_multiHermite β).gaussianNoiseOp
      (by norm_num [abs_of_pos])),
    hermiteCoeff_gaussianNoiseOp (by norm_num [abs_of_pos]) (memLp_multiHermite β),
    hermiteCoeff_multiHermite]
  simp

-- `t ↦ U_{e^{-t}} h_β` has derivative `-L U_{e^{-1}} h_β` at `t = 1`.
example (β : ι → ℕ) :
    HasDerivAt (fun s => noiseClass β (Real.exp (-s)))
      (-ornsteinUhlenbeck (gaussianNoiseOp (Real.exp (-1)) (multiHermite β))) 1 :=
  hasDerivAt_gaussianNoiseOp_exp_neg (memLp_multiHermite β) (noiseClass_ae β) one_pos

end MultiHermite

/-! ### A function outside the domain of `L` -/

/-- The coefficients `(n + 1)⁻¹` of `f = ∑ n, (n + 1)⁻¹ h_n` on `Unit → ℝ`. -/
noncomputable def slowCoeff (α : Unit → ℕ) : ℝ := ((α () : ℝ) + 1)⁻¹

/-- Sums over `Unit → ℕ` are sums over `ℕ`. -/
theorem summable_unit_iff {g : ℕ → ℝ} :
    Summable (fun α : Unit → ℕ => g (α ())) ↔ Summable g :=
  (Equiv.funUnique Unit ℕ).summable_iff

/-- The coefficients `(n + 1)⁻¹` are square-summable. -/
theorem memℓp_slowCoeff : Memℓp slowCoeff 2 := by
  have h : Summable fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2 := by
    refine ((summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)).congr fun n => ?_
    push_cast
    rw [inv_pow]
  refine (memℓp_gen_iff (by norm_num)).2 ((summable_unit_iff.2 h).congr fun α => ?_)
  simp only [slowCoeff, ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- `f = ∑ n, (n + 1)⁻¹ h_n` as an element of `L²(γ)`. -/
noncomputable def slowVec : Lp ℝ 2 (Measure.pi fun _ : Unit => gaussianReal 0 1) :=
  ∑' α, slowCoeff α • hermiteBasis Unit α

/-- `∑ n, n² (n + 1)⁻²` diverges, since its terms are at least `1/4` for `n ≥ 1`. -/
theorem not_summable_slowCoeff :
    ¬ Summable fun α : Unit → ℕ => ((∑ i, α i : ℕ) : ℝ) ^ 2 * slowCoeff α ^ 2 := by
  intro h
  simp only [Finset.univ_unique, Finset.sum_singleton, slowCoeff] at h
  obtain ⟨n, hn, hn1⟩ := ((summable_unit_iff (g := fun n : ℕ => (n : ℝ) ^ 2 *
    ((n : ℝ) + 1)⁻¹ ^ 2)).1 h |>.tendsto_atTop_zero.eventually (gt_mem_nhds
      (by norm_num : (0 : ℝ) < 1 / 4)) |>.and (eventually_ge_atTop 1)).exists
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h2 : (0 : ℝ) < n + 1 := by positivity
  rw [inv_pow, ← div_eq_mul_inv, div_lt_iff₀ (by positivity)] at hn
  nlinarith

-- Exercise 11.18, failing direction: `f ∉ Dom L`, so `ρ ↦ U_ρ f` has no left derivative at `1`.
example {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : Unit => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : Unit => gaussianReal 0 1]
      gaussianNoiseOp ρ ⇑slowVec) :
    ¬ ∃ g, HasDerivWithinAt u g (Set.Iic 1) 1 := by
  rw [exists_hasDerivWithinAt_gaussianNoiseOp_iff (Lp.memLp _) hu, memOrnsteinUhlenbeckDomain_iff]
  rintro ⟨-, h⟩
  simp only [hermiteCoeff_coeFn, slowVec, hermiteBasis_repr_tsum_smul memℓp_slowCoeff] at h
  exact not_summable_slowCoeff h

-- Exercise 11.18(c): `U_{1/2} f` is in the domain of `L`, although `f` is not.
example : MemOrnsteinUhlenbeckDomain (gaussianNoiseOp (1 / 2) ⇑slowVec) :=
  memOrnsteinUhlenbeckDomain_gaussianNoiseOp (Lp.memLp _) (by norm_num [abs_of_pos])

-- Proposition 11.27 without the domain: `ρ ↦ U_ρ f` is differentiable at `ρ = 1/2`.
example {u : ℝ → Lp ℝ 2 (Measure.pi fun _ : Unit => gaussianReal 0 1)}
    (hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[Measure.pi fun _ : Unit => gaussianReal 0 1]
      gaussianNoiseOp ρ ⇑slowVec) :
    HasDerivAt u ((1 / 2 : ℝ)⁻¹ • ornsteinUhlenbeck (gaussianNoiseOp (1 / 2) ⇑slowVec)) (1 / 2) :=
  hasDerivAt_gaussianNoiseOp_eq_inv_smul_ornsteinUhlenbeck (Lp.memLp _) hu
    (by norm_num [abs_of_pos]) (by norm_num)

end CslibFrontierTests.GaussianOrnsteinUhlenbeck
