/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `HermiteExpansion.lean`)

public import CslibFrontier.Foundations.Probability.Gaussian.Hermite
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
import CslibFrontier.Foundations.MeasureTheory.Function.L2Space
import CslibFrontier.Foundations.Probability.Gaussian.PolynomialDense
import Mathlib.Algebra.Polynomial.Sequence

/-!
# Hermite expansions in Gaussian space

The multivariate Hermite polynomials `h_α` (`ProbabilityTheory.multiHermite`) form a Hilbert
basis of `L²(γⁿ)`, for the standard Gaussian measure `γⁿ = Measure.pi fun _ : ι => gaussianReal 0 1`
(`hermiteBasis`; [O'Donnell, Proposition 11.33][ODonnell2014]), and the normalized Hermite
polynomials `h_j` form a Hilbert basis of `L²(γ)` for `γ = gaussianReal 0 1`
(`normalizedHermiteBasis`; [O'Donnell, Proposition 11.30][ODonnell2014]). Orthonormality is
`integral_multiHermite_mul_multiHermite`. Completeness reduces to the density of polynomials
(`topologicalClosure_span_prod_pow_pi_gaussianReal`, Theorem 11.22): each Hermite polynomial `H_j`
has degree `j` and leading coefficient `1`, so every power `x ^ n` is a combination of
`h_0, …, h_n`, and every monomial `∏ i, z i ^ k i` is a combination of the `h_α`. A function
orthogonal to every `h_α` is therefore orthogonal to every monomial, so it vanishes. The
one-dimensional case follows through the measure-preserving equivalence `(Unit → ℝ) ≃ ℝ`.

The *Hermite coefficient* `f̂(α) = ⟨f, h_α⟩ = ∫ f h_α dγⁿ` (`hermiteCoeff`) is the coefficient of
`h_α` in the Hermite expansion `f = ∑ α, f̂(α) h_α`, which converges unconditionally in `L²(γⁿ)`
(`hasSum_hermiteCoeff_smul`; Definition 11.34 and Proposition 11.36); in particular the partial
sums over `|α| ≤ k` converge to `f` (`tendsto_sum_degree_le_hermiteCoeff_smul`). The coefficients
are unique (`hermiteCoeff_eq_of_tendsto_sum_degree_le`, `hermiteCoeff_eq_of_hasSum`), linear on
`L²(γⁿ)`, and satisfy Plancherel's and Parseval's identities `⟨f, g⟩ = ∑ α, f̂(α) ĝ(α)` and
`‖f‖₂² = ∑ α, f̂(α)²` (Proposition 11.36). A multilinear polynomial `∑_S c_S ∏ i ∈ S, zᵢ` has
coefficient `c_S` at the indicator of `S` (`hermiteCoeff_sum_mul_prod`, Remark 11.35). The
Gaussian noise operator acts diagonally, `(U_ρ f)^(α) = ρ ^ |α| f̂(α)`, so
`Stab_ρ[f] = ∑ α, ρ ^ |α| f̂(α)²` (Proposition 11.37).

## Main definitions

* `ProbabilityTheory.hermiteBasis`: the Hilbert basis `(h_α)` of `L²(γⁿ)`.
* `ProbabilityTheory.normalizedHermiteBasis`: the Hilbert basis `(h_j)` of `L²(γ)`.
* `ProbabilityTheory.hermiteCoeff`: the Hermite coefficient `f̂(α) = ⟨f, h_α⟩`.

## Main results

* `ProbabilityTheory.topologicalClosure_span_multiHermite`, `ProbabilityTheory.hermiteBasis`:
  completeness of the Hermite polynomials (Proposition 11.33).
* `ProbabilityTheory.topologicalClosure_span_normalizedHermite`,
  `ProbabilityTheory.normalizedHermiteBasis`: completeness in one dimension (Proposition 11.30).
* `ProbabilityTheory.hermiteBasis_repr`, `ProbabilityTheory.hermiteCoeff_coeFn`,
  `ProbabilityTheory.hermiteBasis_repr_tsum_smul`,
  `ProbabilityTheory.hasSum_hermiteCoeff_smul`,
  `ProbabilityTheory.tendsto_sum_degree_le_hermiteCoeff_smul`,
  `ProbabilityTheory.hermiteCoeff_eq_of_tendsto_sum_degree_le`,
  `ProbabilityTheory.hermiteCoeff_eq_of_hasSum`: the Hermite expansion (Definition 11.34).
* `ProbabilityTheory.hermiteCoeff_sum_mul_multiHermite`,
  `ProbabilityTheory.hermiteCoeff_sum_mul_prod`: the coefficients of finite combinations of
  Hermite polynomials and of multilinear polynomials (Remark 11.35).
* `ProbabilityTheory.hasSum_hermiteCoeff_mul_hermiteCoeff`,
  `ProbabilityTheory.integral_mul_eq_tsum_hermiteCoeff_mul_hermiteCoeff`,
  `ProbabilityTheory.hasSum_hermiteCoeff_sq`,
  `ProbabilityTheory.integral_sq_eq_tsum_hermiteCoeff_sq`: Plancherel and Parseval
  (Proposition 11.36).
* `ProbabilityTheory.hermiteCoeff_gaussianNoiseOp`,
  `ProbabilityTheory.hasSum_hermiteCoeff_gaussianNoiseOp_smul`,
  `ProbabilityTheory.hasSum_gaussianNoiseStability`,
  `ProbabilityTheory.gaussianNoiseStability_eq_tsum`: the Hermite expansions of `U_ρ f` and of
  `Stab_ρ[f]` (Proposition 11.37).

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real Polynomial
open scoped Nat InnerProductSpace

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-! ### Completeness of the Hermite polynomials -/

/-- The Hermite polynomials with real coefficients form a polynomial sequence: `H_j` has degree
`j`. -/
private noncomputable def hermiteSeq : Polynomial.Sequence ℝ where
  elems' j := (hermite j).map (algebraMap ℤ ℝ)
  degree_eq' j := by rw [(hermite_monic j).degree_map, degree_hermite]

/-- Every power `x ^ n` is a finite combination of normalized Hermite polynomials. -/
private theorem exists_pow_eq_sum_normalizedHermite (n : ℕ) :
    ∃ (s : Finset ℕ) (c : ℕ → ℝ), ∀ x : ℝ, x ^ n = ∑ j ∈ s, c j * normalizedHermite j x := by
  have hspan : (X ^ n : ℝ[X]) ∈ Submodule.span ℝ (Set.range hermiteSeq) := by
    rw [hermiteSeq.span fun j => ?_]
    · trivial
    · exact ((hermite_monic j).map (algebraMap ℤ ℝ)).leadingCoeff.symm ▸ isUnit_one
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hspan
  refine ⟨c.support, fun j => c j * √(j ! : ℝ), fun x => ?_⟩
  have hx := congrArg (eval x) hc
  rw [eval_pow, eval_X] at hx
  rw [← hx, Finsupp.sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : √(j ! : ℝ) ≠ 0 := (sqrt_pos.2 (Nat.cast_pos.2 (Nat.factorial_pos j))).ne'
  change eval x (c j • (hermite j).map (algebraMap ℤ ℝ)) = _
  rw [eval_smul, eval_map_algebraMap, normalizedHermite_def, smul_eq_mul, mul_assoc,
    mul_div_cancel₀ _ hj]

/-- A function in `L²(γⁿ)` orthogonal to every `h_α` vanishes almost everywhere: it is orthogonal
to every monomial. -/
private theorem ae_eq_zero_of_forall_integral_mul_multiHermite_eq_zero {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    (h : ∀ α : ι → ℕ,
      ∫ z, f z * multiHermite α z ∂Measure.pi (fun _ : ι => gaussianReal 0 1) = 0) :
    f =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] 0 := by
  classical
  refine ae_eq_zero_of_forall_integral_mul_prod_pow_eq_zero_pi_gaussianReal hf fun k => ?_
  choose s c hsc using exists_pow_eq_sum_normalizedHermite
  have hpt (z : ι → ℝ) : f z * ∏ i, z i ^ k i = ∑ β ∈ Fintype.piFinset fun i => s (k i),
      (∏ i, c (k i) (β i)) * (f z * multiHermite β z) := by
    simp only [hsc, Finset.prod_univ_sum, Finset.mul_sum, multiHermite_def, Finset.prod_mul_distrib]
    exact Finset.sum_congr rfl fun β _ => by ring
  simp only [hpt]
  rw [integral_finsetSum _ fun β _ => ?_]
  · simp only [integral_const_mul, h, mul_zero, Finset.sum_const_zero]
  · exact (hf.integrable_mul (memLp_multiHermite β)).const_mul _

/-- The multivariate Hermite polynomials are orthonormal in `L²(γⁿ)`
[O'Donnell, Proposition 11.33][ODonnell2014]. -/
theorem orthonormal_multiHermite :
    Orthonormal ℝ fun α : ι → ℕ => (memLp_multiHermite α).toLp (multiHermite α) := by
  classical
  refine orthonormal_iff_ite.2 fun α β => ?_
  simp only [L2.inner_toLp_toLp, conj_trivial, integral_multiHermite_mul_multiHermite]

/-- **Completeness of the Hermite polynomials** [O'Donnell, Proposition 11.33][ODonnell2014]: the
multivariate Hermite polynomials `h_α` span a dense subspace of `L²(γⁿ)`. The one-dimensional case,
[O'Donnell, Proposition 11.30][ODonnell2014], is `topologicalClosure_span_normalizedHermite`. -/
theorem topologicalClosure_span_multiHermite :
    (Submodule.span ℝ (Set.range fun α : ι → ℕ =>
      (memLp_multiHermite α).toLp (multiHermite α))).topologicalClosure = ⊤ :=
  L2.topologicalClosure_span_toLp_eq_top _ fun _ =>
    ae_eq_zero_of_forall_integral_mul_multiHermite_eq_zero

/-- The **Hermite basis** of `L²(γⁿ)` [O'Donnell, Proposition 11.33][ODonnell2014]: the
multivariate Hermite polynomials `h_α`, `α : ι → ℕ`, form a Hilbert basis (a complete orthonormal
system) of `L²` of the standard Gaussian measure (`hermiteBasis_apply`). The one-dimensional basis
of [O'Donnell, Proposition 11.30][ODonnell2014] is `normalizedHermiteBasis`. -/
noncomputable def hermiteBasis (ι : Type*) [Fintype ι] :
    HilbertBasis (ι → ℕ) ℝ (Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :=
  HilbertBasis.mk orthonormal_multiHermite topologicalClosure_span_multiHermite.ge

/-- The vectors of the Hermite basis are the classes of the `h_α`. -/
@[simp] theorem coe_hermiteBasis :
    ⇑(hermiteBasis ι) = fun α => (memLp_multiHermite α).toLp (multiHermite α) :=
  HilbertBasis.coe_mk _ _

/-- The `α`-th vector of the Hermite basis is the class of `h_α`. -/
theorem hermiteBasis_apply (α : ι → ℕ) :
    hermiteBasis ι α = (memLp_multiHermite α).toLp (multiHermite α) := by
  rw [coe_hermiteBasis]

/-! ### The one-dimensional Hermite basis -/

/-- The normalized Hermite polynomials are orthonormal in `L²(γ)`
[O'Donnell, Proposition 11.30][ODonnell2014]. -/
theorem orthonormal_normalizedHermite :
    Orthonormal ℝ fun j : ℕ => (memLp_normalizedHermite j).toLp (normalizedHermite j) := by
  classical
  refine orthonormal_iff_ite.2 fun j k => ?_
  simp only [L2.inner_toLp_toLp, conj_trivial, integral_normalizedHermite_mul_normalizedHermite]

/-- **Completeness of the Hermite polynomials in one dimension**
[O'Donnell, Proposition 11.30][ODonnell2014]: the normalized Hermite polynomials `h_j` span a
dense subspace of `L²(γ)`. A function orthogonal to every `h_j` becomes, through
`(Unit → ℝ) ≃ ℝ`, a function orthogonal to every `h_α` with `α : Unit → ℕ`. -/
theorem topologicalClosure_span_normalizedHermite :
    (Submodule.span ℝ (Set.range fun j : ℕ =>
      (memLp_normalizedHermite j).toLp (normalizedHermite j))).topologicalClosure = ⊤ := by
  refine L2.topologicalClosure_span_toLp_eq_top _ fun f hf h => ?_
  have he := measurePreserving_funUnique (gaussianReal 0 1) Unit
  have hg :
      f ∘ MeasurableEquiv.funUnique Unit ℝ =ᵐ[Measure.pi fun _ : Unit => gaussianReal 0 1] 0 :=
    ae_eq_zero_of_forall_integral_mul_multiHermite_eq_zero (hf.comp_measurePreserving he)
      fun α => by
        refine Eq.trans ?_ ((he.integral_comp' fun x => f x * normalizedHermite (α ()) x).trans
          (h (α ())))
        simp only [Function.comp_apply, multiHermite_def, Fintype.prod_unique,
          MeasurableEquiv.funUnique_apply]
  filter_upwards [(he.symm _).quasiMeasurePreserving.ae_eq_comp hg] with x hx
  simpa only [Function.comp_apply, MeasurableEquiv.apply_symm_apply, Pi.zero_apply] using hx

/-- The **one-dimensional Hermite basis** of `L²(γ)` [O'Donnell, Proposition 11.30][ODonnell2014]:
the normalized Hermite polynomials `h_j` form a Hilbert basis of `L²` of the standard Gaussian
measure on `ℝ` (`normalizedHermiteBasis_apply`). -/
noncomputable def normalizedHermiteBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 (gaussianReal 0 1)) :=
  HilbertBasis.mk orthonormal_normalizedHermite topologicalClosure_span_normalizedHermite.ge

/-- The vectors of the one-dimensional Hermite basis are the classes of the `h_j`. -/
@[simp] theorem coe_normalizedHermiteBasis :
    ⇑normalizedHermiteBasis = fun j => (memLp_normalizedHermite j).toLp (normalizedHermite j) :=
  HilbertBasis.coe_mk _ _

/-- The `j`-th vector of the one-dimensional Hermite basis is the class of `h_j`. -/
theorem normalizedHermiteBasis_apply (j : ℕ) :
    normalizedHermiteBasis j = (memLp_normalizedHermite j).toLp (normalizedHermite j) := by
  rw [coe_normalizedHermiteBasis]

/-! ### Hermite coefficients -/

/-- The **Hermite coefficient** `f̂(α) = ⟨f, h_α⟩ = E[f h_α]` of `f` at the multi-index `α`, for
the standard Gaussian measure [O'Donnell, Definition 11.34 and Proposition 11.36][ODonnell2014].
The book defines `f̂(α)` for `f ∈ L²(γⁿ)` as the coefficient of `h_α` in the Hermite expansion of
`f`, and proves `f̂(α) = ⟨f, h_α⟩`. Here that formula is the definition, for arbitrary `f` (the
Bochner integral is `0` when `f h_α` is not integrable). For `f ∈ L²(γⁿ)`, the expansion
`hasSum_hermiteCoeff_smul` and the uniqueness statements
`hermiteCoeff_eq_of_tendsto_sum_degree_le` (for the book's degree-ordered partial sums) and
`hermiteCoeff_eq_of_hasSum` recover the book's definition. -/
noncomputable def hermiteCoeff (f : (ι → ℝ) → ℝ) (α : ι → ℕ) : ℝ :=
  ∫ z, f z * multiHermite α z ∂Measure.pi fun _ : ι => gaussianReal 0 1

/-- Unfolding `f̂(α) = ∫ f h_α dγⁿ`. -/
theorem hermiteCoeff_def (f : (ι → ℝ) → ℝ) (α : ι → ℕ) :
    hermiteCoeff f α = ∫ z, f z * multiHermite α z ∂Measure.pi fun _ : ι => gaussianReal 0 1 := by
  rw [hermiteCoeff]

/-- The Hermite coefficient at the zero multi-index is the mean: `f̂(0) = E[f]`. -/
theorem hermiteCoeff_zero (f : (ι → ℝ) → ℝ) :
    hermiteCoeff f 0 = ∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1 := by
  simp only [hermiteCoeff_def, multiHermite_def, Pi.zero_apply, normalizedHermite_zero,
    Finset.prod_const_one, mul_one]

/-- Functions equal `γⁿ`-almost everywhere have the same Hermite coefficients. -/
theorem hermiteCoeff_congr_ae {f g : (ι → ℝ) → ℝ}
    (h : f =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] g) : hermiteCoeff f = hermiteCoeff g := by
  funext α
  rw [hermiteCoeff_def, hermiteCoeff_def]
  exact integral_congr_ae (h.mono fun z hz => congrArg (· * multiHermite α z) hz)

/-- Hermite coefficients are additive on `L²(γⁿ)`. -/
theorem hermiteCoeff_add {f g : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hg : MemLp g 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) (α : ι → ℕ) :
    hermiteCoeff (fun z => f z + g z) α = hermiteCoeff f α + hermiteCoeff g α := by
  simp only [hermiteCoeff_def, add_mul]
  exact integral_add (hf.integrable_mul (memLp_multiHermite α))
    (hg.integrable_mul (memLp_multiHermite α))

/-- Hermite coefficients commute with scalar multiplication. -/
theorem hermiteCoeff_const_mul (c : ℝ) (f : (ι → ℝ) → ℝ) (α : ι → ℕ) :
    hermiteCoeff (fun z => c * f z) α = c * hermiteCoeff f α := by
  simp only [hermiteCoeff_def, mul_assoc, integral_const_mul]

/-- The Hermite coefficients of `h_α` are those of a basis vector: `ĥ_α(β) = 1` if `α = β` and `0`
otherwise. -/
theorem hermiteCoeff_multiHermite (α β : ι → ℕ) :
    hermiteCoeff (multiHermite α) β = if α = β then 1 else 0 :=
  integral_multiHermite_mul_multiHermite α β

/-- The Hermite coefficients of a finite combination `∑ j ∈ s, c j h_{β j}`: the coefficient at
`α` is the sum of the `c j` with `β j = α`. -/
theorem hermiteCoeff_sum_mul_multiHermite {κ : Type*} (s : Finset κ) (c : κ → ℝ)
    (β : κ → ι → ℕ) (α : ι → ℕ) :
    hermiteCoeff (fun z => ∑ j ∈ s, c j * multiHermite (β j) z) α =
      ∑ j ∈ s, if β j = α then c j else 0 := by
  simp only [hermiteCoeff_def, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ fun j _ => (integrable_multiHermite_mul _ _).const_mul _]
  simp only [integral_const_mul, integral_multiHermite_mul_multiHermite, mul_ite, mul_one,
    mul_zero]

/-- **The Hermite expansion of a multilinear polynomial** [O'Donnell, Remark 11.35][ODonnell2014]:
the multilinear polynomial `∑_{S ∈ s} c_S ∏ i ∈ S, zᵢ` has Hermite coefficient `c_T` at the
indicator multi-index of `T ∈ s`, and `0` at the indicator of `T ∉ s`. By
`hermiteCoeff_sum_mul_multiHermite`, its coefficients at multi-indices that are not indicators
vanish. -/
theorem hermiteCoeff_sum_mul_prod [DecidableEq ι] (s : Finset (Finset ι)) (c : Finset ι → ℝ)
    (T : Finset ι) :
    hermiteCoeff (fun z => ∑ S ∈ s, c S * ∏ i ∈ S, z i) (fun i => if i ∈ T then 1 else 0) =
      if T ∈ s then c T else 0 := by
  have hind (S : Finset ι) : ((fun i => if i ∈ S then 1 else 0 : ι → ℕ) =
      fun i => if i ∈ T then 1 else 0) ↔ S = T := by
    refine ⟨fun h => Finset.ext fun i => ?_, fun h => h ▸ rfl⟩
    have := congrFun h i
    split_ifs at this <;> simp_all
  simp only [← multiHermite_indicator, hermiteCoeff_sum_mul_multiHermite, hind,
    Finset.sum_ite_eq']

/-- The coordinates of `f ∈ L²(γⁿ)` in the Hermite basis are its Hermite coefficients
[O'Donnell, Proposition 11.36][ODonnell2014]. -/
theorem hermiteBasis_repr {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) (α : ι → ℕ) :
    (hermiteBasis ι).repr (hf.toLp f) α = hermiteCoeff f α := by
  rw [HilbertBasis.repr_apply_apply, hermiteBasis_apply, L2.inner_toLp_toLp, hermiteCoeff]
  simp only [conj_trivial, mul_comm]

/-- The Hermite coefficients of an element `v` of `L²(γⁿ)` are its coordinates in the Hermite
basis. -/
theorem hermiteCoeff_coeFn (v : Lp ℝ 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    (α : ι → ℕ) : hermiteCoeff (⇑v) α = (hermiteBasis ι).repr v α := by
  rw [← hermiteBasis_repr (Lp.memLp v), Lp.toLp_coeFn]

/-- A square-summable family `c` is the family of Hermite coordinates of `∑ α, c α h_α`. -/
theorem hermiteBasis_repr_tsum_smul {c : (ι → ℕ) → ℝ} (hc : Memℓp c 2) (α : ι → ℕ) :
    (hermiteBasis ι).repr (∑' β, c β • hermiteBasis ι β) α = c α := by
  rw [((hermiteBasis ι).hasSum_repr_symm ⟨c, hc⟩).tsum_eq, LinearIsometryEquiv.apply_symm_apply]

/-- **The Hermite expansion** [O'Donnell, Definition 11.34 and Proposition 11.36][ODonnell2014]:
every `f ∈ L²(γⁿ)` is the sum `f = ∑ α, f̂(α) h_α`, converging unconditionally in `L²(γⁿ)`. The
book's convergence of the partial sums over `|α| ≤ k` is
`tendsto_sum_degree_le_hermiteCoeff_smul`. -/
theorem hasSum_hermiteCoeff_smul {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    HasSum (fun α => hermiteCoeff f α • (memLp_multiHermite α).toLp (multiHermite α))
      (hf.toLp f) := by
  simpa only [hermiteBasis_repr hf, hermiteBasis_apply] using
    (hermiteBasis ι).hasSum_repr (hf.toLp f)

/-- A multi-index of total degree at most `k` is among those summed in the degree-`k` partial sum
of a Hermite expansion. -/
private theorem mem_degree_le [DecidableEq ι] {α : ι → ℕ} {k : ℕ} (h : ∑ i, α i ≤ k) :
    α ∈ (Fintype.piFinset fun _ : ι => Finset.range (k + 1)).filter (fun α => ∑ i, α i ≤ k) := by
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  exact ⟨fun i => Nat.lt_succ_of_le ((Finset.single_le_sum (fun j _ => Nat.zero_le (α j))
    (Finset.mem_univ i)).trans h), h⟩

/-- The sets of multi-indices of total degree at most `k` exhaust all multi-indices. -/
private theorem tendsto_degree_le [DecidableEq ι] :
    Filter.Tendsto (fun k : ℕ =>
      (Fintype.piFinset fun _ : ι => Finset.range (k + 1)).filter (fun α => ∑ i, α i ≤ k))
      Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_finset_of_monotone
    (fun _ _ hkl _ hα => mem_degree_le ((Finset.mem_filter.1 hα).2.trans hkl))
    fun _ => ⟨_, mem_degree_le le_rfl⟩

/-- **The Hermite expansion by degree** [O'Donnell, Definition 11.34][ODonnell2014]: for
`f ∈ L²(γⁿ)`, the partial sums `∑_{|α| ≤ k} f̂(α) h_α` converge to `f` in `L²(γⁿ)` as `k → ∞`. -/
theorem tendsto_sum_degree_le_hermiteCoeff_smul [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    Filter.Tendsto (fun k : ℕ =>
        ∑ α ∈ (Fintype.piFinset fun _ : ι => Finset.range (k + 1)).filter (fun α => ∑ i, α i ≤ k),
          hermiteCoeff f α • (memLp_multiHermite α).toLp (multiHermite α))
      Filter.atTop (nhds (hf.toLp f)) :=
  (hasSum_hermiteCoeff_smul hf).comp tendsto_degree_le

/-- **Uniqueness of the Hermite expansion by degree** [O'Donnell, Definition 11.34][ODonnell2014]:
if the partial sums `∑_{|α| ≤ k} c α h_α` converge to `f` in `L²(γⁿ)`, then `c` is the family of
Hermite coefficients of `f`. This is the book's definition of `f̂`. -/
theorem hermiteCoeff_eq_of_tendsto_sum_degree_le [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) {c : (ι → ℕ) → ℝ}
    (h : Filter.Tendsto (fun k : ℕ =>
        ∑ α ∈ (Fintype.piFinset fun _ : ι => Finset.range (k + 1)).filter (fun α => ∑ i, α i ≤ k),
          c α • (memLp_multiHermite α).toLp (multiHermite α))
      Filter.atTop (nhds (hf.toLp f))) :
    hermiteCoeff f = c := by
  funext β
  have h' := ((innerSL ℝ ((memLp_multiHermite β).toLp (multiHermite β))).continuous.tendsto
    _).comp h
  rw [← hermiteBasis_repr hf, HilbertBasis.repr_apply_apply, hermiteBasis_apply]
  refine tendsto_nhds_unique h' (tendsto_const_nhds.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop (∑ i, β i)] with k hk
  simp only [Function.comp_apply, map_sum, map_smul, innerSL_apply_apply,
    orthonormal_iff_ite.1 orthonormal_multiHermite β, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, mem_degree_le hk, ite_true]

/-- **Uniqueness of the Hermite expansion** [O'Donnell, Definition 11.34][ODonnell2014]: if
`f = ∑ α, c α h_α` in `L²(γⁿ)`, then `c` is the family of Hermite coefficients of `f`. -/
theorem hermiteCoeff_eq_of_hasSum {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) {c : (ι → ℕ) → ℝ}
    (h : HasSum (fun α => c α • (memLp_multiHermite α).toLp (multiHermite α)) (hf.toLp f)) :
    hermiteCoeff f = c := by
  classical
  exact hermiteCoeff_eq_of_tendsto_sum_degree_le hf (h.comp tendsto_degree_le)

/-- **Plancherel's formula** for Hermite expansions [O'Donnell, Proposition 11.36][ODonnell2014]:
for `f, g ∈ L²(γⁿ)`, `⟨f, g⟩ = ∑ α, f̂(α) ĝ(α)`, the series converging unconditionally. -/
theorem hasSum_hermiteCoeff_mul_hermiteCoeff {f g : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hg : MemLp g 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    HasSum (fun α => hermiteCoeff f α * hermiteCoeff g α)
      (∫ z, f z * g z ∂Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have h := ((hermiteBasis ι).summable_inner_mul_inner (hf.toLp f) (hg.toLp g)).hasSum
  rw [(hermiteBasis ι).tsum_inner_mul_inner, L2.inner_toLp_toLp] at h
  simp only [conj_trivial] at h
  convert h using 2 with α
  rw [← hermiteBasis_repr hf, ← hermiteBasis_repr hg, HilbertBasis.repr_apply_apply,
    HilbertBasis.repr_apply_apply, real_inner_comm]

/-- **Plancherel's formula** for Hermite expansions [O'Donnell, Proposition 11.36][ODonnell2014]:
for `f, g ∈ L²(γⁿ)`, `⟨f, g⟩ = ∑ α, f̂(α) ĝ(α)`. The series is summable by
`hasSum_hermiteCoeff_mul_hermiteCoeff`. -/
theorem integral_mul_eq_tsum_hermiteCoeff_mul_hermiteCoeff {f g : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hg : MemLp g 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ∫ z, f z * g z ∂Measure.pi (fun _ : ι => gaussianReal 0 1) =
      ∑' α, hermiteCoeff f α * hermiteCoeff g α :=
  (hasSum_hermiteCoeff_mul_hermiteCoeff hf hg).tsum_eq.symm

/-- **Parseval's formula** for Hermite expansions [O'Donnell, Proposition 11.36][ODonnell2014]:
for `f ∈ L²(γⁿ)`, `E[f²] = ∑ α, f̂(α)²`, the series converging unconditionally. -/
theorem hasSum_hermiteCoeff_sq {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    HasSum (fun α => hermiteCoeff f α ^ 2)
      (∫ z, f z ^ 2 ∂Measure.pi fun _ : ι => gaussianReal 0 1) := by
  simpa only [sq] using hasSum_hermiteCoeff_mul_hermiteCoeff hf hf

/-- **Parseval's formula** for Hermite expansions [O'Donnell, Proposition 11.36][ODonnell2014]:
for `f ∈ L²(γⁿ)`, `E[f²] = ∑ α, f̂(α)²`. -/
theorem integral_sq_eq_tsum_hermiteCoeff_sq {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ∫ z, f z ^ 2 ∂Measure.pi (fun _ : ι => gaussianReal 0 1) = ∑' α, hermiteCoeff f α ^ 2 :=
  (hasSum_hermiteCoeff_sq hf).tsum_eq.symm

/-! ### The noise operator on Hermite expansions -/

/-- **The noise operator on Hermite coefficients** [O'Donnell, Proposition 11.37][ODonnell2014]:
for `f ∈ L²(γⁿ)` and `|ρ| ≤ 1`, `(U_ρ f)^(α) = ρ ^ |α| f̂(α)`. This follows from self-adjointness
of `U_ρ` and `U_ρ h_α = ρ ^ |α| h_α`, without completeness. -/
theorem hermiteCoeff_gaussianNoiseOp {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) (α : ι → ℕ) :
    hermiteCoeff (gaussianNoiseOp ρ f) α = ρ ^ (∑ i, α i) * hermiteCoeff f α := by
  rw [hermiteCoeff, ← integral_mul_gaussianNoiseOp_comm hρ hf (memLp_multiHermite α)]
  simp only [gaussianNoiseOp_multiHermite hρ, mul_left_comm (f _)]
  rw [integral_const_mul, hermiteCoeff]

/-- **The Hermite expansion of `U_ρ f`** [O'Donnell, Proposition 11.37][ODonnell2014]: for
`f ∈ L²(γⁿ)` and `|ρ| ≤ 1`, `U_ρ f = ∑ α, ρ ^ |α| f̂(α) h_α` in `L²(γⁿ)`. -/
theorem hasSum_hermiteCoeff_gaussianNoiseOp_smul {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    HasSum (fun α => (ρ ^ (∑ i, α i) * hermiteCoeff f α) •
        (memLp_multiHermite α).toLp (multiHermite α))
      ((hf.gaussianNoiseOp hρ one_le_two).toLp (gaussianNoiseOp ρ f)) := by
  simpa only [hermiteCoeff_gaussianNoiseOp hρ hf] using
    hasSum_hermiteCoeff_smul (hf.gaussianNoiseOp hρ one_le_two)

/-- **Noise stability from the Hermite expansion** [O'Donnell, Proposition 11.37][ODonnell2014]:
for `f ∈ L²(γⁿ)` and `|ρ| ≤ 1`, `Stab_ρ[f] = ∑ α, ρ ^ |α| f̂(α)²`, the series converging
unconditionally. -/
theorem hasSum_gaussianNoiseStability {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    HasSum (fun α => ρ ^ (∑ i, α i) * hermiteCoeff f α ^ 2) (gaussianNoiseStability ρ f) := by
  rw [gaussianNoiseStability_eq_integral_mul_gaussianNoiseOp hρ hf]
  convert hasSum_hermiteCoeff_mul_hermiteCoeff hf (hf.gaussianNoiseOp hρ one_le_two) using 2 with α
  rw [hermiteCoeff_gaussianNoiseOp hρ hf]
  ring

/-- **Noise stability from the Hermite expansion** [O'Donnell, Proposition 11.37][ODonnell2014]:
for `f ∈ L²(γⁿ)` and `|ρ| ≤ 1`, `Stab_ρ[f] = ∑ α, ρ ^ |α| f̂(α)²`. -/
theorem gaussianNoiseStability_eq_tsum {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    gaussianNoiseStability ρ f = ∑' α, ρ ^ (∑ i, α i) * hermiteCoeff f α ^ 2 :=
  (hasSum_gaussianNoiseStability hρ hf).tsum_eq.symm

end ProbabilityTheory
