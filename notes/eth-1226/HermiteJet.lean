import Mathlib

/-! Scratch feasibility prototype for #1226: confluent (Hermite) Taylor-jet reconstruction,
manuscript §3.4 (p. 24) and Appendix B.3 (p. 50). Not library code. -/

open Polynomial Finset Function Matrix

namespace Scratch1226

variable {R : Type*} [CommRing R] {Q J : ℕ}

/-- The order-`J` Taylor jet of `p` at the nodes `t`: `jet p (i, j) = [z^j] p(t_i + z)`. -/
noncomputable def taylorJet (t : Fin Q → R) (J : ℕ) (p : R[X]) : Fin Q × Fin J → R :=
  fun r => (taylor (t r.1) p).coeff r.2

/-- **Uniqueness.** A polynomial of degree `< Q * J` whose order-`J` jet vanishes at `Q` nodes with
unit differences is zero. Any commutative ring. -/
theorem eq_zero_of_taylorJet_eq_zero (t : Fin Q → R) (ht : Pairwise fun i j => IsUnit (t i - t j))
    {p : R[X]} (hp : p.natDegree < Q * J) (h : taylorJet t J p = 0) : p = 0 := by
  nontriviality R
  by_contra h0
  have hdvd : ∀ i ∈ (univ : Finset (Fin Q)), (X - C (t i)) ^ J ∣ p := fun i _ => by
    rw [X_sub_C_pow_dvd_iff, ← taylor_apply, X_pow_dvd_iff]
    exact fun d hd => congrFun h (i, ⟨d, hd⟩)
  have hcop : ((univ : Finset (Fin Q)) : Set (Fin Q)).Pairwise
      (IsCoprime on fun i => (X - C (t i)) ^ J) := fun i _ j _ hij =>
    (isCoprime_X_sub_C_of_isUnit_sub (ht hij)).pow
  have hmon : (∏ i : Fin Q, (X - C (t i)) ^ J).Monic :=
    monic_prod_of_monic _ _ fun i _ => (monic_X_sub_C _).pow J
  refine hmon.not_dvd_of_natDegree_lt h0 ?_ (Finset.prod_dvd_of_coprime hcop hdvd)
  rw [natDegree_prod_of_monic _ _ fun i _ => (monic_X_sub_C _).pow J]
  simpa only [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one, one_mul, sum_const,
    card_univ, Fintype.card_fin, smul_eq_mul, mul_comm J] using hp

/-- Column `c` of the Hermite matrix is the monomial `T ^ u c`. -/
abbrev u (c : Fin Q × Fin J) : ℕ := (finProdFinEquiv c : ℕ)

/-- The integer confluent Vandermonde (Hermite) matrix of B.3:
`V (t, j) u = (u choose j) t ^ (u - j)`, zero for `u < j` since the binomial vanishes. -/
def hermiteMatrix (t : Fin Q → ℤ) (J : ℕ) : Matrix (Fin Q × Fin J) (Fin Q × Fin J) ℤ :=
  fun r c => ((u c).choose r.2 : ℤ) * t r.1 ^ (u c - r.2)

/-- Monomial coefficient vector of `p`, indexed like the columns of the Hermite matrix. -/
def coeffVec (p : R[X]) : Fin Q × Fin J → R := fun c => p.coeff (u c)

theorem taylor_coeff_eq_sum (r : R) (p : R[X]) (n j : ℕ) (hp : p.natDegree < n) :
    (taylor r p).coeff j = ∑ a ∈ range n, ((a.choose j : R) * r ^ (a - j)) * p.coeff a := by
  rw [taylor_coeff, hasseDeriv_apply, sum_over_range' _ (fun a => by simp) n hp, eval_finsetSum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [eval_monomial]
  ring

/-- **The Hermite matrix maps coefficients to the jet**, over any commutative ring. -/
theorem hermiteMatrix_mulVec (t : Fin Q → ℤ) {p : R[X]} (hp : p.natDegree < Q * J) :
    (hermiteMatrix t J).map (Int.cast : ℤ → R) *ᵥ coeffVec p =
      taylorJet (fun i => (t i : R)) J p := by
  funext r
  rw [taylorJet, taylor_coeff_eq_sum _ _ (Q * J) _ hp, Matrix.mulVec, dotProduct,
    ← Fin.sum_univ_eq_sum_range, ← finProdFinEquiv.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [hermiteMatrix, coeffVec, u]

/-- The polynomial with a given coefficient vector. -/
noncomputable def ofCoeffVec (v : Fin Q × Fin J → R) : R[X] :=
  ∑ c, monomial (u c) (v c)

theorem coeffVec_ofCoeffVec (v : Fin Q × Fin J → R) : coeffVec (ofCoeffVec v) = v := by
  funext c
  simp only [coeffVec, ofCoeffVec, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single c (fun b _ hb => ?_) (by simp)]
  · simp
  · have : u c ≠ u b := fun h => hb (finProdFinEquiv.injective (Fin.ext h.symm))
    simp only [Ne.symm this, ↓reduceIte]

theorem natDegree_ofCoeffVec_lt (v : Fin Q × Fin J → R) (hQJ : 0 < Q * J) :
    (ofCoeffVec v).natDegree < Q * J := by
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := Q * J - 1) fun c _ =>
    (natDegree_monomial_le _).trans ?_) (by omega)
  have := (finProdFinEquiv c).isLt
  simp only [u]; omega

/-- **Nonsingularity** of the Hermite matrix at distinct integer nodes. -/
theorem det_hermiteMatrix_ne_zero (t : Fin Q → ℤ) (ht : Injective t) :
    (hermiteMatrix t J).det ≠ 0 := by
  rcases Nat.eq_zero_or_pos (Q * J) with hQJ | hQJ
  · have : IsEmpty (Fin Q × Fin J) := by
      rcases Nat.mul_eq_zero.mp hQJ with h | h <;> subst h <;> infer_instance
    simp
  intro h0
  have h0' : ((hermiteMatrix t J).map (Int.cast : ℤ → ℚ)).det = 0 := by
    rw [← Int.cast_det, h0, Int.cast_zero]
  obtain ⟨v, hv, hV⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0'
  have hp := natDegree_ofCoeffVec_lt v hQJ
  have hjet := hermiteMatrix_mulVec t hp
  rw [coeffVec_ofCoeffVec, hV] at hjet
  have hunit : Pairwise fun i j => IsUnit ((t i : ℚ) - t j) := fun i j hij =>
    isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast ht.ne hij))
  have := eq_zero_of_taylorJet_eq_zero _ hunit hp hjet.symm
  exact hv (by rw [← coeffVec_ofCoeffVec v, this]; rfl)

/-- **Cramer recovery of the constant coefficient (B.1)**, over any commutative ring:
`det V * p(0) = det (V with column 0 replaced by the jet of p)`. -/
theorem det_mul_eval_zero (t : Fin Q → ℤ) {p : R[X]} (hp : p.natDegree < Q * J)
    (c₀ : Fin Q × Fin J) (hc₀ : u c₀ = 0) :
    ((hermiteMatrix t J).det : R) * p.eval 0 =
      (((hermiteMatrix t J).map (Int.cast : ℤ → R)).updateCol c₀
        (taylorJet (fun i => (t i : R)) J p)).det := by
  set V := (hermiteMatrix t J).map (Int.cast : ℤ → R)
  have hdet : ((hermiteMatrix t J).det : R) = V.det := Int.cast_det _
  rw [← Matrix.cramer_apply, ← hermiteMatrix_mulVec t hp, Matrix.cramer_eq_adjugate_mulVec,
    Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet, ← coeff_zero_eq_eval_zero]
  simp [Matrix.smul_mulVec, coeffVec, hc₀]

/-- Over a `ℚ`-algebra, the constant coefficient is a rational combination of the jet. -/
theorem eval_zero_eq (A : Type*) [CommRing A] [Algebra ℚ A] (t : Fin Q → ℤ) (ht : Injective t)
    {p : A[X]} (hp : p.natDegree < Q * J) (c₀ : Fin Q × Fin J) (hc₀ : u c₀ = 0) :
    p.eval 0 = ((hermiteMatrix t J).det : ℚ)⁻¹ •
      (((hermiteMatrix t J).map (Int.cast : ℤ → A)).updateCol c₀
        (taylorJet (fun i => (t i : A)) J p)).det := by
  have hd : ((hermiteMatrix t J).det : ℚ) ≠ 0 := by exact_mod_cast det_hermiteMatrix_ne_zero t ht
  rw [← det_mul_eval_zero t hp c₀ hc₀, ← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
    inv_mul_cancel₀ hd, one_smul]

end Scratch1226
