/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, partial derivatives of the generic determinant and permanent)

public import Complexity.Foundations.Data.MvPolynomial.PartialDerivatives
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.StdBasis

/-!
# Partial derivatives of the generic determinant and permanent

The `k`-th order partial derivatives of the generic `n × n` determinant and permanent include, up to
sign, all their `(n - k) × (n - k)` minors, which have disjoint sets of monomials and so are
linearly independent [Kayal and Saptharishi, §5.2][KayalSaptharishi2014]. So their
partial-derivative measure is at least `choose n k ^ 2`. Kayal and Saptharishi state equality; this
file proves the lower bound, over every field.

Both polynomials are sums `∑ σ, w σ • ∏ i, X (σ i, i)` over the permutations, with nonzero weights
`w σ`: signs and ones. Fix sets `R` of rows and `C` of columns, both of size `k`, and a permutation
`τ` mapping `C` onto `R`. Differentiating along the entries `(τ c, c)`, `c ∈ C`, keeps the
permutations that agree with `τ` on `C`, without these entries: the minor deleting `R` and `C`, up
to sign. Instead of comparing supports, evaluate at the `0`/`1` point of the entries `(τ' i, i)` of
another such pair `(R', C', τ')`, with `i ∉ C'`. Some permutation survives only if
`(R', C') = (R, C)`, and then only `τ`. So these `choose n k ^ 2` derivatives are linearly
independent.

## Main results

* `Matrix.choose_sq_le_rank_partialDerivatives_det_mvPolynomialX`,
  `Matrix.choose_sq_le_rank_partialDerivatives_permanent_mvPolynomialX`: the `k`-th order partial
  derivatives of the generic determinant and permanent span at least `choose n k ^ 2` dimensions.

## References

* [N. Kayal, R. Saptharishi, *A selection of lower bounds for arithmetic
  circuits*][KayalSaptharishi2014], §5.2
-/

@[expose] public section

namespace Matrix

open MvPolynomial Equiv Finset

variable {K : Type*} [Field K] {n : ℕ}

/-- The sum of the permutation monomials `∏ i, X (σ i, i)` with weights `w σ`. -/
private noncomputable def permSum (w : Perm (Fin n) → K) : MvPolynomial (Fin n × Fin n) K :=
  ∑ σ, w σ • ∏ i, X (σ i, i)

private theorem pderiv_prod_X (σ : Perm (Fin n)) (r c : Fin n) (S : Finset (Fin n)) :
    pderiv (r, c) (∏ i ∈ S, X (σ i, i) : MvPolynomial (Fin n × Fin n) K) =
      if c ∈ S ∧ σ c = r then ∏ i ∈ S.erase c, X (σ i, i) else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [prod_insert ha, Derivation.leibniz, ih, pderiv_X]
    by_cases hca : c = a
    · subst hca
      by_cases hr : σ c = r <;> simp [ha, hr, erase_insert ha]
    · have hne : (σ a, a) ≠ (r, c) := fun h => hca (congrArg Prod.snd h).symm
      rw [Pi.single_eq_of_ne hne, smul_zero, add_zero, erase_insert_of_ne (Ne.symm hca),
        prod_insert fun h => ha (mem_of_mem_erase h)]
      simp only [mem_insert, hca, false_or]
      split_ifs <;> simp [smul_eq_mul]

private theorem iteratedPDeriv_prod_X (σ τ : Perm (Fin n)) {k : ℕ} (e : Fin k → Fin n)
    (he : Function.Injective e) (S : Finset (Fin n)) :
    iteratedPDeriv (fun t => (τ (e t), e t))
        (∏ i ∈ S, X (σ i, i) : MvPolynomial (Fin n × Fin n) K) =
      if ∀ t, e t ∈ S ∧ σ (e t) = τ (e t) then ∏ i ∈ S \ univ.image e, X (σ i, i) else 0 := by
  classical
  induction k generalizing S with
  | zero => simp
  | succ k ih =>
    rw [iteratedPDeriv_succ_apply]
    have htail : Fin.tail (fun t => (τ (e t), e t)) =
        fun t => (τ ((e ∘ Fin.succ) t), (e ∘ Fin.succ) t) := rfl
    have he0 : e 0 ∉ univ.image (e ∘ Fin.succ) := by
      simpa using fun t h => Fin.succ_ne_zero t (he h)
    have himage : univ.image e = insert (e 0) (univ.image (e ∘ Fin.succ)) := by
      ext x
      simp [Fin.exists_fin_succ, eq_comm]
    rw [htail, ih (e ∘ Fin.succ) (he.comp (Fin.succ_injective k))]
    by_cases htl : ∀ t, (e ∘ Fin.succ) t ∈ S ∧ σ ((e ∘ Fin.succ) t) = τ ((e ∘ Fin.succ) t)
    · rw [ite_eq_left htl, pderiv_prod_X, himage, sdiff_insert]
      have hiff : (∀ t, e t ∈ S ∧ σ (e t) = τ (e t)) ↔ e 0 ∈ S ∧ σ (e 0) = τ (e 0) := by
        rw [Fin.forall_fin_succ]
        exact and_iff_left htl
      by_cases h0 : e 0 ∈ S ∧ σ (e 0) = τ (e 0)
      · rw [ite_eq_left (hiff.2 h0), ite_eq_left ⟨mem_sdiff.2 ⟨h0.1, he0⟩, h0.2⟩]
      · rw [ite_eq_right (mt hiff.1 h0), ite_eq_right fun h => h0 ⟨(mem_sdiff.1 h.1).1, h.2⟩]
    · rw [ite_eq_right htl, map_zero, ite_eq_right fun h => htl fun t => h t.succ]

private theorem iteratedPDeriv_permSum (w : Perm (Fin n) → K) (τ : Perm (Fin n)) {k : ℕ}
    (e : Fin k → Fin n) (he : Function.Injective e) :
    iteratedPDeriv (fun t => (τ (e t), e t)) (permSum w) = ∑ σ, w σ •
      if ∀ t, σ (e t) = τ (e t) then ∏ i ∈ univ \ univ.image e, X (σ i, i) else 0 := by
  simp [permSum, iteratedPDeriv_prod_X _ _ e he]

/-- A permutation mapping a set of columns onto a set of rows of the same size. -/
private theorem exists_perm_mem_iff {R C : Finset (Fin n)} (h : R.card = C.card) :
    ∃ τ : Perm (Fin n), ∀ i, τ i ∈ R ↔ i ∈ C := by
  classical
  let e : {i // i ∈ C} ≃ {i // i ∈ R} := Fintype.equivOfCardEq (by simp [h])
  let f : {i // i ∉ C} ≃ {i // i ∉ R} :=
    Fintype.equivOfCardEq (by simp [Fintype.card_subtype_compl, h])
  refine ⟨Equiv.subtypeCongr e f, fun i => ?_⟩
  by_cases hi : i ∈ C
  · simp [Equiv.subtypeCongr, hi]
  · simpa [Equiv.subtypeCongr, hi] using (f ⟨i, hi⟩).2

/-- If a permutation agrees with `τ` on `C` and with `τ'` off `C`, avoiding `C'`, then the
pairs of rows and columns of `τ` and `τ'` coincide. -/
private theorem eq_of_agree {R C R' C' : Finset (Fin n)} (hR : R.card = R'.card)
    (hC : C.card = C'.card) {σ τ τ' : Perm (Fin n)} (hτ : ∀ i, τ i ∈ R ↔ i ∈ C)
    (hτ' : ∀ i, τ' i ∈ R' ↔ i ∈ C') (hon : ∀ i ∈ C, σ i = τ i)
    (hoff : ∀ i ∉ C, i ∉ C' ∧ τ' i = σ i) : R' = R ∧ C' = C := by
  have hC' : C' = C := eq_of_subset_of_card_le
    (fun i hi => by_contra fun h => (hoff i h).1 hi) hC.le
  refine ⟨eq_of_subset_of_card_le (fun r hr => ?_) hR.le, hC'⟩
  obtain ⟨i, rfl⟩ := σ.surjective r
  by_cases hi : i ∈ C
  · exact hon i hi ▸ (hτ i).2 hi
  · exact absurd ((hoff i hi).2 ▸ hr) (fun h => (hoff i hi).1 ((hτ' i).1 h))

private theorem choose_sq_le_rank_partialDerivatives_permSum (w : Perm (Fin n) → K)
    (hw : ∀ σ, w σ ≠ 0) (k : ℕ) :
    ((n.choose k ^ 2 : ℕ) : Cardinal) ≤ (partialDerivatives k (permSum w)).rank := by
  classical
  -- Pairs of `k`-sets of rows and of columns.
  let s := powersetCard k (univ : Finset (Fin n)) ×ˢ powersetCard k (univ : Finset (Fin n))
  have hcard (ρ : s) : ρ.1.1.card = k ∧ ρ.1.2.card = k := by
    have := ρ.2
    simp only [s, mem_product, mem_powersetCard] at this
    exact ⟨this.1.2, this.2.2⟩
  choose τ hτ using fun ρ : s => exists_perm_mem_iff ((hcard ρ).1.trans (hcard ρ).2.symm)
  -- The columns of each pair, enumerated, and the entries of `τ ρ` there.
  let e (ρ : s) : Fin k → Fin n := ρ.1.2.orderEmbOfFin (hcard ρ).2
  have hrange (ρ : s) : univ.image (e ρ) = ρ.1.2 := image_orderEmbOfFin_univ _ _
  let α (ρ : s) (t : Fin k) : Fin n × Fin n := (τ ρ (e ρ t), e ρ t)
  -- The `0`/`1` point of the entries of `τ ρ` off its columns.
  let point (ρ : s) (x : Fin n × Fin n) : K := if x.2 ∉ ρ.1.2 ∧ τ ρ x.2 = x.1 then 1 else 0
  let E : MvPolynomial (Fin n × Fin n) K →ₗ[K] s → K :=
    LinearMap.pi fun ρ => (aeval (point ρ)).toLinearMap
  have key (ρ ρ' : s) :
      E (iteratedPDeriv (α ρ) (permSum w)) ρ' = if ρ = ρ' then w (τ ρ) else 0 := by
    have hagree (σ : Perm (Fin n)) : ((∀ t, σ (e ρ t) = τ ρ (e ρ t)) ∧
        ∀ i ∈ univ \ univ.image (e ρ), i ∉ ρ'.1.2 ∧ τ ρ' i = σ i) ↔ ρ = ρ' ∧ σ = τ ρ := by
      rw [hrange]
      have hcols : (∀ t, σ (e ρ t) = τ ρ (e ρ t)) ↔ ∀ i ∈ ρ.1.2, σ i = τ ρ i := by
        rw [← hrange ρ]
        simp
      simp only [hcols, mem_sdiff, mem_univ, true_and]
      constructor
      · rintro ⟨hon, hoff⟩
        obtain ⟨hR, hC⟩ := eq_of_agree ((hcard ρ).1.trans (hcard ρ').1.symm)
          ((hcard ρ).2.trans (hcard ρ').2.symm) (hτ ρ) (hτ ρ') hon hoff
        have hρ : ρ = ρ' := Subtype.ext (Prod.ext hR.symm hC.symm)
        subst hρ
        exact ⟨rfl, Equiv.ext fun i => if hi : i ∈ ρ.1.2 then hon i hi else (hoff i hi).2.symm⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨fun _ _ => rfl, fun _ hi => ⟨hi, rfl⟩⟩
    have hterm (σ : Perm (Fin n)) : eval (point ρ') (w σ •
        if ∀ t, σ (e ρ t) = τ ρ (e ρ t) then ∏ i ∈ univ \ univ.image (e ρ), X (σ i, i) else 0) =
          if ρ = ρ' ∧ σ = τ ρ then w σ else 0 := by
      rw [smul_eval, apply_ite (eval (point ρ')), eval_prod, map_zero]
      simp only [eval_X, point, prod_boole, ← hagree σ]
      split_ifs <;> simp_all
    change eval (point ρ') (iteratedPDeriv (α ρ) (permSum w)) = _
    rw [iteratedPDeriv_permSum w (τ ρ) (e ρ) (ρ.1.2.orderEmbOfFin (hcard ρ).2).injective,
      map_sum]
    simp only [hterm]
    by_cases h : ρ = ρ' <;> simp [h]
  have htop : LinearMap.range (E ∘ₗ partialDerivatives k (permSum w)) = ⊤ := by
    refine eq_top_iff.mpr (((Pi.basisFun K s).span_eq).symm.le.trans (Submodule.span_le.mpr ?_))
    rintro _ ⟨ρ, rfl⟩
    refine ⟨Pi.single (α ρ) (w (τ ρ))⁻¹, funext fun ρ' => ?_⟩
    simp only [LinearMap.comp_apply, partialDerivatives_apply,
      Fintype.linearCombination_apply_single, map_smul, Pi.smul_apply, key, Pi.basisFun_apply,
      Pi.single_apply, smul_eq_mul]
    by_cases h : ρ = ρ'
    · subst h
      simp [hw]
    · simp [h, Ne.symm h]
  calc ((n.choose k ^ 2 : ℕ) : Cardinal) = Module.rank K (s → K) := by
        rw [rank_fun', Fintype.card_coe]
        simp [s, sq]
    _ = (E ∘ₗ partialDerivatives k (permSum w)).rank := by rw [LinearMap.rank, htop, rank_top]
    _ ≤ _ := LinearMap.rank_comp_le_right _ _

private theorem det_eq_permSum :
    (mvPolynomialX (Fin n) (Fin n) K).det = permSum fun σ => ((Perm.sign σ : ℤ) : K) := by
  simp [det_apply, permSum, Units.smul_def, Int.cast_smul_eq_zsmul]

/-- The `k`-th order partial derivatives of the generic `n × n` determinant span at least
`choose n k ^ 2` dimensions: up to sign, the `(n - k) × (n - k)` minors are among them, and they
are linearly independent [Kayal and Saptharishi, §5.2][KayalSaptharishi2014]. This holds over
every field. -/
theorem choose_sq_le_rank_partialDerivatives_det_mvPolynomialX (k : ℕ) :
    ((n.choose k ^ 2 : ℕ) : Cardinal) ≤
      (partialDerivatives k (mvPolynomialX (Fin n) (Fin n) K).det).rank := by
  rw [det_eq_permSum]
  refine choose_sq_le_rank_partialDerivatives_permSum _ (fun σ => ?_) k
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]

/-- The `k`-th order partial derivatives of the generic `n × n` permanent span at least
`choose n k ^ 2` dimensions: the `(n - k) × (n - k)` subpermanents are among them, and they are
linearly independent [Kayal and Saptharishi, §5.2][KayalSaptharishi2014]. This holds over every
field. -/
theorem choose_sq_le_rank_partialDerivatives_permanent_mvPolynomialX (k : ℕ) :
    ((n.choose k ^ 2 : ℕ) : Cardinal) ≤
      (partialDerivatives k (mvPolynomialX (Fin n) (Fin n) K).permanent).rank := by
  have : (mvPolynomialX (Fin n) (Fin n) K).permanent = permSum fun _ => 1 := by
    simp [permanent, permSum]
  rw [this]
  exact choose_sq_le_rank_partialDerivatives_permSum _ (fun _ => one_ne_zero) k

end Matrix
