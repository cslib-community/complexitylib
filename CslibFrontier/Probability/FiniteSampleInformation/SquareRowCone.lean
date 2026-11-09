/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.GeneralAsymmetricC1

/-!
# Row-cone geometry for the square simplex

This file contains the stochastic and first-order parts of the square proof.
It is independent of multivariate-polynomial algebra.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`SquareRowCone.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators
open Set Filter

namespace GeneralAsymmetricC1

/-- Delete row `r` and rescale every other row by its row-cone coefficient. -/
def rowConeZeroMatrix {n m : ℕ} (r : Fin n) (lambda : Fin n → ℝ)
    (U : Mat n m) : Mat n m :=
  fun i a => if i = r then 0 else (1 + lambda i) * U i a

/-- Split each nonzero row of `rowConeZeroMatrix` between itself and row `r`. -/
def rowConeChannel {n : ℕ} (r : Fin n) (lambda : Fin n → ℝ) : Mat n n :=
  fun i j => if j = r then
      if i = r then 1 else 0
    else if i = j then 1 / (1 + lambda j)
    else if i = r then lambda j / (1 + lambda j)
    else 0

lemma rowConeZeroMatrix_nonnegative {n m : ℕ} {r : Fin n}
    {lambda : Fin n → ℝ} {U : Mat n m}
    (hlambda : ∀ i, 0 ≤ lambda i) (hU : Nonnegative U) :
    Nonnegative (rowConeZeroMatrix r lambda U) := by
  intro i a
  by_cases hir : i = r
  · simp [rowConeZeroMatrix, hir]
  · simp only [rowConeZeroMatrix, hir, ite_false]
    exact mul_nonneg (by linarith [hlambda i]) (hU i a)

lemma rowConeChannel_stochastic {n : ℕ} {r : Fin n}
    {lambda : Fin n → ℝ} (hlambda : ∀ i, 0 ≤ lambda i) :
    ColumnStochastic (rowConeChannel r lambda) := by
  classical
  constructor
  · intro i j
    by_cases hjr : j = r
    · simp only [rowConeChannel, hjr, ↓reduceIte]
      split_ifs <;> norm_num
    · by_cases hij : i = j
      · subst i
        simp only [rowConeChannel, hjr, ite_false, ite_eq_left]
        exact one_div_nonneg.mpr (by linarith [hlambda j])
      · by_cases hir : i = r
        · subst i
          simp only [rowConeChannel, hjr, ite_false, hij, ite_eq_left]
          exact div_nonneg (hlambda j) (by linarith [hlambda j])
        · simp [rowConeChannel, hjr, hij, hir]
  · intro j
    by_cases hjr : j = r
    · subst j
      simp [rowConeChannel]
    · calc
        ∑ i, rowConeChannel r lambda i j =
            ∑ i, ((if i = j then 1 / (1 + lambda j) else 0) +
              if i = r then lambda j / (1 + lambda j) else 0) := by
                apply Finset.sum_congr rfl
                intro i hi
                by_cases hij : i = j
                · subst i
                  simp [rowConeChannel, hjr]
                · by_cases hir : i = r
                  · subst i
                    simp [rowConeChannel, hjr, hij]
                  · simp [rowConeChannel, hjr, hij, hir]
        _ = 1 / (1 + lambda j) + lambda j / (1 + lambda j) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp
        _ = 1 := by
          have hden : 1 + lambda j ≠ 0 := by linarith [hlambda j]
          field_simp [hden]

lemma rowConeChannel_mul {n m : ℕ} {r : Fin n}
    {lambda : Fin n → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    {U : Mat n m}
    (hrow : ∀ a, U r a =
      ∑ i ∈ Finset.univ.erase r, lambda i * U i a) :
    rowConeChannel r lambda * rowConeZeroMatrix r lambda U = U := by
  classical
  ext i a
  rw [mat_mul_apply]
  by_cases hir : i = r
  · subst i
    calc
      ∑ j, rowConeChannel r lambda r j * rowConeZeroMatrix r lambda U j a =
          ∑ j, if j = r then 0 else lambda j * U j a := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hjr : j = r
            · subst j
              simp [rowConeChannel, rowConeZeroMatrix]
            · simp only [rowConeChannel, rowConeZeroMatrix, hjr, ite_false, ite_eq_left]
              have hden : 1 + lambda j ≠ 0 := by linarith [hlambda j]
              simp only [Ne.symm hjr, ↓reduceIte]
              field_simp [hden]
      _ = ∑ j ∈ Finset.univ.erase r, lambda j * U j a := by
        symm
        calc
          ∑ j ∈ Finset.univ.erase r, lambda j * U j a =
              ∑ j ∈ Finset.univ.erase r,
                (if j = r then 0 else lambda j * U j a) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  simp [Finset.ne_of_mem_erase hj]
          _ = ∑ j, if j = r then 0 else lambda j * U j a :=
            Finset.sum_erase Finset.univ (by simp)
      _ = U r a := (hrow a).symm
  · calc
      ∑ j, rowConeChannel r lambda i j * rowConeZeroMatrix r lambda U j a =
          ∑ j, if j = i then U j a else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hji : j = i
            · subst j
              simp only [rowConeChannel, rowConeZeroMatrix, hir, ite_false, ite_eq_left]
              have hden : 1 + lambda i ≠ 0 := by linarith [hlambda i]
              field_simp [hden]
            · by_cases hjr : j = r
              · subst j
                simp [rowConeChannel, rowConeZeroMatrix, hir, hji]
              · simp [rowConeChannel, rowConeZeroMatrix, hir, hji, hjr, Ne.symm hji]
      _ = U i a := by rw [Finset.sum_ite_eq']; simp

lemma rowConeZeroMatrix_simplex {n m : ℕ} {r : Fin n}
    {lambda : Fin n → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    {U : Mat n m} (hU : Simplex U)
    (hrow : ∀ a, U r a =
      ∑ i ∈ Finset.univ.erase r, lambda i * U i a) :
    Simplex (rowConeZeroMatrix r lambda U) := by
  have hT := rowConeChannel_stochastic (r := r) hlambda
  have hmul := rowConeChannel_mul hlambda hrow
  constructor
  · exact rowConeZeroMatrix_nonnegative hlambda hU.1
  · have hmass := stochastic_mul_mass
      (T := rowConeChannel r lambda)
      (U := rowConeZeroMatrix r lambda U) hT
    rw [hmul, hU.2] at hmass
    exact hmass.symm

lemma fin_two_eq_or_eq {i r s : Fin 2} (hrs : r ≠ s) : i = r ∨ i = s := by
  by_contra h
  push Not at h
  have hirv : i.val ≠ r.val := fun e => h.1 (Fin.ext e)
  have hisv : i.val ≠ s.val := fun e => h.2 (Fin.ext e)
  have hrsv : r.val ≠ s.val := fun e => hrs (Fin.ext e)
  omega

lemma zero_row_vanishing_fin_two {m : ℕ}
    {F : Mat 2 m → ℝ} (hRKO : RKO F)
    {U : Mat 2 m} (hU : Simplex U) {r : Fin 2}
    (hr : ∀ a, U r a = 0) :
    F U = 0 := by
  let s : Fin 2 := if r = 0 then 1 else 0
  have hsr : s ≠ r := by
    dsimp [s]
    split_ifs with h
    · subst r
      decide
    · exact Ne.symm h
  have hcollapse : collapse s * U = U := by
    ext i a
    rw [collapse_mul_apply']
    rcases fin_two_eq_or_eq (i := i) (r := r) (s := s) hsr.symm with hir | his
    · subst i
      simp [hr, Ne.symm hsr]
    · subst i
      simp only [ite_eq_left]
      rw [columnSums]
      have huniv : (Finset.univ : Finset (Fin 2)) = {r, s} := by
        ext j
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        exact fin_two_eq_or_eq (r := r) (s := s) hsr.symm
      rw [huniv]
      simp [hr, Ne.symm hsr]
  have houter : U = outer (rowIndicator s) (columnSums U) := by
    rw [← collapse_mul s U, hcollapse]
  rw [houter]
  exact hRKO (rowIndicator s) (columnSums U) (houter ▸ hU)

theorem zero_row_vanishing_of_two_le {n m : ℕ} [NeZero m]
    (hn : 2 ≤ n) {F : Mat n m → ℝ} (hF : ContDiff ℝ 1 F)
    (hDPI : DPI F) (hRKO : RKO F)
    {U : Mat n m} (hU : Simplex U) {r : Fin n}
    (hr : ∀ a, U r a = 0) :
    F U = 0 := by
  by_cases hn3 : 3 ≤ n
  · exact zero_row_vanishing hn3 hF hDPI hRKO hU hr
  · have hn2 : n = 2 := by omega
    subst n
    exact zero_row_vanishing_fin_two hRKO hU hr

theorem row_cone_vanishing {n m : ℕ} [NeZero m]
    (hn : 2 ≤ n) {F : Mat n m → ℝ} (hF : ContDiff ℝ 1 F)
    (hDPI : DPI F) (hRKO : RKO F)
    {U : Mat n m} (hU : Simplex U) {r : Fin n}
    {lambda : Fin n → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    (hrow : ∀ a, U r a =
      ∑ i ∈ Finset.univ.erase r, lambda i * U i a) :
    F U = 0 := by
  let V := rowConeZeroMatrix r lambda U
  let T := rowConeChannel r lambda
  have hV : Simplex V := rowConeZeroMatrix_simplex hlambda hU hrow
  have hrV : ∀ a, V r a = 0 := by
    intro a
    simp [V, rowConeZeroMatrix]
  have hFV : F V = 0 := zero_row_vanishing_of_two_le hn hF hDPI hRKO hV hrV
  have hT : ColumnStochastic T := rowConeChannel_stochastic hlambda
  have hTU : T * V = U := rowConeChannel_mul hlambda hrow
  have hle := hDPI T V hT hV
  rw [hTU, hFV] at hle
  have hnonneg := nonneg_of_dpi_rko hDPI hRKO hU r
  linarith

lemma positive_tangent_eventually_simplex {n m : ℕ}
    {U V : Mat n m} (hU : Simplex U) (hpos : ∀ i a, 0 < U i a)
    (hmassV : mass V = 0) :
    ∀ᶠ t : ℝ in nhds 0, Simplex (U + t • V) := by
  have hentry : ∀ i a, ∀ᶠ t : ℝ in nhds 0, 0 < U i a + t * V i a := by
    intro i a
    have hc : ContinuousAt (fun t : ℝ => U i a + t * V i a) 0 := by fun_prop
    exact hc.eventually (Ioi_mem_nhds (by simpa using hpos i a))
  have hentry' : ∀ᶠ t : ℝ in nhds 0, ∀ i a, 0 < U i a + t * V i a := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    exact hentry i
  filter_upwards [hentry'] with t ht
  constructor
  · intro i a
    exact (ht i a).le
  · simp [hU.2, hmassV]

lemma row_cone_tangent_derivative_zero {n m : ℕ} [NeZero m]
    (hn : 2 ≤ n) {F : Mat n m → ℝ} (hF : ContDiff ℝ 1 F)
    (hDPI : DPI F) (hRKO : RKO F)
    {U : Mat n m} (hU : Simplex U) (hpos : ∀ i a, 0 < U i a)
    {r : Fin n} {lambda : Fin n → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    (hrow : ∀ a, U r a =
      ∑ i ∈ Finset.univ.erase r, lambda i * U i a)
    {V : Mat n m} (hmassV : mass V = 0) :
    (fderiv ℝ F U) V = 0 := by
  have hFU : F U = 0 := row_cone_vanishing hn hF hDPI hRKO hU hlambda hrow
  have hsimplex := positive_tangent_eventually_simplex hU hpos hmassV
  let phi : ℝ → ℝ := fun t => F (U + t • V)
  have hmin : IsLocalMin phi 0 := by
    change ∀ᶠ t : ℝ in nhds 0, phi 0 ≤ phi t
    filter_upwards [hsimplex] with t ht
    have hnonneg := nonneg_of_dpi_rko hDPI hRKO ht r
    simpa [phi, hFU] using hnonneg
  have hdifferentiable : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hd := hasDerivAt_affine (U := U) (V := V) (hdifferentiable U)
  have hevent : phi =ᶠ[nhds 0] (fun t : ℝ => F (U + t • V)) :=
    Filter.Eventually.of_forall fun _ => rfl
  have hdphi := hd.congr_of_eventuallyEq hevent
  exact hmin.hasDerivAt_eq_zero hdphi

end GeneralAsymmetricC1


end

end Cslib.FiniteSampleInformation
