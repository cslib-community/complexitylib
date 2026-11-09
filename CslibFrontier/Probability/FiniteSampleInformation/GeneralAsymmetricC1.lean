/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib

/-!
# General asymmetric simplex rigidity by the C¹ route

This file formalizes the differential merging-defect proof for `n > m ≥ 2`.
Rank-one vanishing is expressed constructively using outer products; on the
probability simplex this is equivalent to vanishing on rank-at-most-one
matrices, since the zero matrix is not in the simplex.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`GeneralAsymmetricC1.lean` at commit
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

/-- Rectangular real matrices, presented as their (definitionally equal) iterated function type.
This presentation lets the calculus API use the canonical finite-product norm without a
typeclass diamond between `Matrix`'s algebraic instances and its optional norm instances. -/
abbrev Mat (n m : ℕ) := Fin n → Fin m → ℝ

/-- Matrix multiplication on the function presentation of rectangular matrices. -/
instance matHMul {n p m : ℕ} : HMul (Mat n p) (Mat p m) (Mat n m) :=
  ⟨fun A B i a => ∑ j, A i j * B j a⟩

lemma mat_mul_apply {n p m : ℕ} (A : Mat n p) (B : Mat p m)
    (i : Fin n) (a : Fin m) :
    (A * B) i a = ∑ j, A i j * B j a := rfl

/-- Entrywise nonnegativity of a rectangular real table. -/
@[expose] def Nonnegative {n m : ℕ} (U : Mat n m) : Prop :=
  ∀ i a, 0 ≤ U i a

/-- The sum of all entries of a real table. -/
@[expose] def mass {n m : ℕ} (U : Mat n m) : ℝ :=
  ∑ i, ∑ a, U i a

/-- A nonnegative rectangular real table of total mass one. -/
@[expose] def Simplex {n m : ℕ} (U : Mat n m) : Prop :=
  Nonnegative U ∧ mass U = 1

/-- A square nonnegative matrix whose columns sum to one. -/
@[expose] def ColumnStochastic {n : ℕ} (T : Mat n n) : Prop :=
  (∀ i j, 0 ≤ T i j) ∧ (∀ j, ∑ i, T i j = 1)

/-- The outer product of two real vectors. -/
@[expose] def outer {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) : Mat n m :=
  fun i a => x i * y a

/-- One-sided fixed-alphabet data processing on every closed-simplex table. -/
@[expose] def DPI {n m : ℕ} (F : Mat n m → ℝ) : Prop :=
  ∀ (T : Mat n n) (U : Mat n m),
    ColumnStochastic T → Simplex U → F (T * U) ≤ F U

/-- Lean-friendly rank-one vanishing.  The witness is an outer product. -/
@[expose] def RKO {n m : ℕ} (F : Mat n m → ℝ) : Prop :=
  ∀ (x : Fin n → ℝ) (y : Fin m → ℝ),
    Simplex (outer x y) → F (outer x y) = 0

/-- Paper-facing rank-one vanishing: `F` vanishes at every simplex matrix whose
matrix rank is at most one. -/
@[expose] def RankOneVanishing {n m : ℕ} (F : Mat n m → ℝ) : Prop :=
  ∀ U, Simplex U → (Matrix.of U).rank ≤ 1 → F U = 0

/-- Every outer product has matrix rank at most one. -/
lemma rank_outer_le_one {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    (Matrix.of (outer x y)).rank ≤ 1 := by
  change (Matrix.vecMulVec x y).rank ≤ 1
  exact Matrix.rank_vecMulVec_le x y

/-- Over `ℝ`, every matrix of rank at most one is an outer product.  This
algebraic statement also covers the zero matrix, so the simplex mass condition
is not needed for the representation itself. -/
lemma exists_outer_of_rank_le_one {n m : ℕ} (U : Mat n m)
    (hrank : (Matrix.of U).rank ≤ 1) :
    ∃ x : Fin n → ℝ, ∃ y : Fin m → ℝ, U = outer x y := by
  classical
  let A : Matrix (Fin n) (Fin m) ℝ := Matrix.of U
  let W : Submodule ℝ (Fin m → ℝ) :=
    Submodule.span ℝ (Set.range A.row)
  have hfinrank : Module.finrank ℝ W ≤ 1 := by
    rw [← Matrix.rank_eq_finrank_span_row A]
    exact hrank
  obtain ⟨v, hv⟩ := (finrank_le_one_iff (K := ℝ) (V := W)).mp hfinrank
  have hrow : ∀ i : Fin n, ∃ c : ℝ, c • v =
      (⟨A.row i, Submodule.subset_span (Set.mem_range_self i)⟩ : W) := by
    intro i
    exact hv _
  choose x hx using hrow
  refine ⟨x, v.1, ?_⟩
  ext i a
  have hxa := congrArg (fun w : W => w.1 a) (hx i)
  simpa [A, outer] using hxa.symm

/-- The constructive outer-product formulation `RKO` is exactly the paper's
rank-at-most-one formulation on the probability simplex. -/
theorem rko_iff_rankOneVanishing {n m : ℕ} (F : Mat n m → ℝ) :
    RKO F ↔ RankOneVanishing F := by
  constructor
  · intro hRKO U hU hrank
    obtain ⟨x, y, rfl⟩ := exists_outer_of_rank_le_one U hrank
    exact hRKO x y hU
  · intro hRank x y hsimplex
    exact hRank (outer x y) hsimplex (rank_outer_le_one x y)

/-- The precise local regularity used by the proof: `F` is C¹ at every point
of the probability simplex. -/
@[expose] def ContDiffOnSimplex {n m : ℕ} (F : Mat n m → ℝ) : Prop :=
  ∀ U, Simplex U → ContDiffAt ℝ 1 F U

lemma stochastic_mul_nonnegative {n m : ℕ}
    {T : Mat n n} {U : Mat n m}
    (hT : ColumnStochastic T) (hU : Nonnegative U) :
    Nonnegative (T * U) := by
  intro i a
  rw [mat_mul_apply]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hT.1 i j) (hU j a)

lemma stochastic_mul_mass {n m : ℕ}
    {T : Mat n n} {U : Mat n m}
    (hT : ColumnStochastic T) :
    mass (T * U) = mass U := by
  simp only [mass, mat_mul_apply]
  calc
    ∑ i, ∑ a, ∑ j, T i j * U j a =
        ∑ a, ∑ j, (∑ i, T i j) * U j a := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          congr 1
          funext a
          rw [Finset.sum_comm]
    _ = ∑ a, ∑ j, U j a := by simp [hT.2]
    _ = ∑ j, ∑ a, U j a := Finset.sum_comm

lemma stochastic_mul_simplex {n m : ℕ}
    {T : Mat n n} {U : Mat n m}
    (hT : ColumnStochastic T) (hU : Simplex U) :
    Simplex (T * U) := by
  exact ⟨stochastic_mul_nonnegative hT hU.1,
    (stochastic_mul_mass hT).trans hU.2⟩

/-- The constant-output channel sending every state to one designated row. -/
@[expose] def collapse {n : ℕ} (r : Fin n) : Mat n n :=
  fun i _ => if i = r then 1 else 0

lemma collapse_stochastic {n : ℕ} (r : Fin n) :
    ColumnStochastic (collapse r) := by
  classical
  constructor
  · intro i j
    simp only [collapse]
    split_ifs <;> norm_num
  · intro j
    simp [collapse]

/-- The coordinate vector of a designated row. -/
@[expose] def rowIndicator {n : ℕ} (r : Fin n) : Fin n → ℝ :=
  fun i => if i = r then 1 else 0

/-- The vector of column masses of a rectangular table. -/
@[expose] def columnSums {n m : ℕ} (U : Mat n m) : Fin m → ℝ :=
  fun a => ∑ i, U i a

lemma collapse_mul {n m : ℕ} (r : Fin n) (U : Mat n m) :
    collapse r * U = outer (rowIndicator r) (columnSums U) := by
  classical
  ext i a
  by_cases hi : i = r
  · simp [collapse, outer, rowIndicator, columnSums, mat_mul_apply, hi]
  · simp [collapse, outer, rowIndicator, columnSums, mat_mul_apply, hi]

lemma nonneg_of_dpi_rko {n m : ℕ}
    {F : Mat n m → ℝ} (hDPI : DPI F) (hRKO : RKO F)
    {U : Mat n m} (hU : Simplex U) (r : Fin n) :
    0 ≤ F U := by
  have hS := stochastic_mul_simplex (collapse_stochastic r) hU
  have hEq := collapse_mul r U
  have hzero : F (collapse r * U) = 0 := by
    rw [hEq]
    exact hRKO (rowIndicator r) (columnSums U) (hEq ▸ hS)
  have hle := hDPI (collapse r) U (collapse_stochastic r) hU
  simpa [hzero] using hle

/-- Merge source row `r` into target row `i`. -/
def merge {n : ℕ} (i r : Fin n) : Mat n n :=
  fun a b => if b = r then (if a = i then 1 else 0)
    else if a = b then 1 else 0

lemma merge_stochastic {n : ℕ} (i r : Fin n) :
    ColumnStochastic (merge i r) := by
  classical
  constructor
  · intro a b
    simp only [merge]
    split_ifs <;> norm_num
  · intro b
    by_cases hb : b = r
    · simp [merge, hb]
    · simp [merge, hb]

lemma merge_mul_apply {n m : ℕ} {i r : Fin n} (hir : i ≠ r)
    (U : Mat n m) (a : Fin n) (c : Fin m) :
    (merge i r * U) a c =
      if a = i then U i c + U r c else if a = r then 0 else U a c := by
  classical
  rw [mat_mul_apply]
  by_cases hai : a = i
  · subst a
    simp only [ite_eq_left]
    calc
      ∑ b, merge i r i b * U b c =
          ∑ b, ((if b = r then U b c else 0) +
            if b = i then U b c else 0) := by
              apply Finset.sum_congr rfl
              intro b hb
              by_cases hbr : b = r
              · subst b
                simp [merge, Ne.symm hir]
              · by_cases hbi : b = i
                · subst b
                  simp [merge, hbr]
                · simp [merge, hbr, hbi, Ne.symm hbi]
      _ = U r c + U i c := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp
    ring
  · by_cases har : a = r
    · subst a
      simp only [ite_eq_right hai, ite_eq_left]
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hbr : b = r
      · subst b
        simp [merge, Ne.symm hir]
      · simp [merge, hbr, Ne.symm hbr]
    · simp only [ite_eq_right hai, ite_eq_right har]
      calc
        ∑ b, merge i r a b * U b c =
            ∑ b, if b = a then U b c else 0 := by
              apply Finset.sum_congr rfl
              intro b hb
              by_cases hbr : b = r
              · subst b
                simp [merge, hai, Ne.symm har]
              · by_cases hba : b = a
                · subst b
                  simp [merge, hbr]
                · simp [merge, hbr, hba, Ne.symm hba]
        _ = U a c := by rw [Finset.sum_ite_eq']; simp

/-- Split target row `i` into rows `i` and `r`. -/
@[expose] def split {n : ℕ} (i r : Fin n) (theta : ℝ) : Mat n n :=
  fun a b => if b = i then
      (if a = i then theta else if a = r then 1 - theta else 0)
    else if a = b then 1 else 0

lemma split_stochastic {n : ℕ} {i r : Fin n} (hir : i ≠ r)
    {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    ColumnStochastic (split i r theta) := by
  classical
  constructor
  · intro a b
    simp only [split]
    split_ifs <;> norm_num <;> linarith
  · intro b
    by_cases hbi : b = i
    · subst b
      calc
        ∑ a, split i r theta a i =
            ∑ a, ((if a = i then theta else 0) +
              if a = r then 1 - theta else 0) := by
                apply Finset.sum_congr rfl
                intro a ha
                by_cases hai : a = i
                · subst a
                  simp [split, hir]
                · by_cases har : a = r
                  · subst a
                    simp [split, Ne.symm hir]
                  · simp [split, hai, har]
        _ = 1 := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp
    · simp [split, hbi]

lemma split_mul_apply {n m : ℕ} {i r : Fin n} (hir : i ≠ r)
    (theta : ℝ) (U : Mat n m) (a : Fin n) (c : Fin m) :
    (split i r theta * U) a c =
      if a = i then theta * U i c else
        if a = r then (1 - theta) * U i c + U r c else U a c := by
  classical
  rw [mat_mul_apply]
  by_cases hai : a = i
  · subst a
    simp only [ite_eq_left]
    calc
      ∑ b, split i r theta i b * U b c =
          ∑ b, if b = i then theta * U b c else 0 := by
            apply Finset.sum_congr rfl
            intro b hb
            by_cases hbi : b = i
            · subst b
              simp [split]
            · simp [split, hbi, Ne.symm hbi]
      _ = theta * U i c := by rw [Finset.sum_ite_eq']; simp
  · by_cases har : a = r
    · subst a
      simp only [ite_eq_right hai, ite_eq_left]
      calc
        ∑ b, split i r theta r b * U b c =
            ∑ b, ((if b = i then (1 - theta) * U b c else 0) +
              if b = r then U b c else 0) := by
              apply Finset.sum_congr rfl
              intro b hb
              by_cases hbi : b = i
              · subst b
                simp [split, hir, Ne.symm hir]
              · by_cases hbr : b = r
                · subst b
                  simp [split, hbi]
                · simp [split, hbi, hbr, Ne.symm hbr]
        _ = (1 - theta) * U i c + U r c := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp
    · simp only [ite_eq_right hai, ite_eq_right har]
      calc
        ∑ b, split i r theta a b * U b c =
            ∑ b, if b = a then U b c else 0 := by
              apply Finset.sum_congr rfl
              intro b hb
              by_cases hbi : b = i
              · subst b
                simp [split, hai, har, Ne.symm hai]
              · by_cases hba : b = a
                · subst b
                  simp [split, hbi]
                · simp [split, hbi, hba, Ne.symm hba]
        _ = U a c := by rw [Finset.sum_ite_eq']; simp

lemma split_merge_reconstruct {n m : ℕ} {i r : Fin n} (hir : i ≠ r)
    {U : Mat n m} {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hpar : ∀ c, U r c = lambda * U i c) :
    split i r (1 / (1 + lambda)) * (merge i r * U) = U := by
  classical
  have hden : 0 < 1 + lambda := by linarith
  ext a c
  rw [split_mul_apply hir]
  by_cases hai : a = i
  · subst a
    simp only [ite_eq_left]
    rw [merge_mul_apply hir U i c]
    simp only [one_div, ↓reduceIte, hpar]
    field_simp [ne_of_gt hden]
  · by_cases har : a = r
    · subst a
      simp only [ite_eq_right (Ne.symm hir), ite_eq_left]
      rw [merge_mul_apply hir U i c, merge_mul_apply hir U r c]
      simp only [one_div, ↓reduceIte, hpar, Ne.symm hir, add_zero]
      field_simp [ne_of_gt hden]
      ring
    · simp only [ite_eq_right hai, ite_eq_right har]
      rw [merge_mul_apply hir U a c]
      simp [hai, har]

lemma parallel_row_invariance {n m : ℕ}
    {F : Mat n m → ℝ} (hDPI : DPI F)
    {U : Mat n m} (hU : Simplex U)
    {i r : Fin n} (hir : i ≠ r)
    {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hpar : ∀ c, U r c = lambda * U i c) :
    F U = F (merge i r * U) := by
  have hden : 0 < 1 + lambda := by linarith
  have htheta0 : 0 ≤ (1 / (1 + lambda) : ℝ) := (one_div_pos.mpr hden).le
  have htheta1 : (1 / (1 + lambda) : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hden]
    linarith
  have hmerged := stochastic_mul_simplex (merge_stochastic i r) hU
  have hforward := hDPI (merge i r) U (merge_stochastic i r) hU
  have hbackward := hDPI (split i r (1 / (1 + lambda))) (merge i r * U)
    (split_stochastic hir htheta0 htheta1) hmerged
  rw [split_merge_reconstruct hir hlambda hpar] at hbackward
  exact le_antisymm hbackward hforward

/-! ## Elementary tangent directions and one-variable calculus -/

/-- The matrix unit supported at `(i, a)`. -/
@[expose] def unit {n m : ℕ} (i : Fin n) (a : Fin m) : Mat n m :=
  fun j b => if j = i ∧ b = a then 1 else 0

@[simp] lemma unit_apply {n m : ℕ} (i j : Fin n) (a b : Fin m) :
    unit i a j b = if j = i ∧ b = a then 1 else 0 := rfl

@[simp] lemma mass_unit {n m : ℕ} (i : Fin n) (a : Fin m) :
    mass (unit i a) = 1 := by
  classical
  rw [mass]
  calc
    ∑ j, ∑ b, unit i a j b = ∑ j, if j = i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j
        simp [unit]
      · simp [unit, hji]
    _ = 1 := by simp

@[simp] lemma mass_add {n m : ℕ} (U V : Mat n m) :
    mass (U + V) = mass U + mass V := by
  simp [mass, Finset.sum_add_distrib]

@[simp] lemma mass_smul {n m : ℕ} (t : ℝ) (U : Mat n m) :
    mass (t • U) = t * mass U := by
  simp [mass, Finset.mul_sum]

@[simp] lemma mass_neg {n m : ℕ} (U : Mat n m) :
    mass (-U) = -mass U := by
  simp [mass, Finset.sum_neg_distrib]

@[simp] lemma mass_unit_sub_unit {n m : ℕ}
    (i j : Fin n) (a : Fin m) :
    mass (unit i a - unit j a) = 0 := by
  simp [sub_eq_add_neg]

lemma affine_unit_perturb_simplex {n m : ℕ}
    {U : Mat n m} (hU : Simplex U) {r k : Fin n} (hrk : r ≠ k)
    (a : Fin m) {t : ℝ} (ht : t ∈ Ioo (-U r a) (U k a)) :
    Simplex (U + t • (unit r a - unit k a)) := by
  classical
  constructor
  · intro j b
    by_cases hjr : j = r
    · subst j
      by_cases hba : b = a
      · subst b
        simp [unit, hrk]
        linarith [ht.1]
      · simp [unit, hba, hU.1 r b]
    · by_cases hjk : j = k
      · subst j
        by_cases hba : b = a
        · subst b
          simp [unit, Ne.symm hrk]
          linarith [ht.2]
        · simp [unit, hba, hU.1 k b]
      · simp [unit, hjr, hjk, hU.1 j b]
  · simp [hU.2]

lemma hasDerivAt_affine {n m : ℕ}
    {F : Mat n m → ℝ}
    {U V : Mat n m} (hF : DifferentiableAt ℝ F U) :
    HasDerivAt (fun t : ℝ => F (U + t • V)) ((fderiv ℝ F U) V) 0 := by
  have hline : HasDerivAt (fun t : ℝ => U + t • V) V 0 := by
    simpa using ((hasDerivAt_id (x := (0 : ℝ))).smul_const V).const_add U
  have hFU : HasFDerivAt F (fderiv ℝ F U) (U + (0 : ℝ) • V) := by
    simpa using hF.hasFDerivAt
  simpa [Function.comp_def] using
    hFU.comp_hasDerivAt (𝕜 := ℝ) 0 hline

lemma hasDerivAt_affine_at {n m : ℕ}
    {F : Mat n m → ℝ} {U V : Mat n m} (x : ℝ)
    (hF : DifferentiableAt ℝ F (U + x • V)) :
    HasDerivAt (fun t : ℝ => F (U + t • V))
      ((fderiv ℝ F (U + x • V)) V) x := by
  have hline : HasDerivAt (fun t : ℝ => U + t • V) V x := by
    simpa using ((hasDerivAt_id (x := x)).smul_const V).const_add U
  exact hF.hasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) x hline

lemma merge_mul_unit_sub_unit {n m : ℕ} {i r k : Fin n}
    (hir : i ≠ r) (hki : k ≠ i) (hkr : k ≠ r) (a : Fin m) :
    merge i r * (unit r a - unit k a) = unit i a - unit k a := by
  classical
  ext j b
  rw [merge_mul_apply hir]
  by_cases hji : j = i
  · subst j
    simp [unit, hir, Ne.symm hki, Ne.symm hkr]
  · by_cases hjr : j = r
    · subst j
      simp [unit, Ne.symm hir, Ne.symm hkr]
    · simp [unit, hji, hjr]

lemma mat_mul_affine {n p m : ℕ} (A : Mat n p) (U V : Mat p m) (t : ℝ) :
    A * (U + t • V) = A * U + t • (A * V) := by
  ext i a
  simp only [mat_mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma exists_third_row {n : ℕ} (hn : 3 ≤ n) {i r : Fin n} (_hir : i ≠ r) :
    ∃ k : Fin n, k ≠ i ∧ k ≠ r := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, r} := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hki : k = i
    · exact Or.inl hki
    · exact Or.inr (h k hki)
  have hc := Finset.card_le_card hsub
  have hp : ({i, r} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, Fintype.card_fin] at hc
  omega

/-- The row-split path used to approach a zero-row face. -/
def splitPoint {n m : ℕ} (i r : Fin n) (theta : ℝ) (U : Mat n m) : Mat n m :=
  split i r theta * U

lemma continuous_splitPoint {n m : ℕ} {i r : Fin n} (hir : i ≠ r)
    (U : Mat n m) :
    Continuous (fun theta : ℝ => splitPoint i r theta U) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro a
  simp only [splitPoint, split_mul_apply hir]
  split_ifs <;> fun_prop

lemma splitPoint_one_of_zero_row {n m : ℕ} {i r : Fin n} (hir : i ≠ r)
    {U : Mat n m} (hr : ∀ a, U r a = 0) :
    splitPoint i r 1 U = U := by
  ext j a
  rw [splitPoint, split_mul_apply hir]
  by_cases hji : j = i
  · subst j
    simp
  · by_cases hjr : j = r
    · subst j
      simp [Ne.symm hir, hr]
    · simp [hji, hjr]

lemma merge_splitPoint_of_zero_row {n m : ℕ} {i r : Fin n} (hir : i ≠ r)
    {U : Mat n m} (hr : ∀ a, U r a = 0) (theta : ℝ) :
    merge i r * splitPoint i r theta U = U := by
  ext j a
  rw [merge_mul_apply hir, splitPoint]
  by_cases hji : j = i
  · subst j
    simp [split_mul_apply hir, Ne.symm hir, hr]
    ring
  · by_cases hjr : j = r
    · subst j
      simp [hr, Ne.symm hir]
    · simp [split_mul_apply hir, hji, hjr]

lemma splitPoint_parallel {n m : ℕ} {i r : Fin n} (hir : i ≠ r)
    {U : Mat n m} (hr : ∀ a, U r a = 0)
    {theta : ℝ} (htheta : 0 < theta) :
    ∀ a, splitPoint i r theta U r a =
      ((1 - theta) / theta) * splitPoint i r theta U i a := by
  intro a
  simp only [splitPoint, split_mul_apply hir]
  simp only [Ne.symm hir, ↓reduceIte, hr, add_zero]
  field_simp [ne_of_gt htheta]

lemma splitPoint_positive {n m : ℕ} {i r : Fin n} (hir : i ≠ r)
    {U : Mat n m} (hr : ∀ a, U r a = 0)
    (hpos : ∀ j, j ≠ r → ∀ a, 0 < U j a)
    {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) 1) :
    ∀ j a, 0 < splitPoint i r theta U j a := by
  intro j a
  rw [splitPoint, split_mul_apply hir]
  by_cases hji : j = i
  · subst j
    simp only [ite_eq_left]
    exact mul_pos htheta.1 (hpos i hir a)
  · by_cases hjr : j = r
    · subst j
      simp only [Ne.symm hir, ↓reduceIte, hr, add_zero]
      exact mul_pos (sub_pos.mpr htheta.2) (hpos i hir a)
    · simp [hji, hjr, hpos j hjr a]

lemma splitPoint_simplex {n m : ℕ} {i r : Fin n} (hir : i ≠ r)
    {U : Mat n m} (hU : Simplex U) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) 1) :
    Simplex (splitPoint i r theta U) := by
  exact stochastic_mul_simplex
    (split_stochastic hir htheta.1 htheta.2) hU

/-! ## The local-minimum identity at a split point -/

lemma splitPoint_derivative_identity_of_contDiffOnSimplex
    {n m : ℕ}
    {F : Mat n m → ℝ} (hF : ContDiffOnSimplex F) (hDPI : DPI F)
    {U : Mat n m} (hU : Simplex U) {i r k : Fin n}
    (hir : i ≠ r) (hki : k ≠ i) (hkr : k ≠ r)
    (hr : ∀ a, U r a = 0)
    (hpos : ∀ j, j ≠ r → ∀ a, 0 < U j a)
    (a : Fin m) {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ F (splitPoint i r theta U)) (unit r a - unit k a) =
      (fderiv ℝ F U) (unit i a - unit k a) := by
  let S : Mat n m := splitPoint i r theta U
  let W : Mat n m := unit r a - unit k a
  let Z : Mat n m := unit i a - unit k a
  have hS : Simplex S := splitPoint_simplex hir hU
    ⟨htheta.1.le, htheta.2.le⟩
  have hSpos : ∀ j b, 0 < S j b :=
    splitPoint_positive hir hr hpos htheta
  have hmergeS : merge i r * S = U :=
    merge_splitPoint_of_zero_row hir hr theta
  have hmergeW : merge i r * W = Z :=
    merge_mul_unit_sub_unit hir hki hkr a
  have hpert : ∀ᶠ t : ℝ in nhds 0, Simplex (S + t • W) := by
    have hI : Ioo (-S r a) (S k a) ∈ nhds (0 : ℝ) :=
      Ioo_mem_nhds (neg_lt_zero.mpr (hSpos r a)) (hSpos k a)
    filter_upwards [hI] with t ht
    exact affine_unit_perturb_simplex (r := r) (k := k) hS (Ne.symm hkr) a ht
  have hmergeLine (t : ℝ) :
      merge i r * (S + t • W) = U + t • Z := by
    rw [mat_mul_affine, hmergeS, hmergeW]
  have hlambda : 0 ≤ (1 - theta) / theta :=
    div_nonneg (sub_nonneg.mpr htheta.2.le) htheta.1.le
  have hparallel : ∀ b, S r b = ((1 - theta) / theta) * S i b :=
    splitPoint_parallel hir hr htheta.1
  have hbase : F S = F U := by
    rw [← hmergeS]
    exact parallel_row_invariance hDPI hS hir hlambda hparallel
  let phi : ℝ → ℝ := fun t => F (S + t • W) - F (U + t • Z)
  have hphi0 : phi 0 = 0 := by
    simp [phi, hbase]
  have hmin : IsLocalMin phi 0 := by
    change ∀ᶠ t : ℝ in nhds 0, phi 0 ≤ phi t
    filter_upwards [hpert] with t ht
    have hle := hDPI (merge i r) (S + t • W)
      (merge_stochastic i r) ht
    rw [hmergeLine] at hle
    rw [hphi0]
    exact sub_nonneg.mpr hle
  have hd1 := hasDerivAt_affine (U := S) (V := W)
    ((hF S hS).differentiableAt (by norm_num))
  have hd2 := hasDerivAt_affine (U := U) (V := Z)
    ((hF U hU).differentiableAt (by norm_num))
  have hevent : phi =ᶠ[nhds 0]
      ((fun t : ℝ => F (S + t • W)) - fun t : ℝ => F (U + t • Z)) := by
    filter_upwards [] with t
    simp only [phi, Pi.sub_apply]
  have hdphi := (hd1.sub hd2).congr_of_eventuallyEq hevent
  have hz := hmin.hasDerivAt_eq_zero hdphi
  linarith

lemma splitPoint_derivative_identity {n m : ℕ}
    {F : Mat n m → ℝ} (hF : ContDiff ℝ 1 F) (hDPI : DPI F)
    {U : Mat n m} (hU : Simplex U) {i r k : Fin n}
    (hir : i ≠ r) (hki : k ≠ i) (hkr : k ≠ r)
    (hr : ∀ a, U r a = 0)
    (hpos : ∀ j, j ≠ r → ∀ a, 0 < U j a)
    (a : Fin m) {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) 1) :
    (fderiv ℝ F (splitPoint i r theta U)) (unit r a - unit k a) =
      (fderiv ℝ F U) (unit i a - unit k a) := by
  exact splitPoint_derivative_identity_of_contDiffOnSimplex
    (fun X _ => hF.contDiffAt) hDPI hU hir hki hkr hr hpos a htheta

/-! ## First-order rigidity on the relative interior of a zero-row face -/

lemma zero_row_contact_of_contDiffOnSimplex {n m : ℕ} (hn : 3 ≤ n)
    {F : Mat n m → ℝ} (hF : ContDiffOnSimplex F) (hDPI : DPI F)
    {U : Mat n m} (hU : Simplex U) {r i : Fin n} (hir : i ≠ r)
    (hr : ∀ a, U r a = 0)
    (hpos : ∀ j, j ≠ r → ∀ a, 0 < U j a) (a : Fin m) :
    (fderiv ℝ F U) (unit r a - unit i a) = 0 := by
  obtain ⟨k, hki, hkr⟩ := exists_third_row hn hir
  let W : Mat n m := unit r a - unit k a
  let Z : Mat n m := unit i a - unit k a
  let g : ℝ → ℝ := fun theta =>
    (fderiv ℝ F (splitPoint i r theta U)) W
  have hg : ContinuousAt g 1 := by
    have hFU : ContDiffAt ℝ 1 F (splitPoint i r 1 U) := by
      simpa [splitPoint_one_of_zero_row hir hr] using hF U hU
    have hfd : ContinuousAt (fderiv ℝ F) (splitPoint i r 1 U) :=
      hFU.continuousAt_fderiv (by norm_num)
    have hcomp : ContinuousAt
        (fun theta : ℝ => fderiv ℝ F (splitPoint i r theta U)) 1 :=
      ContinuousAt.comp'
        (f := fun theta : ℝ => splitPoint i r theta U) hfd
        (continuous_splitPoint hir U).continuousAt
    exact ContinuousAt.comp'
      (f := fun theta : ℝ => fderiv ℝ F (splitPoint i r theta U))
      (ContinuousLinearMap.apply ℝ ℝ W).continuous.continuousAt hcomp
  have hsubset : Ioo (0 : ℝ) 1 ⊆
      {theta | g theta = (fderiv ℝ F U) Z} := by
    intro theta htheta
    exact splitPoint_derivative_identity_of_contDiffOnSimplex
      hF hDPI hU hir hki hkr hr hpos a htheta
  have honeMem : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by simp
  have hlimit : g 1 = (fderiv ℝ F U) Z :=
    hg.continuousWithinAt.eq_const_of_mem_closure honeMem hsubset
  rw [show g 1 = (fderiv ℝ F U) W by
    simp [g, splitPoint_one_of_zero_row hir hr]] at hlimit
  calc
    (fderiv ℝ F U) (unit r a - unit i a) =
        (fderiv ℝ F U) (W - Z) := by
          congr 1
          ext j b
          simp [W, Z]
    _ = (fderiv ℝ F U) W - (fderiv ℝ F U) Z := by
      rw [map_sub]
    _ = 0 := sub_eq_zero.mpr hlimit

lemma zero_row_contact {n m : ℕ}
    (hn : 3 ≤ n) {F : Mat n m → ℝ} (hF : ContDiff ℝ 1 F) (hDPI : DPI F)
    {U : Mat n m} (hU : Simplex U) {r i : Fin n} (hir : i ≠ r)
    (hr : ∀ a, U r a = 0)
    (hpos : ∀ j, j ≠ r → ∀ a, 0 < U j a) (a : Fin m) :
    (fderiv ℝ F U) (unit r a - unit i a) = 0 := by
  exact zero_row_contact_of_contDiffOnSimplex hn
    (fun X _ => hF.contDiffAt) hDPI hU hir hr hpos a

lemma redistribution_derivative_of_contDiffOnSimplex
    {n m : ℕ}
    (hn : 3 ≤ n) {F : Mat n m → ℝ} (hF : ContDiffOnSimplex F) (hDPI : DPI F)
    {U : Mat n m} (hU : Simplex U) {r i j : Fin n}
    (hir : i ≠ r) (hjr : j ≠ r)
    (hr : ∀ a, U r a = 0)
    (hpos : ∀ q, q ≠ r → ∀ a, 0 < U q a) (a : Fin m) :
    (fderiv ℝ F U) (unit i a - unit j a) = 0 := by
  have hi := zero_row_contact_of_contDiffOnSimplex hn hF hDPI hU hir hr hpos a
  have hj := zero_row_contact_of_contDiffOnSimplex hn hF hDPI hU hjr hr hpos a
  rw [show unit i a - unit j a =
      -(unit r a - unit i a) + (unit r a - unit j a) by
        ext q b
        simp only [Pi.sub_apply, unit, neg_sub, Pi.add_apply, sub_add_sub_cancel]
        ]
  rw [map_add, map_neg, hi, hj]
  simp

lemma redistribution_derivative {n m : ℕ}
    (hn : 3 ≤ n) {F : Mat n m → ℝ} (hF : ContDiff ℝ 1 F) (hDPI : DPI F)
    {U : Mat n m} (hU : Simplex U) {r i j : Fin n}
    (hir : i ≠ r) (hjr : j ≠ r)
    (hr : ∀ a, U r a = 0)
    (hpos : ∀ q, q ≠ r → ∀ a, 0 < U q a) (a : Fin m) :
    (fderiv ℝ F U) (unit i a - unit j a) = 0 := by
  exact redistribution_derivative_of_contDiffOnSimplex hn
    (fun X _ => hF.contDiffAt) hDPI hU hir hjr hr hpos a

lemma tangent_matrix_decomposition {n m : ℕ} {V : Mat n m} (s : Fin n)
    (hcol : ∀ a, ∑ i, V i a = 0) :
    V = ∑ a, ∑ i, V i a • (unit i a - unit s a) := by
  classical
  have hunit : (∑ a, ∑ i, V i a • unit i a) = V := by
    ext j b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc
      ∑ a, ∑ i, V i a * unit i a j b =
          ∑ a, if b = a then V j a else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hba : b = a
            · subst a
              simp [unit]
            · simp [unit, hba]
      _ = V j b := by simp
  symm
  calc
    (∑ a, ∑ i, V i a • (unit i a - unit s a)) =
        ∑ a, ((∑ i, V i a • unit i a) -
          (∑ i, V i a) • unit s a) := by
            apply Finset.sum_congr rfl
            intro a ha
            simp_rw [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
    _ = ∑ a, ∑ i, V i a • unit i a := by simp [hcol]
    _ = V := hunit

lemma zero_row_tangent_derivative_of_contDiffOnSimplex
    {n m : ℕ}
    (hn : 3 ≤ n) {F : Mat n m → ℝ} (hF : ContDiffOnSimplex F) (hDPI : DPI F)
    {U V : Mat n m} (hU : Simplex U) {r s : Fin n} (hsr : s ≠ r)
    (hrU : ∀ a, U r a = 0)
    (hpos : ∀ q, q ≠ r → ∀ a, 0 < U q a)
    (hrV : ∀ a, V r a = 0) (hcolV : ∀ a, ∑ i, V i a = 0) :
    (fderiv ℝ F U) V = 0 := by
  rw [tangent_matrix_decomposition s hcolV]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul]
  by_cases hir : i = r
  · subst i
    simp [hrV]
  · rw [redistribution_derivative_of_contDiffOnSimplex
      hn hF hDPI hU hir hsr hrU hpos a]
    simp

lemma zero_row_tangent_derivative {n m : ℕ}
    (hn : 3 ≤ n) {F : Mat n m → ℝ} (hF : ContDiff ℝ 1 F) (hDPI : DPI F)
    {U V : Mat n m} (hU : Simplex U) {r s : Fin n} (hsr : s ≠ r)
    (hrU : ∀ a, U r a = 0)
    (hpos : ∀ q, q ≠ r → ∀ a, 0 < U q a)
    (hrV : ∀ a, V r a = 0) (hcolV : ∀ a, ∑ i, V i a = 0) :
    (fderiv ℝ F U) V = 0 := by
  exact zero_row_tangent_derivative_of_contDiffOnSimplex hn
    (fun X _ => hF.contDiffAt) hDPI hU hsr hrU hpos hrV hcolV

/-! ## Vanishing on the relative interior of a zero-row face -/

lemma affine_eq_convex {n m : ℕ} (U V : Mat n m) (t : ℝ) :
    U + t • (V - U) = (1 - t) • U + t • V := by
  ext i a
  simp
  ring

lemma convex_simplex {n m : ℕ} {U V : Mat n m}
    (hU : Simplex U) (hV : Simplex V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Simplex ((1 - t) • U + t • V) := by
  constructor
  · intro i a
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht.2) (hU.1 i a))
      (mul_nonneg ht.1 (hV.1 i a))
  · simp [hU.2, hV.2]

lemma collapse_mul_apply' {n m : ℕ} (s : Fin n) (U : Mat n m)
    (i : Fin n) (a : Fin m) :
    (collapse s * U) i a = if i = s then columnSums U a else 0 := by
  rw [collapse_mul]
  simp [outer, rowIndicator]

lemma collapse_preserves_columnSums {n m : ℕ} (s : Fin n) (U : Mat n m) :
    ∀ a, ∑ i, (collapse s * U) i a = ∑ i, U i a := by
  classical
  intro a
  rw [collapse_mul]
  simp [outer, rowIndicator, columnSums]

lemma zero_row_face_interior_vanishing_of_contDiffOnSimplex
    {n m : ℕ}
    (hn : 3 ≤ n) {F : Mat n m → ℝ} (hF : ContDiffOnSimplex F)
    (hDPI : DPI F) (hRKO : RKO F)
    {U : Mat n m} (hU : Simplex U) {r : Fin n}
    (hr : ∀ a, U r a = 0)
    (hpos : ∀ q, q ≠ r → ∀ a, 0 < U q a) :
    F U = 0 := by
  obtain ⟨s, hsr⟩ : ∃ s : Fin n, s ≠ r := by
    let z : Fin n := ⟨0, by omega⟩
    let o : Fin n := ⟨1, by omega⟩
    by_cases hzr : z = r
    · refine ⟨o, ?_⟩
      intro hor
      have hzo : z = o := hzr.trans hor.symm
      have := congrArg Fin.val hzo
      simp [z, o] at this
    · exact ⟨z, hzr⟩
  let V : Mat n m := collapse s * U
  have hV : Simplex V := stochastic_mul_simplex (collapse_stochastic s) hU
  have hrV : ∀ a, V r a = 0 := by
    intro a
    simp [V, collapse_mul_apply', Ne.symm hsr]
  have hcolV : ∀ a, ∑ i, (V - U) i a = 0 := by
    intro a
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [collapse_preserves_columnSums s U]
    simp
  have hrVU : ∀ a, (V - U) r a = 0 := by
    intro a
    simp [hrV, hr]
  let gamma : ℝ → Mat n m := fun t => U + t • (V - U)
  have hgamma_cont : Continuous gamma := by
    dsimp only [gamma]
    fun_prop
  have hgamma_simplex : ∀ t ∈ Icc (0 : ℝ) 1, Simplex (gamma t) := by
    intro t ht
    change Simplex (U + t • (V - U))
    rw [affine_eq_convex]
    exact convex_simplex hU hV ht
  have hgamma_row : ∀ t, ∀ a, gamma t r a = 0 := by
    intro t a
    change U r a + t * (V - U) r a = 0
    rw [hr a, hrVU a]
    ring
  have hgamma_pos : ∀ t ∈ Ioo (0 : ℝ) 1,
      ∀ q, q ≠ r → ∀ a, 0 < gamma t q a := by
    intro t ht q hqr a
    change 0 < (U + t • (V - U)) q a
    rw [affine_eq_convex]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr ht.2) (hpos q hqr a))
      (mul_nonneg ht.1.le (hV.1 q a))
  have hline_deriv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => F (gamma x)) 0 t := by
    intro t ht
    have hSt := hgamma_simplex t ⟨ht.1.le, ht.2.le⟩
    have hz := zero_row_tangent_derivative_of_contDiffOnSimplex
      hn hF hDPI hSt hsr
      (hgamma_row t) (hgamma_pos t ht) hrVU hcolV
    have hd := hasDerivAt_affine_at (F := F) (U := U) (V := V - U) t
      ((hF (gamma t) hSt).differentiableAt (by norm_num))
    rw [hz] at hd
    exact hd
  have hline_cont : ContinuousOn (fun t : ℝ => F (gamma t)) (Icc 0 1) := by
    intro t ht
    exact (ContinuousAt.comp'
      (f := gamma) (hF (gamma t) (hgamma_simplex t ht)).continuousAt
      hgamma_cont.continuousAt).continuousWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
    (fun t : ℝ => F (gamma t)) (fun _ => (0 : ℝ))
    (show (0 : ℝ) < 1 by norm_num) hline_cont hline_deriv
  have hFVU : F V = F U := by
    have : (0 : ℝ) = F V - F U := by
      simpa [gamma] using hslope
    linarith
  have hVouter : V = outer (rowIndicator s) (columnSums U) :=
    collapse_mul s U
  have hFV : F V = 0 := by
    rw [hVouter]
    exact hRKO (rowIndicator s) (columnSums U) (hVouter ▸ hV)
  linarith

lemma zero_row_face_interior_vanishing {n m : ℕ}
    (hn : 3 ≤ n) {F : Mat n m → ℝ} (hF : ContDiff ℝ 1 F)
    (hDPI : DPI F) (hRKO : RKO F)
    {U : Mat n m} (hU : Simplex U) {r : Fin n}
    (hr : ∀ a, U r a = 0)
    (hpos : ∀ q, q ≠ r → ∀ a, 0 < U q a) :
    F U = 0 := by
  exact zero_row_face_interior_vanishing_of_contDiffOnSimplex hn
    (fun X _ => hF.contDiffAt) hDPI hRKO hU hr hpos

/-! ## Closure of the zero-row face -/

lemma sum_if_ne {n : ℕ} (r : Fin n) (c : ℝ) :
    (∑ i : Fin n, if i = r then 0 else c) = (n - 1 : ℕ) * c := by
  classical
  have hn1 : 1 ≤ n := (Nat.one_le_iff_ne_zero).mpr (by
    intro hn
    subst n
    exact Fin.elim0 r)
  calc
    (∑ i : Fin n, if i = r then 0 else c) =
        ∑ i : Fin n, (c - if i = r then c else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hir : i = r <;> simp [hir]
    _ = (∑ _i : Fin n, c) - ∑ i : Fin n, if i = r then c else 0 := by
      rw [Finset.sum_sub_distrib]
    _ = (n : ℝ) * c - c := by simp
    _ = (n - 1 : ℕ) * c := by
      rw [Nat.cast_sub hn1]
      push_cast
      ring

/-- The uniform point in the relative interior of the face with row `r` equal to zero. -/
def faceCenter {n m : ℕ} (r : Fin n) : Mat n m :=
  fun i _ => if i = r then 0 else
    (1 / ((n - 1 : ℕ) : ℝ)) * (1 / (m : ℝ))

lemma faceCenter_simplex {n m : ℕ} [NeZero m] (hn : 2 ≤ n) (r : Fin n) :
    Simplex (faceCenter (m := m) r) := by
  have hnsub : 0 < n - 1 := by omega
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  constructor
  · intro i a
    by_cases hir : i = r
    · simp [faceCenter, hir]
    · simp only [faceCenter, hir, ite_false]
      exact mul_nonneg
        (one_div_nonneg.mpr (Nat.cast_nonneg _))
        (one_div_nonneg.mpr (Nat.cast_nonneg _))
  · rw [mass]
    simp only [faceCenter]
    calc
      (∑ i, ∑ _a : Fin m,
          if i = r then 0 else
            (1 / ((n - 1 : ℕ) : ℝ)) * (1 / (m : ℝ))) =
          ∑ i, if i = r then 0 else
            (m : ℝ) * ((1 / ((n - 1 : ℕ) : ℝ)) * (1 / (m : ℝ))) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hir : i = r
              · simp [hir]
              · simp [hir]
      _ = (n - 1 : ℕ) *
          ((m : ℝ) * ((1 / ((n - 1 : ℕ) : ℝ)) * (1 / (m : ℝ)))) :=
        sum_if_ne r _
      _ = 1 := by
        have hncast : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast hnsub.ne'
        have hmcast : (m : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
        field_simp [hncast, hmcast]

lemma faceCenter_zero_row {n m : ℕ} (r : Fin n) :
    ∀ a, faceCenter (m := m) r r a = 0 := by
  intro a
  simp [faceCenter]

lemma faceCenter_positive {n m : ℕ} [NeZero m] (hn : 2 ≤ n) (r : Fin n) :
    ∀ i, i ≠ r → ∀ a, 0 < faceCenter (m := m) r i a := by
  have hnsub : 0 < n - 1 := by omega
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  intro i hir a
  simp only [faceCenter, hir, ite_false]
  exact mul_pos
    (one_div_pos.mpr (by exact_mod_cast hnsub))
    (one_div_pos.mpr (by exact_mod_cast hmpos))

theorem zero_row_vanishing_of_contDiffOnSimplex
    {n m : ℕ} [NeZero m]
    (hn : 3 ≤ n) {F : Mat n m → ℝ} (hF : ContDiffOnSimplex F)
    (hDPI : DPI F) (hRKO : RKO F)
    {U : Mat n m} (hU : Simplex U) {r : Fin n}
    (hr : ∀ a, U r a = 0) :
    F U = 0 := by
  let W : Mat n m := faceCenter (m := m) r
  have hW : Simplex W := faceCenter_simplex (m := m) (le_trans (by norm_num) hn) r
  have hrW : ∀ a, W r a = 0 := faceCenter_zero_row r
  have hposW : ∀ i, i ≠ r → ∀ a, 0 < W i a :=
    faceCenter_positive (m := m) (le_trans (by norm_num) hn) r
  let gamma : ℝ → Mat n m := fun t => (1 - t) • U + t • W
  have hgamma : Continuous gamma := by
    dsimp only [gamma]
    fun_prop
  have hzero : Ioo (0 : ℝ) 1 ⊆ {t | F (gamma t) = 0} := by
    intro t ht
    have hSt : Simplex (gamma t) := convex_simplex hU hW
      ⟨ht.1.le, ht.2.le⟩
    have hrt : ∀ a, gamma t r a = 0 := by
      intro a
      simp [gamma, hr, hrW]
    have hpost : ∀ i, i ≠ r → ∀ a, 0 < gamma t i a := by
      intro i hir a
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht.2.le) (hU.1 i a))
        (mul_pos ht.1 (hposW i hir a))
    exact zero_row_face_interior_vanishing_of_contDiffOnSimplex
      hn hF hDPI hRKO hSt hrt hpost
  have hFU : ContDiffAt ℝ 1 F (gamma 0) := by
    simpa [gamma] using hF U hU
  have hcont : ContinuousAt (fun t : ℝ => F (gamma t)) 0 :=
    ContinuousAt.comp' (f := gamma) hFU.continuousAt hgamma.continuousAt
  have hmem : F (gamma 0) = 0 :=
    hcont.continuousWithinAt.eq_const_of_mem_closure (by simp) hzero
  simpa [gamma] using hmem

theorem zero_row_vanishing {n m : ℕ} [NeZero m]
    (hn : 3 ≤ n) {F : Mat n m → ℝ} (hF : ContDiff ℝ 1 F)
    (hDPI : DPI F) (hRKO : RKO F)
    {U : Mat n m} (hU : Simplex U) {r : Fin n}
    (hr : ∀ a, U r a = 0) :
    F U = 0 := by
  exact zero_row_vanishing_of_contDiffOnSimplex hn
    (fun X _ => hF.contDiffAt) hDPI hRKO hU hr

/-! ## Asymmetric flattening when every column has positive mass -/

/-- Embed a column index as a row when the table is tall. -/
@[expose] def rowEmbed {n m : ℕ} (hnm : m < n) (a : Fin m) : Fin n :=
  ⟨a.val, lt_trans a.isLt hnm⟩

@[simp] lemma rowEmbed_val {n m : ℕ} (hnm : m < n) (a : Fin m) :
    (rowEmbed hnm a).val = a.val := rfl

lemma rowEmbed_injective {n m : ℕ} (hnm : m < n) :
    Function.Injective (rowEmbed hnm) := by
  intro a b hab
  apply Fin.ext
  simpa [rowEmbed] using congrArg Fin.val hab

/-- Put the mass of column `a` into the single row `rowEmbed hnm a`. -/
def flatten {n m : ℕ} (hnm : m < n) (U : Mat n m) : Mat n m :=
  fun i a => if i = rowEmbed hnm a then columnSums U a else 0

lemma flatten_simplex {n m : ℕ} (hnm : m < n) {U : Mat n m}
    (hU : Simplex U) : Simplex (flatten hnm U) := by
  classical
  constructor
  · intro i a
    by_cases hia : i = rowEmbed hnm a
    · simp only [flatten, ite_eq_left hia, columnSums]
      exact Finset.sum_nonneg fun j hj => hU.1 j a
    · simp [flatten, hia]
  · rw [mass]
    rw [Finset.sum_comm]
    simp only [flatten, columnSums, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_comm]
    exact hU.2

/-- An extra row index available when there are more rows than columns. -/
def unusedRow {n m : ℕ} (hnm : m < n) : Fin n :=
  ⟨m, hnm⟩

lemma unusedRow_ne_embed {n m : ℕ} (hnm : m < n) (a : Fin m) :
    unusedRow hnm ≠ rowEmbed hnm a := by
  intro h
  have hv := congrArg Fin.val h
  simp [unusedRow, rowEmbed] at hv
  omega

lemma flatten_zero_row {n m : ℕ} (hnm : m < n) (U : Mat n m) :
    ∀ a, flatten hnm U (unusedRow hnm) a = 0 := by
  intro a
  simp [flatten, unusedRow_ne_embed hnm a]

/-- The stochastic channel sending a flattened positive column back to the original column. -/
def unflattenChannel {n m : ℕ} (U : Mat n m) : Mat n n :=
  fun i j => if hj : j.val < m then
      U i ⟨j.val, hj⟩ / columnSums U ⟨j.val, hj⟩
    else if i.val = 0 then 1 else 0

lemma unflattenChannel_stochastic {n m : ℕ} [NeZero n]
    {U : Mat n m} (hU : Nonnegative U)
    (hcol : ∀ a, 0 < columnSums U a) :
    ColumnStochastic (unflattenChannel U) := by
  classical
  constructor
  · intro i j
    simp only [unflattenChannel]
    split_ifs with hj hi
    · exact div_nonneg (hU i ⟨j.val, hj⟩) (hcol _).le
    · norm_num
    · norm_num
  · intro j
    by_cases hj : j.val < m
    · simp only [unflattenChannel, dite_eq_left hj]
      rw [← Finset.sum_div]
      change columnSums U ⟨j.val, hj⟩ / columnSums U ⟨j.val, hj⟩ = 1
      exact div_self (hcol _).ne'
    · simp [unflattenChannel, hj]

lemma unflattenChannel_mul_flatten {n m : ℕ}
    (hnm : m < n) {U : Mat n m}
    (hcol : ∀ a, 0 < columnSums U a) :
    unflattenChannel U * flatten hnm U = U := by
  classical
  ext i a
  rw [mat_mul_apply]
  calc
    ∑ j, unflattenChannel U i j * flatten hnm U j a =
        unflattenChannel U i (rowEmbed hnm a) * columnSums U a := by
          simp [flatten]
    _ = U i a := by
      change (if hj : a.val < m then U i ⟨a.val, hj⟩ /
        columnSums U ⟨a.val, hj⟩ else _) * columnSums U a = U i a
      rw [dite_eq_left a.isLt]
      exact div_mul_cancel₀ (U i a) (hcol a).ne'

lemma positive_columns_vanishing_of_contDiffOnSimplex
    {n m : ℕ} [NeZero n] [NeZero m]
    (hm : 2 ≤ m) (hnm : m < n)
    {F : Mat n m → ℝ} (hF : ContDiffOnSimplex F)
    (hDPI : DPI F) (hRKO : RKO F)
    {U : Mat n m} (hU : Simplex U)
    (hcol : ∀ a, 0 < columnSums U a) :
    F U = 0 := by
  have hn : 3 ≤ n := by omega
  let Uf : Mat n m := flatten hnm U
  have hUf : Simplex Uf := flatten_simplex hnm hU
  have hrow : ∀ a, Uf (unusedRow hnm) a = 0 := flatten_zero_row hnm U
  have hzero : F Uf = 0 :=
    zero_row_vanishing_of_contDiffOnSimplex hn hF hDPI hRKO hUf hrow
  let T : Mat n n := unflattenChannel U
  have hT : ColumnStochastic T := unflattenChannel_stochastic hU.1 hcol
  have hTU : T * Uf = U := unflattenChannel_mul_flatten hnm hcol
  have hle := hDPI T Uf hT hUf
  rw [hTU, hzero] at hle
  have hnonneg := nonneg_of_dpi_rko hDPI hRKO hU (unusedRow hnm)
  linarith

lemma positive_columns_vanishing {n m : ℕ} [NeZero n] [NeZero m]
    (hm : 2 ≤ m) (hnm : m < n)
    {F : Mat n m → ℝ} (hF : ContDiff ℝ 1 F)
    (hDPI : DPI F) (hRKO : RKO F)
    {U : Mat n m} (hU : Simplex U)
    (hcol : ∀ a, 0 < columnSums U a) :
    F U = 0 := by
  exact positive_columns_vanishing_of_contDiffOnSimplex hm hnm
    (fun X _ => hF.contDiffAt) hDPI hRKO hU hcol

/-! ## Approximation and the full `n > m ≥ 2` theorem -/

/-- The uniform strictly positive point of the full simplex. -/
def fullCenter {n m : ℕ} : Mat n m :=
  fun _ _ => (1 / (n : ℝ)) * (1 / (m : ℝ))

lemma fullCenter_positive {n m : ℕ} [NeZero n] [NeZero m] :
    ∀ i a, 0 < fullCenter (n := n) (m := m) i a := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  intro i a
  exact mul_pos
    (one_div_pos.mpr (by exact_mod_cast hnpos))
    (one_div_pos.mpr (by exact_mod_cast hmpos))

lemma fullCenter_simplex {n m : ℕ} [NeZero n] [NeZero m] :
    Simplex (fullCenter (n := n) (m := m)) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  constructor
  · intro i a
    exact (fullCenter_positive i a).le
  · rw [mass]
    simp only [fullCenter, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hncast : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have hmcast : (m : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
    field_simp [hncast, hmcast]

/-- C¹ left-DPI rigidity assuming only C¹ regularity at the points of the simplex. -/
theorem general_asymmetric_simplex_C1_of_contDiffOnSimplex
    {n m : ℕ} (hm : 2 ≤ m) (hnm : m < n)
    (F : Mat n m → ℝ) (hF : ContDiffOnSimplex F)
    (hDPI : DPI F) (hRKO : RKO F) :
    ∀ U, Simplex U → F U = 0 := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero n := ⟨by omega⟩
  intro U hU
  let W : Mat n m := fullCenter (n := n) (m := m)
  have hW : Simplex W := fullCenter_simplex
  have hposW : ∀ i a, 0 < W i a := fullCenter_positive
  let gamma : ℝ → Mat n m := fun t => (1 - t) • U + t • W
  have hgamma : Continuous gamma := by
    dsimp only [gamma]
    fun_prop
  have hzero : Ioo (0 : ℝ) 1 ⊆ {t | F (gamma t) = 0} := by
    intro t ht
    have hSt : Simplex (gamma t) := convex_simplex hU hW
      ⟨ht.1.le, ht.2.le⟩
    have hcol : ∀ a, 0 < columnSums (gamma t) a := by
      intro a
      apply Finset.sum_pos'
      · intro i hi
        exact add_nonneg
          (mul_nonneg (sub_nonneg.mpr ht.2.le) (hU.1 i a))
          (mul_nonneg ht.1.le (hW.1 i a))
      · refine ⟨(0 : Fin n), Finset.mem_univ _, ?_⟩
        exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr ht.2.le) (hU.1 0 a))
          (mul_pos ht.1 (hposW 0 a))
    exact positive_columns_vanishing_of_contDiffOnSimplex
      hm hnm hF hDPI hRKO hSt hcol
  have hFU : ContDiffAt ℝ 1 F (gamma 0) := by
    simpa [gamma] using hF U hU
  have hcont : ContinuousAt (fun t : ℝ => F (gamma t)) 0 :=
    ContinuousAt.comp' (f := gamma) hFU.continuousAt hgamma.continuousAt
  have hmem : F (gamma 0) = 0 :=
    hcont.continuousWithinAt.eq_const_of_mem_closure (by simp) hzero
  simpa [gamma] using hmem

/-- C¹ left-DPI rigidity on every rectangular probability simplex with more rows than columns. -/
theorem general_asymmetric_simplex_C1
    {n m : ℕ} (hm : 2 ≤ m) (hnm : m < n)
    (F : Mat n m → ℝ) (hF : ContDiff ℝ 1 F)
    (hDPI : DPI F) (hRKO : RKO F) :
    ∀ U, Simplex U → F U = 0 := by
  exact general_asymmetric_simplex_C1_of_contDiffOnSimplex
    hm hnm F (fun X _ => hF.contDiffAt) hDPI hRKO

/-- Paper-facing open-neighborhood version of asymmetric C¹ rigidity.

Here `F` is written on the ambient finite-dimensional space so that `DPI` and
`RKO` retain their existing definitions.  Only `ContDiffOn ℝ 1 F Ω` is
assumed, so values and regularity outside `Ω` are irrelevant. -/
theorem general_asymmetric_simplex_C1_openNeighborhood
    {n m : ℕ} (hm : 2 ≤ m) (hnm : m < n)
    (Ω : Set (Mat n m)) (hΩ : IsOpen Ω)
    (hsimplex : ∀ U, Simplex U → U ∈ Ω)
    (F : Mat n m → ℝ) (hF : ContDiffOn ℝ 1 F Ω)
    (hDPI : DPI F) (hRankOne : RankOneVanishing F) :
    ∀ U, Simplex U → F U = 0 := by
  apply general_asymmetric_simplex_C1_of_contDiffOnSimplex hm hnm F
  · exact fun U hU => (hΩ.contDiffOn_iff.mp hF) (hsimplex U hU)
  · exact hDPI
  · exact (rko_iff_rankOneVanishing F).mpr hRankOne

end GeneralAsymmetricC1


end

end Cslib.FiniteSampleInformation
