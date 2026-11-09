/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Analysis.Convex.Birkhoff
public import CslibFrontier.Probability.FiniteSampleInformation.GeneralAsymmetricC1

/-!
# Squared Frobenius dependence and restricted data processing

This file formalizes the squared entrywise distance from a joint distribution
to the product of its marginals.  All estimates are written as finite sums of
squares; this avoids choosing a matrix norm instance.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`FrobeniusDependence.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators
open Set

namespace FrobeniusDependence

open GeneralAsymmetricC1

/-- The row sums of a joint table. -/
@[expose] def rowMarginal {n m : ℕ} (U : Mat n m) (i : Fin n) : ℝ :=
  ∑ a, U i a

/-- The column sums of a joint table. -/
@[expose] def columnMarginal {n m : ℕ} (U : Mat n m) (a : Fin m) : ℝ :=
  ∑ i, U i a

/-- Subtract the product of row and column marginals from each entry. -/
@[expose] def centered {n m : ℕ} (U : Mat n m) : Mat n m :=
  fun i a => U i a - rowMarginal U i * columnMarginal U a

/-- Squared Frobenius distance from `U` to the product of its marginals. -/
@[expose] def fdi {n m : ℕ} (U : Mat n m) : ℝ :=
  ∑ i, ∑ a, centered U i a ^ 2

lemma simplex_rowMarginal_sum {n m : ℕ} {U : Mat n m} (hU : Simplex U) :
    ∑ i, rowMarginal U i = 1 := by
  simpa [rowMarginal, mass] using hU.2

lemma simplex_columnMarginal_sum {n m : ℕ} {U : Mat n m} (hU : Simplex U) :
    ∑ a, columnMarginal U a = 1 := by
  change (∑ a, ∑ i, U i a) = 1
  rw [Finset.sum_comm]
  exact hU.2

lemma columnMarginal_mul {n m : ℕ} {T : Mat n n} {U : Mat n m}
    (hT : ColumnStochastic T) :
    columnMarginal (T * U) = columnMarginal U := by
  funext a
  simp only [columnMarginal, mat_mul_apply]
  calc
    (∑ i, ∑ j, T i j * U j a) =
        ∑ j, (∑ i, T i j) * U j a := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ = ∑ j, U j a := by simp [hT.2]

lemma rowMarginal_mul {n m : ℕ} (T : Mat n n) (U : Mat n m) :
    rowMarginal (T * U) = fun i => ∑ j, T i j * rowMarginal U j := by
  funext i
  simp only [rowMarginal, mat_mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]

/-- Covariance equivariance: centering commutes with every stochastic channel. -/
lemma centered_mul {n m : ℕ} {T : Mat n n} {U : Mat n m}
    (hT : ColumnStochastic T) :
    centered (T * U) = T * centered U := by
  ext i a
  rw [centered, rowMarginal_mul, columnMarginal_mul hT, mat_mul_apply]
  change (∑ j, T i j * U j a) -
      (∑ j, T i j * rowMarginal U j) * columnMarginal U a =
    ∑ j, T i j *
      (U j a - rowMarginal U j * columnMarginal U a)
  rw [Finset.sum_mul]
  calc
    (∑ j, T i j * U j a) -
        ∑ j, (T i j * rowMarginal U j) * columnMarginal U a =
        ∑ j, (T i j * U j a -
          (T i j * rowMarginal U j) * columnMarginal U a) :=
      (Finset.sum_sub_distrib _ _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      ring

lemma centered_column_sum_zero {n m : ℕ} {U : Mat n m} (hU : Simplex U)
    (a : Fin m) :
    ∑ i, centered U i a = 0 := by
  change (∑ i, (U i a - rowMarginal U i * columnMarginal U a)) = 0
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
    simplex_rowMarginal_sum hU]
  simp [columnMarginal]

lemma fdi_nonneg {n m : ℕ} (U : Mat n m) : 0 ≤ fdi U := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _

lemma fdi_eq_zero_iff_centered_eq_zero {n m : ℕ} (U : Mat n m) :
    fdi U = 0 ↔ centered U = 0 := by
  constructor
  · intro h
    unfold fdi at h
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _)).mp h
    ext i a
    have hi := hall i (Finset.mem_univ i)
    have hia := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => sq_nonneg (centered U i a))).mp hi a (Finset.mem_univ a)
    exact sq_eq_zero_iff.mp hia
  · intro h
    simp [fdi, h]

lemma centered_eq_zero_iff_product_marginals {n m : ℕ} (U : Mat n m) :
    centered U = 0 ↔
      U = outer (rowMarginal U) (columnMarginal U) := by
  constructor <;> intro h <;> ext i a
  · have := congrFun (congrFun h i) a
    simpa [centered, outer] using sub_eq_zero.mp this
  · have := congrFun (congrFun h i) a
    simpa [centered, outer] using sub_eq_zero.mpr this

lemma matrix_eq_zero_of_rank_eq_zero {n m : ℕ} (U : Mat n m)
    (h : (Matrix.of U).rank = 0) : U = 0 := by
  have hrange : LinearMap.range (Matrix.of U).mulVecLin = ⊥ := by
    exact Submodule.finrank_eq_zero.mp h
  have hlin : (Matrix.of U).mulVecLin = 0 := LinearMap.range_eq_bot.mp hrange
  ext i a
  have happ := LinearMap.congr_fun hlin (Pi.single a (1 : ℝ))
  have happi := congrFun happ i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using happi

lemma simplex_rank_ne_zero {n m : ℕ} {U : Mat n m} (hU : Simplex U) :
    (Matrix.of U).rank ≠ 0 := by
  intro h
  have hzero := matrix_eq_zero_of_rank_eq_zero U h
  subst U
  norm_num [Simplex, mass] at hU

lemma product_marginals_of_outer_simplex {n m : ℕ}
    (x : Fin n → ℝ) (y : Fin m → ℝ) (hU : Simplex (outer x y)) :
    outer x y = outer (rowMarginal (outer x y)) (columnMarginal (outer x y)) := by
  have hmass : (∑ i, x i) * (∑ a, y a) = 1 := by
    calc
      (∑ i, x i) * (∑ a, y a) = ∑ i, x i * (∑ a, y a) :=
        Finset.sum_mul (Finset.univ : Finset (Fin n)) x (∑ a, y a)
      _ = ∑ i, ∑ a, x i * y a := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = 1 := hU.2
  have hr (i : Fin n) : rowMarginal (outer x y) i = x i * ∑ a, y a := by
    simp [rowMarginal, outer, Finset.mul_sum]
  have hc (a : Fin m) : columnMarginal (outer x y) a = (∑ i, x i) * y a := by
    simp [columnMarginal, outer, Finset.sum_mul]
  ext i a
  simp only [outer, hr, hc]
  calc
    x i * y a = x i * y a * 1 := by ring
    _ = x i * y a * ((∑ i, x i) * ∑ a, y a) := by rw [hmass]
    _ = (x i * ∑ a, y a) * ((∑ i, x i) * y a) := by ring

/-- On the probability simplex, FDI vanishes exactly at rank-one matrices. -/
theorem fdi_eq_zero_iff_rank_eq_one {n m : ℕ} (U : Mat n m) (hU : Simplex U) :
    fdi U = 0 ↔ (Matrix.of U).rank = 1 := by
  constructor
  · intro hfdi
    have hcenter := (fdi_eq_zero_iff_centered_eq_zero U).mp hfdi
    have hprod := (centered_eq_zero_iff_product_marginals U).mp hcenter
    have hle : (Matrix.of U).rank ≤ 1 := by
      rw [hprod]
      exact GeneralAsymmetricC1.rank_outer_le_one _ _
    exact Nat.le_antisymm hle (Nat.one_le_iff_ne_zero.mpr (simplex_rank_ne_zero hU))
  · intro hrank
    have hle : (Matrix.of U).rank ≤ 1 := hrank.le
    obtain ⟨x, y, hxy⟩ :=
      GeneralAsymmetricC1.exists_outer_of_rank_le_one U hle
    subst U
    apply (fdi_eq_zero_iff_centered_eq_zero _).2
    apply (centered_eq_zero_iff_product_marginals _).2
    exact product_marginals_of_outer_simplex x y hU

/-- Paper-facing rank-one vanishing for FDI. -/
theorem fdi_rko {n m : ℕ} : RKO (fdi : Mat n m → ℝ) := by
  intro x y hU
  apply (fdi_eq_zero_iff_centered_eq_zero _).2
  apply (centered_eq_zero_iff_product_marginals _).2
  exact product_marginals_of_outer_simplex x y hU

/-- A rank-one erasure channel has every column equal to one vector. -/
def IsErasureChannel {n : ℕ} (R : Mat n n) : Prop :=
  ∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
    R = fun i _ => q i

/-- Lean-friendly witness form of the paper's restricted channel class. -/
def RestrictedChannel {n : ℕ} (T : Mat n n) : Prop :=
  ∃ (c : ℝ) (D R : Mat n n), c ∈ Set.Icc 0 1 ∧
    Matrix.of D ∈ doublyStochastic ℝ (Fin n) ∧
    IsErasureChannel R ∧ T = c • D + (1 - c) • R

/-- The two channel sets appearing in the paper's convex-hull definition. -/
def DoublyStochasticChannels (n : ℕ) : Set (Mat n n) :=
  {D | Matrix.of D ∈ doublyStochastic ℝ (Fin n)}

/-- Channels whose output law is independent of the input state. -/
def ErasureChannels (n : ℕ) : Set (Mat n n) :=
  {R | IsErasureChannel R}

lemma convex_doublyStochasticChannels (n : ℕ) :
    Convex ℝ (DoublyStochasticChannels n) := by
  rintro D hD E hE a b ha hb hab
  have h := (convex_doublyStochastic (R := ℝ) (n := Fin n))
    hD hE ha hb hab
  change Matrix.of (a • D + b • E) ∈ doublyStochastic ℝ (Fin n)
  exact h

lemma convex_erasureChannels (n : ℕ) : Convex ℝ (ErasureChannels n) := by
  rintro R ⟨q, hq0, hqsum, rfl⟩ S ⟨p, hp0, hpsum, rfl⟩ a b ha hb hab
  refine ⟨fun i => a * q i + b * p i, ?_, ?_, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg ha (hq0 i)) (mul_nonneg hb (hp0 i))
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hqsum, hpsum]
    simpa using hab
  · ext i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

lemma doublyStochasticChannels_nonempty (n : ℕ) :
    (DoublyStochasticChannels n).Nonempty := by
  refine ⟨Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℝ), ?_⟩
  change Matrix.of (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℝ)) ∈
    doublyStochastic ℝ (Fin n)
  simp

lemma erasureChannels_nonempty {n : ℕ} (hn : 1 ≤ n) :
    (ErasureChannels n).Nonempty := by
  let i0 : Fin n := ⟨0, hn⟩
  let q : Fin n → ℝ := Pi.single i0 1
  refine ⟨(fun i _ => q i), q, ?_, ?_, rfl⟩
  · intro i
    classical
    simp only [q, Pi.single_apply]
    split_ifs <;> norm_num
  · simp [q]

/-- The witness definition used in the proof is exactly the paper's convex
hull `conv (DS_n ∪ R1_n)`. -/
theorem restrictedChannel_iff_mem_convexHull {n : ℕ} (hn : 1 ≤ n)
    (T : Mat n n) :
    RestrictedChannel T ↔
      T ∈ convexHull ℝ
        (DoublyStochasticChannels n ∪ ErasureChannels n) := by
  rw [(convex_doublyStochasticChannels n).convexHull_union
    (convex_erasureChannels n) (doublyStochasticChannels_nonempty n)
    (erasureChannels_nonempty hn)]
  rw [mem_convexJoin]
  constructor
  · rintro ⟨c, D, R, hc, hD, hR, hT⟩
    refine ⟨D, hD, R, hR, ?_⟩
    exact ⟨c, 1 - c, hc.1, sub_nonneg.mpr hc.2, by ring, hT.symm⟩
  · rintro ⟨D, hD, R, hR, a, b, ha, hb, hab, hT⟩
    have ha1 : a ≤ 1 := by linarith
    have hb_eq : b = 1 - a := by linarith
    refine ⟨a, D, R, ⟨ha, ha1⟩, hD, hR, ?_⟩
    rw [← hb_eq]
    exact hT.symm

lemma erasure_mul_centered_eq_zero {n m : ℕ} {R : Mat n n}
    (hR : IsErasureChannel R) {U : Mat n m} (hU : Simplex U) :
    R * centered U = 0 := by
  obtain ⟨q, hq0, hqsum, rfl⟩ := hR
  ext i a
  change (∑ j, q i * centered U j a) = 0
  rw [← Finset.mul_sum, centered_column_sum_zero hU]
  ring

lemma erasure_columnStochastic {n : ℕ} {R : Mat n n}
    (hR : IsErasureChannel R) : ColumnStochastic R := by
  obtain ⟨q, hq0, hqsum, rfl⟩ := hR
  exact ⟨fun i j => hq0 i, fun j => hqsum⟩

lemma doublyStochastic_columnStochastic {n : ℕ} {D : Mat n n}
    (hD : Matrix.of D ∈ doublyStochastic ℝ (Fin n)) :
    ColumnStochastic D := by
  exact ⟨fun i j => nonneg_of_mem_doublyStochastic hD,
    fun j => sum_col_of_mem_doublyStochastic hD j⟩

lemma restrictedChannel_columnStochastic {n : ℕ} {T : Mat n n}
    (hT : RestrictedChannel T) : ColumnStochastic T := by
  obtain ⟨c, D, R, hc, hD, hR, rfl⟩ := hT
  have hDc := doublyStochastic_columnStochastic hD
  have hRc := erasure_columnStochastic hR
  constructor
  · intro i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hc.1 (hDc.1 i j))
      (mul_nonneg (sub_nonneg.mpr hc.2) (hRc.1 i j))
  · intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, hDc.2 j, hRc.2 j]
    ring

/-- A doubly-stochastic matrix contracts the Euclidean square sum. -/
lemma sum_sq_mulVec_le {n : ℕ} {D : Mat n n}
    (hD : Matrix.of D ∈ doublyStochastic ℝ (Fin n))
    (v : Fin n → ℝ) :
    (∑ i, (∑ j, D i j * v j) ^ 2) ≤ ∑ j, v j ^ 2 := by
  have hrow (i : Fin n) :
      (∑ j, D i j * v j) ^ 2 ≤ ∑ j, D i j * v j ^ 2 := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (s := (Finset.univ : Finset (Fin n)))
      (r := fun j => D i j * v j)
      (f := fun j => D i j)
      (g := fun j => D i j * v j ^ 2)
      (fun j _ => nonneg_of_mem_doublyStochastic hD)
      (fun j _ => mul_nonneg (nonneg_of_mem_doublyStochastic hD) (sq_nonneg _))
      (fun j _ => by ring_nf; exact le_rfl)
    have hrowsum : ∑ j, D i j = 1 := sum_row_of_mem_doublyStochastic hD i
    rw [hrowsum, one_mul] at hcs
    exact hcs
  calc
    (∑ i, (∑ j, D i j * v j) ^ 2) ≤
        ∑ i, ∑ j, D i j * v j ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = ∑ j, (∑ i, D i j) * v j ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ = ∑ j, v j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hcolsum : ∑ i, D i j = 1 := sum_col_of_mem_doublyStochastic hD j
      rw [hcolsum, one_mul]

lemma fdi_doublyStochastic_le {n m : ℕ} {D : Mat n n}
    (hD : Matrix.of D ∈ doublyStochastic ℝ (Fin n))
    (U : Mat n m) :
    (∑ i, ∑ a, (D * centered U) i a ^ 2) ≤ fdi U := by
  unfold fdi
  rw [Finset.sum_comm]
  calc
    (∑ a, ∑ i, (D * centered U) i a ^ 2) ≤
        ∑ a, ∑ i, centered U i a ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      simpa [mat_mul_apply] using
        (sum_sq_mulVec_le hD (fun i => centered U i a))
    _ = ∑ i, ∑ a, centered U i a ^ 2 := Finset.sum_comm

/-- FDI satisfies DPI on the paper's restricted convex channel class. -/
theorem fdi_restricted_dpi {n m : ℕ} {T : Mat n n}
    (hT : RestrictedChannel T) {U : Mat n m} (hU : Simplex U) :
    fdi (T * U) ≤ fdi U := by
  obtain ⟨c, D, R, hc, hD, hR, rfl⟩ := hT
  have hTstoch : ColumnStochastic (c • D + (1 - c) • R) :=
    restrictedChannel_columnStochastic
      ⟨c, D, R, hc, hD, hR, rfl⟩
  have hRzero := erasure_mul_centered_eq_zero hR hU
  have haction : (c • D + (1 - c) • R) * centered U =
      c • (D * centered U) := by
    ext i a
    have hz := congrFun (congrFun hRzero i) a
    change (∑ j, R i j * centered U j a) = 0 at hz
    simp only [mat_mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ x, (c * D i x + (1 - c) * R i x) * centered U x a) =
          ∑ x, (c * (D i x * centered U x a) +
            (1 - c) * (R i x * centered U x a)) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = c * (∑ x, D i x * centered U x a) +
          (1 - c) * (∑ x, R i x * centered U x a) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = c * ∑ j, D i j * centered U j a := by rw [hz]; ring
  unfold fdi
  rw [centered_mul hTstoch, haction]
  have hcontract := fdi_doublyStochastic_le hD U
  have hcsq : c ^ 2 ≤ 1 := by nlinarith [hc.1, hc.2]
  have hDU0 : 0 ≤ ∑ i, ∑ a, (D * centered U) i a ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  calc
    (∑ i, ∑ a, (c • (D * centered U)) i a ^ 2) =
        c ^ 2 * ∑ i, ∑ a, (D * centered U) i a ^ 2 := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
      simp_rw [← Finset.mul_sum]
    _ ≤ 1 * ∑ i, ∑ a, (D * centered U) i a ^ 2 :=
      mul_le_mul_of_nonneg_right hcsq hDU0
    _ ≤ ∑ i, ∑ a, centered U i a ^ 2 := by
      rw [one_mul]
      exact hcontract

/-- Paper-facing formulation of restricted DPI using the literal convex hull
of doubly-stochastic and erasure channels. -/
theorem fdi_convexHull_dpi {n m : ℕ} (hn : 1 ≤ n) {T : Mat n n}
    (hT : T ∈ convexHull ℝ
      (DoublyStochasticChannels n ∪ ErasureChannels n))
    {U : Mat n m} (hU : Simplex U) :
    fdi (T * U) ≤ fdi U := by
  exact fdi_restricted_dpi
    ((restrictedChannel_iff_mem_convexHull hn T).2 hT) hU

/-! ## Exact failure of full stochastic DPI -/

/-- The normalized joint law in the explicit full-DPI counterexample. -/
def counterexampleU : Mat 4 3 :=
  ![![12 / 1001, 123 / 1001, 69 / 1001],
    ![114 / 1001, 154 / 1001, 85 / 1001],
    ![79 / 1001, 11 / 1001, 42 / 1001],
    ![79 / 1001, 107 / 1001, 126 / 1001]]

/-- The stochastic merging channel in the explicit DPI counterexample. -/
def counterexampleT : Mat 4 4 :=
  ![![1, 1, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 1, 1]]

lemma counterexampleU_simplex : Simplex counterexampleU := by
  constructor
  · intro i a
    fin_cases i <;> fin_cases a <;> norm_num [counterexampleU]
  · norm_num [mass, counterexampleU, Fin.sum_univ_succ]

lemma counterexampleT_columnStochastic : ColumnStochastic counterexampleT := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [counterexampleT]
  · intro j
    fin_cases j <;> norm_num [counterexampleT, Fin.sum_univ_succ]

lemma counterexample_fdi_strict :
    fdi counterexampleU < fdi (counterexampleT * counterexampleU) := by
  norm_num [fdi, centered, rowMarginal, columnMarginal, counterexampleU,
    counterexampleT, mat_mul_apply, Fin.sum_univ_succ]

/-- FDI does not satisfy unrestricted column-stochastic DPI. -/
theorem fdi_not_full_dpi : ¬ DPI (fdi : Mat 4 3 → ℝ) := by
  intro h
  have hle := h counterexampleT counterexampleU
    counterexampleT_columnStochastic counterexampleU_simplex
  exact (not_lt_of_ge hle) counterexample_fdi_strict


end FrobeniusDependence

end

end Cslib.FiniteSampleInformation
