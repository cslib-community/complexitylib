/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.FiniteSampleInformation.GeneralAsymmetricC1

/-!
# Dimension-changing information monotones

[Kong2027], Corollary 5.3 (PDF p. 16). Channels may change the number
of rows. Adding a null state has a stochastic left inverse. Smoothness is
required at the boundary of every closed simplex, not just in its interior.
-/

public section
noncomputable section

namespace Cslib.FiniteSampleInformation
open GeneralAsymmetricC1

/-- A rectangular channel acts on column probability vectors. -/
@[expose] def RectangularColumnStochastic {k n : ℕ} (T : Mat k n) : Prop :=
  (∀ i j, 0 ≤ T i j) ∧ (∀ j, ∑ i, T i j = 1)

/-- One-sided DPI across all alphabet sizes at least two. -/
@[expose] def DimensionChangingDPI (F : (n m : ℕ) → Mat n m → ℝ) : Prop :=
  ∀ k n m, 2 ≤ k → 2 ≤ n → 2 ≤ m →
    ∀ T : Mat k n, RectangularColumnStochastic T →
      ∀ U : Mat n m, Simplex U → F k m (T * U) ≤ F n m U

/-- Appending an unused state to the processed alphabet. -/
@[expose] def appendZeroRow {n m : ℕ} (U : Mat n m) : Mat (n + 1) m :=
  Fin.lastCases (fun _ => 0) (fun i => U i)

private def inclusionChannel (n : ℕ) : Mat (n + 1) n :=
  fun i j => Fin.lastCases 0 (fun i => if i = j then 1 else 0) i

private def retractionChannel (n : ℕ) [NeZero n] : Mat n (n + 1) :=
  fun i j => Fin.lastCases (if i = 0 then 1 else 0)
    (fun j => if i = j then 1 else 0) j

private theorem inclusion_stochastic (n : ℕ) :
    RectangularColumnStochastic (inclusionChannel n) := by
  constructor
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [inclusionChannel]
    split_ifs <;> norm_num
  · intro j
    simp [inclusionChannel, Fin.sum_univ_castSucc]

private theorem retraction_stochastic (n : ℕ) [NeZero n] :
    RectangularColumnStochastic (retractionChannel n) := by
  constructor
  · intro i j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [retractionChannel]
    all_goals split_ifs <;> norm_num
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [retractionChannel]

private theorem inclusion_mul {n m : ℕ} (U : Mat n m) :
    inclusionChannel n * U = appendZeroRow U := by
  ext i a
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    simp [mat_mul_apply, inclusionChannel, appendZeroRow]

private theorem retraction_mul {n m : ℕ} [NeZero n] (U : Mat n m) :
    retractionChannel n * appendZeroRow U = U := by
  ext i a
  simp [mat_mul_apply, Fin.sum_univ_castSucc, appendZeroRow, retractionChannel]

/-- Appending a zero row preserves the closed probability simplex. -/
theorem appendZeroRow_simplex {n m : ℕ} {U : Mat n m} (hU : Simplex U) :
    Simplex (appendZeroRow U) := by
  constructor
  · intro i a
    exact Fin.lastCases (by simp [appendZeroRow])
      (fun i => by simpa [appendZeroRow] using hU.1 i a) i
  · simpa [mass, appendZeroRow, Fin.sum_univ_castSucc] using hU.2

/-- Expansibility follows from DPI in both directions along reversible channels. -/
theorem dimensionChanging_expansibility
    {F : (n m : ℕ) → Mat n m → ℝ} (hF : DimensionChangingDPI F)
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) {U : Mat n m} (hU : Simplex U) :
    F (n + 1) m (appendZeroRow U) = F n m U := by
  let : NeZero n := ⟨by omega⟩
  apply le_antisymm
  · simpa only [inclusion_mul] using
      hF (n + 1) n m (by omega) hn hm _ (inclusion_stochastic n) U hU
  · simpa only [retraction_mul] using
      hF n (n + 1) m hn (by omega) hm _ (retraction_stochastic n)
        (appendZeroRow U) (appendZeroRow_simplex hU)

/-- Corollary 5.3: every smooth independence-zero dimension-changing family
vanishes, for every joint law on every pair of alphabets at least two. -/
theorem dimensionChanging_collapse
    {F : (n m : ℕ) → Mat n m → ℝ} (hDPI : DimensionChangingDPI F)
    (hC1 : ∀ n m, 2 ≤ n → 2 ≤ m → ContDiffOnSimplex (F n m))
    (hIZ : ∀ n m, 2 ≤ n → 2 ≤ m → RKO (F n m))
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) {U : Mat n m} (hU : Simplex U) :
    F n m U = 0 := by
  let : NeZero m := ⟨by omega⟩
  have hfixed : DPI (F (n + 1) m) := by
    intro T V hT hV
    exact hDPI (n + 1) (n + 1) m (by omega) (by omega) hm T hT V hV
  rw [← dimensionChanging_expansibility hDPI hn hm hU]
  exact zero_row_vanishing_of_contDiffOnSimplex (by omega)
    (hC1 (n + 1) m (by omega) hm) hfixed (hIZ (n + 1) m (by omega) hm)
    (appendZeroRow_simplex hU) (r := Fin.last n) (by simp [appendZeroRow])

end Cslib.FiniteSampleInformation
