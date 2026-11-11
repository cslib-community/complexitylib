/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/IntegerKernel.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.BasicSolution
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounded integer kernel vectors for wide integer matrices

An integer matrix `A : Matrix m n ℤ` with fewer rows than columns (`card m < card n`) admits a
nonzero integer kernel vector whose entries satisfy an explicit Siegel-style determinant bound
inherited from `Matrix.exists_int_nonneg_mulVec_eq`.

## Main results

* `Matrix.exists_int_mulVec_eq_zero_of_card_lt`: existence of a bounded nonzero integer solution to
  `A *ᵥ c = 0` whenever `Fintype.card m < Fintype.card n`.
-/

public section

namespace Matrix

/-- Explicit entry bound on a nonzero integer kernel vector for an integer matrix with `r` rows
and entry bound `B`. -/
@[expose] def kernelVecBound (r B : ℕ) : ℕ :=
  r.factorial * (r * ((r + 1) * B) ^ 2 + 1) ^ r

private lemma sum_ne_eq_sum_erase {n α : Type*} [Fintype n] [DecidableEq n] [AddCommMonoid α]
    (j₀ : n) (f : n → α) :
    ∑ j : { j : n // j ≠ j₀ }, f j.1 = ∑ j ∈ Finset.univ.erase j₀, f j := by
  let e : { j : n // j ≠ j₀ } ≃ ↥(Finset.univ.erase j₀) :=
    { toFun := fun j => ⟨j.1, Finset.mem_erase.2 ⟨j.2, Finset.mem_univ _⟩⟩
      invFun := fun j => ⟨j.1, (Finset.mem_erase.1 j.2).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.sum_equiv e (fun j => f j.1) (fun j : ↥(Finset.univ.erase j₀) => f j.1)
    (fun _ => rfl)]
  exact Finset.sum_coe_sort (Finset.univ.erase j₀) f

private lemma exists_int_mulVec_eq_zero_of_succ {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℤ) {B : ℕ} (hA : ∀ i j, |A i j| ≤ B)
    (hcard : Fintype.card n = Fintype.card m + 1) :
    ∃ c : n → ℤ, c ≠ 0 ∧ A *ᵥ c = 0 ∧ ∀ j, |c j| ≤ kernelVecBound (Fintype.card m) B := by
  classical
  have hlt : Fintype.card m < Fintype.card n := by omega
  have hnot_inj : ¬ Function.Injective (A.map (Int.cast : ℤ → ℚ)).mulVecLin := by
    intro hinj
    have hrank := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hrank
    omega
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot'] at hnot_inj
  push Not at hnot_inj
  obtain ⟨v, hv_eq, hv0⟩ := hnot_inj
  have hne_univ : (Finset.univ : Finset n).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff]
    omega
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset n) (fun j => |v j|) hne_univ
  have hvj₀ : v j₀ ≠ 0 := fun h => hv0 (funext fun j => by
    have := hj₀ j (Finset.mem_univ j)
    rw [h, abs_zero] at this
    exact abs_nonpos_iff.1 this)
  let w : n → ℚ := (v j₀)⁻¹ • v
  have hw_mul : (A.map (Int.cast : ℤ → ℚ)) *ᵥ w = 0 := by
    change (A.map (Int.cast : ℤ → ℚ)).mulVec ((v j₀)⁻¹ • v) = 0
    rw [Matrix.mulVec_smul, show (A.map (Int.cast : ℤ → ℚ)) *ᵥ v = 0 from hv_eq, smul_zero]
  have hw_j₀ : w j₀ = 1 := by simp [w, hvj₀]
  have hw_abs : ∀ j, |w j| ≤ 1 := fun j => by
    have := hj₀ j (Finset.mem_univ j)
    rw [show w j = (v j₀)⁻¹ * v j by rfl, abs_mul, abs_inv]
    rw [inv_mul_le_iff₀ (abs_pos.2 hvj₀), mul_one]
    exact this
  let n' := { j : n // j ≠ j₀ }
  let A' : Matrix m n' ℤ := fun i j => A i j.1
  let b' : m → ℤ := fun i => -A i j₀ + ∑ j : n', A i j.1
  let x' : n' → ℚ := fun j => w j.1 + 1
  have hx'_nonneg : 0 ≤ x' := by
    intro j
    have := abs_le.1 (hw_abs j.1)
    change 0 ≤ w j.1 + 1
    linarith
  have hAx' : (A'.map Int.cast) *ᵥ x' = fun i => (b' i : ℚ) := by
    ext i
    simp only [mulVec, dotProduct, x', A', b', Int.cast_add, Int.cast_neg, Int.cast_sum]
    have hsplit : ∑ j : n, ((A i j : ℤ) : ℚ) * w j =
        ((A i j₀ : ℤ) : ℚ) * w j₀ + ∑ j ∈ Finset.univ.erase j₀, ((A i j : ℤ) : ℚ) * w j := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j₀)]
    have hrow : ∑ j : n, ((A i j : ℤ) : ℚ) * w j = 0 := congrFun hw_mul i
    have heq_sub : ∑ j : n', ((A i j.1 : ℤ) : ℚ) * w j.1 =
        ∑ j ∈ Finset.univ.erase j₀, ((A i j : ℤ) : ℚ) * w j :=
      sum_ne_eq_sum_erase j₀ fun j => ((A i j : ℤ) : ℚ) * w j
    calc ∑ j : n', ((A i j.1 : ℤ) : ℚ) * (w j.1 + 1)
        = (∑ j : n', ((A i j.1 : ℤ) : ℚ) * w j.1) + ∑ j : n', ((A i j.1 : ℤ) : ℚ) := by
          simp only [mul_add, mul_one, Finset.sum_add_distrib]
      _ = -((A i j₀ : ℤ) : ℚ) + ∑ j : n', ((A i j.1 : ℤ) : ℚ) := by
          rw [hw_j₀, mul_one] at hsplit
          rw [heq_sub]
          linarith [hsplit, hrow]
  let B' : ℕ := (Fintype.card m + 1) * B
  have hA'_bd : ∀ i (j : n'), |A' i j| ≤ B' := fun i j =>
    (hA i j.1).trans (by exact_mod_cast Nat.le_mul_of_pos_left B (Nat.succ_pos _))
  have hb'_bd : ∀ i, |b' i| ≤ B' := fun i => by
    have hsum_bd : |∑ j : n', A i j.1| ≤ (Fintype.card n' : ℤ) * B := by
      calc |∑ j : n', A i j.1|
          ≤ ∑ _j : n', (B : ℤ) :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hA i j.1)
        _ = (Fintype.card n' : ℤ) * B := by simp
    have hn' : Fintype.card n' = Fintype.card m := by
      rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ]
      omega
    calc |b' i| = |-A i j₀ + ∑ j : n', A i j.1| := rfl
      _ ≤ |-A i j₀| + |∑ j : n', A i j.1| := abs_add_le _ _
      _ ≤ B + (Fintype.card n' : ℤ) * B := add_le_add (by simpa [abs_neg] using hA i j₀) hsum_bd
      _ = (B' : ℤ) := by
        rw [hn']
        push_cast [B']
        ring
  obtain ⟨d, p', hd_pos, hp'_nonneg, hAp', hd_le, hp'_le⟩ :=
    Matrix.exists_int_nonneg_mulVec_eq hA'_bd hb'_bd hx'_nonneg hAx'
  have hn' : Fintype.card n' = Fintype.card m := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    omega
  rw [hn'] at hd_le hp'_le
  let c : n → ℤ := fun j => if h : j = j₀ then d else p' ⟨j, h⟩ - d
  refine ⟨c, ?_, ?_, ?_⟩
  · intro hc0
    have h0 := congrFun hc0 j₀
    simp only [c, dite_eq_left rfl, Pi.zero_apply] at h0
    omega
  · ext i
    have hsplit : (A *ᵥ c) i = A i j₀ * c j₀ + ∑ j ∈ Finset.univ.erase j₀, A i j * c j := by
      change ∑ j : n, A i j * c j = _
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j₀)]
    have hc_j₀ : c j₀ = d := by simp [c]
    have hsub : ∑ j ∈ Finset.univ.erase j₀, A i j * c j =
        ∑ j : n', A' i j * (p' j - d) := by
      rw [← sum_ne_eq_sum_erase j₀ (fun j => A i j * c j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [c, j.2, A']
    have hAp_i : ∑ j : n', A' i j * p' j = d * b' i := congrFun hAp' i
    rw [hsplit, hc_j₀, hsub]
    calc A i j₀ * d + ∑ j : n', A' i j * (p' j - d)
        = A i j₀ * d + ((∑ j : n', A' i j * p' j) - d * ∑ j : n', A i j.1) := by
          simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, A', mul_comm _ d]
      _ = A i j₀ * d + (d * (-A i j₀ + ∑ j : n', A i j.1) - d * ∑ j : n', A i j.1) := by
          rw [hAp_i]
      _ = 0 := by ring
  · intro j
    by_cases hj : j = j₀
    · subst hj
      simp only [c, dite_eq_left rfl, abs_of_pos hd_pos]
      exact hd_le
    · simp only [c, dite_eq_right hj]
      have h0 : 0 ≤ p' ⟨j, hj⟩ := hp'_nonneg ⟨j, hj⟩
      have hp_le := hp'_le ⟨j, hj⟩
      rw [abs_le]
      dsimp only [kernelVecBound, B']
      exact ⟨by linarith, by linarith⟩

/-- An integer matrix `A : Matrix m n ℤ` with `Fintype.card m < Fintype.card n` and entry bound `B`
admits a nonzero integer kernel vector bounded in magnitude by `kernelVecBound (card m) B`. -/
theorem exists_int_mulVec_eq_zero_of_card_lt {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℤ) {B : ℕ} (hA : ∀ i j, |A i j| ≤ B)
    (hcard : Fintype.card m < Fintype.card n) :
    ∃ c : n → ℤ, c ≠ 0 ∧ A *ᵥ c = 0 ∧ ∀ j, |c j| ≤ kernelVecBound (Fintype.card m) B := by
  classical
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset n)) hcard
  have hS_card : Fintype.card S = Fintype.card m + 1 := by simp [Fintype.card_coe, hS]
  let AS : Matrix m S ℤ := A.submatrix id Subtype.val
  obtain ⟨cS, hcS0, hAS, hcS_bd⟩ := exists_int_mulVec_eq_zero_of_succ AS
    (fun i j => hA i j.1) hS_card
  let c : n → ℤ := fun j => if hj : j ∈ S then cS ⟨j, hj⟩ else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · intro hc0
    apply hcS0
    ext j
    have := congrFun hc0 j.1
    simpa [c, j.2] using this
  · ext i
    change ∑ j : n, A i j * c j = 0
    have hsplit : ∑ j : n, A i j * c j = ∑ j ∈ S, A i j * c j := by
      rw [← Finset.sum_subset (Finset.subset_univ S)]
      intro j _ hj
      simp [c, hj]
    rw [hsplit, ← Finset.sum_coe_sort S (fun j => A i j * c j)]
    simpa [c, AS, mulVec, dotProduct] using congrFun hAS i
  · intro j
    by_cases hj : j ∈ S
    · simpa [c, hj] using hcS_bd ⟨j, hj⟩
    · simp only [c, hj, ↓reduceDIte, abs_zero]
      exact Int.natCast_nonneg _

end Matrix
