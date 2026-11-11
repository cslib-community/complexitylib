/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BasicSolution
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact

/-!
# Polynomial-Size Nonnegative Integer Witnesses for Non-Copositivity

A symmetric integer or rational matrix `M` is *copositive* if `x ⬝ᵥ M *ᵥ x ≥ 0` for all
entrywise nonnegative vectors `x`. By minimizing the quadratic form `x ⬝ᵥ M *ᵥ x` over the
compact standard simplex, KKT stationarity forces `M *ᵥ x*` to be constant and strictly negative
on the support of any negative minimizer `x*`. Applying
`Matrix.exists_int_nonneg_mulVec_eq` to the principal submatrix on that support produces a
nonnegative integer vector `p` with `p ⬝ᵥ M *ᵥ p < 0` whose entries are singly exponentially
bounded in the dimension and entry bit-length, hence of polynomial bit-length.

As a consequence, copositivity over `ℝ`, `ℚ`, and `ℕ` coincides for symmetric rational matrices.
[MurtyKabadi1987] is cited at paper level from bibliographic metadata only without inspecting
the published text; the KKT + `Matrix.exists_int_nonneg_mulVec_eq` proof and the explicit witness
bound `Nat.factorial (Fintype.card V) * (Fintype.card V * (max B 1) ^ 2 + 1) ^ Fintype.card V`
are original to this library.

## Main definitions

- `Matrix.IsCopositive`: entrywise nonnegative vectors have nonnegative quadratic form.

## Main results

- `Matrix.exists_nat_dotProduct_lt_zero_of_isSymm`: a non-copositive symmetric integer matrix has
  a bounded nonnegative integer certificate `p` with `p ⬝ᵥ M *ᵥ p < 0`.
- `Matrix.isCopositive_int_real_iff_nat`: copositivity over `ℝ` and `ℕ` coincide for symmetric
  integer matrices.
- `Matrix.exists_nat_dotProduct_lt_zero_of_rat`: rational version via a cleared common denominator.
- `Matrix.isCopositive_rat_iff_map_real`: copositivity over `ℚ` and `ℝ` coincide for symmetric
  rational matrices.
- `Matrix.isCopositive_rat_iff_nat`: copositivity over `ℚ` and `ℕ` coincide for symmetric
  rational matrices.

## References

- [MurtyKabadi1987] K. G. Murty and S. N. Kabadi, *Some NP-complete problems in quadratic and
  nonlinear programming*, Mathematical Programming 39(2), 1987, 117–129 (bibliographic metadata
  only; the published article text was not inspected in this pass, and no internal theorem numbers
  are claimed).
-/

public section

namespace Matrix

open Matrix

/-- A square matrix `M` over an ordered commutative semiring is *copositive* if `x ⬝ᵥ M *ᵥ x ≥ 0`
for every entrywise nonnegative vector `x`. -/
@[expose] def IsCopositive {V K : Type*} [Fintype V] [CommSemiring K] [PartialOrder K]
    (M : Matrix V V K) : Prop :=
  ∀ x : V → K, (∀ v, 0 ≤ x v) → 0 ≤ x ⬝ᵥ M *ᵥ x

private theorem dotProduct_add_smul_symm {V K : Type*} [Fintype V] [CommRing K]
    {M : Matrix V V K} (hSymm : M.IsSymm) (x d : V → K) (t : K) :
    (x + t • d) ⬝ᵥ (M *ᵥ (x + t • d)) =
      x ⬝ᵥ (M *ᵥ x) + 2 * t * (d ⬝ᵥ (M *ᵥ x)) + t ^ 2 * (d ⬝ᵥ (M *ᵥ d)) := by
  have hxMd : x ⬝ᵥ (M *ᵥ d) = d ⬝ᵥ (M *ᵥ x) := by
    rw [← dotProduct_transpose_mulVec M d x, hSymm]
  rw [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct,
    dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_dotProduct, hxMd]
  ring

private theorem simplex_isCompact (n : ℕ) :
    IsCompact {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1} := by
  let Δ : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}
  have hsub : Δ ⊆ Set.Icc (0 : Fin n → ℝ) 1 := by
    intro x hx
    refine ⟨hx.1, fun i => ?_⟩
    have hle := Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
    rw [Pi.one_apply]
    linarith [hx.2]
  have hclosed1 : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    have : {x : Fin n → ℝ | ∀ i, 0 ≤ x i} =
        ⋂ i : Fin n, (fun x : Fin n → ℝ => x i) ⁻¹' Set.Ici 0 := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Ici]
    rw [this]
    exact isClosed_iInter fun i => isClosed_Ici.preimage (continuous_apply i)
  have hclosed2 : IsClosed {x : Fin n → ℝ | ∑ i : Fin n, x i = 1} :=
    isClosed_singleton.preimage
      (continuous_finsetSum Finset.univ fun i _ => continuous_apply i)
  exact isCompact_Icc.of_isClosed_subset (hclosed1.inter hclosed2) hsub

private theorem dotProduct_mulVec_continuous {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun x : Fin n → ℝ => x ⬝ᵥ M *ᵥ x := by
  have heq : (fun x : Fin n → ℝ => x ⬝ᵥ M *ᵥ x) =
      fun x => ∑ i : Fin n, x i * ∑ j : Fin n, M i j * x j := by
    ext x
    simp only [dotProduct, mulVec]
  rw [heq]
  refine continuous_finsetSum Finset.univ fun i _ => (continuous_apply i).mul ?_
  exact continuous_finsetSum Finset.univ fun j _ =>
    continuous_const.mul (continuous_apply j)

private theorem kkt_stationarity_on_simplex {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hSymm : M.IsSymm) {x : Fin n → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∑ i, x i = 1)
    (hmin : ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → ∑ i, y i = 1 → x ⬝ᵥ M *ᵥ x ≤ y ⬝ᵥ M *ᵥ y)
    {i j : Fin n} (hi : 0 < x i) (hj : 0 < x j) :
    (M *ᵥ x) i = (M *ᵥ x) j := by
  by_cases hij : i = j
  · subst hij
    rfl
  · by_contra hne
    set d : Fin n → ℝ := Pi.single i 1 - Pi.single j 1
    set a : ℝ := (M *ᵥ x) i - (M *ᵥ x) j
    set c : ℝ := d ⬝ᵥ M *ᵥ d
    have ha_ne : a ≠ 0 := sub_ne_zero.2 hne
    have hδ_pos : 0 < min (x i) (x j) := lt_min hi hj
    set t₀ : ℝ := min (min (x i) (x j)) (|a| / (2 * (|c| + 1)))
    have ht₀_pos : 0 < t₀ := by positivity
    have ht₀_xi : t₀ ≤ x i := le_trans (min_le_left _ _) (min_le_left _ _)
    have ht₀_xj : t₀ ≤ x j := le_trans (min_le_left _ _) (min_le_right _ _)
    have ht₀_c : t₀ ≤ |a| / (2 * (|c| + 1)) := min_le_right _ _
    have hquad_nonneg : ∀ t : ℝ, -x i ≤ t → t ≤ x j → 0 ≤ 2 * t * a + t ^ 2 * c := by
      intro t hti htj
      have hy0 : ∀ k, 0 ≤ (x + t • d) k := by
        intro k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, d, Pi.sub_apply]
        by_cases hki : k = i
        · subst hki
          rw [Pi.single_eq_same, Pi.single_eq_of_ne hij]
          linarith
        · by_cases hkj : k = j
          · subst hkj
            rw [Pi.single_eq_of_ne hki, Pi.single_eq_same]
            linarith
          · rw [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]
            simpa only [sub_self, mul_zero, add_zero] using hx0 k
      have hy1 : ∑ k, (x + t • d) k = 1 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, hx1,
          ← Finset.mul_sum, d, Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, sub_self, mul_zero, add_zero]
      have hdAx : d ⬝ᵥ M *ᵥ x = a := by
        simp only [d, a, Pi.sub_apply, dotProduct, Pi.single_apply, sub_mul,
          Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte]
      have hmin_y := hmin (x + t • d) hy0 hy1
      rw [dotProduct_add_smul_symm hSymm x d t, hdAx] at hmin_y
      exact sub_nonneg.1 (by linarith)
    have habs_bound : t₀ * |c| < |a| := by
      have hc1 : (0 : ℝ) < |c| + 1 := by positivity
      have hmul : t₀ * (2 * (|c| + 1)) ≤ |a| := (le_div_iff₀ (by positivity)).1 ht₀_c
      have hle : t₀ * |c| ≤ t₀ * (|c| + 1) := mul_le_mul_of_nonneg_left (by linarith) ht₀_pos.le
      nlinarith
    rcases lt_or_gt_of_ne ha_ne with ha_neg | ha_pos
    · have hnonneg := hquad_nonneg t₀ (by linarith [hx0 i]) ht₀_xj
      have ha_abs : |a| = -a := abs_of_neg ha_neg
      have htc : t₀ * c ≤ t₀ * |c| := mul_le_mul_of_nonneg_left (le_abs_self c) ht₀_pos.le
      nlinarith
    · have hnonneg := hquad_nonneg (-t₀) (by linarith) (by linarith [hx0 j])
      have ha_abs : |a| = a := abs_of_pos ha_pos
      have htc : (-t₀) ^ 2 * c ≤ t₀ ^ 2 * |c| := by
        rw [neg_sq]
        exact mul_le_mul_of_nonneg_left (le_abs_self c) (sq_nonneg t₀)
      nlinarith

private theorem exists_nat_dotProduct_lt_zero_of_isSymm_fin {n B : ℕ} {M : Matrix (Fin n) (Fin n) ℤ}
    (hSymm : M.IsSymm) (hB : ∀ i j, |M i j| ≤ (B : ℤ))
    (hnc : ¬ (M.map (Int.cast : ℤ → ℝ)).IsCopositive) :
    ∃ p : Fin n → ℕ,
      (∀ i, p i ≤ Nat.factorial n * (n * (max B 1) ^ 2 + 1) ^ n) ∧
        (fun i => (p i : ℤ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℤ)) < 0 := by
  rw [IsCopositive] at hnc
  push Not at hnc
  obtain ⟨x₀, hx₀_nonneg, hx₀_neg⟩ := hnc
  have hx₀_sum_pos : 0 < ∑ i, x₀ i := by
    by_contra hle
    have hsum0 : ∑ i, x₀ i = 0 :=
      le_antisymm (not_lt.1 hle) (Finset.sum_nonneg fun i _ => hx₀_nonneg i)
    have hx₀_zero : ∀ i, x₀ i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hx₀_nonneg j).1 hsum0 i (Finset.mem_univ i)
    have hq0 : x₀ ⬝ᵥ (M.map (Int.cast : ℤ → ℝ) *ᵥ x₀) = 0 := by
      simp only [dotProduct, hx₀_zero, zero_mul, Finset.sum_const_zero]
    linarith
  let y₀ : Fin n → ℝ := (∑ i, x₀ i)⁻¹ • x₀
  have hy₀_nonneg : ∀ i, 0 ≤ y₀ i := fun i => by
    dsimp only [y₀, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hx₀_sum_pos.le) (hx₀_nonneg i)
  have hy₀_sum : ∑ i, y₀ i = 1 := by
    simp only [y₀, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hx₀_sum_pos.ne'
  have hy₀_neg : y₀ ⬝ᵥ (M.map (Int.cast : ℤ → ℝ) *ᵥ y₀) < 0 := by
    rw [show y₀ ⬝ᵥ (M.map (Int.cast : ℤ → ℝ) *ᵥ y₀) =
        (∑ i, x₀ i)⁻¹ ^ 2 * (x₀ ⬝ᵥ (M.map (Int.cast : ℤ → ℝ) *ᵥ x₀)) by
      simp only [y₀, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      ring]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos (inv_pos.2 hx₀_sum_pos)) hx₀_neg
  let Δ : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}
  have hΔ_compact : IsCompact Δ := simplex_isCompact n
  have hΔ_nonempty : Δ.Nonempty := ⟨y₀, hy₀_nonneg, hy₀_sum⟩
  obtain ⟨x, hxΔ, hxmin⟩ := hΔ_compact.exists_isMinOn hΔ_nonempty
    (dotProduct_mulVec_continuous (M.map Int.cast)).continuousOn
  have hx0 : ∀ i, 0 ≤ x i := hxΔ.1
  have hx1 : ∑ i, x i = 1 := hxΔ.2
  have hxmin_all : ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → ∑ i, y i = 1 →
      x ⬝ᵥ (M.map (Int.cast : ℤ → ℝ) *ᵥ x) ≤ y ⬝ᵥ (M.map (Int.cast : ℤ → ℝ) *ᵥ y) :=
    fun y hy0 hy1 => hxmin ⟨hy0, hy1⟩
  set MR : Matrix (Fin n) (Fin n) ℝ := M.map Int.cast
  have hSymmR : MR.IsSymm := by
    ext i j
    simp only [MR, transpose_apply, map_apply]
    exact congrArg Int.cast (congrFun (congrFun hSymm i) j)
  set lam : ℝ := x ⬝ᵥ (MR *ᵥ x)
  have hlam_neg : lam < 0 := lt_of_le_of_lt (hxmin_all y₀ hy₀_nonneg hy₀_sum) hy₀_neg
  let S : Finset (Fin n) := Finset.univ.filter fun i => 0 < x i
  have hS_nonempty : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hxzero : ∀ i, x i = 0 := fun i => by
      have hi : i ∉ S := hemp ▸ Finset.notMem_empty i
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      exact le_antisymm hi (hx0 i)
    have hsum0 : ∑ i, x i = 0 := Finset.sum_eq_zero fun i _ => hxzero i
    linarith
  obtain ⟨i₀, hi₀⟩ := hS_nonempty
  have hi₀_pos : 0 < x i₀ := (Finset.mem_filter.1 hi₀).2
  have hconst : ∀ i ∈ S, (MR *ᵥ x) i = (MR *ᵥ x) i₀ := fun i hi =>
    kkt_stationarity_on_simplex hSymmR hx0 hx1 hxmin_all (Finset.mem_filter.1 hi).2 hi₀_pos
  have hlam_eq : (MR *ᵥ x) i₀ = lam := by
    have hxout : ∀ i, i ∉ S → x i = 0 := fun i hi => by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      exact le_antisymm hi (hx0 i)
    have hdot : x ⬝ᵥ (MR *ᵥ x) = ∑ i ∈ S, x i * (MR *ᵥ x) i := by
      rw [dotProduct, ← Finset.sum_subset (Finset.subset_univ S)]
      intro i _ hi
      rw [hxout i hi, zero_mul]
    have hdot2 : ∑ i ∈ S, x i * (MR *ᵥ x) i = (∑ i ∈ S, x i) * (MR *ᵥ x) i₀ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i hi => by rw [hconst i hi]
    have hxS : ∑ i ∈ S, x i = 1 := by
      rw [← hx1]
      exact Finset.sum_subset (Finset.subset_univ S) fun i _ hi => hxout i hi
    dsimp only [lam]
    rw [hdot, hdot2, hxS, one_mul]
  have hMR_S : ∀ i ∈ S, (MR *ᵥ x) i = lam := fun i hi => (hconst i hi).trans hlam_eq
  let MS : Matrix S S ℤ := Matrix.of fun i j => M i.1 j.1
  let b : S → ℤ := fun _ => -1
  let B' : ℕ := max B 1
  have hMS_le : ∀ i j : S, |MS i j| ≤ (B' : ℤ) := fun i j =>
    (hB i.1 j.1).trans (by exact_mod_cast le_max_left B 1)
  have hb_le : ∀ i : S, |b i| ≤ (B' : ℤ) := fun i => by
    dsimp only [b]
    norm_num
    exact_mod_cast le_max_right B 1
  let z : S → ℝ := fun j => (-lam)⁻¹ * x j.1
  have hz_nonneg : 0 ≤ z := fun j =>
    mul_nonneg (inv_nonneg.2 (neg_pos.2 hlam_neg).le) (hx0 j.1)
  have hMSz : MS.map (Int.cast : ℤ → ℝ) *ᵥ z = fun i => (b i : ℝ) := by
    ext i
    simp only [mulVec, dotProduct, map_apply, MS, of_apply, z, b, Int.cast_neg, Int.cast_one]
    have hsum_eq : ∑ j : S, (M i.1 j.1 : ℝ) * ((-lam)⁻¹ * x j.1) =
        (-lam)⁻¹ * ∑ j : S, (M i.1 j.1 : ℝ) * x j.1 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hxS_sum : ∑ j : S, (M i.1 j.1 : ℝ) * x j.1 = (MR *ᵥ x) i.1 := by
      rw [← Finset.sum_subtype S (fun _ => Iff.rfl) fun j => (M i.1 j : ℝ) * x j]
      simp only [mulVec, dotProduct, MR, map_apply]
      refine Finset.sum_subset (Finset.subset_univ S) fun j _ hj => ?_
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
      rw [le_antisymm hj (hx0 j), mul_zero]
    rw [hsum_eq, hxS_sum, hMR_S i.1 i.2]
    have hlam_ne : lam ≠ 0 := hlam_neg.ne
    field_simp [hlam_ne]
  obtain ⟨d, pS, hd_pos, hpS_nonneg, hAp, _, hpS_le⟩ :=
    Matrix.exists_int_nonneg_mulVec_eq (K := ℝ) hMS_le hb_le hz_nonneg hMSz
  let p : Fin n → ℕ := fun i => if hi : i ∈ S then (pS ⟨i, hi⟩).toNat else 0
  have hcard : Fintype.card S ≤ n := by
    rw [Fintype.card_coe]
    exact (S.card_le_univ).trans_eq (Fintype.card_fin n)
  have hbound_nat :
      Nat.factorial (Fintype.card S) * (Fintype.card S * B' ^ 2 + 1) ^ Fintype.card S ≤
        Nat.factorial n * (n * B' ^ 2 + 1) ^ n := by
    refine Nat.mul_le_mul (Nat.factorial_le hcard) ?_
    have hbase : Fintype.card S * B' ^ 2 + 1 ≤ n * B' ^ 2 + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right (B' ^ 2) hcard) 1
    exact (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (Nat.succ_pos _) hcard)
  refine ⟨p, fun i => ?_, ?_⟩
  · dsimp only [p]
    split_ifs with hi
    · have hleZ : pS ⟨i, hi⟩ ≤ (Nat.factorial n * (n * B' ^ 2 + 1) ^ n : ℕ) :=
        (hpS_le ⟨i, hi⟩).trans (Int.ofNat_le.2 hbound_nat)
      exact Int.toNat_le.2 hleZ
    · exact Nat.zero_le _
  · have hp_out : ∀ i : Fin n, i ∉ S → (p i : ℤ) = 0 := fun i hi => by
      dsimp only [p]
      split_ifs
      rfl
    have hp_in : ∀ i : S, (p i.1 : ℤ) = pS i := fun i => by
      have hi := i.2
      dsimp only [p]
      split_ifs
      exact Int.toNat_of_nonneg (hpS_nonneg i)
    have hquad_S : (fun i => (p i : ℤ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℤ)) =
        ∑ i : S, pS i * (MS *ᵥ pS) i := by
      simp only [dotProduct, mulVec]
      rw [← Finset.sum_subset (Finset.subset_univ S) fun i _ hi => by rw [hp_out i hi, zero_mul]]
      rw [Finset.sum_subtype S (fun _ => Iff.rfl)
        fun i => (p i : ℤ) * ∑ j : Fin n, M i j * (p j : ℤ)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hp_in i]
      congr 1
      rw [← Finset.sum_subset (Finset.subset_univ S) fun j _ hj => by rw [hp_out j hj, mul_zero]]
      rw [Finset.sum_subtype S (fun _ => Iff.rfl)
        fun j => M i.1 j * (p j : ℤ)]
      refine Finset.sum_congr rfl fun j _ => by simp only [MS, of_apply, hp_in j]
    have hMSp_eq : ∀ i : S, (MS *ᵥ pS) i = -d := fun i => by
      have hi := congrFun hAp i
      simpa only [Pi.smul_apply, smul_eq_mul, b, mul_neg, mul_one] using hi
    have hquad_eq : (fun i => (p i : ℤ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℤ)) =
        -d * ∑ i : S, pS i := by
      rw [hquad_S, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hMSp_eq i]; ring
    have hpS_sum_pos : 0 < ∑ i : S, pS i := by
      by_contra hle
      have hsum0 : ∑ i : S, pS i = 0 :=
        le_antisymm (not_lt.1 hle) (Finset.sum_nonneg fun i _ => hpS_nonneg i)
      have hpS_zero : ∀ i : S, pS i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hpS_nonneg j).1 hsum0 i (Finset.mem_univ i)
      have hi₀S : S := ⟨i₀, hi₀⟩
      have hcontra := hMSp_eq hi₀S
      simp only [mulVec, dotProduct, hpS_zero, mul_zero, Finset.sum_const_zero] at hcontra
      linarith
    rw [hquad_eq]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.2 hd_pos) hpS_sum_pos

/-- If a symmetric integer matrix `M` has a nonnegative real vector with negative quadratic form,
then it has a nonnegative integer vector `p` with `p ⬝ᵥ M *ᵥ p < 0` and entries bounded by
`Nat.factorial (Fintype.card V) * (Fintype.card V * (max B 1) ^ 2 + 1) ^ Fintype.card V`, where
`B` bounds `|M i j|`. (The KKT + `Matrix.exists_int_nonneg_mulVec_eq` proof and this explicit
bound are this library's formulation, not verified against [MurtyKabadi1987].) -/
theorem exists_nat_dotProduct_lt_zero_of_isSymm {V : Type*} [Fintype V] {B : ℕ} {M : Matrix V V ℤ}
    (hSymm : M.IsSymm) (hB : ∀ i j, |M i j| ≤ (B : ℤ))
    (hnc : ¬ (M.map (Int.cast : ℤ → ℝ)).IsCopositive) :
    ∃ p : V → ℕ,
      (∀ v, p v ≤
          Nat.factorial (Fintype.card V) * (Fintype.card V * (max B 1) ^ 2 + 1) ^ Fintype.card V) ∧
        (fun v => (p v : ℤ)) ⬝ᵥ (M *ᵥ fun v => (p v : ℤ)) < 0 := by
  classical
  obtain ⟨e⟩ := Fintype.truncEquivFin V
  let M_fin : Matrix (Fin (Fintype.card V)) (Fin (Fintype.card V)) ℤ :=
    Matrix.of fun i j => M (e.symm i) (e.symm j)
  have hSymm_fin : M_fin.IsSymm := by
    ext i j
    simp only [M_fin, transpose_apply, of_apply]
    exact congrFun (congrFun hSymm (e.symm i)) (e.symm j)
  have hB_fin : ∀ i j, |M_fin i j| ≤ (B : ℤ) := fun i j => hB (e.symm i) (e.symm j)
  have hnc_fin : ¬ (M_fin.map (Int.cast : ℤ → ℝ)).IsCopositive := by
    intro hcop
    apply hnc
    intro x hx
    have hsub := hcop (x ∘ e.symm) fun i => hx (e.symm i)
    have hdot :
        (x ∘ e.symm) ⬝ᵥ (M_fin.map (Int.cast : ℤ → ℝ) *ᵥ (x ∘ e.symm)) =
          x ⬝ᵥ (M.map (Int.cast : ℤ → ℝ) *ᵥ x) := by
      simp only [dotProduct, mulVec, Function.comp_apply, M_fin, map_apply, of_apply]
      refine Fintype.sum_equiv e.symm _ _ fun i => ?_
      refine congrArg (x (e.symm i) * ·) ?_
      exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
    rwa [hdot] at hsub
  obtain ⟨p_fin, hp_le, hp_neg⟩ :=
    exists_nat_dotProduct_lt_zero_of_isSymm_fin hSymm_fin hB_fin hnc_fin
  refine ⟨fun v => p_fin (e v), fun v => hp_le (e v), ?_⟩
  have hdotZ :
      (fun v => (p_fin (e v) : ℤ)) ⬝ᵥ (M *ᵥ fun v => (p_fin (e v) : ℤ)) =
        (fun i => (p_fin i : ℤ)) ⬝ᵥ (M_fin *ᵥ fun i => (p_fin i : ℤ)) := by
    simp only [dotProduct, mulVec, M_fin, of_apply]
    refine (Fintype.sum_equiv e.symm _ _ fun i => ?_).symm
    simp only [Equiv.apply_symm_apply]
    refine congrArg ((p_fin i : ℤ) * ·) ?_
    exact Fintype.sum_equiv e.symm _ _ fun _ => by simp only [Equiv.apply_symm_apply]
  rwa [hdotZ]

/-- For a symmetric integer matrix, copositivity over `ℝ` coincides with nonnegativity on all
nonnegative integer vectors. -/
theorem isCopositive_int_real_iff_nat {V : Type*} [Fintype V] {M : Matrix V V ℤ}
    (hSymm : M.IsSymm) :
    (M.map (Int.cast : ℤ → ℝ)).IsCopositive ↔
      ∀ p : V → ℕ, 0 ≤ (fun i => (p i : ℤ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℤ)) := by
  constructor
  · intro hcop p
    have hreal := hcop (fun i => (p i : ℝ)) fun i => Nat.cast_nonneg (p i)
    have hcast :
        (Int.cast ((fun i => (p i : ℤ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℤ))) : ℝ) =
          (fun i => (p i : ℝ)) ⬝ᵥ (M.map (Int.cast : ℤ → ℝ) *ᵥ fun i => (p i : ℝ)) := by
      simp only [dotProduct, mulVec, map_apply, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    rw [← hcast] at hreal
    exact not_lt.1 fun hn =>
      not_le_of_gt (show (Int.cast ((fun i => (p i : ℤ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℤ))) : ℝ) < 0
        from Int.cast_lt_zero.2 hn) hreal
  · intro hnat
    by_contra hnc
    let B : ℕ := Finset.univ.sup fun p : V × V => (M p.1 p.2).natAbs
    have hB : ∀ i j, |M i j| ≤ (B : ℤ) := fun i j => by
      rw [← Int.natCast_natAbs (M i j)]
      exact Int.ofNat_le.2 (Finset.le_sup (f := fun p : V × V => (M p.1 p.2).natAbs)
        (Finset.mem_univ (i, j)))
    obtain ⟨p, _, hp_neg⟩ := exists_nat_dotProduct_lt_zero_of_isSymm hSymm hB hnc
    exact (not_lt_of_ge (hnat p)) hp_neg

private theorem isCopositive_of_map_real {V : Type*} [Fintype V] {M : Matrix V V ℚ}
    (hcopR : (M.map (Rat.cast : ℚ → ℝ)).IsCopositive) : M.IsCopositive := by
  intro x hx
  have hR := hcopR (fun i => ((x i : ℚ) : ℝ)) fun i => Rat.cast_nonneg.2 (hx i)
  have hcast :
      (Rat.cast (x ⬝ᵥ (M *ᵥ x)) : ℝ) =
        (fun i => ((x i : ℚ) : ℝ)) ⬝ᵥ (M.map (Rat.cast : ℚ → ℝ) *ᵥ fun i => ((x i : ℚ) : ℝ)) := by
    simp only [dotProduct, mulVec, map_apply, Rat.cast_sum, Rat.cast_mul]
  rw [← hcast] at hR
  exact Rat.cast_nonneg.1 hR

private theorem exists_rat_clearDenom {V : Type*} [Finite V] (M : Matrix V V ℚ) :
    ∃ (d B : ℕ) (M_Z : Matrix V V ℤ),
      0 < d ∧ (∀ i j, (d : ℚ) * M i j = (M_Z i j : ℚ)) ∧ ∀ i j, |M_Z i j| ≤ (B : ℤ) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let d : ℕ := Finset.univ.prod fun p : V × V => (M p.1 p.2).den
  have hd : 0 < d := Finset.prod_pos fun p _ => (M p.1 p.2).pos
  let M_Z : Matrix V V ℤ := Matrix.of fun i j =>
    (M i j).num * ((d / (M i j).den : ℕ) : ℤ)
  have hMZ : ∀ i j, (d : ℚ) * M i j = (M_Z i j : ℚ) := by
    intro i j
    have hdvd : (M i j).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ (i, j))
    have hden_ne : ((M i j).den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (M i j).pos.ne'
    have hden_mul : ((d / (M i j).den : ℕ) : ℚ) * ((M i j).den : ℚ) = (d : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    calc
      (d : ℚ) * M i j
          = ((d / (M i j).den : ℕ) : ℚ) * ((M i j).den : ℚ) * M i j := by rw [hden_mul]
      _ = ((d / (M i j).den : ℕ) : ℚ) *
            (((M i j).den : ℚ) * ((M i j).num / ((M i j).den : ℚ))) := by
        rw [Rat.num_div_den]; ring
      _ = ((d / (M i j).den : ℕ) : ℚ) * ((M i j).num : ℚ) := by
        rw [mul_div_cancel₀ _ hden_ne]
      _ = (M_Z i j : ℚ) := by
        simp only [M_Z, of_apply, Int.cast_mul, Int.cast_natCast]
        ring
  let B : ℕ := Finset.univ.sup fun p : V × V => (M_Z p.1 p.2).natAbs
  have hB : ∀ i j, |M_Z i j| ≤ (B : ℤ) := fun i j => by
    rw [← Int.natCast_natAbs (M_Z i j)]
    exact Int.ofNat_le.2 (Finset.le_sup (f := fun p : V × V => (M_Z p.1 p.2).natAbs)
      (Finset.mem_univ (i, j)))
  exact ⟨d, B, M_Z, hd, hMZ, hB⟩

private theorem exists_nat_dotProduct_lt_zero_of_rat_real {V : Type*} [Fintype V] {d B : ℕ}
    {M : Matrix V V ℚ} {M_Z : Matrix V V ℤ}
    (hd : 0 < d) (hSymm : M.IsSymm) (hMZ : ∀ i j, (d : ℚ) * M i j = (M_Z i j : ℚ))
    (hB : ∀ i j, |M_Z i j| ≤ (B : ℤ)) (hnc : ¬ (M.map (Rat.cast : ℚ → ℝ)).IsCopositive) :
    ∃ p : V → ℕ,
      (∀ i, p i ≤
          Nat.factorial (Fintype.card V) * (Fintype.card V * (max B 1) ^ 2 + 1) ^ Fintype.card V) ∧
        (fun i => (p i : ℚ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℚ)) < 0 := by
  have hd_ne : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hSymmZ : M_Z.IsSymm := by
    ext i j
    apply Int.cast_injective (α := ℚ)
    rw [transpose_apply, ← hMZ j i, ← hMZ i j]
    exact congrArg (fun z : ℚ => (d : ℚ) * z) (congrFun (congrFun hSymm i) j)
  have hncZ : ¬ (M_Z.map (Int.cast : ℤ → ℝ)).IsCopositive := by
    intro hcopZ
    apply hnc
    intro x hx
    have hrealZ := hcopZ x hx
    have hscale : (d : ℝ) * (x ⬝ᵥ (M.map (Rat.cast : ℚ → ℝ) *ᵥ x)) =
        x ⬝ᵥ (M_Z.map (Int.cast : ℤ → ℝ) *ᵥ x) := by
      simp only [dotProduct, mulVec, map_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hcast := congrArg (Rat.cast : ℚ → ℝ) (hMZ i j)
      push_cast at hcast
      calc
        (d : ℝ) * (x i * ((M i j : ℝ) * x j)) = x i * (((d : ℝ) * (M i j : ℝ)) * x j) := by ring
        _ = x i * ((M_Z i j : ℝ) * x j) := by rw [hcast]
    rw [← hscale] at hrealZ
    exact (mul_nonneg_iff_of_pos_left (Nat.cast_pos.2 hd)).1 hrealZ
  obtain ⟨p, hp_le, hp_negZ⟩ := exists_nat_dotProduct_lt_zero_of_isSymm hSymmZ hB hncZ
  refine ⟨p, hp_le, ?_⟩
  have hscaleQ : (d : ℚ) * ((fun i => (p i : ℚ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℚ))) =
      (Int.cast ((fun i => (p i : ℤ)) ⬝ᵥ (M_Z *ᵥ fun i => (p i : ℤ))) : ℚ) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij := hMZ i j
    calc
      (d : ℚ) * ((p i : ℚ) * (M i j * (p j : ℚ))) =
          (p i : ℚ) * (((d : ℚ) * M i j) * (p j : ℚ)) := by ring
      _ = (p i : ℚ) * ((M_Z i j : ℚ) * (p j : ℚ)) := by rw [hij]
  have hnegQ : (Int.cast ((fun i => (p i : ℤ)) ⬝ᵥ (M_Z *ᵥ fun i => (p i : ℤ))) : ℚ) < 0 :=
    Int.cast_lt_zero.2 hp_negZ
  rw [← hscaleQ] at hnegQ
  exact lt_of_not_ge fun h => not_lt_of_ge (mul_nonneg (Nat.cast_nonneg d) h) hnegQ

/-- Given a symmetric rational matrix `M` and an integer scaling `(d : ℚ) * M = M_Z` with `0 < d`
and `|M_Z i j| ≤ B`, non-copositivity of `M` yields a nonnegative integer certificate `p` with
`p ⬝ᵥ M *ᵥ p < 0` and entries bounded by
`Nat.factorial (Fintype.card V) * (Fintype.card V * (max B 1) ^ 2 + 1) ^ Fintype.card V`
(library proof and bound, not verified against [MurtyKabadi1987]). -/
theorem exists_nat_dotProduct_lt_zero_of_rat {V : Type*} [Fintype V] {d B : ℕ}
    {M : Matrix V V ℚ} {M_Z : Matrix V V ℤ}
    (hd : 0 < d) (hSymm : M.IsSymm) (hMZ : ∀ i j, (d : ℚ) * M i j = (M_Z i j : ℚ))
    (hB : ∀ i j, |M_Z i j| ≤ (B : ℤ)) (hnc : ¬ M.IsCopositive) :
    ∃ p : V → ℕ,
      (∀ i, p i ≤
          Nat.factorial (Fintype.card V) * (Fintype.card V * (max B 1) ^ 2 + 1) ^ Fintype.card V) ∧
        (fun i => (p i : ℚ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℚ)) < 0 :=
  exists_nat_dotProduct_lt_zero_of_rat_real hd hSymm hMZ hB fun hreal =>
    hnc (isCopositive_of_map_real hreal)

/-- For a symmetric rational matrix, copositivity over `ℚ` and over `ℝ` coincide. -/
theorem isCopositive_rat_iff_map_real {V : Type*} [Fintype V] {M : Matrix V V ℚ}
    (hSymm : M.IsSymm) :
    M.IsCopositive ↔ (M.map (Rat.cast : ℚ → ℝ)).IsCopositive := by
  constructor
  · intro hcop
    by_contra hncR
    obtain ⟨d, B, M_Z, hd, hMZ, hB⟩ := exists_rat_clearDenom M
    obtain ⟨p, _, hp_neg⟩ := exists_nat_dotProduct_lt_zero_of_rat_real hd hSymm hMZ hB hncR
    exact (not_lt_of_ge (hcop (fun i => (p i : ℚ)) fun i => Nat.cast_nonneg (p i))) hp_neg
  · exact isCopositive_of_map_real

/-- For a symmetric rational matrix, copositivity over `ℚ` coincides with nonnegativity on all
nonnegative integer vectors. -/
theorem isCopositive_rat_iff_nat {V : Type*} [Fintype V] {M : Matrix V V ℚ} (hSymm : M.IsSymm) :
    M.IsCopositive ↔ ∀ p : V → ℕ, 0 ≤ (fun i => (p i : ℚ)) ⬝ᵥ (M *ᵥ fun i => (p i : ℚ)) := by
  constructor
  · intro hcop p
    exact hcop (fun i => (p i : ℚ)) fun i => Nat.cast_nonneg (p i)
  · intro hnat
    by_contra hnc
    obtain ⟨d, B, M_Z, hd, hMZ, hB⟩ := exists_rat_clearDenom M
    obtain ⟨p, _, hp_neg⟩ := exists_nat_dotProduct_lt_zero_of_rat hd hSymm hMZ hB hnc
    exact (not_lt_of_ge (hnat p)) hp_neg

end Matrix
