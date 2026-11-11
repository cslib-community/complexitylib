/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.AffineSource
import CslibFrontier.Foundations.Data.BitString.AffineSubspace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Linear affine somewhere condensers from dimension expanders

This module formalizes the linear affine somewhere condenser construction from Section 3 of
[Li and Zhong, CCC 2024][LiZhong2024]:

* `Cslib.AffineDisperser.Li.IsAffineSomewhereCondenser`: a `(δ, γ)` affine somewhere condenser
  mapping every affine source of rate `≥ δ` to a tuple of outputs at least one of which is an
  affine source of rate `≥ γ` (`[LiZhong2024, Def. 21]`).
* `Cslib.AffineDisperser.Li.IsDimensionExpander`: an `α`-dimension expander of degree `d` over
  `𝔽₂` (`[LiZhong2024, Def. 22]`).
* `Cslib.AffineDisperser.Li.basicCond`: the single-step halving condenser (`[LiZhong2024, Alg. 1]`)
  sending `(x₁, x₂)` to `(x₁, x₂, x₁ + T₁ x₂, x₂ + T₁ x₁, …, x₁ + T_d x₂, x₂ + T_d x₁)`.
* `Cslib.AffineDisperser.Li.sCond`: the iterated linear somewhere condenser
  (`[LiZhong2024, Alg. 2]`).

## Main results

* `Cslib.AffineDisperser.Li.isAffineSomewhereCondenser_basicCond`: **Rate-boosting lemma**
  (`[LiZhong2024, Lemma 20]`), proving `basicCond T` is a `(δ, (1 + α / (4 * d)) * δ)` affine
  somewhere condenser for any `0 < δ ≤ 1 / 2`, `3 ≤ d`, `0 < α ≤ 1`.
* `Cslib.AffineDisperser.Li.isAffineSomewhereCondenser_sCond`: **Iterated linear condenser**
  (`[LiZhong2024, Thm. 18]`), amplifying any affine entropy rate `0 < δ ≤ 1 / 2` to rate
  `1 / 2 + α / (8 * d)` in `h + 1` halving rounds when `1 / 2 ≤ δ * (1 + α / (4 * d)) ^ h`.

## References

* [X. Li and Y. Zhong, *Explicit Directional Affine Extractors and Improved Hardness for Linear
  Branching Programs*][LiZhong2024], Section 3 (Definitions 21–22, Lemma 20, Theorem 18)
-/

public section

namespace Cslib.AffineDisperser.Li

open Cslib.BitString Module

/-! ### Definitions -/

/-- A **`(δ, γ)` affine somewhere condenser**: for every `(n, k)` affine source `X` with
`k ≥ δ * n`, some output coordinate `f · i` distributes as an affine source of dimension
`k' ≥ γ * m` ([LiZhong2024, Def. 21]). -/
@[expose] def IsAffineSomewhereCondenser {n m ℓ : ℕ}
    (f : BitString n → Fin ℓ → BitString m) (δ γ : ℝ) : Prop :=
  ∀ (X : PMF (BitString n)) (k : ℕ), IsAffineSource X k → δ * n ≤ k →
    ∃ (i : Fin ℓ) (k' : ℕ), IsAffineSource (X.map fun x => f x i) k' ∧ γ * m ≤ k'

/-- An **`α`-dimension expander** of degree `d` over `𝔽₂`: a family of `d` linear maps
`T : Fin d → BitString n →ₗ[Bool] BitString n` expanding every subspace of dimension at most `n / 2`
by a factor `(1 + α)` ([LiZhong2024, Def. 22]). -/
@[expose] def IsDimensionExpander {n d : ℕ}
    (T : Fin d → BitString n →ₗ[Bool] BitString n) (α : ℝ) : Prop :=
  ∀ V : Submodule Bool (BitString n), 2 * finrank Bool V ≤ n →
    (1 + α) * (finrank Bool V : ℝ) ≤ (finrank Bool ↥(⨆ i : Fin d, V.map (T i)) : ℝ)

/-! ### Bit-splitting equivalences and basic condenser -/

/-- Split a bit string of length `m + m` into its first and second halves as a `Bool`-linear
equivalence. -/
@[expose] def splitHalfEquiv (m : ℕ) :
    BitString (m + m) ≃ₗ[Bool] BitString m × BitString m where
  toFun x := (fun i => x ⟨i.1, by omega⟩, fun i => x ⟨m + i.1, by omega⟩)
  invFun p j := if h : j.1 < m then p.1 ⟨j.1, h⟩ else p.2 ⟨j.1 - m, by omega⟩
  left_inv x := by
    funext j
    dsimp only
    split_ifs with h
    · rfl
    · congr 1
      exact Fin.ext (by dsimp only; omega)
  right_inv p := by
    ext i <;> dsimp only
    · rw [dite_eq_left i.2]
    · rw [dite_eq_right (by omega)]
      exact congrArg p.2 (Fin.ext (by dsimp only; omega))
  map_add' x y := by
    ext i <;> rfl
  map_smul' c x := by
    ext i <;> rfl

/-- Linear equivalence of bit strings of equal lengths. -/
@[expose] def bitStringCongr {n₁ n₂ : ℕ} (h : n₁ = n₂) : BitString n₁ ≃ₗ[Bool] BitString n₂ where
  toFun x i := x (Fin.cast h.symm i)
  invFun y j := y (Fin.cast h j)
  left_inv x := by funext j; simp
  right_inv y := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def projLeft (m : ℕ) : BitString (m + m) →ₗ[Bool] BitString m where
  toFun x := (splitHalfEquiv m x).1
  map_add' x y := by rw [map_add]; rfl
  map_smul' c x := by rw [map_smul]; rfl

private def projRight (m : ℕ) : BitString (m + m) →ₗ[Bool] BitString m where
  toFun x := (splitHalfEquiv m x).2
  map_add' x y := by rw [map_add]; rfl
  map_smul' c x := by rw [map_smul]; rfl

/-- **Single-step basic affine somewhere condenser** (`BasicCond`, [LiZhong2024, Alg. 1]):
splits `x ∈ BitString (m + m)` into `(x₁, x₂)` and outputs the `2 * d + 2` linear projections
`(x₁, x₂, x₁ + T₀ x₂, x₂ + T₀ x₁, …)`. -/
@[expose] def basicCond {m d : ℕ} (T : Fin d → BitString m →ₗ[Bool] BitString m) :
    BitString (m + m) →ₗ[Bool] (Fin (2 * d + 2) → BitString m) where
  toFun x idx :=
    let p := splitHalfEquiv m x
    if h0 : idx.1 = 0 then p.1
    else if h1 : idx.1 = 1 then p.2
    else
      if (idx.1 - 2) % 2 = 0 then p.1 + T ⟨(idx.1 - 2) / 2, by have := idx.2; omega⟩ p.2
      else p.2 + T ⟨(idx.1 - 2) / 2, by have := idx.2; omega⟩ p.1
  map_add' x y := by
    funext idx
    have hxy : splitHalfEquiv m (x + y) =
        ((splitHalfEquiv m x).1 + (splitHalfEquiv m y).1,
         (splitHalfEquiv m x).2 + (splitHalfEquiv m y).2) := by
      rw [map_add]; rfl
    dsimp only
    rw [hxy]
    by_cases h0 : idx.1 = 0
    · simp only [h0, ↓reduceDIte, Pi.add_apply]
    · by_cases h1 : idx.1 = 1
      · simp only [h1, one_ne_zero, ↓reduceDIte, Pi.add_apply]
      · simp only [h0, h1, ↓reduceDIte, Pi.add_apply]
        split_ifs <;> simp only [map_add] <;> abel
  map_smul' c x := by
    funext idx
    have hsmul : splitHalfEquiv m (c • x) =
        (c • (splitHalfEquiv m x).1, c • (splitHalfEquiv m x).2) := by
      rw [map_smul]; rfl
    dsimp only
    rw [hsmul]
    by_cases h0 : idx.1 = 0
    · simp only [h0, ↓reduceDIte, RingHom.id_apply, Pi.smul_apply]
    · by_cases h1 : idx.1 = 1
      · simp only [h1, one_ne_zero, ↓reduceDIte, RingHom.id_apply, Pi.smul_apply]
      · simp only [h0, h1, ↓reduceDIte, RingHom.id_apply, Pi.smul_apply]
        split_ifs <;> simp only [map_smul, smul_add]

private theorem basicCond_zero {m d : ℕ} (T : Fin d → BitString m →ₗ[Bool] BitString m)
    (x : BitString (m + m)) :
    basicCond T x 0 = projLeft m x := by
  simp [basicCond, projLeft]

private theorem basicCond_one {m d : ℕ} (T : Fin d → BitString m →ₗ[Bool] BitString m)
    (x : BitString (m + m)) :
    basicCond T x ⟨1, by omega⟩ = projRight m x := by
  simp [basicCond, projRight]

private theorem basicCond_even {m d : ℕ} (T : Fin d → BitString m →ₗ[Bool] BitString m)
    (x : BitString (m + m)) (i : Fin d) :
    basicCond T x ⟨2 + 2 * i.1, by omega⟩ = projLeft m x + T i (projRight m x) := by
  change (if h0 : (2 + 2 * i.1) = 0 then (splitHalfEquiv m x).1
    else if h1 : (2 + 2 * i.1) = 1 then (splitHalfEquiv m x).2
    else if ((2 + 2 * i.1) - 2) % 2 = 0 then
      (splitHalfEquiv m x).1 +
        T ⟨((2 + 2 * i.1) - 2) / 2, by have := i.2; omega⟩ (splitHalfEquiv m x).2
    else
      (splitHalfEquiv m x).2 +
        T ⟨((2 + 2 * i.1) - 2) / 2, by have := i.2; omega⟩ (splitHalfEquiv m x).1) =
    projLeft m x + T i (projRight m x)
  rw [dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_left (by omega)]
  exact congrArg (fun k => projLeft m x + T k (projRight m x)) (Fin.ext (by dsimp only; omega))

private theorem basicCond_odd {m d : ℕ} (T : Fin d → BitString m →ₗ[Bool] BitString m)
    (x : BitString (m + m)) (i : Fin d) :
    basicCond T x ⟨2 + 2 * i.1 + 1, by omega⟩ = projRight m x + T i (projLeft m x) := by
  change (if h0 : (2 + 2 * i.1 + 1) = 0 then (splitHalfEquiv m x).1
    else if h1 : (2 + 2 * i.1 + 1) = 1 then (splitHalfEquiv m x).2
    else if ((2 + 2 * i.1 + 1) - 2) % 2 = 0 then
      (splitHalfEquiv m x).1 +
        T ⟨((2 + 2 * i.1 + 1) - 2) / 2, by have := i.2; omega⟩ (splitHalfEquiv m x).2
    else
      (splitHalfEquiv m x).2 +
        T ⟨((2 + 2 * i.1 + 1) - 2) / 2, by have := i.2; omega⟩ (splitHalfEquiv m x).1) =
    projRight m x + T i (projLeft m x)
  rw [dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega)]
  exact congrArg (fun k => projRight m x + T k (projLeft m x)) (Fin.ext (by dsimp only; omega))

private def basicCondAt {m d : ℕ} (T : Fin d → BitString m →ₗ[Bool] BitString m)
    (idx : Fin (2 * d + 2)) : BitString (m + m) →ₗ[Bool] BitString m :=
  (LinearMap.proj idx).comp (basicCond T)

private theorem isAffine_of_linearMap {n m : ℕ} (L : BitString n →ₗ[Bool] BitString m) :
    IsAffine L := fun x y z => by
  simp only [map_add]

private theorem toAffineMap_linear_of_isAffine_linearMap {n m : ℕ}
    (L : BitString n →ₗ[Bool] BitString m) :
    (isAffine_of_linearMap L).toAffineMap.linear = L :=
  LinearMap.ext fun x => by
    simpa [vsub_eq_sub, sub_zero, map_zero, IsAffine.coe_toAffineMap] using
      (isAffine_of_linearMap L).toAffineMap.linear_apply_vsub x 0

/-! ### Subspace dimension lemmas for `basicCond` -/

/-- Sum-of-excess dimension inequality over a `Finset` of `Bool`-submodules:
`finrank (B ⊔ ⨆ i ∈ s, S i) ≤ finrank B + ∑ i ∈ s, (finrank (B ⊔ S i) - finrank B)`. -/
private theorem finrank_sup_biSup_le {m : ℕ} (B : Submodule Bool (BitString m))
    {d : ℕ} (S : Fin d → Submodule Bool (BitString m)) (s : Finset (Fin d)) :
    finrank Bool ↥(B ⊔ ⨆ i ∈ s, S i) ≤
      finrank Bool B + ∑ i ∈ s, (finrank Bool ↥(B ⊔ S i) - finrank Bool B) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hem : (⨆ i ∈ (∅ : Finset (Fin d)), S i) = ⊥ :=
      eq_bot_iff.mpr (iSup₂_le fun i hi => absurd hi (Finset.notMem_empty i))
    rw [hem, sup_bot_eq, Finset.sum_empty, add_zero]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.iSup_insert]
    have hUW_eq : B ⊔ (S j ⊔ ⨆ i ∈ s, S i) = (B ⊔ ⨆ i ∈ s, S i) ⊔ (B ⊔ S j) := by
      apply le_antisymm
      · refine sup_le (le_sup_of_le_left le_sup_left)
          (sup_le (le_sup_of_le_right le_sup_right) (le_sup_of_le_left le_sup_right))
      · refine sup_le (sup_le le_sup_left (le_sup_of_le_right le_sup_right))
          (sup_le le_sup_left (le_sup_of_le_right le_sup_left))
    have hB_le : B ≤ (B ⊔ ⨆ i ∈ s, S i) ⊓ (B ⊔ S j) := le_inf le_sup_left le_sup_left
    have hinf_le : finrank Bool B ≤ finrank Bool ↥((B ⊔ ⨆ i ∈ s, S i) ⊓ (B ⊔ S j)) :=
      Submodule.finrank_mono hB_le
    have hsup := finrank_sup_add_finrank_inf_bitString (B ⊔ ⨆ i ∈ s, S i) (B ⊔ S j)
    have hB_W : finrank Bool B ≤ finrank Bool ↥(B ⊔ S j) := Submodule.finrank_mono le_sup_left
    have hle1 : finrank Bool ↥(B ⊔ (S j ⊔ ⨆ i ∈ s, S i)) + finrank Bool B ≤
        finrank Bool ↥(B ⊔ ⨆ i ∈ s, S i) + finrank Bool ↥(B ⊔ S j) := by
      rw [hUW_eq]
      exact Nat.add_le_add_left hinf_le _ |>.trans hsup.le
    omega

/-- Pigeonhole over `[d]`: `finrank (⨆ j, S j) ≤ finrank B + d * (finrank (B ⊔ S i) - finrank B)`
for some `i : Fin d`. -/
private theorem exists_finrank_sup_ge_of_finrank_iSup {m d : ℕ} (hd : 0 < d)
    (B : Submodule Bool (BitString m)) (S : Fin d → Submodule Bool (BitString m)) :
    ∃ i : Fin d, finrank Bool ↥(⨆ j : Fin d, S j) ≤
      finrank Bool B + d * (finrank Bool ↥(B ⊔ S i) - finrank Bool B) := by
  have hle_B : finrank Bool ↥(⨆ j : Fin d, S j) ≤ finrank Bool ↥(B ⊔ ⨆ j : Fin d, S j) :=
    Submodule.finrank_mono le_sup_right
  have hiSup : (⨆ j : Fin d, S j) = ⨆ j ∈ (Finset.univ : Finset (Fin d)), S j := by
    simp
  have hsum := finrank_sup_biSup_le B S Finset.univ
  rw [← hiSup] at hsum
  by_contra hno
  push Not at hno
  have hsum_strict : ∑ i ∈ (Finset.univ : Finset (Fin d)),
      (finrank Bool ↥(B ⊔ S i) - finrank Bool B) * d <
      ∑ _i ∈ (Finset.univ : Finset (Fin d)),
        (finrank Bool ↥(⨆ j : Fin d, S j) - finrank Bool B) := by
    refine Finset.sum_lt_sum_of_nonempty ⟨⟨0, hd⟩, Finset.mem_univ _⟩ fun i _ => ?_
    have hi := hno i
    rw [mul_comm]
    omega
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul] at hsum_strict
  have hsum_le : d * ∑ i : Fin d, (finrank Bool ↥(B ⊔ S i) - finrank Bool B) <
      d * (finrank Bool ↥(⨆ j : Fin d, S j) - finrank Bool B) := by
    rw [mul_comm d]
    exact hsum_strict
  have hlt := Nat.lt_of_mul_lt_mul_left hsum_le
  omega

/-- Algebraic core of [LiZhong2024, Lemma 20]: from `(1 + α) * x ≤ y + d * (M + t - y)` with
`x + y = k`, `2 * x ≤ k`, `t ≤ α / (4 * d) * k`, `d ≥ 3`, and `0 < α ≤ 1`, deduce
`(1 / 2 + α / (8 * d)) * k ≤ M`. -/
private theorem basicCond_rate_algebra {d : ℕ} (hd : 3 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {k x y M t : ℝ} (hk0 : 0 ≤ k) (hx_half : 2 * x ≤ k) (hxy : x + y = k)
    (ht : t ≤ α / (4 * (d : ℝ)) * k)
    (hexp : (1 + α) * x ≤ y + (d : ℝ) * (M + t - y)) :
    (1 / 2 + α / (8 * (d : ℝ))) * k ≤ M := by
  have hd_real : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd_pos : (0 : ℝ) < d := by linarith
  set eps := α / (8 * (d : ℝ))
  have heps_pos : 0 < eps := by positivity
  have h1 : (d : ℝ) * (M + t) ≥ (1 + α) * x + ((d : ℝ) - 1) * y := by linarith
  have h2 : (1 + α) * x + ((d : ℝ) - 1) * y = ((d : ℝ) - 1) * k + (2 + α - (d : ℝ)) * x := by
    rw [← hxy]; ring
  have hneg : 2 + α - (d : ℝ) ≤ 0 := by linarith
  have h3 : (2 + α - (d : ℝ)) * (k / 2) ≤ (2 + α - (d : ℝ)) * x := by nlinarith
  have h4 : ((d : ℝ) / 2 + α / 2) * k = ((d : ℝ) - 1) * k + (2 + α - (d : ℝ)) * (k / 2) := by
    ring
  have h5 : ((d : ℝ) / 2 + α / 2) * k ≤ (d : ℝ) * (M + t) := by linarith
  have h6 : (1 / 2 + 4 * eps) * k ≤ M + t := by
    have hmul : (d : ℝ) * ((1 / 2 + 4 * eps) * k) = ((d : ℝ) / 2 + α / 2) * k := by
      dsimp [eps]; field_simp; ring
    exact (mul_le_mul_iff_left₀ hd_pos).mp (by linarith)
  have hhalf_4 : (1 / 2 + 4 * eps) * k = k / 2 + 4 * (eps * k) := by ring
  have hhalf_1 : (1 / 2 + eps) * k = k / 2 + eps * k := by ring
  have ht'' : t ≤ 2 * (eps * k) := by
    calc t ≤ α / (4 * (d : ℝ)) * k := ht
      _ = 2 * (eps * k) := by dsimp [eps]; ring
  have h0 : 0 ≤ eps * k := mul_nonneg heps_pos.le hk0
  linarith

/-- Shared arithmetic finale for `basicCond_subspace_boost_case1` and `_case2`. -/
private theorem basicCond_subspace_boost_step {m d k : ℕ} (hd : 3 ≤ d) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) {T : Fin d → BitString m →ₗ[Bool] BitString m}
    (A₀ B₀ M C : Submodule Bool (BitString m))
    (hA_half : 2 * finrank Bool A₀ ≤ k) (hsum : finrank Bool A₀ + finrank Bool B₀ = k)
    (ht_lt : (finrank Bool C : ℝ) ≤ α / (4 * (d : ℝ)) * (k : ℝ))
    (hexpand : (1 + α) * (finrank Bool A₀ : ℝ) ≤ (finrank Bool ↥(⨆ j : Fin d, A₀.map (T j)) : ℝ))
    (hi_pig : finrank Bool ↥(⨆ j : Fin d, A₀.map (T j)) ≤
      finrank Bool B₀ + d * (finrank Bool M + finrank Bool C - finrank Bool B₀))
    (hB_le : finrank Bool B₀ ≤ finrank Bool M + finrank Bool C) :
    (1 / 2 + α / (8 * (d : ℝ))) * (k : ℝ) ≤ (finrank Bool M : ℝ) := by
  set s := finrank Bool A₀
  set r := finrank Bool B₀
  set t := finrank Bool C
  have hnat : finrank Bool ↥(⨆ j : Fin d, A₀.map (T j)) ≤ r + d * (finrank Bool M + t - r) :=
    hi_pig
  have hchain_real :
      (1 + α) * (s : ℝ) ≤ (r : ℝ) + (d : ℝ) * ((finrank Bool M : ℝ) + (t : ℝ) - (r : ℝ)) := by
    have hcast : ((r + d * (finrank Bool M + t - r) : ℕ) : ℝ) =
        (r : ℝ) + (d : ℝ) * ((finrank Bool M : ℝ) + (t : ℝ) - (r : ℝ)) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hB_le, Nat.cast_add]
    have hnat_r : (finrank Bool ↥(⨆ j : Fin d, A₀.map (T j)) : ℝ) ≤
        ((r + d * (finrank Bool M + t - r) : ℕ) : ℝ) := by exact_mod_cast hnat
    exact hexpand.trans (hnat_r.trans_eq hcast)
  exact basicCond_rate_algebra hd hα0 hα1 (Nat.cast_nonneg k)
    (by exact_mod_cast hA_half) (by exact_mod_cast hsum) ht_lt hchain_real

/-- Case 1 of `basicCond_subspace_boost` (`2 * s ≤ k`). -/
private theorem basicCond_subspace_boost_case1 {m d : ℕ} (hd : 3 ≤ d) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    {T : Fin d → BitString m →ₗ[Bool] BitString m} (hT : IsDimensionExpander T α)
    (V : Submodule Bool (BitString (m + m))) (B C : Submodule Bool (BitString m))
    (hB_eq : B = (V ⊓ LinearMap.ker (projLeft m)).map (projRight m))
    (hP2_eq : V.map (projRight m) = B ⊔ C)
    (hm_bound : 2 * finrank Bool ↥(V.map (projLeft m)) ≤ m)
    (hsr : finrank Bool ↥(V.map (projLeft m)) + finrank Bool B = finrank Bool V)
    (hs_half : 2 * finrank Bool ↥(V.map (projLeft m)) ≤ finrank Bool V)
    (ht_lt : (finrank Bool C : ℝ) ≤ α / (4 * (d : ℝ)) * (finrank Bool V : ℝ)) :
    ∃ idx : Fin (2 * d + 2),
      (1 / 2 + α / (8 * (d : ℝ))) * (finrank Bool V : ℝ) ≤
        (finrank Bool ↥(V.map (basicCondAt T idx)) : ℝ) := by
  let A' : Submodule Bool (BitString m) := V.map (projLeft m)
  set s := finrank Bool A'
  set r := finrank Bool B
  set t := finrank Bool C
  set k := finrank Bool V
  have hexpand := hT A' hm_bound
  obtain ⟨i, hi_pig⟩ := exists_finrank_sup_ge_of_finrank_iSup (by omega : 0 < d) B
    (fun j => A'.map (T j))
  let idx : Fin (2 * d + 2) := ⟨2 + 2 * i.1 + 1, by omega⟩
  let M : Submodule Bool (BitString m) := V.map (basicCondAt T idx)
  have hB_le_M : B ≤ M := by
    rw [hB_eq]
    rintro y ⟨w, ⟨hwV, hwker⟩, rfl⟩
    refine Submodule.mem_map.mpr ⟨w, hwV, ?_⟩
    change basicCond T w idx = projRight m w
    rw [basicCond_odd, LinearMap.mem_ker.mp hwker, map_zero, add_zero]
  have hsup_le : B ⊔ A'.map (T i) ≤ M ⊔ C := by
    refine sup_le (hB_le_M.trans le_sup_left) ?_
    rintro z ⟨a', ⟨v, hvV, rfl⟩, rfl⟩
    have hv_M : projRight m v + T i (projLeft m v) ∈ M :=
      Submodule.mem_map.mpr ⟨v, hvV, by change basicCond T v idx = _; exact basicCond_odd T v i⟩
    have hv_P2 : projRight m v ∈ B ⊔ C := by
      rw [← hP2_eq]
      exact Submodule.mem_map.mpr ⟨v, hvV, rfl⟩
    have hv_MC : projRight m v ∈ M ⊔ C :=
      (sup_le (hB_le_M.trans le_sup_left) le_sup_right) hv_P2
    have hadd := (M ⊔ C).add_mem ((le_sup_left : M ≤ M ⊔ C) hv_M) hv_MC
    have heq : (projRight m v + T i (projLeft m v)) + projRight m v = T i (projLeft m v) := by
      have hself : projRight m v + projRight m v = 0 := BitString.add_self _
      calc (projRight m v + T i (projLeft m v)) + projRight m v
          = (projRight m v + projRight m v) + T i (projLeft m v) := by abel
        _ = T i (projLeft m v) := by rw [hself, zero_add]
    rwa [heq] at hadd
  have hfin_sup : finrank Bool ↥(B ⊔ A'.map (T i)) ≤ finrank Bool M + t := by
    have h1 : finrank Bool ↥(B ⊔ A'.map (T i)) ≤ finrank Bool ↥(M ⊔ C) :=
      Submodule.finrank_mono hsup_le
    have h2 := finrank_sup_add_finrank_inf_bitString M C
    have h3 : finrank Bool ↥(M ⊔ C) ≤ finrank Bool M + t := by
      change finrank Bool ↥(M ⊔ C) + finrank Bool ↥(M ⊓ C) = finrank Bool M + t at h2
      omega
    exact h1.trans h3
  have hB_le_sup : r ≤ finrank Bool ↥(B ⊔ A'.map (T i)) := Submodule.finrank_mono le_sup_left
  refine ⟨idx, basicCond_subspace_boost_step hd hα0 hα1 A' B M C hs_half hsr ht_lt hexpand
    (hi_pig.trans (Nat.add_le_add_left (Nat.mul_le_mul_left d (by omega)) r))
    (hB_le_sup.trans hfin_sup)⟩

/-- Case 2 of `basicCond_subspace_boost` (`2 * r ≤ k`). -/
private theorem basicCond_subspace_boost_case2 {m d : ℕ} (hd : 3 ≤ d) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    {T : Fin d → BitString m →ₗ[Bool] BitString m} (hT : IsDimensionExpander T α)
    (V : Submodule Bool (BitString (m + m))) (B C : Submodule Bool (BitString m))
    (hB_eq : B = (V ⊓ LinearMap.ker (projLeft m)).map (projRight m))
    (hP2_eq : V.map (projRight m) = B ⊔ C)
    (hm_bound : 2 * finrank Bool B ≤ m)
    (hsr : finrank Bool ↥(V.map (projLeft m)) + finrank Bool B = finrank Bool V)
    (hr_half : 2 * finrank Bool B ≤ finrank Bool V)
    (ht_lt : (finrank Bool C : ℝ) ≤ α / (4 * (d : ℝ)) * (finrank Bool V : ℝ)) :
    ∃ idx : Fin (2 * d + 2),
      (1 / 2 + α / (8 * (d : ℝ))) * (finrank Bool V : ℝ) ≤
        (finrank Bool ↥(V.map (basicCondAt T idx)) : ℝ) := by
  let A' : Submodule Bool (BitString m) := V.map (projLeft m)
  set s := finrank Bool A'
  set r := finrank Bool B
  set t := finrank Bool C
  set k := finrank Bool V
  have hexpand := hT B hm_bound
  obtain ⟨i, hi_pig⟩ := exists_finrank_sup_ge_of_finrank_iSup (by omega : 0 < d) A'
    (fun j => B.map (T j))
  let idx : Fin (2 * d + 2) := ⟨2 + 2 * i.1, by omega⟩
  let M : Submodule Bool (BitString m) := V.map (basicCondAt T idx)
  have hTB_le_M : B.map (T i) ≤ M := by
    rw [hB_eq]
    rintro y ⟨_, ⟨w, ⟨hwV, hwker⟩, rfl⟩, rfl⟩
    refine Submodule.mem_map.mpr ⟨w, hwV, ?_⟩
    change basicCond T w idx = T i (projRight m w)
    rw [basicCond_even, LinearMap.mem_ker.mp hwker, zero_add]
  have hsup_le : A' ⊔ B.map (T i) ≤ M ⊔ C.map (T i) := by
    refine sup_le ?_ (hTB_le_M.trans le_sup_left)
    rintro z ⟨v, hvV, rfl⟩
    have hv_M : projLeft m v + T i (projRight m v) ∈ M :=
      Submodule.mem_map.mpr ⟨v, hvV, by change basicCond T v idx = _; exact basicCond_even T v i⟩
    have hv_P2 : projRight m v ∈ B ⊔ C := by
      rw [← hP2_eq]
      exact Submodule.mem_map.mpr ⟨v, hvV, rfl⟩
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp hv_P2
    have hTib : T i b ∈ M ⊔ C.map (T i) :=
      (le_sup_left : M ≤ M ⊔ C.map (T i)) (hTB_le_M (Submodule.mem_map.mpr ⟨b, hb, rfl⟩))
    have hTic : T i c ∈ M ⊔ C.map (T i) :=
      (le_sup_right : C.map (T i) ≤ M ⊔ C.map (T i)) (Submodule.mem_map.mpr ⟨c, hc, rfl⟩)
    have hTip2 : T i (projRight m v) ∈ M ⊔ C.map (T i) := by
      rw [← hbc, map_add]
      exact (M ⊔ C.map (T i)).add_mem hTib hTic
    have hadd := (M ⊔ C.map (T i)).add_mem ((le_sup_left : M ≤ M ⊔ C.map (T i)) hv_M) hTip2
    have heq : (projLeft m v + T i (projRight m v)) + T i (projRight m v) = projLeft m v := by
      have hself : T i (projRight m v) + T i (projRight m v) = 0 := BitString.add_self _
      rw [add_assoc, hself, add_zero]
    rwa [heq] at hadd
  have hCt_le : finrank Bool ↥(C.map (T i)) ≤ t := by
    have hrank := finrank_range_add_finrank_ker_bitString (T i) C
    change finrank Bool ↥(C.map (T i)) + _ = t at hrank
    omega
  have hfin_sup : finrank Bool ↥(A' ⊔ B.map (T i)) ≤ finrank Bool M + t := by
    have h1 : finrank Bool ↥(A' ⊔ B.map (T i)) ≤ finrank Bool ↥(M ⊔ C.map (T i)) :=
      Submodule.finrank_mono hsup_le
    have h2 := finrank_sup_add_finrank_inf_bitString M (C.map (T i))
    have h3 : finrank Bool ↥(M ⊔ C.map (T i)) ≤ finrank Bool M + finrank Bool ↥(C.map (T i)) := by
      calc finrank Bool ↥(M ⊔ C.map (T i))
          ≤ finrank Bool ↥(M ⊔ C.map (T i)) + finrank Bool ↥(M ⊓ C.map (T i)) :=
            Nat.le_add_right _ _
        _ = finrank Bool M + finrank Bool ↥(C.map (T i)) := h2
    exact h1.trans (h3.trans (Nat.add_le_add_left hCt_le _))
  have hA_le_sup : s ≤ finrank Bool ↥(A' ⊔ B.map (T i)) := Submodule.finrank_mono le_sup_left
  refine ⟨idx, basicCond_subspace_boost_step hd hα0 hα1 B A' M C hr_half (by omega) ht_lt hexpand
    (hi_pig.trans (Nat.add_le_add_left (Nat.mul_le_mul_left d (by omega)) s))
    (hA_le_sup.trans hfin_sup)⟩

/-- Key subspace dimension boost of `basicCond` for a subspace `V` of `BitString (m + m)` of
dimension `k ≤ m` with `δ * (2 * m) ≤ k` and `0 < m`. -/
private theorem basicCond_subspace_boost {m d : ℕ} (hm : 0 < m) (hd : 3 ≤ d) {α δ : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 < δ) (_hδhalf : δ ≤ 1 / 2)
    {T : Fin d → BitString m →ₗ[Bool] BitString m} (hT : IsDimensionExpander T α)
    (V : Submodule Bool (BitString (m + m)))
    (hk_le : finrank Bool V ≤ m) (hk_ge : δ * ((m + m : ℕ) : ℝ) ≤ finrank Bool V) :
    ∃ idx : Fin (2 * d + 2),
      (1 + α / (4 * (d : ℝ))) * δ * (m : ℝ) ≤ (finrank Bool ↥(V.map (basicCondAt T idx)) : ℝ) := by
  set k := finrank Bool V
  let W : Submodule Bool (BitString (m + m)) := V ⊓ LinearMap.ker (projLeft m)
  let A' : Submodule Bool (BitString m) := V.map (projLeft m)
  let B : Submodule Bool (BitString m) := W.map (projRight m)
  let P2 : Submodule Bool (BitString m) := V.map (projRight m)
  set s := finrank Bool A'
  set r := finrank Bool B
  have hB_le_P2 : B ≤ P2 := Submodule.map_mono inf_le_left
  have hdim_W : finrank Bool W = r := by
    have hkerW : W ⊓ LinearMap.ker (projRight m) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨⟨_, hx1⟩, hx2⟩
      have hx1' : projLeft m x = 0 := LinearMap.mem_ker.mp hx1
      have hx2' : projRight m x = 0 := LinearMap.mem_ker.mp hx2
      apply (splitHalfEquiv m).injective
      rw [map_zero]
      ext i <;> [exact congrFun hx1' i; exact congrFun hx2' i]
    have hrank := finrank_range_add_finrank_ker_bitString (projRight m) W
    rw [hkerW, finrank_bot, add_zero] at hrank
    exact hrank.symm
  have hsr : s + r = k := by
    have hrank := finrank_range_add_finrank_ker_bitString (projLeft m) V
    change s + finrank Bool W = k at hrank
    rwa [hdim_W] at hrank
  obtain ⟨C, hC_le, hC_inf, hC_sup⟩ := exists_isCompl_submodule B P2 hB_le_P2
  set t := finrank Bool C
  have hP2_dim : finrank Bool P2 = r + t := by
    have hsum := finrank_sup_add_finrank_inf_bitString C B
    rw [hC_inf, hC_sup, finrank_bot, add_zero, add_comm] at hsum
    exact hsum
  have hd_pos : (0 : ℝ) < d := by positivity
  have hk_2m : δ * (2 * (m : ℝ)) ≤ (k : ℝ) := by
    have hlen : ((m + m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    change δ * ((m + m : ℕ) : ℝ) ≤ (k : ℝ) at hk_ge
    rwa [hlen] at hk_ge
  have htarget_le : (1 + α / (4 * (d : ℝ))) * δ * (m : ℝ) ≤
      (1 / 2 + α / (8 * (d : ℝ))) * (k : ℝ) := by
    have : (1 / 2 + α / (8 * (d : ℝ))) * (2 * (m : ℝ)) =
        (1 + α / (4 * (d : ℝ))) * (m : ℝ) := by field_simp; ring
    have hcoef_pos : 0 < 1 / 2 + α / (8 * (d : ℝ)) := by positivity
    nlinarith
  by_cases hs_big : (1 / 2 + α / (8 * (d : ℝ))) * (k : ℝ) ≤ (s : ℝ)
  · refine ⟨0, htarget_le.trans ?_⟩
    have hmap0 : V.map (basicCondAt T 0) = A' := by
      ext y; simp [basicCondAt, basicCond_zero, A']
    rw [hmap0]
    exact hs_big
  push Not at hs_big
  by_cases hP2_big : (1 / 2 + α / (8 * (d : ℝ))) * (k : ℝ) ≤ (finrank Bool P2 : ℝ)
  · refine ⟨⟨1, by omega⟩, htarget_le.trans ?_⟩
    have hmap1 : V.map (basicCondAt T ⟨1, by omega⟩) = P2 := by
      ext y
      simp only [basicCondAt, P2, Submodule.mem_map, LinearMap.comp_apply, LinearMap.proj_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (basicCond_one T x).symm⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, basicCond_one T x⟩
    rw [hmap1]
    exact hP2_big
  push Not at hP2_big
  have ht_lt : (t : ℝ) ≤ α / (4 * (d : ℝ)) * (k : ℝ) := by
    set eps := α / (8 * (d : ℝ))
    have h2eps : α / (4 * (d : ℝ)) = 2 * eps := by dsimp [eps]; ring
    have hsr_r : (s : ℝ) + (r : ℝ) = k := by exact_mod_cast hsr
    have hP2_r : (finrank Bool P2 : ℝ) = (r : ℝ) + (t : ℝ) := by exact_mod_cast hP2_dim
    have h1 : (s : ℝ) < (k : ℝ) / 2 + eps * (k : ℝ) := by
      have : (1 / 2 + eps) * (k : ℝ) = (k : ℝ) / 2 + eps * (k : ℝ) := by ring
      linarith
    have h2 : (r : ℝ) + (t : ℝ) < (k : ℝ) / 2 + eps * (k : ℝ) := by
      have : (1 / 2 + eps) * (k : ℝ) = (k : ℝ) / 2 + eps * (k : ℝ) := by ring
      linarith
    have h3 : (t : ℝ) ≤ 2 * (eps * (k : ℝ)) := by linarith
    have heq : 2 * (eps * (k : ℝ)) = α / (4 * (d : ℝ)) * (k : ℝ) := by rw [h2eps]; ring
    linarith
  have hP2_eq : V.map (projRight m) = B ⊔ C := by
    change C ⊔ B = V.map (projRight m) at hC_sup
    rw [← hC_sup, sup_comm]
  rcases le_or_gt (2 * s) k with hs_half | hr_half
  · obtain ⟨idx, hidx⟩ := basicCond_subspace_boost_case1 hd hα0 hα1 hT V B C rfl hP2_eq
      (hs_half.trans hk_le) hsr hs_half ht_lt
    exact ⟨idx, htarget_le.trans hidx⟩
  · have hr_half' : 2 * r ≤ k := by omega
    obtain ⟨idx, hidx⟩ := basicCond_subspace_boost_case2 hd hα0 hα1 hT V B C rfl hP2_eq
      (hr_half'.trans hk_le) hsr hr_half' ht_lt
    exact ⟨idx, htarget_le.trans hidx⟩

/-- **Rate-boosting lemma for `basicCond`** ([LiZhong2024, Lemma 20]):
if `T` is an `α`-dimension expander of degree `d ≥ 3` (`0 < α ≤ 1`), then `basicCond T` is a
`(δ, (1 + α / (4 * d)) * δ)` affine somewhere condenser for every `0 < δ ≤ 1 / 2`. -/
theorem isAffineSomewhereCondenser_basicCond {m d : ℕ} (hd : 3 ≤ d) {α δ : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {T : Fin d → BitString m →ₗ[Bool] BitString m} (hT : IsDimensionExpander T α) :
    IsAffineSomewhereCondenser (basicCond T) δ ((1 + α / (4 * (d : ℝ))) * δ) := by
  intro X k hX hk
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨k', -, -, hXk'⟩ := isAffineSource_map_of_isAffine hX
      (isAffine_of_linearMap (basicCondAt T 0))
    exact ⟨0, k', hXk', by simp⟩
  rcases hX with ⟨A, hA, hdim, rfl⟩
  have hboost : ∃ idx : Fin (2 * d + 2),
      (1 + α / (4 * (d : ℝ))) * δ * (m : ℝ) ≤
        (finrank Bool ↥(A.direction.map (basicCondAt T idx)) : ℝ) := by
    by_cases hk_le : finrank Bool A.direction ≤ m
    · exact basicCond_subspace_boost hm hd hα0 hα1 hδ0 hδhalf hT A.direction hk_le
        (by rw [hdim]; exact hk)
    · push Not at hk_le
      obtain ⟨V', hV'_le, hV'_dim⟩ :=
        exists_submodule_finrank_eq_bitString A.direction m hk_le.le
      have hge' : δ * ((m + m : ℕ) : ℝ) ≤ finrank Bool V' := by
        rw [hV'_dim]
        have : ((m + m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
        rw [this]
        nlinarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
      obtain ⟨idx, hidx⟩ := basicCond_subspace_boost hm hd hα0 hα1 hδ0 hδhalf hT V'
        hV'_dim.le hge'
      refine ⟨idx, hidx.trans ?_⟩
      exact_mod_cast Submodule.finrank_mono (Submodule.map_mono hV'_le)
  obtain ⟨idx, hidx⟩ := hboost
  let L := basicCondAt T idx
  have hLA : IsAffine L := isAffine_of_linearMap L
  have hX' : IsAffineSource ((uniformAffine A hA).map (fun x => basicCond T x idx))
      (finrank Bool ↥(A.direction.map L)) := by
    refine ⟨A.map hLA.toAffineMap, by
      obtain ⟨x₀, hx₀⟩ := hA
      exact ⟨L x₀, AffineSubspace.mem_map.mpr ⟨x₀, hx₀, rfl⟩⟩, ?_, ?_⟩
    · rw [AffineSubspace.map_direction, toAffineMap_linear_of_isAffine_linearMap]
    · exact uniformAffine_map_of_isAffine A hA hLA
  exact ⟨idx, _, hX', hidx⟩

/-! ### Iterated linear affine somewhere condenser (`SCond`, [LiZhong2024, Alg. 2 & Thm. 18]) -/

/-- **Iterated linear affine somewhere condenser** (`SCond`, [LiZhong2024, Alg. 2]):
applies `basicCond` across `h` halving rounds from `m * 2 ^ h` down to `m`, producing
`(2 * d + 2) ^ h` linear projections of length `m`. -/
@[expose] def sCond {d : ℕ} (T : ∀ m, Fin d → BitString m →ₗ[Bool] BitString m) :
    ∀ (h m : ℕ), BitString (m * 2 ^ h) →ₗ[Bool] (Fin ((2 * d + 2) ^ h) → BitString m)
  | 0, m =>
    { toFun := fun x _ => bitStringCongr (by ring) x
      map_add' := fun x y => by funext _; rw [map_add]; rfl
      map_smul' := fun c x => by funext _; rw [map_smul]; rfl }
  | h + 1, m =>
    let split : BitString (m * 2 ^ (h + 1)) →ₗ[Bool] BitString (m * 2 ^ h + m * 2 ^ h) :=
      (bitStringCongr (by ring)).toLinearMap
    let step1 := (basicCond (T (m * 2 ^ h))).comp split
    { toFun := fun x idx =>
        let p := finProdFinEquiv.symm (idx.cast (@Nat.pow_succ' (2 * d + 2) h))
        sCond T h m (step1 x p.1) p.2
      map_add' := fun x y => by
        funext idx
        simp only [map_add, Pi.add_apply]
      map_smul' := fun c x => by
        funext idx
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }

private noncomputable def condStepRate (α : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  if r ≤ 1 / 2 then (1 + α / (4 * (d : ℝ))) * r else 1 / 2 + α / (8 * (d : ℝ))

private theorem condStepRate_ge_of_ge_half {α r : ℝ} {d : ℕ} (hr : 1 / 2 ≤ r) (hd : 0 < d) :
    1 / 2 + α / (8 * (d : ℝ)) ≤ condStepRate α d r := by
  unfold condStepRate
  split_ifs with h
  · have hEq : r = 1 / 2 := le_antisymm h hr
    subst hEq
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    apply le_of_eq
    field_simp
    ring
  · exact le_rfl

private theorem isAffineSomewhereCondenser_sCond_aux {d : ℕ} (hd : 3 ≤ d) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    {T : ∀ m, Fin d → BitString m →ₗ[Bool] BitString m}
    (hT : ∀ m, IsDimensionExpander (T m) α) :
    ∀ (h m : ℕ) (r : ℝ), 0 < r →
      IsAffineSomewhereCondenser (sCond T h m) r ((condStepRate α d)^[h] r)
  | 0, m, r, hr => by
    intro X k hX hk
    refine ⟨0, k, ?_, ?_⟩
    · let e : BitString (m * 2 ^ 0) ≃ₗ[Bool] BitString m := bitStringCongr (by ring)
      let L0 : BitString (m * 2 ^ 0) →ₗ[Bool] BitString m := e.toLinearMap
      have hL : IsAffine (fun x => sCond T 0 m x 0) := isAffine_of_linearMap L0
      obtain ⟨A, hA, hdim, rfl⟩ := hX
      refine ⟨A.map hL.toAffineMap, by
        obtain ⟨x₀, hx₀⟩ := hA
        exact ⟨sCond T 0 m x₀ 0, AffineSubspace.mem_map.mpr ⟨x₀, hx₀, rfl⟩⟩, ?_, ?_⟩
      · have hlin : (A.map hL.toAffineMap).direction = A.direction.map L0 := by
          rw [AffineSubspace.map_direction]
          exact congrArg (Submodule.map · A.direction)
            (toAffineMap_linear_of_isAffine_linearMap L0)
        rw [hlin, ← hdim]
        exact (e.submoduleMap A.direction).finrank_eq.symm
      · exact uniformAffine_map_of_isAffine A hA hL
    · simp only [Function.iterate_zero, id_eq]
      have hmul : (m * 2 ^ 0 : ℕ) = m := by ring
      simpa [hmul] using hk
  | h + 1, m, r, hr => by
    intro X k hX hk
    have hr' : 0 < condStepRate α d r := by
      unfold condStepRate
      split_ifs <;> positivity
    let eCongr : BitString (m * 2 ^ (h + 1)) ≃ₗ[Bool] BitString (m * 2 ^ h + m * 2 ^ h) :=
      bitStringCongr (by ring)
    let r₀ : ℝ := min r (1 / 2)
    have hr₀_pos : 0 < r₀ := lt_min hr (by norm_num)
    have hr₀_half : r₀ ≤ 1 / 2 := min_le_right _ _
    have hX_congr : IsAffineSource (X.map eCongr) k := by
      obtain ⟨A, hA, hdim, rfl⟩ := hX
      have he : IsAffine
          (eCongr : BitString (m * 2 ^ (h + 1)) → BitString (m * 2 ^ h + m * 2 ^ h)) :=
        isAffine_of_linearMap eCongr.toLinearMap
      refine ⟨A.map he.toAffineMap, by
        obtain ⟨x₀, hx₀⟩ := hA
        exact ⟨eCongr x₀, AffineSubspace.mem_map.mpr ⟨x₀, hx₀, rfl⟩⟩, ?_, ?_⟩
      · rw [AffineSubspace.map_direction, toAffineMap_linear_of_isAffine_linearMap, ← hdim]
        exact (eCongr.submoduleMap A.direction).finrank_eq.symm
      · exact uniformAffine_map_of_isAffine A hA he
    have hk_congr : r₀ * ((m * 2 ^ h + m * 2 ^ h : ℕ) : ℝ) ≤ (k : ℝ) := by
      have hlen : ((m * 2 ^ h + m * 2 ^ h : ℕ) : ℝ) = ((m * 2 ^ (h + 1) : ℕ) : ℝ) := by
        push_cast; ring
      rw [hlen]
      exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)).trans hk
    obtain ⟨i₁, k₁, hX₁, hk₁⟩ :=
      isAffineSomewhereCondenser_basicCond hd hα0 hα1 hr₀_pos hr₀_half (hT (m * 2 ^ h))
        (X.map eCongr) k hX_congr hk_congr
    have hk₁' : condStepRate α d r * ((m * 2 ^ h : ℕ) : ℝ) ≤ (k₁ : ℝ) := by
      refine (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)).trans hk₁
      unfold condStepRate
      split_ifs with hle
      · simp [r₀, min_eq_left hle]
      · have hr_half : 1 / 2 ≤ r := (lt_of_not_ge hle).le
        have hmin : r₀ = 1 / 2 := min_eq_right hr_half
        rw [hmin]
        apply le_of_eq
        have hd0 : (d : ℝ) ≠ 0 := by positivity
        field_simp; ring
    have hX₁_eq : (X.map eCongr).map (fun y => basicCond (T (m * 2 ^ h)) y i₁) =
        X.map (fun x => basicCond (T (m * 2 ^ h)) (eCongr x) i₁) := by
      rw [PMF.map_comp]; rfl
    rw [hX₁_eq] at hX₁
    obtain ⟨i₂, k₂, hX₂, hk₂⟩ :=
      isAffineSomewhereCondenser_sCond_aux hd hα0 hα1 hT h m (condStepRate α d r) hr'
        _ k₁ hX₁ hk₁'
    rw [Function.iterate_succ_apply]
    let idx : Fin ((2 * d + 2) ^ (h + 1)) :=
      (finProdFinEquiv (i₁, i₂)).cast (@Nat.pow_succ' (2 * d + 2) h).symm
    refine ⟨idx, k₂, ?_, hk₂⟩
    have hmap : X.map (fun x => sCond T (h + 1) m x idx) =
        (X.map (fun x => basicCond (T (m * 2 ^ h)) (eCongr x) i₁)).map
          (fun y => sCond T h m y i₂) := by
      rw [PMF.map_comp]
      congr 1 with x
      have hcast : idx.cast (@Nat.pow_succ' (2 * d + 2) h) = finProdFinEquiv (i₁, i₂) := by
        ext; simp [idx]
      simp only [sCond, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
        LinearEquiv.coe_coe, hcast, finProdFinEquiv.symm_apply_apply]
      rfl
    rw [hmap]
    exact hX₂

/-- **Iterated linear affine somewhere condenser** ([LiZhong2024, Thm. 18]):
given any family `T` of `α`-dimension expanders of degree `d ≥ 3` (`0 < α ≤ 1`), for every
`0 < δ ≤ 1 / 2` and every `h` satisfying `1 / 2 ≤ δ * (1 + α / (4 * d)) ^ h`, iterating
`basicCond` for `h + 1` steps gives a linear `(δ, 1 / 2 + α / (8 * d))` affine somewhere
condenser `sCond T (h + 1) m`. -/
theorem isAffineSomewhereCondenser_sCond {d : ℕ} (hd : 3 ≤ d) {α δ : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hδ0 : 0 < δ)
    {h : ℕ} (hh : 1 / 2 ≤ δ * (1 + α / (4 * (d : ℝ))) ^ h)
    {T : ∀ m, Fin d → BitString m →ₗ[Bool] BitString m}
    (hT : ∀ m, IsDimensionExpander (T m) α) (m : ℕ) :
    IsAffineSomewhereCondenser (sCond T (h + 1) m) δ (1 / 2 + α / (8 * (d : ℝ))) := by
  have hd_pos : 0 < d := by omega
  have hge_half : 1 / 2 ≤ (condStepRate α d)^[h] δ := by
    have hiter : ∀ j : ℕ, 1 / 2 ≤ (condStepRate α d)^[j] δ ∨
        (condStepRate α d)^[j] δ = δ * (1 + α / (4 * (d : ℝ))) ^ j := by
      intro j
      induction j with
      | zero => right; simp
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        rcases ih with hj | hj
        · left
          exact (le_add_of_nonneg_right (by positivity : 0 ≤ α / (8 * (d : ℝ)))).trans
            (condStepRate_ge_of_ge_half hj hd_pos)
        · rw [hj]
          by_cases hle : δ * (1 + α / (4 * (d : ℝ))) ^ j ≤ 1 / 2
          · right
            unfold condStepRate
            rw [ite_eq_left hle, pow_succ]
            ring
          · left
            have hj_ge : 1 / 2 ≤ δ * (1 + α / (4 * (d : ℝ))) ^ j := (lt_of_not_ge hle).le
            exact (le_add_of_nonneg_right (by positivity : 0 ≤ α / (8 * (d : ℝ)))).trans
              (condStepRate_ge_of_ge_half hj_ge hd_pos)
    rcases hiter h with h1 | h2
    · exact h1
    · rw [h2]; exact hh
  have hstep : 1 / 2 + α / (8 * (d : ℝ)) ≤ (condStepRate α d)^[h + 1] δ := by
    rw [Function.iterate_succ_apply']
    exact condStepRate_ge_of_ge_half hge_half hd_pos
  intro X k hX hk
  obtain ⟨i, k', hX', hk'⟩ :=
    isAffineSomewhereCondenser_sCond_aux hd hα0 hα1 hT (h + 1) m δ hδ0 X k hX hk
  exact ⟨i, k', hX', (mul_le_mul_of_nonneg_right hstep (Nat.cast_nonneg m)).trans hk'⟩

end Cslib.AffineDisperser.Li
