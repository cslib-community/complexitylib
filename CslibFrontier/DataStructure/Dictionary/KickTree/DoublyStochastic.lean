/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.FeistelPerm
public import CslibFrontier.Probability.StatisticalDistance
public import CslibFrontier.Probability.StatisticalDistance.ClosedForm
public import CslibFrontier.Probability.StatisticalDistance.Event
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Matrix.Basic
import CslibFrontier.Probability.KWiseIndependent.Coupling
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.StatisticalDistance.Coupling
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Doubly-stochastic `k`-tuple contraction and without-replacement negative correlation

This module develops two general finite-domain permutation building blocks used by
`CslibFrontier.DataStructure.Dictionary.KickTree.SmallUniversePerm` and
`CslibFrontier.DataStructure.Dictionary.KickTree.QuotientPerm`:

1. **Elementary doubly-stochastic matrix contraction**: For any nonempty finite state space `Ω`,
   letting `U = unifMatrix Ω` have every entry `|Ω|⁻¹`, any two doubly-stochastic matrices `P₁, P₂`
   satisfy `(P₁ - U) * (P₂ - U) = P₁ * P₂ - U` (`sub_unifMatrix_mul_sub_unifMatrix`). Submultiplicativity
   of the row-`ℓ₁` norm yields total-variation contraction for composed random bijections on
   injective `T`-tuples `T ↪ α` (`dist_permTupleKernel_composePermDist_le`), proving that `t ≥ 1`
   independent `k`-wise `δ`-dependent permutations compose to a `k`-wise
   `((1 / 2) * (2 * δ) ^ t)`-dependent permutation ([ArbitmanNaorSegev2010], `arXiv:0912.5424v3`,
   Section 5.3, Theorem 5.6, PDF p. 25 / printed p. 24).
2. **Negative correlation of uniform random injections**: Under `e ← PMF.uniformOfFintype (T ↪ α)`,
   the probability that every coordinate `e i` lands in `Q : Finset α` is at most
   `(#Q / |α|) ^ |T|` (`prob_uniformOfFintype_embedding_forall_mem_le`, formalizing the
   without-replacement negative-correlation inequality of
   [BenderFarachColtonKuszmaulKuszmaulLiu2022], `arXiv:2111.00602v2`, Section 5.3, PDF p. 36 /
   printed p. 35).

## Main definitions

* `Cslib.DataStructure.Dictionary.KickTree.unifMatrix`,
  `Cslib.DataStructure.Dictionary.KickTree.IsDoublyStochastic`,
  `Cslib.DataStructure.Dictionary.KickTree.kernelMatrix`,
  `Cslib.DataStructure.Dictionary.KickTree.permTupleEquiv`,
  `Cslib.DataStructure.Dictionary.KickTree.permTupleKernel`,
  `Cslib.DataStructure.Dictionary.KickTree.composePermDist`: doubly-stochastic matrices, Markov
  kernels, and composed random-permutation kernels on `T ↪ α`.

## Main results

* `Cslib.DataStructure.Dictionary.KickTree.sub_unifMatrix_mul_sub_unifMatrix`,
  `Cslib.DataStructure.Dictionary.KickTree.dist_permTupleKernel_composePermDist_le`:
  `(P₁ - U) * (P₂ - U) = P₁ * P₂ - U` and `(1 / 2) * (2 * δ) ^ t` statistical-distance contraction.
* `Cslib.DataStructure.Dictionary.KickTree.prob_uniformOfFintype_embedding_forall_mem_le`,
  `Cslib.DataStructure.Dictionary.KickTree.prob_perm_forall_mem_le_of_dist`: without-replacement
  multiplicative upper bound and statistical-distance transfer.

## References

* [Y. Arbitman, M. Naor and G. Segev, *Backyard Cuckoo Hashing: Constant Worst-Case Operations
  with a Succinct Representation*][ArbitmanNaorSegev2010]
* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, *On the Optimal
  Time/Space Tradeoff for Hash Tables*][BenderFarachColtonKuszmaulKuszmaulLiu2022]
-/

public section

namespace Cslib.DataStructure.Dictionary.KickTree

open Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.FeistelPerm
open Cslib.Probability Cslib.Probability.PMF Finset Fintype
open scoped BigOperators ENNReal Matrix Cslib.Probability.PMF

/-! ## Section 1: Doubly-stochastic matrix identity `(P₁ - U)(P₂ - U) = P₁ P₂ - U` -/

/-- The uniform transition matrix on a finite type `Ω`, with every entry `(Fintype.card Ω : ℝ)⁻¹`. -/
noncomputable def unifMatrix (Ω : Type*) [Fintype Ω] : Matrix Ω Ω ℝ :=
  Matrix.of fun _ _ => (Fintype.card Ω : ℝ)⁻¹

@[simp] theorem unifMatrix_apply (Ω : Type*) [Fintype Ω] (x y : Ω) :
    unifMatrix Ω x y = (Fintype.card Ω : ℝ)⁻¹ := by unfold unifMatrix; rfl

/-- A real matrix `P` on `Ω` is *doubly stochastic* if its entries are nonnegative and every row
and column sums to `1`. -/
structure IsDoublyStochastic {Ω : Type*} [Fintype Ω] (P : Matrix Ω Ω ℝ) : Prop where
  /-- Every matrix entry is nonnegative. -/
  nonneg : ∀ x y, 0 ≤ P x y
  /-- Every row sums to `1`. -/
  row_sum : ∀ x, ∑ y : Ω, P x y = 1
  /-- Every column sums to `1`. -/
  col_sum : ∀ y, ∑ x : Ω, P x y = 1

namespace IsDoublyStochastic

theorem mul_unifMatrix {Ω : Type*} [Fintype Ω] {P : Matrix Ω Ω ℝ}
    (hP : IsDoublyStochastic P) : P * unifMatrix Ω = unifMatrix Ω := by
  ext x z; simp only [Matrix.mul_apply, unifMatrix_apply, ← sum_mul, hP.row_sum x, one_mul]

theorem unifMatrix_mul {Ω : Type*} [Fintype Ω] {P : Matrix Ω Ω ℝ}
    (hP : IsDoublyStochastic P) : unifMatrix Ω * P = unifMatrix Ω := by
  ext x z; simp only [Matrix.mul_apply, unifMatrix_apply, ← mul_sum, hP.col_sum z, mul_one]

theorem mul {Ω : Type*} [Fintype Ω] {P₁ P₂ : Matrix Ω Ω ℝ}
    (h₁ : IsDoublyStochastic P₁) (h₂ : IsDoublyStochastic P₂) :
    IsDoublyStochastic (P₁ * P₂) where
  nonneg x z := sum_nonneg fun y _ => mul_nonneg (h₁.nonneg x y) (h₂.nonneg y z)
  row_sum x := by
    simp only [Matrix.mul_apply]; rw [sum_comm]
    simp only [← mul_sum, h₂.row_sum, mul_one, h₁.row_sum]
  col_sum z := by
    simp only [Matrix.mul_apply]; rw [sum_comm]
    simp only [← sum_mul, h₁.col_sum, one_mul, h₂.col_sum]

end IsDoublyStochastic

theorem unifMatrix_mul_self (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    unifMatrix Ω * unifMatrix Ω = unifMatrix Ω := by
  ext x z
  have hne : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Matrix.mul_apply, unifMatrix_apply, sum_const, card_univ, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- **Doubly-stochastic centering identity**: `(P₁ - U) * (P₂ - U) = P₁ * P₂ - U`. -/
theorem sub_unifMatrix_mul_sub_unifMatrix {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {P₁ P₂ : Matrix Ω Ω ℝ} (h₁ : IsDoublyStochastic P₁) (h₂ : IsDoublyStochastic P₂) :
    (P₁ - unifMatrix Ω) * (P₂ - unifMatrix Ω) = P₁ * P₂ - unifMatrix Ω := by
  rw [sub_mul, mul_sub, mul_sub, h₁.mul_unifMatrix, h₂.unifMatrix_mul, unifMatrix_mul_self]; abel

/-- Row-`ℓ₁` submultiplicativity for centered doubly-stochastic matrices. -/
theorem rowSum_abs_sub_unifMatrix_mul_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {P₁ P₂ : Matrix Ω Ω ℝ} (h₁ : IsDoublyStochastic P₁) (h₂ : IsDoublyStochastic P₂)
    {c₁ c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hb₁ : ∀ x, ∑ y, |(P₁ - unifMatrix Ω) x y| ≤ c₁)
    (hb₂ : ∀ y, ∑ z, |(P₂ - unifMatrix Ω) y z| ≤ c₂) (x : Ω) :
    ∑ z, |(P₁ * P₂ - unifMatrix Ω) x z| ≤ c₁ * c₂ := by
  rw [← sub_unifMatrix_mul_sub_unifMatrix h₁ h₂]
  calc ∑ z, |((P₁ - unifMatrix Ω) * (P₂ - unifMatrix Ω)) x z|
      = ∑ z, |∑ y, (P₁ - unifMatrix Ω) x y * (P₂ - unifMatrix Ω) y z| := by
        simp only [Matrix.mul_apply]
    _ ≤ ∑ z, ∑ y, |(P₁ - unifMatrix Ω) x y| * |(P₂ - unifMatrix Ω) y z| :=
        sum_le_sum fun z _ => (abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun y _ => (abs_mul _ _).le)
    _ = ∑ y, |(P₁ - unifMatrix Ω) x y| * ∑ z, |(P₂ - unifMatrix Ω) y z| := by
        rw [sum_comm]; exact sum_congr rfl fun y _ => (mul_sum _ _ _).symm
    _ ≤ ∑ y, |(P₁ - unifMatrix Ω) x y| * c₂ :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hb₂ y) (abs_nonneg _)
    _ = (∑ y, |(P₁ - unifMatrix Ω) x y|) * c₂ := (sum_mul _ _ _).symm
    _ ≤ c₁ * c₂ := mul_le_mul_of_nonneg_right (hb₁ x) hc₂

/-! ## Section 2: Markov kernels and composed random-permutation contraction on `T ↪ α` -/

/-- Transition matrix of a finite Markov kernel `K : Ω → PMF Ω`. -/
noncomputable def kernelMatrix {Ω : Type*} (K : Ω → PMF Ω) : Matrix Ω Ω ℝ :=
  Matrix.of fun x y => (K x y).toReal

@[simp] theorem kernelMatrix_apply {Ω : Type*} (K : Ω → PMF Ω) (x y : Ω) :
    kernelMatrix K x y = (K x y).toReal := by unfold kernelMatrix; rfl

theorem kernelMatrix_bind {Ω : Type*} [Fintype Ω] (K₁ K₂ : Ω → PMF Ω) :
    kernelMatrix (fun x => (K₁ x).bind K₂) = kernelMatrix K₁ * kernelMatrix K₂ := by
  ext x z; simp only [kernelMatrix_apply, Matrix.mul_apply, bind_apply_toReal]

theorem rowSum_abs_kernelMatrix_sub_unifMatrix {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (K : Ω → PMF Ω) (x : Ω) :
    ∑ y : Ω, |(kernelMatrix K - unifMatrix Ω) x y| =
      2 * dist (K x) (PMF.uniformOfFintype Ω) := by
  rw [PMF.dist_eq]
  have hunif (y : Ω) : (PMF.uniformOfFintype Ω y).toReal = (Fintype.card Ω : ℝ)⁻¹ := by
    simp [PMF.uniformOfFintype_apply]
  have hsum : ∑ y : Ω, |(kernelMatrix K - unifMatrix Ω) x y| =
      ∑ y : Ω, |(K x y).toReal - (PMF.uniformOfFintype Ω y).toReal| :=
    sum_congr rfl fun y _ => by simp only [Matrix.sub_apply, kernelMatrix_apply,
      unifMatrix_apply, hunif]
  rw [hsum]; ring

/-- **Doubly-stochastic Markov kernel contraction**: composing two doubly-stochastic kernels whose
rows are within `δ₁` and `δ₂` of uniform produces a kernel within `δ₁ * (2 * δ₂)` of uniform. -/
theorem dist_kernel_bind_le_mul {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {K₁ K₂ : Ω → PMF Ω}
    (h₁ : IsDoublyStochastic (kernelMatrix K₁)) (h₂ : IsDoublyStochastic (kernelMatrix K₂))
    {δ₁ δ₂ : ℝ}
    (hb₁ : ∀ x, dist (K₁ x) (PMF.uniformOfFintype Ω) ≤ δ₁)
    (hb₂ : ∀ y, dist (K₂ y) (PMF.uniformOfFintype Ω) ≤ δ₂) (x : Ω) :
    dist ((K₁ x).bind K₂) (PMF.uniformOfFintype Ω) ≤ δ₁ * (2 * δ₂) := by
  have hδ₂ : 0 ≤ δ₂ := dist_nonneg.trans (hb₂ x)
  have hrow := rowSum_abs_sub_unifMatrix_mul_le h₁ h₂ (c₁ := 2 * δ₁) (c₂ := 2 * δ₂) (by positivity)
    (fun a => (rowSum_abs_kernelMatrix_sub_unifMatrix K₁ a).trans_le (by linarith [hb₁ a]))
    (fun b => (rowSum_abs_kernelMatrix_sub_unifMatrix K₂ b).trans_le (by linarith [hb₂ b])) x
  rw [← kernelMatrix_bind, rowSum_abs_kernelMatrix_sub_unifMatrix] at hrow; linarith

/-- Bijection induced on injective `T`-tuples `T ↪ α` by post-composing with `π : Equiv.Perm α`. -/
@[expose] def permTupleEquiv {T α : Type*} (π : Equiv.Perm α) : Equiv.Perm (T ↪ α) where
  toFun x := x.trans π.toEmbedding
  invFun y := y.trans π.symm.toEmbedding
  left_inv x := by ext i; simp
  right_inv y := by ext i; simp

@[simp] theorem permTupleEquiv_apply {T α : Type*} (π : Equiv.Perm α) (x : T ↪ α) (i : T) :
    permTupleEquiv π x i = π (x i) := rfl

@[simp] theorem permTupleEquiv_refl {T α : Type*} :
    permTupleEquiv (T := T) (Equiv.refl α) = Equiv.refl (T ↪ α) := by ext x i; rfl

theorem permTupleEquiv_trans {T α : Type*} (π₁ π₂ : Equiv.Perm α) (x : T ↪ α) :
    permTupleEquiv (π₁.trans π₂) x = permTupleEquiv π₂ (permTupleEquiv π₁ x) := by ext i; rfl

/-- Markov kernel on `T ↪ α` induced by applying a random permutation `π ← ρ` coordinatewise. -/
noncomputable def permTupleKernel {T α : Type*} (ρ : PMF (Equiv.Perm α)) (x : T ↪ α) :
    PMF (T ↪ α) :=
  ρ.map (fun π => permTupleEquiv π x)

theorem permTupleKernel_eq {T α : Type*} (ρ : PMF (Equiv.Perm α)) (x : T ↪ α) :
    permTupleKernel ρ x = ρ.map (fun π => permTupleEquiv π x) := by
  unfold permTupleKernel; rfl

/-- Every random permutation `ρ : PMF (Equiv.Perm α)` induces a **doubly-stochastic** transition
matrix on injective `T`-tuples `T ↪ α`. -/
theorem isDoublyStochastic_permTupleKernel {T α : Type*}
    [Fintype T] [DecidableEq T] [Fintype α] [DecidableEq α]
    (ρ : PMF (Equiv.Perm α)) :
    IsDoublyStochastic (kernelMatrix (permTupleKernel (T := T) ρ)) where
  nonneg _ _ := ENNReal.toReal_nonneg
  row_sum x := sum_toReal (permTupleKernel ρ x)
  col_sum y := by
    classical
    have hentry (x : T ↪ α) :
        (permTupleKernel ρ x y).toReal =
          ∑ π : Equiv.Perm α, if permTupleEquiv π x = y then (ρ π).toReal else 0 := by
      rw [permTupleKernel, map_apply_toReal]
      refine sum_congr rfl fun π _ => ?_
      by_cases h : permTupleEquiv π x = y
      · simp [h]
      · simp [h, Ne.symm h]
    simp only [kernelMatrix_apply, hentry]
    rw [sum_comm]
    have hinner (π : Equiv.Perm α) :
        (∑ x : T ↪ α, if permTupleEquiv π x = y then (ρ π).toReal else 0) = (ρ π).toReal := by
      have hiff (x : T ↪ α) : permTupleEquiv π x = y ↔ x = (permTupleEquiv π).symm y :=
        (permTupleEquiv π).apply_eq_iff_eq_symm_apply
      simp only [hiff, Fintype.sum_ite_eq']
    simp only [hinner]
    exact sum_toReal ρ

/-- Left-to-right composition `π₀.trans (π₁.trans ⋯)` of `t` independent random permutations. -/
noncomputable def composePermDist {α : Type*} :
    (t : ℕ) → (Fin t → PMF (Equiv.Perm α)) → PMF (Equiv.Perm α)
  | 0, _ => PMF.pure (Equiv.refl α)
  | t + 1, ρs =>
    (composePermDist t (fun i => ρs i.castSucc)).bind fun π₁ =>
      (ρs (Fin.last t)).map fun π₂ => π₁.trans π₂

@[simp] theorem composePermDist_zero {α : Type*} (ρs : Fin 0 → PMF (Equiv.Perm α)) :
    composePermDist 0 ρs = PMF.pure (Equiv.refl α) := by
  unfold composePermDist; rfl

@[simp] theorem composePermDist_succ {α : Type*} (t : ℕ)
    (ρs : Fin (t + 1) → PMF (Equiv.Perm α)) :
    composePermDist (t + 1) ρs =
      (composePermDist t (fun i => ρs i.castSucc)).bind fun π₁ =>
        (ρs (Fin.last t)).map fun π₂ => π₁.trans π₂ := by
  conv_lhs => unfold composePermDist

theorem permTupleKernel_composePermDist_succ {T α : Type*} (t : ℕ)
    (ρs : Fin (t + 1) → PMF (Equiv.Perm α)) (x : T ↪ α) :
    permTupleKernel (composePermDist (t + 1) ρs) x =
      (permTupleKernel (composePermDist t (fun i => ρs i.castSucc)) x).bind
        (permTupleKernel (ρs (Fin.last t))) := by
  unfold permTupleKernel
  simp only [composePermDist, PMF.map_bind, PMF.bind_map]
  refine congrArg ((composePermDist t (fun i => ρs i.castSucc)).bind ·) (funext fun π₁ => ?_)
  simp only [PMF.map_comp, Function.comp_def, permTupleEquiv_trans]

private theorem dist_permTupleKernel_composePermDist_succ_le {T α : Type*}
    [Fintype T] [DecidableEq T] [Fintype α] [DecidableEq α] [Nonempty (T ↪ α)] {δ : ℝ} :
    ∀ (m : ℕ) (ρs : Fin (m + 1) → PMF (Equiv.Perm α)),
      (∀ (i : Fin (m + 1)) (x : T ↪ α),
        dist (permTupleKernel (ρs i) x) (PMF.uniformOfFintype (T ↪ α)) ≤ δ) →
      ∀ x : T ↪ α,
        dist (permTupleKernel (composePermDist (m + 1) ρs) x)
          (PMF.uniformOfFintype (T ↪ α)) ≤ (1 / 2 : ℝ) * (2 * δ) ^ (m + 1)
  | 0, ρs, hδ, x => by
    have heq : permTupleKernel (composePermDist 1 ρs) x = permTupleKernel (ρs 0) x := by
      rw [permTupleKernel_composePermDist_succ]
      simp only [composePermDist, permTupleKernel, PMF.pure_map, permTupleEquiv_refl,
        Equiv.refl_apply, PMF.pure_bind]
      rfl
    rw [heq, pow_one]
    linarith [hδ 0 x]
  | m + 1, ρs, hδ, x => by
    rw [permTupleKernel_composePermDist_succ]
    have hprev := dist_permTupleKernel_composePermDist_succ_le m
      (fun i => ρs i.castSucc) (fun i z => hδ i.castSucc z)
    have hlast := fun y : T ↪ α => hδ (Fin.last (m + 1)) y
    have hmul := dist_kernel_bind_le_mul
      (isDoublyStochastic_permTupleKernel _)
      (isDoublyStochastic_permTupleKernel _) hprev hlast x
    have hpow : ((1 / 2 : ℝ) * (2 * δ) ^ (m + 1)) * (2 * δ) =
        (1 / 2 : ℝ) * (2 * δ) ^ (m + 2) := by
      rw [pow_succ (2 * δ) (m + 1)]
      ring
    exact hmul.trans_eq hpow

/-- **`t`-round doubly-stochastic statistical-distance contraction** ([ArbitmanNaorSegev2010],
`arXiv:0912.5424v3`, Section 5.3, Theorem 5.6, PDF p. 25 / printed p. 24): composing `t ≥ 1`
independent random permutations, each within statistical distance `δ` of uniform on `T ↪ α`,
yields a random permutation within `(1 / 2) * (2 * δ) ^ t` of uniform on `T ↪ α`. -/
theorem dist_permTupleKernel_composePermDist_le {T α : Type*}
    [Fintype T] [DecidableEq T] [Fintype α] [DecidableEq α] [Nonempty (T ↪ α)]
    {t : ℕ} (ht : 1 ≤ t) (ρs : Fin t → PMF (Equiv.Perm α)) {δ : ℝ}
    (hδ : ∀ (i : Fin t) (x : T ↪ α),
      dist (permTupleKernel (ρs i) x) (PMF.uniformOfFintype (T ↪ α)) ≤ δ)
    (x : T ↪ α) :
    dist (permTupleKernel (composePermDist t ρs) x) (PMF.uniformOfFintype (T ↪ α)) ≤
      (1 / 2 : ℝ) * (2 * δ) ^ t := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, (Nat.sub_add_cancel ht).symm⟩
  exact dist_permTupleKernel_composePermDist_succ_le m ρs hδ x

/-! ## Section 3: Negative correlation of without-replacement uniform injections -/

/-- Falling-factorial comparison `Q.descFactorial r * U ^ r ≤ Q ^ r * U.descFactorial r` when
`Q ≤ U` (sampling without replacement vs. sampling with replacement). -/
theorem descFactorial_mul_pow_le {Q U : ℕ} (hQU : Q ≤ U) (r : ℕ) :
    Q.descFactorial r * U ^ r ≤ Q ^ r * U.descFactorial r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hstep : (Q - r) * U ≤ Q * (U - r) := by
      rcases le_or_gt Q r with hle | hlt
      · rw [Nat.sub_eq_zero_of_le hle, zero_mul]
        exact Nat.zero_le _
      · rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_comm r U]
        exact Nat.sub_le_sub_left (Nat.mul_le_mul_right r hQU) (Q * U)
    calc Q.descFactorial (r + 1) * U ^ (r + 1)
        = (Q.descFactorial r * U ^ r) * ((Q - r) * U) := by
          rw [Nat.descFactorial_succ, pow_succ]
          ring
      _ ≤ (Q ^ r * U.descFactorial r) * (Q * (U - r)) := Nat.mul_le_mul ih hstep
      _ = Q ^ (r + 1) * U.descFactorial (r + 1) := by
          rw [Nat.descFactorial_succ, pow_succ]
          ring

/-- **Without-replacement multiplicative upper bound**
([BenderFarachColtonKuszmaulKuszmaulLiu2022], `arXiv:2111.00602v2`, Section 5.3, PDF p. 36 /
printed p. 35): for a uniform random injection `e ← PMF.uniformOfFintype (T ↪ α)`
(`Fintype.card T ≤ Fintype.card α`, `Nonempty α`) and any target set `Q : Finset α`, the
probability that `e i ∈ Q` for all `i : T` is at most `(#Q / |α|) ^ |T|`. -/
theorem prob_uniformOfFintype_embedding_forall_mem_le {T α : Type*}
    [Fintype T] [DecidableEq T] [Fintype α] [DecidableEq α] [Nonempty α]
    (hT : Fintype.card T ≤ Fintype.card α) (Q : Finset α) :
    haveI : Nonempty (T ↪ α) := Function.Embedding.nonempty_of_card_le hT
    ((PMF.uniformOfFintype (T ↪ α)).toOuterMeasure {e : T ↪ α | ∀ i : T, e i ∈ Q}).toReal ≤
      ((#Q : ℝ) / (Fintype.card α : ℝ)) ^ Fintype.card T := by
  classical
  haveI : Nonempty (T ↪ α) := Function.Embedding.nonempty_of_card_le hT
  let E : Set (T ↪ α) := {e : T ↪ α | ∀ i : T, e i ∈ Q}
  let toSub : {e : T ↪ α // e ∈ E} ↪ (T ↪ Q) :=
    { toFun := fun ⟨e, he⟩ =>
        ⟨fun i => ⟨e i, he i⟩, fun i j h => e.injective (congrArg Subtype.val h)⟩
      inj' := fun ⟨_, _⟩ ⟨_, _⟩ h =>
        Subtype.ext (DFunLike.ext _ _ fun i => congrArg Subtype.val (DFunLike.congr_fun h i)) }
  have hcard_good : #(univ.filter (· ∈ E)) ≤ (#Q).descFactorial (Fintype.card T) := by
    calc #(univ.filter (· ∈ E))
        = Fintype.card {e : T ↪ α // e ∈ E} := (Fintype.card_subtype _).symm
      _ ≤ Fintype.card (T ↪ Q) := Fintype.card_le_of_injective toSub toSub.injective
      _ = (#Q).descFactorial (Fintype.card T) := by rw [Fintype.card_embedding_eq, Fintype.card_coe]
  change ((PMF.uniformOfFintype (T ↪ α)).toOuterMeasure E).toReal ≤ _
  rw [toOuterMeasure_uniformOfFintype_toReal]
  have hcard_emb : Fintype.card (T ↪ α) = (Fintype.card α).descFactorial (Fintype.card T) :=
    Fintype.card_embedding_eq
  have hdesc_pos : 0 < (Fintype.card α).descFactorial (Fintype.card T) :=
    hcard_emb ▸ Fintype.card_pos
  have hα_pos : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [hcard_emb, div_pow, div_le_div_iff₀ (Nat.cast_pos.mpr hdesc_pos) (pow_pos hα_pos _)]
  have hnat :
      #(univ.filter (· ∈ E)) * Fintype.card α ^ Fintype.card T ≤
        (#Q) ^ Fintype.card T * (Fintype.card α).descFactorial (Fintype.card T) :=
    (Nat.mul_le_mul_right _ hcard_good).trans
      (descFactorial_mul_pow_le (card_le_univ Q) (Fintype.card T))
  exact_mod_cast hnat

/-- Transferring the without-replacement multiplicative upper bound across `dist ≤ δ`: if a random
permutation `ρ` is `δ`-close to uniform on `x : T ↪ α`, then `Pr[∀ i, π (x i) ∈ Q] ≤
(#Q / |α|) ^ |T| + δ`. -/
theorem prob_perm_forall_mem_le_of_dist {T α : Type*}
    [Fintype T] [DecidableEq T] [Fintype α] [DecidableEq α] [Nonempty α]
    (ρ : PMF (Equiv.Perm α)) (x : T ↪ α) (Q : Finset α) {δ : ℝ}
    (hdist :
      haveI : Nonempty (T ↪ α) := ⟨x⟩
      dist (permTupleKernel ρ x) (PMF.uniformOfFintype (T ↪ α)) ≤ δ) :
    (ρ.toOuterMeasure {π : Equiv.Perm α | ∀ i : T, π (x i) ∈ Q}).toReal ≤
      ((#Q : ℝ) / (Fintype.card α : ℝ)) ^ Fintype.card T + δ := by
  haveI : Nonempty (T ↪ α) := ⟨x⟩
  have hcard : Fintype.card T ≤ Fintype.card α := Fintype.card_le_of_injective x x.injective
  let E : Set (T ↪ α) := {e : T ↪ α | ∀ i : T, e i ∈ Q}
  have hmap : ρ.toOuterMeasure {π : Equiv.Perm α | ∀ i : T, π (x i) ∈ Q} =
      (permTupleKernel ρ x).toOuterMeasure E := by
    rw [permTupleKernel, PMF.toOuterMeasure_map_apply]
    rfl
  rw [hmap]
  have habs := abs_toOuterMeasure_toReal_sub_le_dist
    (permTupleKernel ρ x) (PMF.uniformOfFintype (T ↪ α)) E
  have hunif := prob_uniformOfFintype_embedding_forall_mem_le hcard Q
  linarith [(le_abs_self _).trans habs]

theorem ratio_not_injective_fun_le {T : Type*} [Fintype T] [DecidableEq T] (s : ℕ) :
    (#(univ.filter fun f : T → Fin (2 ^ s) => ¬ Function.Injective f) : ℝ) /
        (Fintype.card (T → Fin (2 ^ s)) : ℝ) ≤
      ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (2 ^ s : ℝ)) := by
  let S₀ : Finset (Fin (2 ^ s) × T) :=
    (univ : Finset T).map ⟨fun i => (0, i), fun _ _ h => congrArg Prod.snd h⟩
  have hS₀_card : #S₀ = Fintype.card T := by simp [S₀]
  have hid_pw : IsPairwiseIndependentHash (id : (T → Fin (2 ^ s)) → T → Fin (2 ^ s)) :=
    (isKWiseIndependentHash_id 2).isPairwiseIndependentHash le_rfl
  have hfeistel := dens_not_injOn_feistelHead_le hid_pw S₀
  rw [hS₀_card, dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast,
    NNRat.cast_natCast] at hfeistel
  have hsub : #(univ.filter fun f : T → Fin (2 ^ s) => ¬ Function.Injective f) ≤
      #{f : T → Fin (2 ^ s) | ¬ Set.InjOn (feistelHead (id f)) (S₀ : Set (Fin (2 ^ s) × T))} := by
    refine card_le_card fun f hf => ?_
    rw [mem_filter] at hf ⊢
    refine ⟨mem_univ f, fun hInj => hf.2 fun i₁ i₂ heq => ?_⟩
    have h1 : ((0 : Fin (2 ^ s)), i₁) ∈ S₀ := mem_map.mpr ⟨i₁, mem_univ i₁, rfl⟩
    have h2 : ((0 : Fin (2 ^ s)), i₂) ∈ S₀ := mem_map.mpr ⟨i₂, mem_univ i₂, rfl⟩
    have hhd : feistelHead f (0, i₁) = feistelHead f (0, i₂) := by simp [feistelHead, heq]
    exact congrArg Prod.snd (hInj h1 h2 hhd)
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr hsub) (Nat.cast_nonneg _)).trans hfeistel

theorem prob_not_injective_uniform_le {T : Type*} [Fintype T] [DecidableEq T] (s : ℕ) :
    ((PMF.uniformOfFintype (T → Fin (2 ^ s))).toOuterMeasure
      {f : T → Fin (2 ^ s) | ¬ Function.Injective f}).toReal ≤
      ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (2 ^ s : ℝ)) := by
  classical
  let E : Set (T → Fin (2 ^ s)) := {f | ¬ Function.Injective f}
  change ((PMF.uniformOfFintype (T → Fin (2 ^ s))).toOuterMeasure E).toReal ≤ _
  rw [toOuterMeasure_uniformOfFintype_toReal]
  have hfilt : univ.filter (· ∈ E) =
      univ.filter (fun f : T → Fin (2 ^ s) => ¬ Function.Injective f) :=
    filter_congr fun _ _ => Iff.rfl
  rw [hfilt]
  exact ratio_not_injective_fun_le s

theorem dist_uniform_embedding_to_fun {T : Type*} [Fintype T] [DecidableEq T]
    (a' : ℕ) (hcard : Fintype.card T ≤ 2 ^ a') :
    haveI : Nonempty (T ↪ Fin (2 ^ a')) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hcard)
    dist ((PMF.uniformOfFintype (T ↪ Fin (2 ^ a'))).map
        (fun e : T ↪ Fin (2 ^ a') => (e : T → Fin (2 ^ a'))))
      (PMF.uniformOfFintype (T → Fin (2 ^ a'))) ≤
      ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (2 ^ a' : ℝ)) := by
  classical
  haveI : Nonempty (T ↪ Fin (2 ^ a')) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  let j : (T ↪ Fin (2 ^ a')) → (T → Fin (2 ^ a')) := fun e i => e i
  have hj : Function.Injective j := fun _ _ h => DFunLike.ext' h
  let InjSet : Finset (T → Fin (2 ^ a')) := univ.image j
  have hInj_ne : InjSet.Nonempty := univ_nonempty.image j
  have hmap_eq : (PMF.uniformOfFintype (T ↪ Fin (2 ^ a'))).map j =
      PMF.uniformOfFinset InjSet hInj_ne := by
    ext f
    simp only [PMF.map_apply, PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply,
      tsum_fintype, InjSet, card_image_of_injective univ hj, card_univ]
    by_cases hf : f ∈ univ.image j
    · obtain ⟨e, _, rfl⟩ := mem_image.mp hf
      simp only [hf, ↓reduceIte, eq_comm (a := j e), hj.eq_iff, Fintype.sum_ite_eq']
    · have hnone : ∀ e : T ↪ Fin (2 ^ a'), f ≠ j e :=
        fun e h => hf (h ▸ mem_image_of_mem j (mem_univ e))
      simp [hf, hnone]
  have hunif_eq : PMF.uniformOfFintype (T → Fin (2 ^ a')) =
      PMF.uniformOfFinset (univ : Finset (T → Fin (2 ^ a'))) univ_nonempty := by
    ext f
    simp [PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply]
  rw [hmap_eq, hunif_eq, dist_uniformOfFinset_of_card_le hInj_ne univ_nonempty (card_le_univ _),
    card_univ]
  have hsub : #(univ \ InjSet) ≤
      #(univ.filter fun f : T → Fin (2 ^ a') => ¬ Function.Injective f) := by
    refine card_le_card fun f hf => ?_
    rw [mem_sdiff] at hf
    rw [mem_filter]
    exact ⟨mem_univ f, fun hfinj => hf.2 (mem_image.mpr ⟨⟨f, hfinj⟩, mem_univ _, rfl⟩)⟩
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr hsub) (Nat.cast_nonneg _)).trans
    (ratio_not_injective_fun_le a')

/-- Uniform `k`-wise hash family mapped on a finite input domain of size `≤ κ` is uniform. -/
theorem uniformOfFintype_map_of_isKWise {ι X Y : Type*}
    [Fintype ι] [Nonempty ι] [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    {κ : ℕ} {h : ι → X → Y} (hh : IsKWiseIndependentHash κ h) (hX : Fintype.card X ≤ κ) :
    (PMF.uniformOfFintype ι).map h = PMF.uniformOfFintype (X → Y) := by
  classical
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [toReal_uniformOfFintype_map_apply]
  let y' : (x : (univ : Finset X)) → Y := fun x => y x.1
  have hcard : #(univ : Finset X) ≤ κ := by simpa using hX
  have hset : (univ.filter fun s : ι => h s = y) =
      (univ.filter fun s : ι => (univ : Finset X).restrict (h s) = y') := by
    ext s
    simp only [mem_filter, mem_univ, true_and, funext_iff, restrict]
    exact ⟨fun hs x => hs x.1, fun hs x => hs ⟨x, mem_univ x⟩⟩
  rw [hset, hh.dens_filter_restrict_eq hcard y']
  simp [PMF.uniformOfFintype_apply, Fintype.card_pi]

/-- Averaging `dist (f a) U` over a uniform draw `a ← PMF.uniformOfFintype α` given
`dist (f a) U ≤ b` on `Good : Set α`. -/
theorem dist_bind_uniform_of_good {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (f : α → PMF β) (U : PMF β) (Good : Set α) {b : ℝ} (hb : 0 ≤ b)
    (hgood : ∀ a ∈ Good, dist (f a) U ≤ b) :
    dist ((PMF.uniformOfFintype α).bind f) U ≤
      ((PMF.uniformOfFintype α).toOuterMeasure Goodᶜ).toReal + b := by
  classical
  calc dist ((PMF.uniformOfFintype α).bind f) U
      ≤ ∑ a : α, ((PMF.uniformOfFintype α) a).toReal * dist (f a) U := dist_bind_left_le _ _ _
    _ ≤ ∑ a : α, ((if a ∈ Goodᶜ then ((PMF.uniformOfFintype α) a).toReal else 0) +
          ((PMF.uniformOfFintype α) a).toReal * b) := by
        refine sum_le_sum fun a _ => ?_
        by_cases ha : a ∈ Good
        · simp only [Set.mem_compl_iff, ha, not_true_eq_false, ↓reduceIte, zero_add]
          exact mul_le_mul_of_nonneg_left (hgood a ha) ENNReal.toReal_nonneg
        · simp only [Set.mem_compl_iff, ha, not_false_eq_true, ↓reduceIte]
          have hle1 := mul_le_mul_of_nonneg_left (dist_le_one (f a) U)
            (ENNReal.toReal_nonneg (a := (PMF.uniformOfFintype α) a))
          linarith [mul_nonneg (ENNReal.toReal_nonneg (a := (PMF.uniformOfFintype α) a)) hb]
    _ = ((PMF.uniformOfFintype α).toOuterMeasure Goodᶜ).toReal + b := by
        rw [sum_add_distrib, ← sum_mul, sum_toReal, one_mul, toOuterMeasure_apply_toReal]
        congr 1
        exact sum_congr rfl fun a _ => by by_cases ha : a ∈ Goodᶜ <;> simp [ha]

/-- Falling-factorial lower bound `A ^ r ≤ 2 * A.descFactorial r` whenever `2 * r ^ 2 ≤ A`. -/
theorem pow_le_two_mul_descFactorial {A r : ℕ} (h : 2 * r ^ 2 ≤ A) :
    A ^ r ≤ 2 * A.descFactorial r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hrA : r ≤ A := by nlinarith
  have hsub_le : ∀ j ≤ r, (A - r) ^ j ≤ A.descFactorial j := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Nat.descFactorial_succ, Nat.mul_comm (A - j)]
      exact Nat.mul_le_mul (ih (Nat.le_of_succ_le hj)) (by omega)
  have hbern : ∀ k : ℕ, 1 ≤ k → A ^ k ≤ (A - r) ^ k + k * r * A ^ (k - 1) := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
    induction m with
    | zero => simp; omega
    | succ m ih =>
      have ih' := ih (Nat.succ_pos m)
      have hsplit : (A - r) + r = A := Nat.sub_add_cancel hrA
      have h1 : (A - r) ^ (m + 1) ≤ A ^ (m + 1) := Nat.pow_le_pow_left (Nat.sub_le A r) _
      calc A ^ (m + 2)
          = A ^ (m + 1) * A := pow_succ A (m + 1)
        _ ≤ ((A - r) ^ (m + 1) + (m + 1) * r * A ^ m) * A := Nat.mul_le_mul_right A ih'
        _ = (A - r) ^ (m + 1) * ((A - r) + r) + (m + 1) * r * A ^ (m + 1) := by
            rw [hsplit]; ring
        _ = (A - r) ^ (m + 2) + r * (A - r) ^ (m + 1) + (m + 1) * r * A ^ (m + 1) := by ring
        _ ≤ (A - r) ^ (m + 2) + r * A ^ (m + 1) + (m + 1) * r * A ^ (m + 1) :=
            Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left r h1) _) _
        _ = (A - r) ^ (m + 2) + (m + 2) * r * A ^ (m + 1) := by ring
  have htop := hbern r hr
  have h2r : 2 * r * r * A ^ (r - 1) ≤ A ^ r := by
    calc 2 * r * r * A ^ (r - 1) = (2 * r ^ 2) * A ^ (r - 1) := by ring
      _ ≤ A * A ^ (r - 1) := Nat.mul_le_mul_right _ h
      _ = A ^ r := by rw [← pow_succ', Nat.sub_add_cancel hr]
  have h2sub : A ^ r ≤ 2 * (A - r) ^ r := by linarith
  exact h2sub.trans (Nat.mul_le_mul_left 2 (hsub_le r le_rfl))

/-- **Per-coordinate without-replacement upper bound**: for any per-coordinate target sets
`Q : T → Finset α` and `2 * |T| ^ 2 ≤ |α|`, a uniform injection `e ← PMF.uniformOfFintype (T ↪ α)`
lands in `∏ᵢ Q i` with probability at most `2 * ∏ᵢ (#(Q i) / |α|)`. -/
theorem prob_uniformOfFintype_embedding_forall_mem_perKey_le {T α : Type*}
    [Fintype T] [DecidableEq T] [Fintype α] [DecidableEq α] [Nonempty α]
    (hcard2 : 2 * (Fintype.card T) ^ 2 ≤ Fintype.card α) (Q : T → Finset α) :
    haveI : Nonempty (T ↪ α) := Function.Embedding.nonempty_of_card_le (by nlinarith)
    ((PMF.uniformOfFintype (T ↪ α)).toOuterMeasure {e : T ↪ α | ∀ i : T, e i ∈ Q i}).toReal ≤
      2 * ∏ i : T, ((#(Q i) : ℝ) / (Fintype.card α : ℝ)) := by
  classical
  have hT : Fintype.card T ≤ Fintype.card α := by nlinarith
  haveI : Nonempty (T ↪ α) := Function.Embedding.nonempty_of_card_le hT
  let E : Set (T ↪ α) := {e : T ↪ α | ∀ i : T, e i ∈ Q i}
  let toPi : {e : T ↪ α // e ∈ E} ↪ ((i : T) → Q i) :=
    { toFun := fun ⟨e, he⟩ i => ⟨e i, he i⟩
      inj' := fun ⟨_, _⟩ ⟨_, _⟩ h =>
        Subtype.ext (DFunLike.ext _ _ fun i => congrArg Subtype.val (congrFun h i)) }
  have hcard_good : #(univ.filter (· ∈ E)) ≤ ∏ i : T, #(Q i) := by
    calc #(univ.filter (· ∈ E))
        = Fintype.card {e : T ↪ α // e ∈ E} := (Fintype.card_subtype _).symm
      _ ≤ Fintype.card ((i : T) → Q i) := Fintype.card_le_of_injective toPi toPi.injective
      _ = ∏ i : T, #(Q i) := by simp [Fintype.card_pi]
  change ((PMF.uniformOfFintype (T ↪ α)).toOuterMeasure E).toReal ≤ _
  rw [toOuterMeasure_uniformOfFintype_toReal, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, ← mul_div_assoc]
  have hcard_emb : Fintype.card (T ↪ α) = (Fintype.card α).descFactorial (Fintype.card T) :=
    Fintype.card_embedding_eq
  have hdesc_pos : 0 < (Fintype.card α).descFactorial (Fintype.card T) :=
    hcard_emb ▸ Fintype.card_pos
  have hα_pos : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [hcard_emb, div_le_div_iff₀ (Nat.cast_pos.mpr hdesc_pos) (pow_pos hα_pos _)]
  have hnat :
      #(univ.filter (· ∈ E)) * Fintype.card α ^ Fintype.card T ≤
        (2 * ∏ i : T, #(Q i)) * (Fintype.card α).descFactorial (Fintype.card T) := by
    calc #(univ.filter (· ∈ E)) * Fintype.card α ^ Fintype.card T
        ≤ (∏ i : T, #(Q i)) * (2 * (Fintype.card α).descFactorial (Fintype.card T)) :=
          Nat.mul_le_mul hcard_good (pow_le_two_mul_descFactorial hcard2)
      _ = (2 * ∏ i : T, #(Q i)) * (Fintype.card α).descFactorial (Fintype.card T) := by ring
  exact_mod_cast hnat


end Cslib.DataStructure.Dictionary.KickTree
