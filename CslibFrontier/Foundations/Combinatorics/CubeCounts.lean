/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Pi.Interval
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Probability.BoundedDifferences
import CslibFrontier.Probability.Product
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Foundations.Data.Nat.Choose.MaxTerm
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Counting small and large vectors in a cube

Two counts that bound the tables of the trimmed convolution in `[r]^d`
([ChanItakuraMaYu2026], Lemma 3.2 and the proof of Theorem 3.4), for vectors `x : ι → ℕ` with
`d = |ι|` coordinates and size `∑ i, x i`.

* **Few small vectors** (`card_cube_sum_le_le`): the vectors of the cube `[r]^d` (every
  coordinate below `r`) of size at most `s` number at most
  `r ^ d exp (-2 ε ^ 2 / (d (r - 1) ^ 2))` whenever `s ≤ d (r - 1) / 2 - ε`. This is the paper's
  Chernoff bound on `H_r(d, ≤ s)`, as McDiarmid's inequality for the size of a uniform vector of
  the cube (`Cslib.Probability.HasBoundedDifferences.pi_le_mean_sub`). For
  `s ≤ (1 - δ) d (r - 1) / 2` the bound is `r ^ d exp (-δ ^ 2 d / 2)`
  (`card_cube_sum_le_le_of_le_mul`).
* **Few large vectors below a vector** (`card_Iic_filter_le_sum_le`): the vectors `y ≤ C` of size
  at least `s` number at most `∑_{j ≤ t - s} (t choose j)` for `t = ∑ i, C i`. This is the paper's
  bound `H_r(d, t, ≥ s) ≤ binom(t, ≥ s)`, here for every `C` of size `t` and not only for its
  maximum. Removing `y` from `C` leaves a vector of size at most `t - s`, and the vectors below `C`
  of size `j` inject into the `j`-subsets of a set of `t` elements. With the entropy-tight bound of
  `Nat.sum_choose_mul_pow_mul_pow_le_pow` it gives
  `count · m ^ m (t - m) ^ (t - m) ≤ t ^ t` for `m = t - s ≤ t / 2`
  (`card_Iic_filter_le_mul_pow_mul_pow_le`).

These are explicit inequalities for every `r`, `d`, `s` and `C`; the asymptotic forms of the paper
(`2 ^ (-Θ(δ² d))`, `(1/δ) ^ O(δ r d)`) are not stated.

**Constants.** The paper cites "a Chernoff bound" for `H_r(d, ≤ s) ≤ r ^ d 2 ^ (-Θ(δ² d))` without
an explicit constant. The bound here is the Hoeffding/McDiarmid form for coordinates in
`[0, r - 1]`, `exp (-δ ^ 2 d / 2)`, whose constant does not depend on `r`; it is of the paper's form
`2 ^ (-c δ² d)` with `c = 1 / (2 ln 2)`. A sharper Chernoff bound for the uniform distribution on
`[r]` (whose variance is about `(r - 1) ^ 2 / 12`, not the worst case `(r - 1) ^ 2 / 4`) would
improve the constant; that is not needed for the paper's `Θ` and is not proved.

## Main results

* `Cslib.card_cube_sum_le_le`, `Cslib.card_cube_sum_le_le_of_le_mul`: few small vectors.
* `Cslib.card_Iic_filter_le_sum_le`, `Cslib.card_Iic_filter_le_mul_pow_mul_pow_le`: few large
  vectors below a vector.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
* [C. McDiarmid, *On the method of bounded differences*][McDiarmid1989], Lemma 1.2
-/

public section

namespace Cslib

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Small vectors of the cube -/

/-- The small vectors of the cube, as vectors of `ι → Fin r`. -/
private theorem card_cube_filter_eq (r s : ℕ) :
    #((Fintype.piFinset fun _ : ι => range r).filter fun x => ∑ i, x i ≤ s) =
      #((univ : Finset (ι → Fin r)).filter fun x => ∑ i, (x i : ℕ) ≤ s) := by
  symm
  refine card_bij (fun x _ => fun i => (x i : ℕ)) (fun x hx => ?_) (fun x _ y _ h => ?_)
    (fun y hy => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hx
    simp only [mem_filter, Fintype.mem_piFinset, mem_range, Fin.is_lt, implies_true, true_and]
    exact hx
  · funext i; exact Fin.ext (congrFun h i)
  · simp only [mem_filter, Fintype.mem_piFinset, mem_range] at hy
    exact ⟨fun i => ⟨y i, hy.1 i⟩, by simpa using hy.2, rfl⟩

private theorem sum_fin_cast (r : ℕ) : ∑ a : Fin r, ((a : ℕ) : ℝ) = r * (r - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (k : ℝ)) r]
  have h := Finset.sum_range_id_mul_two r
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have h' : ((∑ i ∈ range r, i : ℕ) : ℝ) * 2 = r * ((r - 1 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hr.ne')] at h'
  linarith

/-- **Few small vectors of the cube** (the Chernoff bound on `H_r(d, ≤ s)` in
[ChanItakuraMaYu2026], proof of Theorem 3.4): if `s ≤ d (r - 1) / 2 - ε` with `ε ≥ 0`, at most
`r ^ d exp (-2 ε ^ 2 / (d (r - 1) ^ 2))` vectors of `[r]^d` have size at most `s`. -/
theorem card_cube_sum_le_le {r s : ℕ} (hr : 0 < r) {ε : ℝ} (hε : 0 ≤ ε)
    (hs : (s : ℝ) ≤ Fintype.card ι * (r - 1) / 2 - ε) :
    (#((Fintype.piFinset fun _ : ι => range r).filter fun x => ∑ i, x i ≤ s) : ℝ) ≤
      r ^ Fintype.card ι * exp (-2 * ε ^ 2 / (Fintype.card ι * (r - 1) ^ 2)) := by
  have : NeZero r := ⟨hr.ne'⟩
  set p : ι → PMF (Fin r) := fun _ => Probability.PMF.uniformOfFintype (Fin r)
  set f : (ι → Fin r) → ℝ := fun x => ∑ i, ((x i : ℕ) : ℝ)
  have hbd : Probability.HasBoundedDifferences f fun _ => ((r : ℝ) - 1) :=
    Probability.hasBoundedDifferences_sum (α := fun _ => Fin r)
      (score := fun _ a => ((a : ℕ) : ℝ)) fun _ a b => by
        have ha := a.is_lt; have hb := b.is_lt
        rw [abs_le]
        constructor
        · have : (b : ℝ) ≤ r - 1 := by
            have : (b : ℕ) + 1 ≤ r := hb
            have : ((b : ℕ) : ℝ) + 1 ≤ r := by exact_mod_cast this
            linarith
          have : (0 : ℝ) ≤ (a : ℕ) := Nat.cast_nonneg _
          linarith
        · have : ((a : ℕ) : ℝ) + 1 ≤ r := by exact_mod_cast ha
          have : (0 : ℝ) ≤ (b : ℕ) := Nat.cast_nonneg _
          linarith
  have hmean : ∑ y, (Probability.PMF.pi p y).toReal * f y = Fintype.card ι * (r - 1) / 2 := by
    rw [Probability.PMF.sum_pi_mul_sum (score := fun _ (a : Fin r) => ((a : ℕ) : ℝ))]
    simp only [p, Probability.PMF.uniformOfFintype_apply, Fintype.card_fin]
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ← mul_sum, sum_fin_cast, sum_const,
      card_univ, nsmul_eq_mul]
    field_simp
  have h := hbd.pi_le_mean_sub p hε
  rw [hmean] at h
  have hsub : {x : ι → Fin r | ∑ i, (x i : ℕ) ≤ s} ⊆
      {x | f x ≤ Fintype.card ι * (r - 1) / 2 - ε} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have : f x ≤ s := by simp only [f]; exact_mod_cast hx
    linarith
  have hmono := ENNReal.toReal_mono
    (by
      change (Probability.PMF.pi p).toOuterMeasure _ ≠ ⊤
      rw [PMF.toOuterMeasure_apply]
      exact PMF.tsum_coe_indicator_ne_top _ _)
    ((Probability.PMF.pi p).toOuterMeasure.mono hsub)
  have hcard : (#((univ : Finset (ι → Fin r)).filter fun x => ∑ i, (x i : ℕ) ≤ s) : ℝ) =
      r ^ Fintype.card ι * ((Probability.PMF.pi p).toOuterMeasure
        {x : ι → Fin r | ∑ i, (x i : ℕ) ≤ s}).toReal := by
    rw [show Probability.PMF.pi p = _ from Probability.PMF.pi_uniformOfFintype,
      Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, Fintype.card_fun, Fintype.card_fin]
    have : (0 : ℝ) < r ^ Fintype.card ι := by positivity
    push_cast
    field_simp
    rfl
  have hsq : ∑ _i : ι, ((r : ℝ) - 1) ^ 2 = (Fintype.card ι : ℝ) * ((r : ℝ) - 1) ^ 2 := by
    rw [sum_const, card_univ, nsmul_eq_mul]
  rw [card_cube_filter_eq, hcard]
  rw [hsq] at h
  exact mul_le_mul_of_nonneg_left (hmono.trans h) (by positivity)

/-- **Few small vectors of the cube, relative form**: if `s ≤ (1 - δ) d (r - 1) / 2` with
`0 ≤ δ ≤ 1`, at most `r ^ d exp (-δ ^ 2 d / 2)` vectors of `[r]^d` have size at most `s`. -/
theorem card_cube_sum_le_le_of_le_mul {r s : ℕ} (hr : 1 < r) {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : (s : ℝ) ≤ (1 - δ) * (Fintype.card ι * (r - 1) / 2)) :
    (#((Fintype.piFinset fun _ : ι => range r).filter fun x => ∑ i, x i ≤ s) : ℝ) ≤
      r ^ Fintype.card ι * exp (-(δ ^ 2 * Fintype.card ι / 2)) := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hε : 0 ≤ δ * (Fintype.card ι * (r - 1) / 2) := by
    have : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ r - 1 := by linarith
    positivity
  refine (card_cube_sum_le_le (by omega) hε (by linarith)).trans_eq ?_
  congr 2
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hd | hd
  · simp [hd]
  · have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
    have : (r : ℝ) - 1 ≠ 0 := by linarith
    field_simp

/-! ### Large vectors below a vector -/

/-- The cells of the blocks of `C`: `C i` cells for each coordinate `i`. -/
private abbrev blockCells (C : ι → ℕ) : Finset (Σ _ : ι, ℕ) := univ.sigma fun i => range (C i)

/-- The cells of `C` not covered by `y`: in block `i`, the cells `k` with `y i ≤ k < C i`. -/
private abbrev restCells (C y : ι → ℕ) : Finset (Σ _ : ι, ℕ) :=
  (blockCells C).filter fun q => y q.1 ≤ q.2

omit [DecidableEq ι] in
private theorem card_restCells (C y : ι → ℕ) : #(restCells C y) = ∑ i, (C i - y i) := by
  have : restCells C y = univ.sigma fun i => Ico (y i) (C i) := by
    ext ⟨i, k⟩
    simp only [mem_filter, mem_sigma, mem_univ, mem_range, mem_Ico, true_and]
    tauto
  rw [this, card_sigma]
  simp

omit [DecidableEq ι] in
private theorem mem_restCells {C y : ι → ℕ} {i : ι} {k : ℕ} :
    (⟨i, k⟩ : Σ _ : ι, ℕ) ∈ restCells C y ↔ k < C i ∧ y i ≤ k := by
  simp [mem_filter, mem_sigma]

/-- **Few large vectors below a vector** (the paper's `H_r(d, t, ≥ s) ≤ binom(t, ≥ s)`): the
vectors `y ≤ C` of size at least `s` number at most `∑_{j ≤ t - s} (t choose j)`, where
`t = ∑ i, C i`. -/
theorem card_Iic_filter_le_sum_le (C : ι → ℕ) (s : ℕ) :
    #((Iic C).filter fun y => s ≤ ∑ i, y i) ≤
      ∑ j ∈ range (∑ i, C i - s + 1), (∑ i, C i).choose j := by
  set t := ∑ i, C i
  have hU : #(blockCells C) = t := by rw [card_sigma]; simp [t]
  have hmaps : ∀ y ∈ (Iic C).filter (fun y => s ≤ ∑ i, y i),
      restCells C y ∈ (range (t - s + 1)).biUnion fun j => (blockCells C).powersetCard j := by
    intro y hy
    obtain ⟨hyC, hys⟩ := mem_filter.mp hy
    have hyC : ∀ i, y i ≤ C i := mem_Iic.mp hyC
    have hcard : #(restCells C y) = t - ∑ i, y i := by
      rw [card_restCells, sum_tsub_distrib _ fun i _ => hyC i]
    refine mem_biUnion.mpr ⟨#(restCells C y), mem_range.mpr (by omega),
      mem_powersetCard.mpr ⟨filter_subset _ _, rfl⟩⟩
  have hinj : Set.InjOn (restCells C) ((Iic C).filter fun y => s ≤ ∑ i, y i) := by
    intro y hy y' hy' h
    have hyC : ∀ i, y i ≤ C i := mem_Iic.mp (mem_filter.mp hy).1
    have hyC' : ∀ i, y' i ≤ C i := mem_Iic.mp (mem_filter.mp hy').1
    funext i
    have key : ∀ k, (k < C i ∧ y i ≤ k) ↔ (k < C i ∧ y' i ≤ k) := fun k => by
      rw [← mem_restCells, ← mem_restCells, h]
    have h1 := key (y i)
    have h2 := key (y' i)
    have := hyC i
    have := hyC' i
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd (h1.mp ⟨by omega, le_rfl⟩).2 (by omega)
    · exact absurd (h2.mpr ⟨by omega, le_rfl⟩).2 (by omega)
  refine (card_le_card_of_injOn _ hmaps hinj).trans ((card_biUnion_le).trans ?_)
  exact (sum_congr rfl fun j _ => by rw [card_powersetCard, hU]).le

/-- **Large vectors below a vector, entropy form**: for `m = t - s ≤ t - m`, the count of
`card_Iic_filter_le_sum_le` times `m ^ m (t - m) ^ (t - m)` is at most `t ^ t`. -/
theorem card_Iic_filter_le_mul_pow_mul_pow_le (C : ι → ℕ) (s : ℕ)
    (hm : ∑ i, C i - s ≤ ∑ i, C i - (∑ i, C i - s)) :
    #((Iic C).filter fun y => s ≤ ∑ i, y i) *
        ((∑ i, C i - s) ^ (∑ i, C i - s) *
          (∑ i, C i - (∑ i, C i - s)) ^ (∑ i, C i - (∑ i, C i - s))) ≤
      (∑ i, C i) ^ ∑ i, C i :=
  (Nat.mul_le_mul_right _ (card_Iic_filter_le_sum_le C s)).trans
    (Nat.sum_choose_mul_pow_mul_pow_le_pow hm)

end Cslib
