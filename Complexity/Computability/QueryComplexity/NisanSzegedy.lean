/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.ApproximateDegree
public import Complexity.Computability.QueryComplexity.Huang
public import Complexity.Computability.QueryComplexity.Relations
import Complexity.Foundations.Analysis.MarkovBrothersInequality
import Complexity.Foundations.BooleanAnalysis.Symmetrization
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

/-!
# The Nisan–Szegedy bounds

Block sensitivity is at most quadratic in the degree and in the approximate degree:
`bs(f) ≤ 2 deg(f)²` and `bs(f) ≤ 6 adeg(f)²` with `adeg = adeg_{1/3}` [NisanSzegedy1994].

Both follow from one argument (`QueryComplexity.one_sub_two_mul_mul_blockSensitivity_le`). Let a
real function `p` of degree at most `D` be within `ε < 1/2` of `f`, and let `x` have `b = bs(f)`
pairwise disjoint sensitive blocks `B₁, …, B_b`. Normalizing so that `f(x)` reads as `0`, the
function `g(y) = p(x ⊕ ⋃_{yⱼ = 1} Bⱼ)` on `{0,1}ᵇ` still has degree at most `D`
(`BitString.comp_mem_lowDegree`), lies in `[-ε, 1 + ε]`, is at most `ε` at `0` and at least
`1 - ε` at each unit vector. Its Minsky–Papert symmetrization `q`
(`BitString.exists_natDegree_le_eval_eq_layerAverage`) is a univariate polynomial of degree at
most `D` with the same bounds at the integers `0, …, b`, and the mean value theorem gives a point
of `[0, 1]` where `q' ≥ 1 - 2ε`. The Nisan–Szegedy lemma, a consequence of Markov's inequality
(`Polynomial.mul_le_sq_mul_of_le_abs_eval_derivative`), then gives
`(1 - 2ε) b ≤ D² (1 - 2ε + 1 + 2ε) = 2 D²`. If `p` takes values in `[-δ, 1 + δ]`, the same
argument gives `(1 - 2ε) b ≤ (2 - 2ε + 2δ) D²`
(`QueryComplexity.one_sub_two_mul_mul_blockSensitivity_le_of_mem_Icc`). The case `δ = 0`, of a
polynomial that is a probability, is the step in the proof of Theorem 4.13 of
[BealsBuhrmanCleveMoscaDeWolf2001] (arXiv:quant-ph/9802049v3) that gives `bs(f) ≤ 16 T²` for
`T`-query quantum algorithms (`Cslib.Quantum.blockSensitivity_le_sixteen_mul_sq`).

With Huang's theorem `deg(f) ≤ s(f)²` this gives `bs(f) ≤ 2 s(f)⁴`, and with
`D(f) ≤ bs(f)³` [BealsBuhrmanCleveMoscaDeWolf2001] it gives `D(f) ≤ 216 adeg(f)⁶`.
The sharper exact-degree bound `D(f) ≤ 2 deg(f)³` is proved in
`Complexity.Computability.QueryComplexity.Midrijanis`.

## Main results

* `Cslib.QueryComplexity.one_sub_two_mul_mul_blockSensitivity_le_of_mem_lowDegree`: a real
  function of degree at most `D` within `ε` of `f` gives `(1 - 2ε) bs(f) ≤ 2 D²`.
* `Cslib.QueryComplexity.one_sub_two_mul_mul_blockSensitivity_le_of_mem_Icc`: if it also takes
  values in `[-δ, 1 + δ]` and `ε < 1/2`, then `(1 - 2ε) bs(f) ≤ (2 - 2ε + 2δ) D²`.
* `Cslib.QueryComplexity.blockSensitivity_le_two_mul_degree_sq`: `bs(f) ≤ 2 deg(f)²`.
* `Cslib.QueryComplexity.one_sub_two_mul_mul_blockSensitivity_le`:
  `(1 - 2ε) bs(f) ≤ 2 adeg_ε(f)²`.
* `Cslib.QueryComplexity.blockSensitivity_le_six_mul_approxDegree_sq`:
  `bs(f) ≤ 6 adeg_{1/3}(f)²`.
* `Cslib.QueryComplexity.blockSensitivity_le_two_mul_sensitivity_pow_four`: `bs(f) ≤ 2 s(f)⁴`.
* `Cslib.DecisionTree.complexity_le_mul_approxDegree_pow_six`: `D(f) ≤ 216 adeg_{1/3}(f)⁶`.

## References

* [N. Nisan, M. Szegedy, *On the degree of Boolean functions as real polynomials*][NisanSzegedy1994]
* [R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf, *Quantum lower bounds by
  polynomials*][BealsBuhrmanCleveMoscaDeWolf2001]
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Cslib

open Finset BitString Polynomial

namespace QueryComplexity

variable {n : ℕ} {f : BooleanFunction n}

/-- Flip in `x` the blocks `B j` of the coordinates `j` set in `y`. -/
private def flipBlocks {m : ℕ} (B : Fin m → Block n) (x : BitString n) (y : BitString m) :
    BitString n :=
  flipBlock (({j | y j = true} : Finset (Fin m)).biUnion B) x

/-- With pairwise disjoint blocks, each bit of `flipBlocks B x y` is a bit of `x`, or that bit
flipped by one bit of `y`, so it has degree at most `1` as a function of `y`. -/
private theorem bitVal_flipBlocks_mem_lowDegree {m : ℕ} {B : Fin m → Block n}
    (hB : Pairwise fun j j' => Disjoint (B j) (B j')) (x : BitString n) (i : Fin n) :
    (fun y => bitVal ℝ (flipBlocks B x y i)) ∈ lowDegree ℝ (Fin m) 1 := by
  by_cases hi : ∃ j, i ∈ B j
  · obtain ⟨j, hj⟩ := hi
    have hmem (y : BitString m) :
        i ∈ ({j | y j = true} : Finset (Fin m)).biUnion B ↔ y j = true := by
      simp only [mem_biUnion, mem_filter, mem_univ, true_and]
      refine ⟨fun ⟨j', hj', hij'⟩ => ?_, fun h => ⟨j, h, hj⟩⟩
      by_cases hjj : j' = j
      · exact hjj ▸ hj'
      · exact absurd (hB hjj) (Finset.not_disjoint_iff.2 ⟨i, hij', hj⟩)
    have h : (fun y => bitVal ℝ (flipBlocks B x y i)) = fun y => bitVal ℝ (x i ^^ y j) := by
      funext y
      unfold flipBlocks
      by_cases hy : y j = true
      · rw [flipBlock_apply_of_mem ((hmem y).2 hy), hy, Bool.xor_true]
      · rw [flipBlock_apply_of_notMem (mt (hmem y).1 hy), Bool.eq_false_iff.2 hy,
          Bool.xor_false]
    rw [h]
    cases x i
    · simpa using bitVal_mem_lowDegree (R := ℝ) j
    · have := one_sub_mem_lowDegree (bitVal_mem_lowDegree (R := ℝ) j)
      convert this using 1
      funext y
      simp [bitVal_not]
  · push Not at hi
    have h : (fun y => bitVal ℝ (flipBlocks B x y i)) = fun _ => bitVal ℝ (x i) := by
      funext y
      unfold flipBlocks
      rw [flipBlock_apply_of_notMem]
      simp only [mem_biUnion, not_exists, not_and]
      exact fun j _ => hi j
    rw [h]
    exact const_mem_lowDegree 1 _

private theorem bitVal_mem_Icc (b : Bool) : bitVal ℝ b ∈ Set.Icc (0 : ℝ) 1 := by
  cases b <;> simp

/-- **The Nisan–Szegedy argument with a range**: if a real function of degree at most `D` is within
`ε < 1/2` of `f` at every input and takes values in `[-δ, 1 + δ]`, then
`(1 - 2ε) bs(f) ≤ (2 - 2ε + 2δ) D²`. A function within `ε` of `f` takes values in `[-ε, 1 + ε]`,
which gives `2 D²`; a probability, with values in `[0, 1]`, gives `(2 - 2ε) D²`. -/
theorem one_sub_two_mul_mul_blockSensitivity_le_of_mem_Icc {p : BitString n → ℝ} {D : ℕ}
    (hp : p ∈ lowDegree ℝ (Fin n) D) {ε δ : ℝ} (hpf : ∀ x, |p x - bitVal ℝ (f x)| ≤ ε)
    (hpI : ∀ x, p x ∈ Set.Icc (-δ) (1 + δ)) (hε2 : 2 * ε < 1) :
    (1 - 2 * ε) * blockSensitivity f ≤ (2 - 2 * ε + 2 * δ) * D ^ 2 := by
  have hε : 0 < 1 - 2 * ε := by linarith
  have hδ : 0 ≤ 2 - 2 * ε + 2 * δ := by
    have := hpI fun _ => false
    linarith [this.1, this.2]
  -- an input and a family of pairwise disjoint sensitive blocks attaining `bs(f)`
  obtain ⟨x, -, hx⟩ := exists_mem_eq_sup univ univ_nonempty (blockSensitivityAt f)
  obtain ⟨F, hF, hFcard⟩ := exists_mem_eq_sup (sensitiveFamilies f x)
    ⟨∅, mem_sensitiveFamilies.2 ⟨by simp, by simp⟩⟩ card
  rw [mem_sensitiveFamilies] at hF
  rw [blockSensitivity, hx, blockSensitivityAt, hFcard]
  set m := #F
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm, Nat.cast_zero, mul_zero]
    exact mul_nonneg hδ (by positivity)
  set B : Fin m → Block n := fun j => (F.equivFin.symm j : Block n)
  have hBF (j : Fin m) : B j ∈ F := (F.equivFin.symm j).2
  have hBinj : Function.Injective B := fun j j' h =>
    F.equivFin.symm.injective (Subtype.ext h)
  have hB : Pairwise fun j j' => Disjoint (B j) (B j') := fun j j' hjj =>
    hF.2 (hBF j) (hBF j') (hBinj.ne hjj)
  -- normalize so that `f x` reads as `0`
  set h : BitString n → ℝ := fun z => if f x then 1 - p z else p z
  have hh : h ∈ lowDegree ℝ (Fin n) D := by
    cases hfx : f x
    · simpa [h, hfx] using hp
    · convert one_sub_mem_lowDegree hp using 1
      funext z
      simp [h, hfx]
  have hhf (z : BitString n) : |h z - bitVal ℝ (f z ^^ f x)| ≤ ε := by
    have := hpf z
    cases hfx : f x
    · simpa [h, hfx] using this
    · rw [← abs_neg] at this
      convert this using 2
      simp only [h, hfx, ↓reduceIte, Bool.xor_true, bitVal_not]
      ring
  -- the restriction to the subcube spanned by the blocks
  set g : BitString m → ℝ := fun y => h (flipBlocks B x y)
  have hg : g ∈ lowDegree ℝ (Fin m) D :=
    comp_mem_lowDegree (bitVal_flipBlocks_mem_lowDegree hB x) hh
  have hgI (y : BitString m) : g y ∈ Set.Icc (-δ) (1 + δ) := by
    have h₁ := hpI (flipBlocks B x y)
    simp only [g, h]
    split_ifs
    · exact ⟨by linarith [h₁.2], by linarith [h₁.1]⟩
    · exact h₁
  have hg₀ (y : BitString m) (hy : weight y = 0) : g y ≤ ε := by
    have hy' : ({j | y j = true} : Finset (Fin m)) = ∅ := card_eq_zero.1 hy
    have := (abs_le.1 (hhf (flipBlocks B x y))).2
    simp only [flipBlocks, hy', biUnion_empty, flipBlock_empty, Bool.xor_self, bitVal_false]
      at this
    change h (flipBlocks B x y) ≤ ε
    simp only [flipBlocks, hy', biUnion_empty, flipBlock_empty]
    linarith
  have hg₁ (y : BitString m) (hy : weight y = 1) : 1 - ε ≤ g y := by
    obtain ⟨j, hj⟩ := card_eq_one.1 hy
    have := (abs_le.1 (hhf (flipBlocks B x y))).1
    have hsens : f (flipBlock (B j) x) ≠ f x := hF.1 _ (hBF j)
    have hxor : (f (flipBlock (B j) x) ^^ f x) = true := by
      cases h₁ : f (flipBlock (B j) x) <;> cases h₂ : f x <;> simp_all
    simp only [flipBlocks, hj, singleton_biUnion, hxor, bitVal_true] at this
    change 1 - ε ≤ h (flipBlocks B x y)
    simp only [flipBlocks, hj, singleton_biUnion]
    linarith
  -- its symmetrization
  obtain ⟨q, hqdeg, hq⟩ := exists_natDegree_le_eval_eq_layerAverage hg
  have hlayer {k : ℕ} (hk : k ≤ m) :
      ({x : BitString m | weight x = k} : Finset (BitString m)).Nonempty :=
    weightLayer_nonempty hk
  have hqI (k : ℕ) (hk : k ≤ m) : q.eval (k : ℝ) ∈ Set.Icc (-δ) (1 + δ) := by
    rw [hq k (by rw [Fintype.card_fin]; exact hk), layerAverage]
    exact ⟨le_expect (hlayer hk) fun y _ => (hgI y).1,
      expect_le (hlayer hk) fun y _ => (hgI y).2⟩
  have hq₀ : q.eval 0 ≤ ε := by
    have := hq 0 (Nat.zero_le _)
    rw [Nat.cast_zero] at this
    rw [this, layerAverage]
    exact expect_le (hlayer (Nat.zero_le m)) fun y hy => hg₀ y (mem_filter.1 hy).2
  have hq₁ : 1 - ε ≤ q.eval 1 := by
    have := hq 1 (by rw [Fintype.card_fin]; exact hm)
    rw [Nat.cast_one] at this
    rw [this, layerAverage]
    exact le_expect (hlayer hm) fun y hy => hg₁ y (mem_filter.1 hy).2
  -- the mean value theorem on `[0, 1]`
  obtain ⟨ξ, hξ, hξq⟩ := exists_hasDerivAt_eq_slope (fun t => q.eval t)
    (fun t => (derivative q).eval t) zero_lt_one q.continuous.continuousOn
    fun t _ => q.hasDerivAt t
  rw [sub_zero, div_one] at hξq
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have := mul_le_sq_mul_of_le_abs_eval_derivative hqdeg hm hqI
    (ξ := ξ) (c := 1 - 2 * ε) ⟨hξ.1.le, hξ.2.le.trans hm1⟩ hε.le
    (by rw [hξq]; exact (by linarith : 1 - 2 * ε ≤ q.eval 1 - q.eval 0).trans (le_abs_self _))
  linarith

/-- **The Nisan–Szegedy argument**: if a real function of degree at most `D` is within `ε` of `f`
at every input, then `(1 - 2ε) bs(f) ≤ 2 D²`. -/
theorem one_sub_two_mul_mul_blockSensitivity_le_of_mem_lowDegree {p : BitString n → ℝ} {D : ℕ}
    (hp : p ∈ lowDegree ℝ (Fin n) D) {ε : ℝ} (hpf : ∀ x, |p x - bitVal ℝ (f x)| ≤ ε) :
    (1 - 2 * ε) * blockSensitivity f ≤ 2 * D ^ 2 := by
  rcases le_or_gt (1 - 2 * ε) 0 with hε | hε
  · exact (mul_nonpos_of_nonpos_of_nonneg hε (Nat.cast_nonneg _)).trans (by positivity)
  have := one_sub_two_mul_mul_blockSensitivity_le_of_mem_Icc hp hpf (δ := ε) (fun x => ?_)
    (by linarith)
  · linarith
  · have h₁ := abs_le.1 (hpf x)
    have h₂ := bitVal_mem_Icc (f x)
    exact ⟨by linarith [h₁.1, h₂.1], by linarith [h₁.2, h₂.2]⟩

/-- **Nisan–Szegedy**: `bs(f) ≤ 2 deg(f)²`. -/
theorem blockSensitivity_le_two_mul_degree_sq (f : BooleanFunction n) :
    blockSensitivity f ≤ 2 * degree f ^ 2 := by
  have := one_sub_two_mul_mul_blockSensitivity_le_of_mem_lowDegree (f := f)
    (p := fun x => bitVal ℝ (f x)) (mem_lowDegree_totalDegree _) (ε := 0) fun x => by simp
  rw [mul_zero, sub_zero, one_mul] at this
  exact_mod_cast this

/-- **Nisan–Szegedy for approximate degree**: `(1 - 2ε) bs(f) ≤ 2 adeg_ε(f)²` for `ε ≥ 0`. -/
theorem one_sub_two_mul_mul_blockSensitivity_le {ε : ℝ} (hε : 0 ≤ ε) (f : BooleanFunction n) :
    (1 - 2 * ε) * blockSensitivity f ≤ 2 * approxDegree ε f ^ 2 := by
  obtain ⟨p, hp, hpf⟩ := exists_mem_lowDegree_approxDegree (f := f) hε
  exact one_sub_two_mul_mul_blockSensitivity_le_of_mem_lowDegree hp hpf

/-- **Nisan–Szegedy**: `bs(f) ≤ 6 adeg(f)²`, for the approximate degree `adeg = adeg_{1/3}`. -/
theorem blockSensitivity_le_six_mul_approxDegree_sq (f : BooleanFunction n) :
    blockSensitivity f ≤ 6 * approxDegree (1 / 3) f ^ 2 := by
  have := one_sub_two_mul_mul_blockSensitivity_le (by norm_num : (0 : ℝ) ≤ 1 / 3) f
  have h : (blockSensitivity f : ℝ) ≤ 6 * approxDegree (1 / 3) f ^ 2 := by linarith
  exact_mod_cast h

/-- `bs(f) ≤ 2 s(f)⁴`, from Nisan–Szegedy and Huang's theorem `deg(f) ≤ s(f)²`. -/
theorem blockSensitivity_le_two_mul_sensitivity_pow_four (f : BooleanFunction n) :
    blockSensitivity f ≤ 2 * sensitivity f ^ 4 :=
  (blockSensitivity_le_two_mul_degree_sq f).trans (Nat.mul_le_mul_left 2 (by
    rw [show 4 = 2 * 2 from rfl, pow_mul]
    exact Nat.pow_le_pow_left (degree_le_sensitivity_sq f) 2))

end QueryComplexity

namespace DecisionTree

open QueryComplexity

variable {n : ℕ}

/-- `D(f) ≤ 216 adeg(f)⁶` for the approximate degree `adeg = adeg_{1/3}`, from `D(f) ≤ bs(f)³` and
`bs(f) ≤ 6 adeg(f)²`. -/
theorem complexity_le_mul_approxDegree_pow_six (f : BooleanFunction n) :
    complexity f ≤ 216 * approxDegree (1 / 3) f ^ 6 :=
  (complexity_le_blockSensitivity_pow_three f).trans
    ((Nat.pow_le_pow_left (blockSensitivity_le_six_mul_approxDegree_sq f) 3).trans_eq (by ring))

end DecisionTree

end Cslib
