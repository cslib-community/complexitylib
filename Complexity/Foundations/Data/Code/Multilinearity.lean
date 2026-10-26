/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.MultilinearExtension
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Multilinearity testing

A function `f : (ι → F) → F` on the points of `F ^ ι` over a field `F` is *multilinear* when its
restriction to every axis-parallel line, `t ↦ f (update x i t)`, is affine
(`Cslib.Code.IsMultilinear`) [Babai, Fortnow, Lund, Definition 5.1][BabaiFortnowLund1991].
Equivalently, `f` evaluates the multilinear extension of its values on the cube `{0, 1} ^ ι`
(`Cslib.Code.isMultilinear_iff_eq_eval_multilinearExtension`), or evaluates some polynomial of
degree at most one in each variable (`Cslib.Code.isMultilinear_iff_exists_mem_restrictDegree`).
The proof of uniqueness pushes zeros off the cube one coordinate at a time: an affine function of
one variable vanishing at `0` and `1` vanishes everywhere.

The *multilinearity test* picks a uniformly random direction `i` and a uniformly random point `x`,
reads `f` on the whole axis-parallel line through `x` in direction `i`, and accepts when that
restriction is affine. Its rejection probability `Cslib.Code.multilinearityTestRejection` is the
average, over the directions, of the proportion of lines in that direction on which `f` is not
affine. In the terms of [Babai, Fortnow, Lund, Definition 5.3][BabaiFortnowLund1991], it accepts
exactly the *correct* lines, those on which `f` is linear; `wrongPoints f i` collects the points
of the lines in direction `i` that are not correct. Their `δ`-wrong lines are those on which `f`
is not `δ`-approximately linear, and since their `δ`-approximation is strict (fewer than `δ |X|`
disagreements, Definition 3.4), for every `δ ∈ (0, 1]` a `δ`-wrong line is not correct. So the
proportion of lines in direction `i` that are not correct bounds their proportion of wrong lines
for every such `δ`. Our test differs from theirs (Section 5.1) in reading whole lines, where their
subtest samples `m₁ + 2` points of a line, and in sampling one random direction, where their test
samples lines in every direction.

* **Completeness and zero-error soundness**: the test rejects with probability zero exactly when
  `f` is multilinear (`Cslib.Code.multilinearityTestRejection_eq_zero_iff`).
* **Quantitative soundness** (`Cslib.Code.exists_isMultilinear_hammingDist_le`): over
  `F ^ n`, some multilinear `g` differs from `f` on at most `∑ i, 2 ^ i * #(wrongPoints f i)`
  points, where `wrongPoints f i` is the set of points whose line in direction `i` is not affine.
  So `f` is within relative distance `n * 2 ^ (n - 1) * ρ` of a multilinear function, where `ρ` is
  the rejection probability (`Cslib.Code.exists_isMultilinear_hammingDist_div_le`).

The quantitative bound is original, and it is weaker than the literature's: its constant is
exponential in the dimension. Its proof adapts the interpolation step in the proof of
[Babai, Fortnow, Lund, Lemma 5.11][BabaiFortnowLund1991] and inducts on the dimension, without
their self-improvement lemma: interpolating multilinear approximations of the two best
slices `x 0 = t₁` and `x 0 = t₂` gives a multilinear function that agrees with `f` on every
direction-`0` line that is affine and on which both slices are correct. Babai, Fortnow and Lund
prove a bound polynomial in the dimension: if in every direction the proportion of `δ`-wrong
lines is less than `ε`, then `f` is `3 n ^ 2 (ε + δ + 1 / N)`-approximately multilinear when
`N ≥ 40 n ^ 2`, `δ ≤ 1 / (400 n ^ 2)` and `ε ≤ 1 / (800 n ^ 3)` [Babai, Fortnow, Lund, Theorem 5.13]
[BabaiFortnowLund1991]. That bound, for the whole-line test, is
`Cslib.Code.exists_isMultilinear_hammingDist_lt`, in the module
`Complexity.Foundations.Data.Code.MultilinearitySoundness`.

## Main definitions

* `Cslib.Code.lineRestrict`: the restriction of a function to an axis-parallel line.
* `Cslib.Code.IsAffineFun`: a function of one variable is affine.
* `Cslib.Code.IsMultilinear`: every axis-parallel restriction is affine.
* `Cslib.Code.wrongPoints`: the points whose line in a given direction is not affine.
* `Cslib.Code.multilinearityTestRejection`: the rejection probability of the multilinearity test.

## Main results

* `Cslib.Code.IsAffineFun.eq_of_eq_of_eq`: affine functions agreeing at two points are equal.
* `Cslib.Code.IsMultilinear.eq_zero_of_forall_bitPoint`: a multilinear function vanishing on the
  cube vanishes.
* `Cslib.Code.isMultilinear_eval_multilinearExtension`,
  `Cslib.Code.isMultilinear_iff_eq_eval_multilinearExtension`: multilinear functions are the
  multilinear extensions of functions on the cube.
* `Cslib.Code.isAffineFun_iff_exists_affineMap`: affine functions of one variable are affine maps.
* `Cslib.BitString.indicatorPoly_mem_restrictDegree`,
  `Cslib.BitString.multilinearExtension_mem_restrictDegree`: multilinear extensions have degree at
  most one in each variable.
* `Cslib.Code.isMultilinear_eval_of_mem_restrictDegree`,
  `Cslib.Code.isMultilinear_iff_exists_mem_restrictDegree`: multilinear functions are the
  evaluations of polynomials of degree at most one in each variable.
* `Cslib.Code.multilinearityTestRejection_eq_zero_iff`: completeness and zero-error soundness.
* `Cslib.Code.card_wrongPoints_succ`: the wrong points in direction `j.succ` are those of the
  slices in direction `j`.
* `Cslib.Code.exists_isMultilinear_hammingDist_le_of_slices`: interpolating multilinear
  approximations of two slices.
* `Cslib.Code.exists_isMultilinear_hammingDist_le`,
  `Cslib.Code.exists_isMultilinear_hammingDist_div_le`: quantitative soundness with a constant
  exponential in the dimension.

## References

* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991], Section 5
-/

@[expose] public section

namespace Cslib.Code

open Finset Function MvPolynomial Cslib.BitString
open scoped BigOperators

variable {F ι : Type*} [Field F]

/-! ### Affine functions of one variable -/

/-- A function of one variable over a field is *affine* when it is `t ↦ a * t + b` for some `a`
and `b`, that is, the underlying function of an affine map `F →ᵃ[F] F`
(`Cslib.Code.isAffineFun_iff_exists_affineMap`). Babai, Fortnow and Lund call such functions
linear. This is not `Cslib.BitString.IsAffine`, which asks that a map preserve sums of three
points. -/
def IsAffineFun (g : F → F) : Prop :=
  ∃ a b : F, ∀ t, g t = a * t + b

instance [Fintype F] [DecidableEq F] : DecidablePred (IsAffineFun (F := F)) :=
  fun g => inferInstanceAs (Decidable (∃ a b : F, ∀ t, g t = a * t + b))

/-- An affine function is determined by its values at `0` and `1`. -/
theorem isAffineFun_iff {g : F → F} : IsAffineFun g ↔ ∀ t, g t = (g 1 - g 0) * t + g 0 := by
  refine ⟨fun ⟨a, b, h⟩ t => ?_, fun h => ⟨_, _, h⟩⟩
  rw [h t, h 1, h 0]
  ring

/-- Affine functions of one variable are the underlying functions of Mathlib's affine maps. -/
theorem isAffineFun_iff_exists_affineMap {g : F → F} :
    IsAffineFun g ↔ ∃ φ : F →ᵃ[F] F, ⇑φ = g := by
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨a • AffineMap.id F F + AffineMap.const F F b, funext fun t => ?_⟩
    simp [h t]
  · rintro ⟨φ, rfl⟩
    refine ⟨φ.linear 1, φ 0, fun t => ?_⟩
    have hl : φ.linear t = φ.linear 1 * t := by
      calc φ.linear t = φ.linear (t • 1) := by rw [smul_eq_mul, mul_one]
        _ = t • φ.linear 1 := map_smul _ _ _
        _ = φ.linear 1 * t := by rw [smul_eq_mul, mul_comm]
    rw [← hl]
    exact congrFun φ.decomp t

/-- A constant function is affine. -/
theorem isAffineFun_const (c : F) : IsAffineFun fun _ : F => c :=
  ⟨0, c, fun t => by ring⟩

/-- The identity is affine. -/
theorem isAffineFun_id : IsAffineFun fun t : F => t :=
  ⟨1, 0, fun t => by ring⟩

/-- `t ↦ 1 - t` is affine. -/
theorem isAffineFun_one_sub : IsAffineFun fun t : F => 1 - t :=
  ⟨-1, 1, fun t => by ring⟩

/-- The sum of affine functions is affine. -/
theorem IsAffineFun.add {g h : F → F} (hg : IsAffineFun g) (hh : IsAffineFun h) :
    IsAffineFun fun t => g t + h t := by
  obtain ⟨a, b, hg⟩ := hg
  obtain ⟨c, d, hh⟩ := hh
  exact ⟨a + c, b + d, fun t => by simp only [hg, hh]; ring⟩

/-- The difference of affine functions is affine. -/
theorem IsAffineFun.sub {g h : F → F} (hg : IsAffineFun g) (hh : IsAffineFun h) :
    IsAffineFun fun t => g t - h t := by
  obtain ⟨a, b, hg⟩ := hg
  obtain ⟨c, d, hh⟩ := hh
  exact ⟨a - c, b - d, fun t => by simp only [hg, hh]; ring⟩

/-- A constant multiple of an affine function is affine. -/
theorem IsAffineFun.const_mul {g : F → F} (hg : IsAffineFun g) (c : F) :
    IsAffineFun fun t => c * g t := by
  obtain ⟨a, b, hg⟩ := hg
  exact ⟨c * a, c * b, fun t => by simp only [hg]; ring⟩

/-- An affine function times a constant is affine. -/
theorem IsAffineFun.mul_const {g : F → F} (hg : IsAffineFun g) (c : F) :
    IsAffineFun fun t => g t * c := by
  simpa only [mul_comm _ c] using hg.const_mul c

/-- A finite sum of affine functions is affine. -/
theorem isAffineFun_sum {κ : Type*} (s : Finset κ) {g : κ → F → F}
    (hg : ∀ k ∈ s, IsAffineFun (g k)) :
    IsAffineFun fun t => ∑ k ∈ s, g k t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isAffineFun_const (0 : F)
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hg k (mem_insert_self k s)).add (ih fun k' hk' => hg k' (mem_insert_of_mem hk'))

/-- **Affine functions agreeing at two points are equal.** -/
theorem IsAffineFun.eq_of_eq_of_eq {g h : F → F} (hg : IsAffineFun g) (hh : IsAffineFun h) {s u : F}
    (hsu : s ≠ u) (hs : g s = h s) (hu : g u = h u) : g = h := by
  obtain ⟨a, b, hg⟩ := hg
  obtain ⟨c, d, hh⟩ := hh
  rw [hg, hh] at hs hu
  have hac : a = c := by
    have : (a - c) * (s - u) = 0 := by linear_combination hs - hu
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hsu))
  subst hac
  have hbd : b = d := by linear_combination hs
  subst hbd
  funext t
  rw [hg, hh]

/-! ### Multilinear extensions have degree at most one in each variable -/

section RestrictDegree

variable {R : Type*} [CommRing R]

/-- An indicator polynomial has degree at most one in each variable. -/
theorem _root_.Cslib.BitString.indicatorPoly_mem_restrictDegree [Fintype ι] (a : ι → Bool) :
    (indicatorPoly a : MvPolynomial ι R) ∈ restrictDegree ι R 1 := by
  classical
  nontriviality R
  rw [mem_restrictDegree]
  intro s hs j
  refine (degreeOf_le_iff.mp ?_) s hs
  refine (degreeOf_prod_le j _ _).trans ?_
  calc ∑ k, degreeOf j (if a k then X k else 1 - X k : MvPolynomial ι R)
      ≤ ∑ k, if j = k then 1 else 0 := sum_le_sum fun k _ => by
        have hX : degreeOf j (X k : MvPolynomial ι R) = if j = k then 1 else 0 := degreeOf_X j k
        by_cases hk : a k
        · simp only [hk, ite_true, hX, le_refl]
        · simp only [hk, Bool.false_eq_true, ite_false]
          refine (degreeOf_sub_le _ _ _).trans ?_
          rw [hX, ← C_1, degreeOf_C]
          simp
    _ = 1 := by simp

/-- The multilinear extension of a function on the cube has degree at most one in each
variable. -/
theorem _root_.Cslib.BitString.multilinearExtension_mem_restrictDegree [Fintype ι] [DecidableEq ι]
    (g : (ι → Bool) → R) : multilinearExtension g ∈ restrictDegree ι R 1 :=
  Submodule.sum_mem _ fun a _ => by
    rw [C_mul']
    exact Submodule.smul_mem _ _ (indicatorPoly_mem_restrictDegree a)

end RestrictDegree

/-! ### Multilinear functions -/

section Multilinear

variable [DecidableEq ι]

/-- The restriction of `f` to the axis-parallel line through `x` in direction `i`:
`t ↦ f (update x i t)`. -/
def lineRestrict (f : (ι → F) → F) (x : ι → F) (i : ι) (t : F) : F :=
  f (update x i t)

/-- A function on `F ^ ι` is *multilinear* when its restriction to every axis-parallel line is
affine [Babai, Fortnow, Lund, Definition 5.1][BabaiFortnowLund1991]. -/
def IsMultilinear (f : (ι → F) → F) : Prop :=
  ∀ x i, IsAffineFun (lineRestrict f x i)

omit [Field F] in
/-- The restriction of `f` to a line, read at the point where the line passes through `x`, is
`f x`. -/
@[simp] theorem lineRestrict_self (f : (ι → F) → F) (x : ι → F) (i : ι) :
    lineRestrict f x i (x i) = f x := by
  simp [lineRestrict]

/-- The difference of multilinear functions is multilinear. -/
theorem IsMultilinear.sub {f g : (ι → F) → F} (hf : IsMultilinear f) (hg : IsMultilinear g) :
    IsMultilinear (f - g) :=
  fun x i => (hf x i).sub (hg x i)

open Classical in
/-- A function vanishing at every point all of whose coordinates are `0` or `1`, and multilinear,
vanishes at every point: induction on the number of coordinates that are not `0` or `1`. -/
private theorem IsMultilinear.eq_zero_aux [Fintype ι] {h : (ι → F) → F} (hh : IsMultilinear h)
    (h0 : ∀ x : ι → F, (∀ i, x i = 0 ∨ x i = 1) → h x = 0) (k : ℕ) :
    ∀ x : ι → F, #{i | x i ≠ 0 ∧ x i ≠ 1} ≤ k → h x = 0 := by
  induction k with
  | zero =>
    intro x hx
    refine h0 x fun i => ?_
    by_contra hi
    push Not at hi
    have : i ∈ ({i | x i ≠ 0 ∧ x i ≠ 1} : Finset ι) := by simp [hi]
    simp_all
  | succ k ih =>
    intro x hx
    by_cases hb : ∃ i, x i ≠ 0 ∧ x i ≠ 1
    · obtain ⟨i, hi⟩ := hb
      have hc (c : F) (hc : c = 0 ∨ c = 1) : h (update x i c) = 0 := by
        refine ih _ ?_
        have hsub : ({j | update x i c j ≠ 0 ∧ update x i c j ≠ 1} : Finset ι) ⊆
            ({j | x j ≠ 0 ∧ x j ≠ 1} : Finset ι).erase i := by
          intro j hj
          simp only [mem_filter, mem_univ, true_and] at hj
          by_cases hji : j = i
          · subst hji
            simp only [update_self] at hj
            rcases hc with rfl | rfl <;> simp_all
          · simp only [update_of_ne hji] at hj
            simp [hji, hj]
        have hmem : i ∈ ({j | x j ≠ 0 ∧ x j ≠ 1} : Finset ι) := by simp [hi]
        have := card_le_card hsub
        rw [card_erase_of_mem hmem] at this
        omega
      have hline := (hh x i).eq_of_eq_of_eq (isAffineFun_const 0) zero_ne_one
        (hc 0 (Or.inl rfl)) (hc 1 (Or.inr rfl))
      simpa using congrFun hline (x i)
    · push Not at hb
      exact h0 x fun i => by
        by_cases h0i : x i = 0
        · exact Or.inl h0i
        · exact Or.inr (hb i h0i)

/-- **Uniqueness**: a multilinear function vanishing on the cube `{0, 1} ^ ι` vanishes. -/
theorem IsMultilinear.eq_zero_of_forall_bitPoint [Finite ι] {h : (ι → F) → F}
    (hh : IsMultilinear h) (h0 : ∀ b : ι → Bool, h (bitPoint b) = 0) : h = 0 := by
  classical
  have := Fintype.ofFinite ι
  funext x
  refine hh.eq_zero_aux (fun y hy => ?_) _ x le_rfl
  have : y = bitPoint fun i => decide (y i = 1) := by
    funext i
    rcases hy i with h | h <;> simp [h, bitVal]
  rw [this]
  exact h0 _

/-- The multilinear extension of a function on the cube is multilinear. -/
theorem isMultilinear_eval_multilinearExtension [Fintype ι] (g : (ι → Bool) → F) :
    IsMultilinear fun x => eval x (multilinearExtension g) := by
  intro x i
  have key (a : ι → Bool) (t : F) :
      (∏ j, if a j then update x i t j else 1 - update x i t j) =
        (if a i then t else 1 - t) * ∏ j ∈ univ \ {i}, if a j then x j else 1 - x j := by
    rw [← prod_update_of_mem (mem_univ i)]
    exact prod_congr rfl fun j _ =>
      apply_update (fun j (s : F) => if a j then s else 1 - s) x i t j
  unfold lineRestrict
  simp only [eval_multilinearExtension_eq_sum, eval_indicatorPoly_apply, key]
  refine isAffineFun_sum _ fun a _ => (IsAffineFun.mul_const ?_ _).const_mul (g a)
  split_ifs
  · exact isAffineFun_id
  · exact isAffineFun_one_sub

/-- **Multilinear functions are multilinear extensions**: a function on `F ^ ι` is multilinear
exactly when it evaluates the multilinear extension of its values on the cube. -/
theorem isMultilinear_iff_eq_eval_multilinearExtension [Fintype ι] {f : (ι → F) → F} :
    IsMultilinear f ↔ f = fun x => eval x (multilinearExtension fun b => f (bitPoint b)) := by
  refine ⟨fun hf => ?_, fun h => by rw [h]; exact isMultilinear_eval_multilinearExtension _⟩
  have := IsMultilinear.eq_zero_of_forall_bitPoint
    (hf.sub (isMultilinear_eval_multilinearExtension fun b => f (bitPoint b))) fun b => by
      simp only [Pi.sub_apply, eval_multilinearExtension, sub_self]
  funext x
  exact sub_eq_zero.mp (congrFun this x)

/-- The evaluation of a polynomial of degree at most one in each variable is multilinear. -/
theorem isMultilinear_eval_of_mem_restrictDegree [Finite ι] {P : MvPolynomial ι F}
    (hP : P ∈ restrictDegree ι F 1) : IsMultilinear fun x => eval x P := by
  have := Fintype.ofFinite ι
  intro x i
  unfold lineRestrict
  simp only [eval_eq']
  refine isAffineFun_sum _ fun s hs => IsAffineFun.const_mul ?_ _
  have key (t : F) : (∏ j, update x i t j ^ s j) =
      t ^ s i * ∏ j ∈ univ \ {i}, x j ^ s j := by
    rw [← prod_update_of_mem (mem_univ i)]
    exact prod_congr rfl fun j _ => apply_update (fun j (y : F) => y ^ s j) x i t j
  simp only [key]
  refine IsAffineFun.mul_const ?_ _
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ((mem_restrictDegree ι P 1).mp hP s hs i) with h | h
  · simpa [h] using isAffineFun_const (1 : F)
  · simpa [h] using isAffineFun_id

/-- **Multilinear functions are polynomials of degree at most one in each variable.** -/
theorem isMultilinear_iff_exists_mem_restrictDegree [Finite ι] {f : (ι → F) → F} :
    IsMultilinear f ↔ ∃ P ∈ restrictDegree ι F 1, f = fun x => eval x P := by
  have := Fintype.ofFinite ι
  refine ⟨fun hf => ⟨_, multilinearExtension_mem_restrictDegree _,
    isMultilinear_iff_eq_eval_multilinearExtension.mp hf⟩, ?_⟩
  rintro ⟨P, hP, rfl⟩
  exact isMultilinear_eval_of_mem_restrictDegree hP

end Multilinear

/-! ### The multilinearity test -/

section Test

variable [DecidableEq ι] [Fintype ι] [Fintype F] [DecidableEq F]

/-- The points whose axis-parallel line in direction `i` carries a restriction of `f` that is not
affine. Each wrong line contributes all of its `|F|` points. -/
def wrongPoints (f : (ι → F) → F) (i : ι) : Finset (ι → F) :=
  {x | ¬IsAffineFun (lineRestrict f x i)}

/-- The rejection probability of the multilinearity test on `f`: the probability, over a uniformly
random direction `i` and a uniformly random point `x`, that the restriction of `f` to the
axis-parallel line through `x` in direction `i` is not affine. The test reads `f` on the whole
line. -/
noncomputable def multilinearityTestRejection (f : (ι → F) → F) : ℝ :=
  𝔼 i, 𝔼 x, if IsAffineFun (lineRestrict f x i) then 0 else 1

/-- The rejection probability averages, over the directions, the proportion of wrong points. -/
theorem multilinearityTestRejection_eq (f : (ι → F) → F) :
    multilinearityTestRejection f =
      𝔼 i, (#(wrongPoints f i) : ℝ) / Fintype.card (ι → F) := by
  refine expect_congr rfl fun i _ => ?_
  rw [Fintype.expect_eq_sum_div_card, wrongPoints, Finset.natCast_card_filter]
  simp only [ite_not]

/-- The rejection probability is nonnegative. -/
theorem multilinearityTestRejection_nonneg (f : (ι → F) → F) :
    0 ≤ multilinearityTestRejection f :=
  expect_nonneg fun _ _ => expect_nonneg fun _ _ => by split_ifs <;> norm_num

/-- **Completeness and zero-error soundness of the multilinearity test**: it rejects with
probability zero exactly when `f` is multilinear. -/
theorem multilinearityTestRejection_eq_zero_iff {f : (ι → F) → F} :
    multilinearityTestRejection f = 0 ↔ IsMultilinear f := by
  have h01 (x : ι → F) (i : ι) : 0 ≤ (if IsAffineFun (lineRestrict f x i) then (0 : ℝ) else 1) := by
    split_ifs <;> norm_num
  rw [multilinearityTestRejection, expect_eq_zero_iff_of_nonneg fun i _ =>
    expect_nonneg fun x _ => h01 x i]
  simp only [expect_eq_zero_iff_of_nonneg fun x _ => h01 x _, mem_univ, true_implies,
    ite_eq_left_iff, one_ne_zero, imp_false, not_not]
  exact forall_comm

/-- **Completeness of the multilinearity test**: a multilinear function is never rejected. -/
theorem IsMultilinear.multilinearityTestRejection_eq_zero {f : (ι → F) → F}
    (hf : IsMultilinear f) : multilinearityTestRejection f = 0 :=
  multilinearityTestRejection_eq_zero_iff.mpr hf

end Test

/-! ### Quantitative soundness -/

section Soundness

variable [Fintype F] [DecidableEq F] {n : ℕ}

omit [Field F] [DecidableEq F] in
/-- Counting the points of `F ^ (n + 1)` by their first coordinate and their tail. -/
private theorem card_filter_zero_tail (P : F → (Fin n → F) → Prop) [∀ t, DecidablePred (P t)] :
    #{x : Fin (n + 1) → F | P (x 0) (Fin.tail x)} = ∑ t, #{y : Fin n → F | P t y} := by
  simp only [card_filter]
  rw [← (Fin.consEquiv fun _ => F).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv]

omit [Field F] [Fintype F] [DecidableEq F] in
/-- The lines of `f` in direction `j.succ` are the lines of its slices `x 0 = t` in direction
`j`. -/
private theorem lineRestrict_succ (f : (Fin (n + 1) → F) → F) (x : Fin (n + 1) → F) (j : Fin n) :
    lineRestrict f x j.succ = lineRestrict (fun y => f (Fin.cons (x 0) y)) (Fin.tail x) j := by
  funext t
  simp only [lineRestrict, Fin.cons_update, Fin.cons_self_tail]

/-- The wrong points of `f` in direction `j.succ` are those of its slices `x 0 = t` in direction
`j`. -/
theorem card_wrongPoints_succ (f : (Fin (n + 1) → F) → F) (j : Fin n) :
    #(wrongPoints f j.succ) = ∑ t, #(wrongPoints (fun y => f (Fin.cons t y)) j) := by
  have : wrongPoints f j.succ = ({x | ¬IsAffineFun (lineRestrict (fun y => f (Fin.cons (x 0) y))
      (Fin.tail x) j)} : Finset (Fin (n + 1) → F)) := by
    ext x
    simp only [wrongPoints, mem_filter, mem_univ, true_and, lineRestrict_succ]
  rw [this]
  exact card_filter_zero_tail
    (fun t y => ¬IsAffineFun (lineRestrict (fun y => f (Fin.cons t y)) y j))

omit [DecidableEq F] in
/-- The sum of the two smallest of `q ≥ 2` natural numbers, times `q`, is at most twice their
total. -/
private theorem exists_two_mul_le_sum (D : F → ℕ) :
    ∃ t₁ t₂, t₁ ≠ t₂ ∧ Fintype.card F * (D t₁ + D t₂) ≤ 2 * ∑ t, D t := by
  classical
  obtain ⟨t₁, -, h₁⟩ := exists_min_image univ D univ_nonempty
  have hne : (univ.erase t₁).Nonempty := ⟨if t₁ = 0 then 1 else 0, by
    split_ifs with h <;> simp [h, eq_comm]⟩
  obtain ⟨t₂, ht₂, h₂⟩ := exists_min_image _ D hne
  refine ⟨t₁, t₂, (ne_of_mem_erase ht₂).symm, ?_⟩
  have hsum : D t₁ + (Fintype.card F - 1) * D t₂ ≤ ∑ t, D t := by
    rw [← add_sum_erase _ _ (mem_univ t₁)]
    have := card_nsmul_le_sum _ D (D t₂) h₂
    rw [card_erase_of_mem (mem_univ t₁), smul_eq_mul] at this
    exact Nat.add_le_add_left (by simpa using this) _
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 2 := ⟨_, (Nat.sub_add_cancel hq).symm⟩
  rw [hm] at hsum ⊢
  have h12 : D t₁ ≤ D t₂ := h₁ t₂ (mem_univ _)
  have := Nat.mul_le_mul_left m h12
  rw [show m + 2 - 1 = m + 1 by omega] at hsum
  nlinarith

/-- **Interpolating two slices**: if `g₁` and `g₂` are multilinear functions on `F ^ n` and
`t₁ ≠ t₂`, then interpolating them in the first coordinate gives a multilinear function on
`F ^ (n + 1)` that differs from `f` only at points that are wrong in direction `0` or that lie
over a point where one of the slices `x 0 = t₁`, `x 0 = t₂` of `f` differs from `g₁`, `g₂`. This is
the interpolation step in the proof of [Babai, Fortnow, Lund, Lemma 5.11][BabaiFortnowLund1991],
for lines that are exactly affine. -/
theorem exists_isMultilinear_hammingDist_le_of_slices (f : (Fin (n + 1) → F) → F) {t₁ t₂ : F}
    (h12 : t₁ ≠ t₂) {g₁ g₂ : (Fin n → F) → F} (hg₁ : IsMultilinear g₁) (hg₂ : IsMultilinear g₂) :
    ∃ g, IsMultilinear g ∧ hammingDist f g ≤ #(wrongPoints f 0) +
      Fintype.card F * (hammingDist (fun y => f (Fin.cons t₁ y)) g₁ +
        hammingDist (fun y => f (Fin.cons t₂ y)) g₂) := by
  have hd : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  -- The interpolation of `g₁` and `g₂` in the first coordinate.
  let g : (Fin (n + 1) → F) → F := fun x =>
    g₁ (Fin.tail x) + (x 0 - t₁) / (t₂ - t₁) * (g₂ (Fin.tail x) - g₁ (Fin.tail x))
  have hg0 (x : Fin (n + 1) → F) : lineRestrict g x 0 = fun t =>
      g₁ (Fin.tail x) + (t - t₁) / (t₂ - t₁) * (g₂ (Fin.tail x) - g₁ (Fin.tail x)) := by
    funext t
    simp only [g, lineRestrict, Fin.tail_update_zero, update_self]
  have hg : IsMultilinear g := by
    intro x i
    induction i using Fin.cases with
    | zero =>
      rw [hg0]
      exact ⟨(g₂ (Fin.tail x) - g₁ (Fin.tail x)) / (t₂ - t₁),
        g₁ (Fin.tail x) - t₁ * ((g₂ (Fin.tail x) - g₁ (Fin.tail x)) / (t₂ - t₁)),
        fun t => by ring⟩
    | succ j =>
      have : lineRestrict g x j.succ = fun t => lineRestrict g₁ (Fin.tail x) j t +
          (x 0 - t₁) / (t₂ - t₁) *
            (lineRestrict g₂ (Fin.tail x) j t - lineRestrict g₁ (Fin.tail x) j t) := by
        funext t
        simp only [g, lineRestrict, Fin.tail_update_succ,
          update_of_ne (Fin.succ_ne_zero j).symm]
      rw [this]
      exact (hg₁ _ j).add (((hg₂ _ j).sub (hg₁ _ j)).const_mul _)
  refine ⟨g, hg, ?_⟩
  -- Every point where `f` and `g` differ is wrong in direction `0`, or lies over a point where
  -- one of the two slices differs from its approximation.
  let bad (t : F) (h : (Fin n → F) → F) : Finset (Fin (n + 1) → F) :=
    {x | f (Fin.cons t (Fin.tail x)) ≠ h (Fin.tail x)}
  have hsub : ({x | f x ≠ g x} : Finset (Fin (n + 1) → F)) ⊆
      wrongPoints f 0 ∪ (bad t₁ g₁ ∪ bad t₂ g₂) := by
    intro x hx
    simp only [wrongPoints, bad, mem_filter, mem_univ, true_and, mem_union] at hx ⊢
    by_contra! hc
    obtain ⟨haff, h1, h2⟩ := hc
    have hcons (t : F) : update x 0 t = Fin.cons t (Fin.tail x) := by
      rw [← Fin.update_cons_zero (x 0) (Fin.tail x) t, Fin.cons_self_tail]
    have hline := haff.eq_of_eq_of_eq (hg x 0) h12
      (by rw [hg0]; simp only [lineRestrict, hcons, h1, sub_self, zero_div, zero_mul, add_zero])
      (by rw [hg0]; simp only [lineRestrict, hcons, h2, div_self hd, one_mul,
        add_sub_cancel])
    exact hx (by simpa using congrFun hline (x 0))
  have hcard (t : F) (h : (Fin n → F) → F) :
      #(bad t h) = Fintype.card F * hammingDist (fun y => f (Fin.cons t y)) h := by
    rw [card_filter_zero_tail (fun _ y => f (Fin.cons t y) ≠ h y), sum_const, card_univ,
      smul_eq_mul, hammingDist]
  calc hammingDist f g = #({x | f x ≠ g x} : Finset (Fin (n + 1) → F)) := rfl
    _ ≤ #(wrongPoints f 0) + (#(bad t₁ g₁) + #(bad t₂ g₂)) :=
      (card_le_card hsub).trans ((card_union_le _ _).trans
        (Nat.add_le_add_left (card_union_le _ _) _))
    _ = _ := by rw [hcard, hcard, mul_add]

/-- **Quantitative soundness of the multilinearity test**, with a constant exponential in the
dimension (an original bound): some multilinear `g` differs from `f` on at most
`∑ i, 2 ^ i * #(wrongPoints f i)` points of `F ^ n`. The proof interpolates multilinear
approximations of the two best slices `x 0 = t₁` and `x 0 = t₂` and inducts on the dimension.
This adapts the interpolation step in the proof of
[Babai, Fortnow, Lund, Lemma 5.11][BabaiFortnowLund1991], without their self-improvement lemma. -/
theorem exists_isMultilinear_hammingDist_le (f : (Fin n → F) → F) :
    ∃ g, IsMultilinear g ∧ hammingDist f g ≤ ∑ i : Fin n, 2 ^ (i : ℕ) * #(wrongPoints f i) := by
  induction n with
  | zero => exact ⟨f, fun _ i => i.elim0, by simp⟩
  | succ n ih =>
    choose gs hgs hdist using fun t : F => ih fun y => f (Fin.cons t y)
    obtain ⟨t₁, t₂, h12, hD⟩ :=
      exists_two_mul_le_sum fun t => hammingDist (fun y => f (Fin.cons t y)) (gs t)
    obtain ⟨g, hg, hfg⟩ := exists_isMultilinear_hammingDist_le_of_slices f h12 (hgs t₁) (hgs t₂)
    refine ⟨g, hg, ?_⟩
    calc hammingDist f g ≤ #(wrongPoints f 0) +
          2 * ∑ t, hammingDist (fun y => f (Fin.cons t y)) (gs t) :=
        hfg.trans (Nat.add_le_add_left hD _)
      _ ≤ #(wrongPoints f 0) + 2 * ∑ t, ∑ j : Fin n,
            2 ^ (j : ℕ) * #(wrongPoints (fun y => f (Fin.cons t y)) j) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ (sum_le_sum fun t _ => hdist t)) _
      _ = ∑ i : Fin (n + 1), 2 ^ (i : ℕ) * #(wrongPoints f i) := by
        rw [Fin.sum_univ_succ, sum_comm, mul_sum]
        simp only [card_wrongPoints_succ, mul_sum, Fin.val_zero, pow_zero, one_mul,
          Fin.val_succ, pow_succ]
        congr 1
        refine sum_congr rfl fun j _ => sum_congr rfl fun t _ => by ring

/-- **Quantitative soundness of the multilinearity test**, as a probability: some multilinear `g`
is within relative distance `n * 2 ^ (n - 1) * ρ` of `f`, where `ρ` is the rejection probability
of the test. The constant is exponential in the dimension; the polynomial bound of
[Babai, Fortnow, Lund, Theorem 5.13][BabaiFortnowLund1991] is
`Cslib.Code.exists_isMultilinear_hammingDist_lt`. -/
theorem exists_isMultilinear_hammingDist_div_le (f : (Fin n → F) → F) :
    ∃ g, IsMultilinear g ∧ (hammingDist f g : ℝ) / Fintype.card (Fin n → F) ≤
      n * 2 ^ (n - 1) * multilinearityTestRejection f := by
  obtain ⟨g, hg, hdist⟩ := exists_isMultilinear_hammingDist_le f
  refine ⟨g, hg, ?_⟩
  have hcard : (0 : ℝ) < Fintype.card (Fin n → F) := by exact_mod_cast Fintype.card_pos
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : hammingDist f g = 0 := by simpa using hdist
    simp [this]
  have hle : (hammingDist f g : ℝ) ≤ 2 ^ (n - 1) * ∑ i : Fin n, (#(wrongPoints f i) : ℝ) := by
    calc (hammingDist f g : ℝ) ≤ ∑ i : Fin n, (2 : ℝ) ^ (i : ℕ) * #(wrongPoints f i) := by
          exact_mod_cast hdist
      _ ≤ ∑ i : Fin n, (2 : ℝ) ^ (n - 1) * #(wrongPoints f i) :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
      _ = 2 ^ (n - 1) * ∑ i : Fin n, (#(wrongPoints f i) : ℝ) := by rw [mul_sum]
  rw [multilinearityTestRejection_eq, Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    ← sum_div, div_le_iff₀ hcard]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc (hammingDist f g : ℝ) ≤ 2 ^ (n - 1) * ∑ i : Fin n, (#(wrongPoints f i) : ℝ) := hle
    _ = n * 2 ^ (n - 1) * ((∑ i : Fin n, (#(wrongPoints f i) : ℝ)) /
          Fintype.card (Fin n → F) / n) * Fintype.card (Fin n → F) := by
      field_simp

end Soundness

end Cslib.Code
