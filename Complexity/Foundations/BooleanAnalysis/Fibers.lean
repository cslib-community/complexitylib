/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Fintype.Pi
import Complexity.Foundations.Analysis.SpecialFunctions.LogSum
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Logic.Equiv.Prod
import Mathlib.Combinatorics.Pigeonhole

/-!
# Coordinate fibers and Korten's entropy lemma

Fix a set `s : ι → Bool` of coordinates of the cube `ι → Bool`. Completing a pattern on `s` by the
coordinates of a point `x` outside `s` (`completePattern`) and replacing the coordinates of `x` in
`s` by those of a point `y` (`resample`) glue points of the cube along `s`. The fiber of a set `X`
of points over the coordinates of `x` outside `s` is a set of patterns on `s` (`coordinateFiber`),
and its density (`coordinateDensity`) is the probability that resampling the coordinates in `s`
lands in `X` (`coordinateDensity_eq_expect`). Averaging a function over the coordinates outside `s`
projects it to `s`, either as a function on the cube (`projectionAverage`) or as a function of the
patterns on `s` (`coordinateMarginal`).

The min-entropy deficit of a nonempty set `X` of points is `|ι| - log₂ |X|` (`uniformDeficit`).
Conditioning on the coordinates outside `s` does not increase the average deficit
[Korten, Lemma 4][Korten2026] (`expect_uniformDeficit_coordinateFiber`), so by Markov's inequality
most points of `X` have fibers of small deficit (`le_expect_uniformDeficit_coordinateFiber_le`). By
the pigeonhole principle, a map from `X` to at most `2 ^ m` values has a nonempty fiber of deficit
at most `m` more than that of `X` (`exists_uniformDeficit_fiber_le`). The density of `X` relative to
the uniform distribution (`uniformDensity`) connects deficits to the pointwise bounds of the
light-patterns lemma.

## Main definitions

* `Cslib.BitString.uniformMass`, `Cslib.BitString.uniformDensity`: the uniform
  distribution on a set, and its density.
* `Cslib.BitString.uniformDeficit`: the min-entropy deficit of a set.
* `Cslib.BitString.completePattern`, `Cslib.BitString.resample`: gluing points along
  a set of coordinates.
* `Cslib.BitString.coordinateFiber`, `Cslib.BitString.coordinateDensity`: the fiber
  of a set over the coordinates outside `s`, and its density.
* `Cslib.BitString.projectionAverage`, `Cslib.BitString.coordinateMarginal`: averages
  over the coordinates outside `s`.

## Main results

* `Cslib.BitString.expect_uniformDeficit_coordinateFiber`: Korten's entropy lemma.
* `Cslib.BitString.le_expect_uniformDeficit_coordinateFiber_le`: most fibers have small deficit.
* `Cslib.BitString.exists_uniformDeficit_fiber_le`: pigeonhole for deficits.
* `Cslib.BitString.uniformMass_le_rpow`, `Cslib.BitString.uniformDensity_le_rpow`: a deficit
  bound bounds the uniform probability mass and density pointwise.
* `Cslib.BitString.coordinateDensity_eq_expect`: the density of a fiber is the probability
  that resampling the coordinates in `s` lands in the set.
* `Cslib.BitString.projectionAverage_eq_expect_piecewise`,
  `Cslib.BitString.projectionAverage_eq_coordinateMarginal`,
  `Cslib.BitString.expect_projectionAverage`, `Cslib.BitString.expect_resample`: the
  two projections agree, and projecting or resampling preserves the mean.
* `Cslib.BitString.expect_ite_eq_one_half_of_update_not`,
  `Cslib.BitString.coordinateDensity_filter_eq_one_half_of_update_not`: a Boolean function that
  flips with a coordinate is true on half of the cube, and on half of every fiber that frees the
  coordinate.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

/-! ### Uniform distributions and min-entropy deficits -/

/-- Uniform probability mass on a nonempty finite set; zero off the set.
The empty set gives the zero mass function. -/
noncomputable def uniformMass {α : Type*} [DecidableEq α] (X : Finset α) (x : α) : ℝ :=
  if x ∈ X then 1 / X.card else 0

/-- Min-entropy deficit of the uniform distribution on a nonempty Boolean
cube subset. The real formula takes value `card ι` at the empty set because
`Real.logb 2 0 = 0`; entropy interpretations require nonemptiness. -/
noncomputable def uniformDeficit {ι : Type*} [Fintype ι]
    (X : Finset (ι → Bool)) : ℝ :=
  Fintype.card ι - Real.logb 2 X.card

/-- Density of uniform mass relative to the uniform Boolean cube. Its
uniform cube expectation is one when `X` is nonempty. -/
noncomputable def uniformDensity {ι : Type*} [Fintype ι]
    (X : Finset (ι → Bool)) (x : ι → Bool) : ℝ :=
  (2 : ℝ) ^ Fintype.card ι * uniformMass X x

/-- Uniform masses are nonnegative, including for the empty set. -/
theorem uniformMass_nonneg {α : Type*} [DecidableEq α] (X : Finset α) (x : α) :
    0 ≤ uniformMass X x := by
  unfold uniformMass
  split_ifs <;> positivity

/-- Uniform mass on a nonempty finite set sums to one. -/
theorem sum_uniformMass {α : Type*} [Fintype α] [DecidableEq α]
    {X : Finset α} (hX : X.Nonempty) : (∑ x, uniformMass X x) = 1 := by
  have hp : (X.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hX).ne'
  simp [uniformMass, hp]

/-- Summing against uniform mass agrees with the finite-set expectation. -/
theorem sum_uniformMass_mul {α : Type*} [Fintype α] [DecidableEq α]
    (X : Finset α) (f : α → ℝ) : (∑ x, uniformMass X x * f x) = 𝔼 x ∈ X, f x := by
  simp only [uniformMass, ite_mul, zero_mul]
  rw [sum_ite, sum_const_zero, add_zero]
  simp only [filter_mem_eq_inter, univ_inter, ← mul_sum, expect_eq_sum_div_card]
  ring

/-- Uniform densities are nonnegative, including for the empty set. -/
theorem uniformDensity_nonneg {ι : Type*} [Fintype ι]
    (X : Finset (ι → Bool)) (x : ι → Bool) : 0 ≤ uniformDensity X x :=
  mul_nonneg (by positivity) (uniformMass_nonneg X x)

/-- Uniform deficits are nonnegative. For the empty set this follows from
the documented real-logarithm convention. -/
theorem uniformDeficit_nonneg {ι : Type*} [Fintype ι]
    (X : Finset (ι → Bool)) : 0 ≤ uniformDeficit X := by
  classical
  by_cases hx : X.Nonempty
  · have hpos : (0 : ℝ) < X.card := by exact_mod_cast card_pos.mpr hx
    have hc : (X.card : ℝ) ≤ (2 : ℝ) ^ (Fintype.card ι : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast (show X.card ≤ 2 ^ Fintype.card ι by simpa using card_le_univ X)
    have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hpos).mpr hc
    exact sub_nonneg.mpr h
  · rw [not_nonempty_iff_eq_empty.mp hx]
    simp [uniformDeficit]

/-- A nonempty subset has cardinality `2^(dimension - deficit)`. -/
theorem card_eq_rpow_sub_uniformDeficit {ι : Type*} [Fintype ι] {X : Finset (ι → Bool)}
    (hX : X.Nonempty) : (X.card : ℝ) = (2 : ℝ) ^ ((Fintype.card ι : ℝ) - uniformDeficit X) := by
  have hp : (0 : ℝ) < X.card := by exact_mod_cast card_pos.mpr hX
  dsimp [uniformDeficit]
  rw [sub_sub_cancel, Real.rpow_logb (by norm_num) (by norm_num) hp]

/-- A deficit bound is equivalent to the corresponding density lower bound
when the subset is nonempty. -/
theorem uniformDeficit_le_iff {ι : Type*} [Fintype ι] {X : Finset (ι → Bool)}
    (hX : X.Nonempty) {k : ℝ} : uniformDeficit X ≤ k ↔
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) - k) ≤ X.card := by
  have he := Real.rpow_le_rpow_left_iff (x := (2 : ℝ))
    (y := (Fintype.card ι : ℝ) - k)
    (z := (Fintype.card ι : ℝ) - uniformDeficit X) (by norm_num)
  rw [← card_eq_rpow_sub_uniformDeficit hX] at he
  exact he.trans (by constructor <;> intro h <;> linarith) |>.symm

/-- A uniform deficit bound implies the light-patterns lemma's pointwise
probability-mass hypothesis. -/
theorem uniformMass_le_rpow {ι : Type*} [Fintype ι]
    {X : Finset (ι → Bool)} (hX : X.Nonempty) {k : ℝ} (hdef : uniformDeficit X ≤ k)
    (x : ι → Bool) : uniformMass X x ≤ (2 : ℝ) ^ (k - Fintype.card ι) := by
  calc
    _ ≤ 1 / (X.card : ℝ) := by
      unfold uniformMass
      split_ifs
      · exact le_rfl
      · positivity
    _ = (2 : ℝ) ^ (uniformDeficit X - Fintype.card ι) := by
      rw [card_eq_rpow_sub_uniformDeficit hX, one_div,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- Entropy deficit bounds the normalized density pointwise. -/
theorem uniformDensity_le_rpow {ι : Type*} [Fintype ι] {X : Finset (ι → Bool)}
    (hX : X.Nonempty) {k : ℝ} (hk : uniformDeficit X ≤ k) (x : ι → Bool) :
    uniformDensity X x ≤ (2 : ℝ) ^ k := by
  have hproduct : (2 : ℝ) ^ Fintype.card ι * (2 : ℝ) ^ (k - Fintype.card ι) =
      (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  exact (mul_le_mul_of_nonneg_left (uniformMass_le_rpow hX hk x) (by positivity)).trans_eq
    hproduct

/-- The density is `2^deficit` on the nonempty set and zero elsewhere. -/
theorem uniformDensity_eq_deficit {ι : Type*} [Fintype ι] {X : Finset (ι → Bool)}
    (hX : X.Nonempty) (z : ι → Bool) :
    uniformDensity X z = (2 : ℝ) ^ uniformDeficit X * (if z ∈ X then 1 else 0) := by
  by_cases hz : z ∈ X
  · simp only [uniformDensity, uniformMass, ite_eq_left hz, mul_one, mul_one_div]
    rw [card_eq_rpow_sub_uniformDeficit hX, ← Real.rpow_natCast,
      ← Real.rpow_sub (by norm_num)]
    congr 1
    ring
  · simp [uniformDensity, uniformMass, hz]

/-- Normalization of the density of a nonempty finite cube subset. -/
theorem expect_uniformDensity {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Finset (ι → Bool)}
    (hX : X.Nonempty) : (𝔼 x, uniformDensity X x) = 1 := by
  unfold uniformDensity
  rw [Fintype.expect_eq_sum_div_card, ← mul_sum, sum_uniformMass hX]
  simp

/-- **Pigeonhole for deficits**: some fiber of a map from a nonempty set `X` to a type of at most
`2 ^ m` elements is nonempty, of deficit at most the deficit of `X` plus `m`. -/
theorem exists_uniformDeficit_fiber_le {ι M : Type*} [Fintype ι] [Fintype M] [DecidableEq M]
    (X : Finset (ι → Bool)) (hX : X.Nonempty) (send : (ι → Bool) → M)
    {m : ℝ} (hm : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) :
    ∃ a : M, (X.filter fun x => send x = a).Nonempty ∧
      uniformDeficit (X.filter fun x => send x = a) ≤ uniformDeficit X + m := by
  obtain ⟨x, hx⟩ := hX
  have : Nonempty M := ⟨send x⟩
  have hXpos : (0 : ℝ) < X.card := by exact_mod_cast card_pos.mpr ⟨x, hx⟩
  let b : ℝ := X.card / (2 : ℝ) ^ m
  have hb : Fintype.card M • b ≤ (X.card : ℝ) := by
    rw [nsmul_eq_mul]
    calc
      _ ≤ (2 : ℝ) ^ m * b := mul_le_mul_of_nonneg_right hm (by dsimp [b]; positivity)
      _ = _ := by dsimp [b]; field_simp
  obtain ⟨a, _, ha⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := X) (t := univ) (f := send) (b := b) (fun _ _ => mem_univ _) univ_nonempty
    (by simpa only [card_univ] using hb)
  have hne : (X.filter fun x => send x = a).Nonempty := by
    apply card_pos.mp
    have hbpos : 0 < b := by dsimp [b]; positivity
    exact_mod_cast hbpos.trans_le ha
  refine ⟨a, hne, (uniformDeficit_le_iff hne).mpr ?_⟩
  convert ha using 1
  dsimp [b]
  rw [card_eq_rpow_sub_uniformDeficit (show X.Nonempty from ⟨x, hx⟩),
    ← Real.rpow_sub (by norm_num)]
  congr 1
  ring

/-! ### Gluing points along a set of coordinates -/

/-- Insert a pattern on selected coordinates, retaining `x` elsewhere. -/
def completePattern {ι : Type*} (s x : ι → Bool)
    (z : {i // s i = true} → Bool) : ι → Bool :=
  fun i => if h : s i = true then z ⟨i, h⟩ else x i

/-- Replace selected coordinates of `x` by those of `y`. -/
def resample {ι : Type*} (s x y : ι → Bool) : ι → Bool :=
  Set.piecewise {i | s i = true} y x

/-- The fiber of `X` over the bits of `x` outside `s`, represented on the
selected-coordinate cube. This is Korten's `X_{x,S}` inside its own subcube. -/
def coordinateFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (s x : ι → Bool) : Finset ({i // s i = true} → Bool) :=
  univ.filter (fun z => completePattern s x z ∈ X)

/-- Fraction of the free-coordinate cube over `x` that belongs to `X`. -/
noncomputable def coordinateDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (s x : ι → Bool) : ℝ :=
  (coordinateFiber X s x).card / (2 : ℝ) ^ Fintype.card {i // s i = true}

/-- The average of `f` over the coordinates outside `selected`, keeping the selected coordinates
of `x`. It depends only on the selected coordinates of `x`. -/
noncomputable def projectionAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (selected x : ι → Bool) : ℝ :=
  𝔼 y, f (resample selected y x)

/-- The marginal of `f` on the patterns on the selected coordinates: the average of `f` over the
completions of a pattern. For a density `f` relative to the uniform distribution, it is the density
of the projection to the selected coordinates. -/
noncomputable def coordinateMarginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (selected : ι → Bool)
    (pattern : {i // selected i = true} → Bool) : ℝ :=
  𝔼 rest : {i // selected i ≠ true} → Bool,
    f (fun i => if h : selected i = true then pattern ⟨i, h⟩ else rest ⟨i, h⟩)

section Gluing

variable {ι : Type*}

/-- Evaluating `resample` at a coordinate selects from `y` when `s i` holds and `x` otherwise. -/
@[simp] theorem resample_apply (s x y : ι → Bool) (i : ι) :
    resample s x y i = if s i then y i else x i := rfl

/-- Resampling no coordinates leaves the point unchanged. -/
@[simp] theorem resample_false (x y : ι → Bool) : resample (fun _ => false) x y = x := rfl

/-- Resampling all coordinates gives the source point. -/
@[simp] theorem resample_true (x y : ι → Bool) : resample (fun _ => true) x y = y := rfl

/-- Resampling is `Set.piecewise` on the selected coordinates. -/
theorem resample_eq_piecewise (s x y : ι → Bool) :
    resample s x y = Set.piecewise {i | s i = true} y x := rfl

/-- Resampling completes the restriction of the sampled point. -/
theorem resample_eq_completePattern (s x y : ι → Bool) :
    resample s x y = completePattern s x (fun i => y i) := by
  funext i
  by_cases hi : s i = true <;> simp [resample, completePattern, hi]

/-- Resampling the coordinates outside `s` of `x` from `y` is resampling the coordinates in `s`
of `y` from `x`. -/
theorem resample_not (s x y : ι → Bool) : resample (fun i => !s i) x y = resample s y x := by
  funext i
  cases hs : s i <;> simp [resample, hs]

private theorem resample_update_not [DecidableEq ι] {s : ι → Bool} {i : ι} (hi : s i = true)
    (x y : ι → Bool) :
    resample s x (Function.update y i (!y i)) =
      Function.update (resample s x y) i (!(resample s x y i)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [resample, hi]
  · simp [resample, Set.piecewise, Function.update_of_ne hj]

variable [Fintype ι] [DecidableEq ι]

/-- The free-coordinate fiber counts exactly the full assignments in `X`
whose unselected coordinates agree with `x`. -/
theorem card_coordinateFiber (X : Finset (ι → Bool)) (s x : ι → Bool) :
    (coordinateFiber X s x).card =
      (X.filter fun y => (fun i : {i // s i ≠ true} => y i) =
        (fun i : {i // s i ≠ true} => x i)).card := by
  refine card_bij (fun z _ => completePattern s x z) ?_ ?_ ?_
  · intro z hz
    refine mem_filter.mpr ⟨(mem_filter.mp hz).2, ?_⟩
    funext i
    simp [completePattern, i.property]
  · intro z hz w hw he
    funext i
    have h := congrFun he i
    simpa [completePattern, i.property] using h
  · intro y hy
    have he : completePattern s x (fun i => y i) = y := by
      funext i
      by_cases hi : s i = true
      · simp [completePattern, hi]
      · have h := congrFun (mem_filter.mp hy).2 ⟨i, hi⟩
        simpa [completePattern, hi] using h.symm
    refine ⟨fun i => y i, ?_, he⟩
    exact mem_filter.mpr ⟨mem_univ _, by rw [he]; exact (mem_filter.mp hy).1⟩

/-- Conditioning at a point of `X` leaves a nonempty fiber. -/
theorem coordinateFiber_nonempty {X : Finset (ι → Bool)} (s : ι → Bool) {x : ι → Bool}
    (hx : x ∈ X) : (coordinateFiber X s x).Nonempty := by
  refine ⟨fun i => x i, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
  have he : completePattern s x (fun i => x i) = x := by
    funext i
    simp [completePattern]
  rwa [he]

/-- Fiber densities are nonnegative, including for empty fibers. -/
theorem coordinateDensity_nonneg (X : Finset (ι → Bool)) (s x : ι → Bool) :
    0 ≤ coordinateDensity X s x := by
  unfold coordinateDensity
  positivity

/-- The fraction of a fiber is the probability that coordinate resampling
lands in the set. -/
theorem coordinateDensity_eq_expect (X : Finset (ι → Bool)) (s x : ι → Bool) :
    coordinateDensity X s x = 𝔼 y, if resample s x y ∈ X then (1 : ℝ) else 0 := by
  simp_rw [resample_eq_completePattern]
  rw [Fintype.expect_restrict_coordinates
    (fun z => if completePattern s x z ∈ X then (1 : ℝ) else 0)]
  simp [coordinateDensity, coordinateFiber, Fintype.expect_eq_sum_div_card]

/-- Resampling `x` on `P ∪ Q` instead of `P` does not change the density of its fiber over the
coordinates outside `Q`. -/
theorem coordinateDensity_resample_union (X : Finset (ι → Bool)) (P Q x y : ι → Bool) :
    coordinateDensity X Q (resample P x y) =
      coordinateDensity X Q (resample (fun i => P i || Q i) x y) := by
  rw [coordinateDensity_eq_expect, coordinateDensity_eq_expect]
  apply expect_congr rfl
  intro z _
  apply congrArg (fun t => if t ∈ X then (1 : ℝ) else 0)
  funext i
  cases hp : P i <;> cases hq : Q i <;> simp [resample, hp, hq]

end Gluing

/-! ### Projections to a set of coordinates -/

/-- An equivalence of coordinate types commutes with projections. -/
theorem projectionAverage_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (f : (κ → Bool) → ℝ) (s x : ι → Bool) :
    projectionAverage (fun y => f (fun j => y (e.symm j))) s x =
      projectionAverage f (fun j => s (e.symm j)) (fun j => x (e.symm j)) :=
  Fintype.expect_equiv (Equiv.arrowCongr e (Equiv.refl Bool)) _ _ (fun _ => rfl)

section Projection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Projections of nonnegative functions are nonnegative. -/
theorem projectionAverage_nonneg {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (selected x : ι → Bool) : 0 ≤ projectionAverage f selected x :=
  expect_nonneg fun _ _ => hf _

/-- Projection commutes with multiplication by a constant. -/
theorem projectionAverage_const_mul (a : ℝ) (f : (ι → Bool) → ℝ) (s x : ι → Bool) :
    projectionAverage (fun y => a * f y) s x = a * projectionAverage f s x :=
  (mul_expect _ _ _).symm

/-- The projection of `f` to `selected` is the uniform expectation over `Finset.piecewise`. -/
theorem projectionAverage_eq_expect_piecewise (f : (ι → Bool) → ℝ) (selected x : ι → Bool) :
    projectionAverage f selected x =
      𝔼 y, f ((univ.filter fun i => selected i = true).piecewise x y) := by
  unfold projectionAverage
  refine expect_congr rfl fun y _ => congrArg f (funext fun i => ?_)
  by_cases h : selected i = true <;> simp [resample, Set.piecewise, h]

/-- The marginal of `f` at a pattern is the average of `f` at the completions of the pattern by a
uniform point. -/
theorem coordinateMarginal_eq_expect_completePattern (f : (ι → Bool) → ℝ) (s : ι → Bool)
    (z : {i // s i = true} → Bool) :
    coordinateMarginal f s z = 𝔼 x, f (completePattern s x z) :=
  (Fintype.expect_restrict_coordinates (p := fun i => s i ≠ true)
    (fun rest => f (fun i => if h : s i = true then z ⟨i, h⟩ else rest ⟨i, h⟩))).symm

/-- The projection of `f` at `x` is its marginal at the selected coordinates of `x`. -/
theorem projectionAverage_eq_coordinateMarginal (f : (ι → Bool) → ℝ) (selected x : ι → Bool) :
    projectionAverage f selected x = coordinateMarginal f selected (fun i => x i) := by
  rw [coordinateMarginal_eq_expect_completePattern, projectionAverage]
  simp_rw [resample_eq_completePattern]

/-- Marginalization preserves the uniform mean, hence also density normalization. -/
theorem expect_coordinateMarginal (f : (ι → Bool) → ℝ) (selected : ι → Bool) :
    (𝔼 z, coordinateMarginal f selected z) = 𝔼 x, f x := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => selected i = true) (fun _ => Bool)
  rw [← Fintype.expect_equiv e.symm (fun z => f (e.symm z)) f (fun _ => rfl),
    ← univ_product_univ, expect_product]
  rfl

/-- The values of the projection of `f` at a uniform point are distributed as the values of its
marginal at a uniform pattern. -/
theorem expect_comp_projectionAverage (f : (ι → Bool) → ℝ) (s : ι → Bool) (g : ℝ → ℝ) :
    (𝔼 x, g (projectionAverage f s x)) = 𝔼 z, g (coordinateMarginal f s z) := by
  simp_rw [projectionAverage_eq_coordinateMarginal]
  exact Fintype.expect_restrict_coordinates (fun z => g (coordinateMarginal f s z))

/-- Projection preserves the uniform mean. -/
theorem expect_projectionAverage (f : (ι → Bool) → ℝ) (s : ι → Bool) :
    (𝔼 x, projectionAverage f s x) = 𝔼 x, f x :=
  (expect_comp_projectionAverage f s id).trans (expect_coordinateMarginal f s)

/-- Resampling the coordinates in `P` of a uniform point gives a uniform point. -/
theorem expect_resample (f : (ι → Bool) → ℝ) (P : ι → Bool) :
    (𝔼 x, 𝔼 y, f (resample P x y)) = 𝔼 z, f z := by
  simp_rw [← resample_not P]
  exact expect_projectionAverage f _

/-- When the coordinates in `P` of a uniform point of `X` are resampled, each point of the cube has
probability at most `1 / |X|`, so the average of a nonnegative function is at most its sum divided
by `|X|`. -/
theorem expect_resample_subset_le (X : Finset (ι → Bool)) {f : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (P : ι → Bool) :
    (𝔼 x ∈ X, 𝔼 y, f (resample P x y)) ≤ (∑ z, f z) / (X.card : ℝ) := by
  rw [expect_eq_sum_div_card]
  have hs : (∑ x ∈ X, 𝔼 y, f (resample P x y)) ≤ ∑ x, 𝔼 y, f (resample P x y) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ X)
      (fun x _ _ => expect_nonneg (fun y _ => hf _))
  rw [← Fintype.card_mul_expect, expect_resample, Fintype.card_mul_expect] at hs
  exact div_le_div_of_nonneg_right hs (by positivity)

/-- The density of the fiber of `X` over the coordinates of `x` outside `s` is the projection of
the indicator of `X` to the coordinates outside `s`. -/
theorem coordinateDensity_eq_projectionAverage (X : Finset (ι → Bool)) (s x : ι → Bool) :
    coordinateDensity X s x =
      projectionAverage (fun y => if y ∈ X then 1 else 0) (fun i => !s i) x := by
  rw [coordinateDensity_eq_expect, projectionAverage]
  simp_rw [resample_not]

/-- Projecting the restriction of `f` to the fiber over `x`, a function of the patterns on `s`, to
the coordinates `R` is projecting `f` to `R` together with the coordinates outside `s`. -/
theorem projectionAverage_comp_completePattern (f : (ι → Bool) → ℝ) (s x : ι → Bool)
    (R u : {i // s i = true} → Bool) :
    projectionAverage (fun z => f (completePattern s x z)) R u =
      projectionAverage f (fun i => if h : s i = true then R ⟨i, h⟩ else true)
        (completePattern s x u) := by
  unfold projectionAverage
  rw [← Fintype.expect_restrict_coordinates (p := fun i => s i = true)]
  refine expect_congr rfl fun y _ => congrArg f (funext fun i => ?_)
  by_cases hs : s i = true <;> simp [completePattern, resample, Set.piecewise, hs]

end Projection

/-! ### Korten's entropy lemma -/

/-- The logarithm of the size of the fiber of a uniform point of `X` under a map to `β` is on
average at least `log |X| - log |β|`. -/
theorem expect_log_card_fiber {α β : Type*} [Fintype β] [Nonempty β] [DecidableEq β]
    (X : Finset α) (hX : X.Nonempty) (g : α → β) :
    Real.log X.card - Real.log (Fintype.card β) ≤
      𝔼 x ∈ X, Real.log (X.filter (fun y => g y = g x)).card := by
  let m : β → ℝ := fun b => (X.filter fun x => g x = b).card
  have hsum : (∑ b, m b) = (X.card : ℝ) := by
    dsimp [m]
    exact_mod_cast (card_eq_sum_card_fiberwise (s := X) (t := univ)
      (f := g) (by intro x hx; exact mem_univ _) ).symm
  have hN : (0 : ℝ) < X.card := by exact_mod_cast card_pos.mpr hX
  have hB : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have h := Real.sum_mul_log_div_card_le univ (x := m) (by intro b _; dsimp [m]; positivity)
  rw [card_univ] at h
  rw [hsum, Real.log_div hN.ne' hB.ne'] at h
  have he : (∑ x ∈ X, Real.log (X.filter (fun y => g y = g x)).card) =
      ∑ b, m b * Real.log (m b) := by
    rw [← sum_fiberwise' X g (fun b => Real.log (m b))]
    simp only [sum_const, nsmul_eq_mul]
    rfl
  rw [expect_eq_sum_div_card, he]
  exact (le_div_iff₀ hN).mpr (by nlinarith)

/-- Korten's entropy lemma (Lemma 4): conditioning on the unselected bits
does not increase the average deficit in the selected-coordinate cube. -/
theorem expect_uniformDeficit_coordinateFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (hX : X.Nonempty) (s : ι → Bool) :
    (𝔼 x ∈ X, uniformDeficit (coordinateFiber X s x)) ≤ uniformDeficit X := by
  have h := expect_log_card_fiber X hX (fun x (i : {i // s i ≠ true}) => x i)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (Fintype.card {i // s i = true} : ℝ) +
      Fintype.card {i // s i ≠ true} = Fintype.card ι := by
    have hle := Fintype.card_subtype_le (fun i => s i = true)
    have he : Fintype.card {i // s i = true} +
        Fintype.card {i // s i ≠ true} = Fintype.card ι := by
      rw [Fintype.card_subtype_compl]
      omega
    exact_mod_cast he
  have he : (𝔼 x ∈ X, uniformDeficit (coordinateFiber X s x)) =
      Fintype.card {i // s i = true} -
        (𝔼 x ∈ X, Real.log (X.filter fun y =>
          (fun i : {i // s i ≠ true} => y i) =
          (fun i : {i // s i ≠ true} => x i)).card) / Real.log 2 := by
    simp only [uniformDeficit, Real.logb, expect_sub_distrib, ← expect_div,
      expect_const hX, card_coordinateFiber]
  rw [he]
  have hcard : Real.log (Fintype.card ({i // s i ≠ true} → Bool)) =
      Fintype.card {i // s i ≠ true} * Real.log 2 := by
    simp
  rw [hcard] at h
  dsimp [uniformDeficit, Real.logb]
  have hd := div_le_div_of_nonneg_right h hl.le
  simp only [sub_div, mul_div_cancel_right₀ _ hl.ne', ne_eq] at hd
  linarith only [hc, hd]

/-- For every fixed set of free coordinates, a uniform point of `X` yields
a fiber of deficit at most `64*k` with probability at least `63/64`. -/
theorem le_expect_uniformDeficit_coordinateFiber_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (hX : X.Nonempty) (s : ι → Bool)
    {k : ℝ} (hk : 0 < k) (hdef : uniformDeficit X ≤ k) :
    63 / 64 ≤ 𝔼 x ∈ X, if uniformDeficit (coordinateFiber X s x) ≤ 64 * k then
      (1 : ℝ) else 0 := by
  have hp : 0 < 64 * k := by positivity
  have hpoint (x : ι → Bool) :
      1 ≤ (if uniformDeficit (coordinateFiber X s x) ≤ 64 * k then (1 : ℝ) else 0) +
        uniformDeficit (coordinateFiber X s x) / (64 * k) := by
    by_cases hx : uniformDeficit (coordinateFiber X s x) ≤ 64 * k
    · rw [ite_eq_left hx]
      have := div_nonneg (uniformDeficit_nonneg (coordinateFiber X s x)) hp.le
      linarith
    · rw [ite_eq_right hx, zero_add]
      exact (le_div_iff₀ hp).mpr (by linarith)
  have h := expect_le_expect (s := X) (fun x _ => hpoint x)
  rw [expect_const hX, expect_add_distrib, ← expect_div] at h
  have hd := div_le_div_of_nonneg_right
    ((expect_uniformDeficit_coordinateFiber X hX s).trans hdef) hp.le
  have he : k / (64 * k) = 1 / 64 := by field_simp
  rw [he] at hd
  linarith

/-! ### Functions that flip with a coordinate -/

/-- A Boolean function that flips with one coordinate is true on half of the cube. -/
theorem expect_ite_eq_one_half_of_update_not {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) (i : ι) (hf : ∀ x, f (Function.update x i (!x i)) = !f x) (b : Bool) :
    (𝔼 x, if f x = b then (1 : ℝ) else 0) = 1 / 2 := by
  let flip (x : ι → Bool) := Function.update x i (!x i)
  have hinv : Function.Involutive flip := fun x => by simp [flip]
  have he := Fintype.expect_equiv (hinv.toPerm flip)
    (fun x => if f (flip x) = b then (1 : ℝ) else 0)
    (fun x => if f x = b then (1 : ℝ) else 0) (fun _ => rfl)
  have hpoint (x : ι → Bool) : (if f (flip x) = b then (1 : ℝ) else 0) =
      1 - (if f x = b then 1 else 0) := by
    rw [hf]
    cases h : f x <;> cases b <;> norm_num
  simp_rw [hpoint, expect_sub_distrib, Fintype.expect_const] at he
  linarith

/-- A Boolean function that flips with the coordinate `i` is true on half of every fiber over a
set of coordinates containing `i`. -/
theorem coordinateDensity_filter_eq_one_half_of_update_not {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) (i : ι) (hf : ∀ x, f (Function.update x i (!x i)) = !f x)
    (P x : ι → Bool) (hi : P i = true) (b : Bool) :
    coordinateDensity (univ.filter fun z => f z = b) P x = 1 / 2 := by
  rw [coordinateDensity_eq_expect]
  simp only [mem_filter, mem_univ, true_and]
  exact expect_ite_eq_one_half_of_update_not (fun y => f (resample P x y)) i
    (fun y => by rw [resample_update_not hi, hf]) b

end Cslib.BitString
