/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Analysis.HarmonicMean
public import Complexity.Foundations.BooleanAnalysis.Bernoulli
public import Complexity.Foundations.BooleanAnalysis.Fibers
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Real.Sqrt
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Korten's harmonic mean transform

The harmonic mean transform of a function on the cube (`harmonicTransform`,
[Korten, Definition 5][Korten2026]) projects the function to a set of selected coordinates and takes
the harmonic mean (`Cslib.harmonicMean`) of the projection. It is the harmonic mean of the marginal
on the selected coordinates (`harmonicTransform_eq_harmonicMean_coordinateMarginal`), and it is
concave in the function, antitone in the selected set and at most the mean
[Korten, Corollary 1][Korten2026]. Korten's inequality bounds the expected square root of a function
by the expected square root of its transform at a random set containing each coordinate with
probability `1 / 4` [Korten, Lemma 12][Korten2026]
(`expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform`), which gives the sampling estimate in the
proof of Lemma 10 (`le_bernoulliAverage_le_harmonicTransform`). The sparse sampling conclusion of
Lemma 10 is `BitString.le_bernoulliAverage_le_harmonicTransform_of_rpow`.

## Main definitions

* `Cslib.BitString.harmonicTransform`: Korten's harmonic mean transform.

## Main results

* `Cslib.BitString.concaveOn_harmonicTransform`,
  `Cslib.BitString.harmonicTransform_antitone`,
  `Cslib.BitString.harmonicTransform_le_expect`: the transform is concave in the function,
  antitone in the selected set, and at most the mean.
* `Cslib.BitString.expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform`: Korten's
  inequality.
* `Cslib.BitString.le_bernoulliAverage_le_harmonicTransform`: the sampling estimate of Lemma 10.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.BitString

open scoped BigOperators
open Finset

/-! ### The harmonic mean transform

A coordinate set is its Boolean membership function. The transform is represented on the full cube:
`projectionAverage f selected` depends only on the selected coordinates, and averaging on the full
cube gives each projected pattern the same multiplicity, so its harmonic mean is the harmonic mean
over the projected patterns (`harmonicTransform_eq_harmonicMean_coordinateMarginal`). -/

/-- Korten's harmonic mean transform [Korten, Definition 5][Korten2026]: the harmonic mean of the
projection of `f` to the selected coordinates, represented on the full cube. -/
noncomputable def harmonicTransform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (selected : ι → Bool) : ℝ :=
  harmonicMean (projectionAverage f selected)

/-- An equivalence of coordinate types commutes with the harmonic transform. -/
theorem harmonicTransform_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (f : (κ → Bool) → ℝ)
    (s : ι → Bool) :
    harmonicTransform (fun y => f (fun j => y (e.symm j))) s =
      harmonicTransform f (fun j => s (e.symm j)) := by
  unfold harmonicTransform
  change harmonicMean (fun x => projectionAverage
    (fun y => f (fun j => y (e.symm j))) s x) = _
  simp_rw [projectionAverage_reindex e f s]
  exact harmonicMean_equiv (Equiv.arrowCongr e (Equiv.refl Bool)) _

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The transform agrees with Definition 5 on the actual projected cube;
repeating each pattern on the full cube does not change its harmonic mean. -/
theorem harmonicTransform_eq_harmonicMean_coordinateMarginal
    (f : (ι → Bool) → ℝ) (selected : ι → Bool) :
    harmonicTransform f selected = harmonicMean (coordinateMarginal f selected) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => selected i = true) (fun _ => Bool)
  have he (z : ({i // selected i = true} → Bool) × ({i // selected i ≠ true} → Bool)) :
      projectionAverage f selected (e.symm z) = coordinateMarginal f selected z.1 := by
    rw [projectionAverage_eq_coordinateMarginal]
    exact congrArg (coordinateMarginal f selected) (congrArg Prod.fst (e.apply_symm_apply z))
  rw [harmonicTransform, ← harmonicMean_equiv e.symm]
  simp_rw [he]
  simp [harmonicMean, Fintype.expect_prod_type]

/-- Lemma 11 on the selected-coordinate cube, with nonnegative weights of mean one. -/
theorem harmonicTransform_variational {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (selected : ι → Bool) :
    harmonicTransform f selected = sInf {a : ℝ |
      ∃ w : ({i // selected i = true} → Bool) → ℝ,
        (∀ z, 0 ≤ w z) ∧ (𝔼 z, w z) = 1 ∧
          (𝔼 z, coordinateMarginal f selected z * w z ^ 2) = a} := by
  rw [harmonicTransform_eq_harmonicMean_coordinateMarginal]
  exact harmonicMean_variational fun _ => Finset.expect_nonneg fun _ _ => hf _

/-- The harmonic transform is nonnegative on nonnegative functions. -/
theorem harmonicTransform_nonneg {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (selected : ι → Bool) : 0 ≤ harmonicTransform f selected :=
  harmonicMean_nonneg (projectionAverage_nonneg hf selected)

/-- Constants are fixed by the harmonic transform. -/
theorem harmonicTransform_const (c : ℝ) (selected : ι → Bool) :
    harmonicTransform (fun _ => c) selected = c := by
  have he : projectionAverage (fun _ => c) selected = fun _ => c := by
    funext x
    simp [projectionAverage]
  rw [harmonicTransform, he, harmonicMean_const]

/-- Selecting no coordinates gives the ordinary mean. -/
theorem harmonicTransform_empty (f : (ι → Bool) → ℝ) :
    harmonicTransform f (fun _ => false) = 𝔼 x, f x := by
  have he : projectionAverage f (fun _ => false) = fun _ => 𝔼 x, f x := by
    funext x
    simp only [projectionAverage, resample_false]
  rw [harmonicTransform, he, harmonicMean_const]

/-- Selecting all coordinates gives the harmonic mean of the original function. -/
theorem harmonicTransform_full (f : (ι → Bool) → ℝ) :
    harmonicTransform f (fun _ => true) = harmonicMean f := by
  have he : projectionAverage f (fun _ => true) = f := by
    funext x
    simp only [projectionAverage, resample_true, Fintype.expect_const]
  rw [harmonicTransform, he]

/-- **The transform is concave in the function** [Korten, Corollary 1][Korten2026]: for every
selected set, it is concave on nonnegative functions. -/
theorem concaveOn_harmonicTransform (selected : ι → Bool) :
    ConcaveOn ℝ (Set.Ici 0) (fun f : (ι → Bool) → ℝ => harmonicTransform f selected) := by
  refine ⟨convex_Ici 0, fun f hf g hg a b ha hb hab => ?_⟩
  have he : projectionAverage (a • f + b • g) selected =
      a • projectionAverage f selected + b • projectionAverage g selected := by
    funext x
    simp only [projectionAverage, Pi.add_apply, Pi.smul_apply, smul_eq_mul, expect_add_distrib,
      ← mul_expect]
  simp only [harmonicTransform, he]
  exact concaveOn_harmonicMean.2 (projectionAverage_nonneg hf selected)
    (projectionAverage_nonneg hg selected) ha hb hab

private theorem harmonicTransform_midpoint {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 ≤ g x) (selected : ι → Bool) :
    (harmonicTransform f selected + harmonicTransform g selected) / 2 ≤
      harmonicTransform (fun x => (f x + g x) / 2) selected := by
  have he : (fun x => (f x + g x) / 2) = (1 / 2 : ℝ) • f + (1 / 2 : ℝ) • g := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h := (concaveOn_harmonicTransform selected).2 hf hg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [he]
  simp only [smul_eq_mul] at h
  linarith

end

/-! ### Splitting off the first coordinate

The proofs of the antitonicity of the transform and of Korten's Lemma 12 are inductions on the
dimension, on the cube `Fin n → Bool`, which split off the first coordinate. -/

private theorem resample_cons {n : ℕ} (s y x : Fin n → Bool) (a b c : Bool) :
    resample (Fin.cons a s : Fin (n + 1) → Bool) (Fin.cons b y) (Fin.cons c x) =
      Fin.cons (if a then c else b) (resample s y x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [resample, Set.piecewise]

theorem projectionAverage_cons_false {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) (selected x : Fin n → Bool) (b : Bool) :
    projectionAverage f (Fin.cons false selected) (Fin.cons b x) =
      projectionAverage (fun x => (f (Fin.cons false x) + f (Fin.cons true x)) / 2)
        selected x := by
  unfold projectionAverage
  rw [Fin.expect_univ_cons_bool]
  simp only [resample_cons, Bool.false_eq_true, ite_false]
  rw [← expect_div, expect_add_distrib]

theorem projectionAverage_cons_true {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) (selected x : Fin n → Bool) (b : Bool) :
    projectionAverage f (Fin.cons true selected) (Fin.cons b x) =
      projectionAverage (fun x => f (Fin.cons b x)) selected x := by
  unfold projectionAverage
  rw [Fin.expect_univ_cons_bool]
  simp only [resample_cons, ite_true]
  ring

theorem harmonicTransform_cons_false {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) (selected : Fin n → Bool) :
    harmonicTransform f (Fin.cons false selected) =
      harmonicTransform
        (fun x => (f (Fin.cons false x) + f (Fin.cons true x)) / 2) selected := by
  unfold harmonicTransform
  rw [← harmonicMean_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))]
  change harmonicMean (fun x : Bool × (Fin n → Bool) =>
    projectionAverage f (Fin.cons false selected) (Fin.cons x.1 x.2)) = _
  simp_rw [projectionAverage_cons_false]
  simp [harmonicMean, Fintype.expect_prod_type]

theorem harmonicTransform_cons_true {n : ℕ}
    {f : (Fin (n + 1) → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (selected : Fin n → Bool) :
    harmonicTransform f (Fin.cons true selected) =
      2 * harmonicTransform (fun x => f (Fin.cons false x)) selected *
        harmonicTransform (fun x => f (Fin.cons true x)) selected /
      (harmonicTransform (fun x => f (Fin.cons false x)) selected +
        harmonicTransform (fun x => f (Fin.cons true x)) selected) := by
  unfold harmonicTransform
  rw [← harmonicMean_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))]
  change harmonicMean (fun x : Bool × (Fin n → Bool) =>
    projectionAverage f (Fin.cons true selected) (Fin.cons x.1 x.2)) = _
  simp_rw [projectionAverage_cons_true]
  exact harmonicMean_pair fun b =>
    projectionAverage_nonneg (fun x => hf (Fin.cons b x)) selected

/-! ### The transform is antitone in the selected set -/

private theorem two_mul_mul_div_add_le_add_div_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * a * b / (a + b) ≤ (a + b) / 2 := by
  have h := harmonicMean_le_expect (α := Bool) (f := fun x => if x then b else a)
    fun x => by cases x <;> assumption
  rwa [harmonicMean_bool ha hb, Fintype.expect_bool] at h

private theorem two_mul_mul_div_add_mono {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hac : a ≤ c) (hbd : b ≤ d) : 2 * a * b / (a + b) ≤ 2 * c * d / (c + d) := by
  have h := harmonicMean_mono (α := Bool) (f := fun x => if x then b else a)
    (g := fun x => if x then d else c) (fun x => by cases x <;> assumption)
    (fun x => by cases x <;> assumption)
  rwa [harmonicMean_bool ha hb, harmonicMean_bool (ha.trans hac) (hb.trans hbd)] at h

private theorem harmonicTransform_antitone_fin {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) : Antitone (harmonicTransform f) := by
  intro r s hrs
  induction n with
  | zero => exact le_of_eq (congrArg (harmonicTransform f) (Subsingleton.elim _ _))
  | succ n ih =>
    obtain ⟨⟨rb, r⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective r
    obtain ⟨⟨sb, s⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective s
    change harmonicTransform f (Fin.cons sb s) ≤ harmonicTransform f (Fin.cons rb r)
    have htail : r ≤ s := fun i => hrs i.succ
    have h0 := fun x => hf (Fin.cons false x)
    have h1 := fun x => hf (Fin.cons true x)
    have havg : ∀ x, 0 ≤ (f (Fin.cons false x) + f (Fin.cons true x)) / 2 :=
      fun x => div_nonneg (add_nonneg (h0 x) (h1 x)) (by norm_num)
    cases rb <;> cases sb
    · rw [harmonicTransform_cons_false, harmonicTransform_cons_false]
      exact ih havg htail
    · rw [harmonicTransform_cons_true hf, harmonicTransform_cons_false]
      exact (two_mul_mul_div_add_le_add_div_two (harmonicTransform_nonneg h0 s)
        (harmonicTransform_nonneg h1 s)).trans
        ((harmonicTransform_midpoint h0 h1 s).trans (ih havg htail))
    · exact absurd (hrs 0) (by simp)
    · rw [harmonicTransform_cons_true hf, harmonicTransform_cons_true hf]
      exact two_mul_mul_div_add_mono (harmonicTransform_nonneg h0 s)
        (harmonicTransform_nonneg h1 s) (ih h0 htail) (ih h1 htail)

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Selecting more coordinates decreases the harmonic transform**
[Korten, Corollary 1][Korten2026]. -/
theorem harmonicTransform_antitone {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    Antitone (harmonicTransform f) := by
  intro s t hst
  let e := (Fintype.equivFin ι).symm
  have h := harmonicTransform_antitone_fin (f := fun y => f (fun j => y (e.symm j)))
    (fun _ => hf _) (show (fun j => s (e j)) ≤ fun j => t (e j) from fun j => hst (e j))
  simpa only [harmonicTransform_reindex, Equiv.apply_symm_apply] using h

/-- The harmonic transform is at most the ordinary mean [Korten, Corollary 1][Korten2026]. -/
theorem harmonicTransform_le_expect {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (selected : ι → Bool) : harmonicTransform f selected ≤ 𝔼 x, f x := by
  rw [← harmonicTransform_empty f]
  exact harmonicTransform_antitone hf fun _ => Bool.false_le _

end

/-! ### Korten's harmonic mean inequality

The inequality [Korten, Lemma 12][Korten2026] follows from a scalar inequality by induction on the
dimension, using concavity of the harmonic mean. No strict-positivity assumption is needed. -/

private theorem add_sqrt_div_two_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a + Real.sqrt b) / 2 ≤
      3 / 4 * Real.sqrt ((a + b) / 2) + 1 / 4 * Real.sqrt (2 * a * b / (a + b)) := by
  by_cases hz : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  have hp : 0 < (a + b) / 2 := by positivity
  let c := Real.sqrt ((a + b) / 2)
  have hc : 0 < c := Real.sqrt_pos.mpr hp
  have hc2 : c ^ 2 = (a + b) / 2 := Real.sq_sqrt hp.le
  have hroot : Real.sqrt (2 * a * b / (a + b)) = Real.sqrt a * Real.sqrt b / c := by
    calc
      _ = Real.sqrt (a * b / ((a + b) / 2)) := by congr 1; field_simp
      _ = _ := by rw [Real.sqrt_div (mul_nonneg ha hb), Real.sqrt_mul ha]
  rw [hroot]
  change _ ≤ 3 / 4 * c + 1 / 4 * (Real.sqrt a * Real.sqrt b / c)
  apply (mul_le_mul_iff_of_pos_right hc).mp
  field_simp
  nlinarith [sq_nonneg (c - (Real.sqrt a + Real.sqrt b) / 2),
    Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- One coordinate step of Korten's harmonic-transform inequality on `Fin (n + 1) → Bool`. -/
private theorem add_sqrt_harmonicTransform_cons_le {n : ℕ} {f : (Fin (n + 1) → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (s : Fin n → Bool) :
    1 / 2 * Real.sqrt (harmonicTransform (fun x => f (Fin.cons false x)) s) +
      1 / 2 * Real.sqrt (harmonicTransform (fun x => f (Fin.cons true x)) s) ≤
    3 / 4 * Real.sqrt
        (harmonicTransform (fun x => (f (Fin.cons false x) + f (Fin.cons true x)) / 2) s) +
      1 / 4 * Real.sqrt (harmonicTransform f (Fin.cons true s)) := by
  have h0 : ∀ x, 0 ≤ f (Fin.cons false x) := fun x => hf (Fin.cons false x)
  have h1 : ∀ x, 0 ≤ f (Fin.cons true x) := fun x => hf (Fin.cons true x)
  have hb := add_sqrt_div_two_le
    (harmonicTransform_nonneg h0 s) (harmonicTransform_nonneg h1 s)
  have hc := Real.sqrt_le_sqrt (harmonicTransform_midpoint h0 h1 s)
  rw [harmonicTransform_cons_true hf]
  linarith

private theorem expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform_fin {n : ℕ}
    {f : (Fin n → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x, Real.sqrt (f x)) ≤
      bernoulliAverage (1 / 4) (fun selected => Real.sqrt (harmonicTransform f selected)) := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) :=
      funext fun x => congrArg f (Subsingleton.elim _ _)
    rw [he]
    simp [harmonicTransform_const, bernoulliAverage_const]
  | succ n ih =>
    let f0 := fun x => f (Fin.cons false x)
    let f1 := fun x => f (Fin.cons true x)
    have hi0 := ih (fun x => hf (Fin.cons false x))
    have hi1 := ih (fun x => hf (Fin.cons true x))
    rw [Fin.expect_univ_cons_bool]
    calc
      _ ≤ 1 / 2 * bernoulliAverage (1 / 4) (fun s => Real.sqrt (harmonicTransform f0 s)) +
          1 / 2 * bernoulliAverage (1 / 4) (fun s => Real.sqrt (harmonicTransform f1 s)) := by
        linarith
      _ = bernoulliAverage (1 / 4) (fun s =>
          1 / 2 * Real.sqrt (harmonicTransform f0 s) +
            1 / 2 * Real.sqrt (harmonicTransform f1 s)) := by
        rw [bernoulliAverage_add, bernoulliAverage_const_mul, bernoulliAverage_const_mul]
      _ ≤ bernoulliAverage (1 / 4) (fun s =>
          3 / 4 * Real.sqrt (harmonicTransform (fun x => (f0 x + f1 x) / 2) s) +
            1 / 4 * Real.sqrt (harmonicTransform f (Fin.cons true s))) :=
        bernoulliAverage_mono (by norm_num) (by norm_num) (add_sqrt_harmonicTransform_cons_le hf)
      _ = _ := by
        rw [bernoulliAverage_add, bernoulliAverage_const_mul, bernoulliAverage_const_mul,
          bernoulliAverage_cons]
        simp_rw [harmonicTransform_cons_false]
        norm_num
        rfl

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Korten's harmonic mean inequality** [Korten, Lemma 12][Korten2026]: on the `1/4`-biased
coordinate cube, the mean square root of the harmonic transform dominates the uniform mean square
root of `f`. -/
theorem expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform {f : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x, Real.sqrt (f x)) ≤
      bernoulliAverage (1 / 4) (fun selected => Real.sqrt (harmonicTransform f selected)) := by
  let e := (Fintype.equivFin ι).symm
  have h := expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform_fin
    (f := fun y => f (fun j => y (e.symm j))) (fun _ => hf _)
  simp_rw [harmonicTransform_reindex e] at h
  rwa [bernoulliAverage_reindex e (1 / 4) (fun s => Real.sqrt (harmonicTransform f s)),
    Fintype.expect_equiv (Equiv.arrowCongr e (Equiv.refl Bool))
      (fun x => Real.sqrt (f (fun j => x (e.symm j)))) (fun x => Real.sqrt (f x))
      (fun _ => rfl)] at h

/-! ### Dense distributions and good coordinate projections

The first probability estimate in the proof of Korten's Lemma 10, before transference to a sparse
coordinate set. We use a pointwise density bound `B` instead of writing it as `2 ^ k`. -/

/-- Intermediate estimate in the proof of Lemma 10: a normalized density bounded
by `B` has harmonic transform at least `1 / (4 * B)` with probability at least
`1 / (2 * sqrt B)` under `1/4`-coordinate sampling. The `LightPatterns` module
transfers this estimate to sparse sampling. -/
theorem le_bernoulliAverage_le_harmonicTransform
    {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1)
    {B : ℝ} (hB : 1 ≤ B) (hbound : ∀ x, f x ≤ B) :
    1 / (2 * Real.sqrt B) ≤ bernoulliAverage (1 / 4)
      (fun selected => if 1 / (4 * B) ≤ harmonicTransform f selected then 1 else 0) := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBp
  let a := 1 / (2 * Real.sqrt B)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha2 : a ^ 2 = 1 / (4 * B) := by
    dsimp [a]
    rw [div_pow, mul_pow, Real.sq_sqrt hBp.le]
    norm_num
  have hlower : 1 / Real.sqrt B ≤ 𝔼 x, Real.sqrt (f x) := by
    apply (div_le_iff₀ hBs).mpr
    rw [← hmean, expect_mul]
    apply expect_le_expect
    intro x _
    calc
      f x = Real.sqrt (f x) * Real.sqrt (f x) := (Real.mul_self_sqrt (hf x)).symm
      _ ≤ Real.sqrt (f x) * Real.sqrt B :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hbound x)) (Real.sqrt_nonneg _)
  have hpoint (s : ι → Bool) : Real.sqrt (harmonicTransform f s) ≤
      a + if 1 / (4 * B) ≤ harmonicTransform f s then 1 else 0 := by
    by_cases hs : 1 / (4 * B) ≤ harmonicTransform f s
    · rw [ite_eq_left hs]
      have hupper : Real.sqrt (harmonicTransform f s) ≤ 1 := by
        have h := Real.sqrt_le_sqrt (harmonicTransform_le_expect hf s)
        simpa [hmean] using h
      linarith
    · rw [ite_eq_right hs, add_zero]
      calc
        _ ≤ Real.sqrt (1 / (4 * B)) := Real.sqrt_le_sqrt (le_of_not_ge hs)
        _ = a := by rw [← ha2, Real.sqrt_sq ha]
  have havg := bernoulliAverage_mono (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 : ℝ) / 4 ≤ 1) hpoint
  rw [bernoulliAverage_add, bernoulliAverage_const] at havg
  have hmain := expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform hf
  have ha' : 2 * a = 1 / Real.sqrt B := by dsimp [a]; field_simp
  linarith

/-- A positive transform lower bound bounds the fraction of light projected
patterns. The expectation ranges over the actual selected-coordinate cube. -/
theorem coordinateMarginal_light_fraction_le {f : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (selected : ι → Bool) {a b : ℝ} (ha : 0 < a)
    (ha' : a ≤ harmonicTransform f selected) (hb : 0 ≤ b) :
    (𝔼 z, if coordinateMarginal f selected z ≤ b then (1 : ℝ) else 0) ≤ b / a := by
  rw [harmonicTransform_eq_harmonicMean_coordinateMarginal] at ha'
  exact harmonicMean_light_fraction_le
    (fun _ => Finset.expect_nonneg fun _ _ => hf _) ha ha' hb

end

end Cslib.BitString
