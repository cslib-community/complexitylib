/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib / Cslib, Cauchy rational-function and Cauchy reconstruction)

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rational-function and Cauchy reconstruction over fields and finite fields

Implements extended-Euclidean rational-function reconstruction (`Polynomial.PolyRat.reconstruct`)
over `F[X] / (M)` for an arbitrary field `F` (including finite fields such as `ZMod p`), together
with degree-based height and denominator bounds, modular uniqueness, completeness under
`N + D < M.natDegree`, and Cauchy rational-function interpolation (`Polynomial.PolyRat.cauchy`)
from evaluation points via `Lagrange.interpolate`.

## Main definitions

* `Polynomial.PolyRat`: documented fraction pair `{ num, den : F[X] }`.
* `Polynomial.PolyRat.height`: degree height `max num.natDegree den.natDegree`.
* `Polynomial.PolyRat.reconstruct`: extended-Euclidean rational-function reconstruction modulo
  `M : F[X]` with numerator degree bound `N` and denominator degree bound `D`.
* `Polynomial.PolyRat.cauchy`: Cauchy rational-function interpolation from evaluations on a finset
  `s : Finset F`.

## Main results

* `Polynomial.PolyRat.mul_eq_mul_of_dvd_sub_of_degree_lt`,
  `Polynomial.PolyRat.eq_of_isCoprime_of_monic`, `Polynomial.PolyRat.eq_of_dvd_sub_of_bounds`,
  `Polynomial.PolyRat.eq_of_dvd_sub_of_height_lt`: modular uniqueness under degree and height
  bounds.
* `Polynomial.PolyRat.reconstruct_eq_some`: soundness (monicity, degree/denominator bounds,
  coprimality, and modular congruence).
* `Polynomial.PolyRat.reconstruct_of_eq`: completeness (recovering `some p` whenever
  `N + D < M.natDegree`, `p.den.Monic`, `IsCoprime p.num p.den`, and `IsCoprime p.den M`).
* `Polynomial.PolyRat.cauchy_eq_some`, `Polynomial.PolyRat.cauchy_of_eq`: soundness and recovery
  for Cauchy rational-function interpolation at evaluations on `s : Finset F`.

## References

* [J. von zur Gathen, J. Gerhard, *Modern Computer Algebra*][vonZurGathenGerhard2013], §§5.7–5.8
  (§5.7, p. 115 for rational function reconstruction; §5.8, p. 118 for Cauchy interpolation).
-/

public section

namespace Polynomial

open Finset

/-- A rational-function numerator-denominator pair `num / den` over `F[X]`. -/
@[ext]
structure PolyRat (F : Type*) [Semiring F] where
  /-- Numerator polynomial. -/
  num : F[X]
  /-- Denominator polynomial. -/
  den : F[X]

namespace PolyRat

noncomputable section

section HeightAndUniqueness

variable {F : Type*}

/-- Polynomial degree height `max num.natDegree den.natDegree`. -/
@[expose] def height [Semiring F] (p : PolyRat F) : ℕ :=
  max p.num.natDegree p.den.natDegree

theorem height_def [Semiring F] (p : PolyRat F) :
    p.height = max p.num.natDegree p.den.natDegree :=
  rfl

theorem natDegree_num_le_height [Semiring F] (p : PolyRat F) : p.num.natDegree ≤ p.height :=
  le_max_left _ _

theorem natDegree_den_le_height [Semiring F] (p : PolyRat F) : p.den.natDegree ≤ p.height :=
  le_max_right _ _

/-- Cross-multiplication uniqueness modulo `M`: if `M ∣ p.num - p.den * u`,
`M ∣ q.num - q.den * u`, `(p.num.degree + q.den.degree < M.degree)`, and
`(q.num.degree + p.den.degree < M.degree)`, then `p.num * q.den = q.num * p.den`. -/
theorem mul_eq_mul_of_dvd_sub_of_degree_lt [Field F] {M u : F[X]} {p q : PolyRat F}
    (hp : M ∣ p.num - p.den * u) (hq : M ∣ q.num - q.den * u)
    (hdeg₁ : p.num.degree + q.den.degree < M.degree)
    (hdeg₂ : q.num.degree + p.den.degree < M.degree) :
    p.num * q.den = q.num * p.den := by
  have hdvd : M ∣ p.num * q.den - q.num * p.den := by
    have heq : p.num * q.den - q.num * p.den =
        (p.num - p.den * u) * q.den - (q.num - q.den * u) * p.den := by ring
    rw [heq]
    exact dvd_sub (dvd_mul_of_dvd_left hp q.den) (dvd_mul_of_dvd_left hq p.den)
  have hdeg_sub : (p.num * q.den - q.num * p.den).degree < M.degree := by
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_mul_le _ _) hdeg₁
    · exact lt_of_le_of_lt (Polynomial.degree_mul_le _ _) hdeg₂
  have hzero : p.num * q.den - q.num * p.den = 0 := by
    by_contra hne
    exact absurd (Polynomial.degree_le_of_dvd hdvd hne) (not_le_of_gt hdeg_sub)
  exact sub_eq_zero.mp hzero

/-- Two reduced monic pairs with the same cross-product are equal. -/
theorem eq_of_isCoprime_of_monic [Field F] {p q : PolyRat F} (hmul : p.num * q.den = q.num * p.den)
    (hcp : IsCoprime p.num p.den) (hcq : IsCoprime q.num q.den) (hmp : p.den.Monic)
    (hmq : q.den.Monic) : p = q := by
  have hdvd1 : p.den ∣ q.den :=
    hcp.symm.dvd_of_dvd_mul_left ⟨q.num, by rw [hmul, mul_comm]⟩
  have hdvd2 : q.den ∣ p.den :=
    hcq.symm.dvd_of_dvd_mul_left ⟨p.num, by rw [← hmul, mul_comm]⟩
  have hden : p.den = q.den :=
    Polynomial.eq_of_monic_of_associated hmp hmq (associated_of_dvd_dvd hdvd1 hdvd2)
  have hnum : p.num = q.num := by
    rw [hden] at hmul
    exact mul_right_cancel₀ hmq.ne_zero hmul
  exact PolyRat.ext hnum hden

private theorem eq_of_dvd_sub_of_deg_bounds [Field F] {M u : F[X]} {Np Dp Nq Dq : ℕ}
    {p q : PolyRat F} (hMp : p.den.Monic) (hMq : q.den.Monic) (hcp : IsCoprime p.num p.den)
    (hcq : IsCoprime q.num q.den) (hpn : p.num.degree ≤ Np) (hqn : q.num.degree ≤ Nq)
    (hpd : p.den.natDegree ≤ Dp) (hqd : q.den.natDegree ≤ Dq)
    (h1 : Np + Dq < M.natDegree) (h2 : Nq + Dp < M.natDegree)
    (hp : M ∣ p.num - p.den * u) (hq : M ∣ q.num - q.den * u) : p = q := by
  have hM : M ≠ 0 := fun h0 => by simp [h0] at h1
  have hMdeg₁ : ((Np + Dq : ℕ) : WithBot ℕ) < M.degree := by
    rw [Polynomial.degree_eq_natDegree hM]
    exact WithBot.coe_lt_coe.mpr h1
  have hMdeg₂ : ((Nq + Dp : ℕ) : WithBot ℕ) < M.degree := by
    rw [Polynomial.degree_eq_natDegree hM]
    exact WithBot.coe_lt_coe.mpr h2
  have hpd' : p.den.degree ≤ Dp := by
    rw [Polynomial.degree_eq_natDegree hMp.ne_zero]
    exact WithBot.coe_le_coe.mpr hpd
  have hqd' : q.den.degree ≤ Dq := by
    rw [Polynomial.degree_eq_natDegree hMq.ne_zero]
    exact WithBot.coe_le_coe.mpr hqd
  have hlt₁ : p.num.degree + q.den.degree < M.degree :=
    lt_of_le_of_lt (add_le_add hpn hqd') (by simpa only [Nat.cast_add] using hMdeg₁)
  have hlt₂ : q.num.degree + p.den.degree < M.degree :=
    lt_of_le_of_lt (add_le_add hqn hpd') (by simpa only [Nat.cast_add] using hMdeg₂)
  exact eq_of_isCoprime_of_monic
    (mul_eq_mul_of_dvd_sub_of_degree_lt hp hq hlt₁ hlt₂) hcp hcq hMp hMq

/-- Modular uniqueness of reduced monic pairs under numerator/denominator degree bounds
`N + D < M.natDegree`. -/
theorem eq_of_dvd_sub_of_bounds [Field F] {M u : F[X]} {N D : ℕ} {p q : PolyRat F}
    (hMp : p.den.Monic) (hMq : q.den.Monic) (hcp : IsCoprime p.num p.den)
    (hcq : IsCoprime q.num q.den) (hpn : p.num.degree ≤ N) (hqn : q.num.degree ≤ N)
    (hpd : p.den.natDegree ≤ D) (hqd : q.den.natDegree ≤ D) (hMdeg : N + D < M.natDegree)
    (hp : M ∣ p.num - p.den * u) (hq : M ∣ q.num - q.den * u) : p = q :=
  eq_of_dvd_sub_of_deg_bounds hMp hMq hcp hcq hpn hqn hpd hqd hMdeg hMdeg hp hq

/-- Modular uniqueness of reduced monic pairs under `PolyRat.height`: if `M ∣ p.num - p.den * u`,
`M ∣ q.num - q.den * u`, and `p.height + q.height < M.natDegree`, then `p = q`. -/
theorem eq_of_dvd_sub_of_height_lt [Field F] {M u : F[X]} {p q : PolyRat F}
    (hMp : p.den.Monic) (hMq : q.den.Monic) (hcp : IsCoprime p.num p.den)
    (hcq : IsCoprime q.num q.den) (hMdeg : p.height + q.height < M.natDegree)
    (hp : M ∣ p.num - p.den * u) (hq : M ∣ q.num - q.den * u) : p = q := by
  have hpn : p.num.degree ≤ p.height :=
    le_trans Polynomial.degree_le_natDegree (WithBot.coe_le_coe.mpr p.natDegree_num_le_height)
  have hqn : q.num.degree ≤ q.height :=
    le_trans Polynomial.degree_le_natDegree (WithBot.coe_le_coe.mpr q.natDegree_num_le_height)
  exact eq_of_dvd_sub_of_deg_bounds hMp hMq hcp hcq hpn hqn p.natDegree_den_le_height
    q.natDegree_den_le_height hMdeg (by rw [add_comm]; exact hMdeg) hp hq

end HeightAndUniqueness

section EuclideanReconstruction

variable {F : Type*} [Field F]

private structure PolyEuclidState (F : Type*) [Field F] where
  r0 : F[X]
  t0 : F[X]
  r1 : F[X]
  t1 : F[X]

private lemma polyMeasure_mod_lt {r0 r1 : F[X]} (hr1 : r1 ≠ 0) :
    letI := Classical.decEq F
    (r0 % r1).natDegree + (if r0 % r1 = 0 then 0 else 1) <
      r1.natDegree + (if r1 = 0 then 0 else 1) := by
  classical
  have hdeg_lt := Polynomial.degree_mod_lt r0 hr1
  simp only [hr1, ↓reduceIte]
  by_cases hr2 : r0 % r1 = 0
  · simp only [hr2, Polynomial.natDegree_zero, ↓reduceIte, zero_add]
    exact Nat.succ_pos _
  · simp only [hr2, ↓reduceIte]
    have hnat : (r0 % r1).natDegree < r1.natDegree := Polynomial.natDegree_lt_natDegree hr2 hdeg_lt
    omega

open Classical in
private def polyLoop (N : ℕ) (r0 t0 r1 t1 : F[X]) : PolyEuclidState F :=
  if h : (N : WithBot ℕ) < r1.degree then
    let q := r0 / r1
    let r2 := r0 % r1
    let t2 := t0 - q * t1
    have _ : r2.natDegree + (if r2 = 0 then 0 else 1) < r1.natDegree + (if r1 = 0 then 0 else 1) :=
      polyMeasure_mod_lt (fun h0 => by simp [h0] at h)
    polyLoop N r1 t1 r2 t2
  else
    ⟨r0, t0, r1, t1⟩
termination_by r1.natDegree + (if r1 = 0 then 0 else 1)
decreasing_by
  have hr1 : r1 ≠ 0 := fun h0 => by simp [h0] at h
  have hlt := polyMeasure_mod_lt (r0 := r0) hr1
  simpa only [EuclideanDomain.mod_eq_zero] using hlt

private structure PolyStepInv (M u r0 t0 r1 t1 : F[X]) : Prop where
  r0_ne : r0 ≠ 0
  r1_lt : r1.degree < r0.degree
  mod0 : M ∣ r0 - t0 * u
  mod1 : M ∣ r1 - t1 * u
  t_deg : t0.degree < t1.degree
  t1_ne : t1 ≠ 0
  bezout : ∃ s : ℤ, s * s = 1 ∧ r0 * t1 - r1 * t0 = (s : F[X]) * M

private theorem polyStepInv_step {M u r0 t0 r1 t1 : F[X]} {N : ℕ}
    (hinv : PolyStepInv M u r0 t0 r1 t1) (hlt : (N : WithBot ℕ) < r1.degree) :
    PolyStepInv M u r1 t1 (r0 % r1) (t0 - (r0 / r1) * t1) := by
  have hr1_nz : r1 ≠ 0 := fun h0 => by simp [h0] at hlt
  have hmod_eq : r0 % r1 = r0 - r1 * (r0 / r1) := EuclideanDomain.mod_eq_sub_mul_div r0 r1
  have hq_nz : r0 / r1 ≠ 0 := by
    rw [ne_eq, Polynomial.div_eq_zero_iff hr1_nz]
    exact not_lt_of_gt hinv.r1_lt
  have hq_nat : 0 < (r0 / r1).natDegree := by
    have hadd := Polynomial.degree_add_div hr1_nz (le_of_lt hinv.r1_lt)
    rw [Polynomial.degree_eq_natDegree hr1_nz, Polynomial.degree_eq_natDegree hinv.r0_ne,
      Polynomial.degree_eq_natDegree hq_nz] at hadd
    have hadd_nat : r1.natDegree + (r0 / r1).natDegree = r0.natDegree := by exact_mod_cast hadd
    have hr10_nat : r1.natDegree < r0.natDegree := by
      have h1 := hinv.r1_lt
      rw [Polynomial.degree_eq_natDegree hr1_nz, Polynomial.degree_eq_natDegree hinv.r0_ne] at h1
      exact_mod_cast h1
    omega
  have ht_mul_deg : t1.degree < (r0 / r1 * t1).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree hq_nz,
      Polynomial.degree_eq_natDegree hinv.t1_ne]
    exact_mod_cast (by omega : t1.natDegree < (r0 / r1).natDegree + t1.natDegree)
  have ht0_lt : t0.degree < (r0 / r1 * t1).degree := lt_trans hinv.t_deg ht_mul_deg
  have ht2_deg : (t0 - (r0 / r1) * t1).degree = (r0 / r1 * t1).degree :=
    Polynomial.degree_sub_eq_right_of_degree_lt ht0_lt
  have ht2_ne : t0 - (r0 / r1) * t1 ≠ 0 := fun h0 => by
    have hdeg := ht2_deg
    rw [h0, Polynomial.degree_zero] at hdeg
    exact absurd hdeg.symm (ne_of_gt (lt_of_le_of_lt bot_le ht_mul_deg))
  refine
    { r0_ne := hr1_nz
      r1_lt := Polynomial.degree_mod_lt r0 hr1_nz
      mod0 := hinv.mod1
      mod1 := ?_
      t_deg := ht2_deg ▸ ht_mul_deg
      t1_ne := ht2_ne
      bezout := ?_ }
  · rw [hmod_eq]
    have heq : r0 - r1 * (r0 / r1) - (t0 - (r0 / r1) * t1) * u =
        (r0 - t0 * u) - (r0 / r1) * (r1 - t1 * u) := by ring
    rw [heq]
    exact dvd_sub hinv.mod0 (dvd_mul_of_dvd_right hinv.mod1 _)
  · rcases hinv.bezout with ⟨s, hs1, hs2⟩
    refine ⟨-s, by linear_combination hs1, ?_⟩
    rw [hmod_eq]
    have hcast : ((-s : ℤ) : F[X]) = -(s : F[X]) := by push_cast; rfl
    rw [hcast, neg_mul, ← hs2]
    ring

open Classical in
private theorem polyLoop_spec {M u r0 t0 r1 t1 : F[X]} {N : ℕ}
    (hinv : PolyStepInv M u r0 t0 r1 t1) :
    let st := polyLoop N r0 t0 r1 t1
    PolyStepInv M u st.r0 st.t0 st.r1 st.t1 ∧ st.r1.degree ≤ (N : WithBot ℕ) ∧
      ((st.r0 = r0 ∧ st.t0 = t0 ∧ st.r1 = r1 ∧ st.t1 = t1) ∨
        (N : WithBot ℕ) < st.r0.degree) := by
  dsimp only
  rw [polyLoop]
  by_cases hlt : (N : WithBot ℕ) < r1.degree
  · simp only [hlt, ↓reduceDIte]
    have hinv' := polyStepInv_step hinv hlt
    have ih := polyLoop_spec (M := M) (u := u) (N := N) hinv'
    dsimp only at ih ⊢
    rcases ih with ⟨hs, hle, hor⟩
    refine ⟨hs, hle, Or.inr ?_⟩
    rcases hor with ⟨hr0_eq, _, _, _⟩ | hrec
    · rw [hr0_eq]
      exact hlt
    · exact hrec
  · simp only [hlt, ↓reduceDIte]
    exact ⟨hinv, not_lt.mp hlt, Or.inl (by simp)⟩
termination_by r1.natDegree + (if r1 = 0 then 0 else 1)
decreasing_by
  have hr1 : r1 ≠ 0 := fun h0 => by simp [h0] at hlt
  have hlt' := polyMeasure_mod_lt (r0 := r0) hr1
  simpa only [EuclideanDomain.mod_eq_zero] using hlt'

open Classical in
/-- Extended-Euclidean rational-function reconstruction over `F[X]` modulo `M`. Returns `some p`
with `p.den.Monic`, `p.num.degree ≤ N`, `p.den.natDegree ≤ D`, `IsCoprime p.num p.den`,
`IsCoprime p.den M`, and `M ∣ p.num - p.den * u`, when the Euclidean sequence meets the bounds. -/
def reconstruct (M u : F[X]) (N D : ℕ) : Option (PolyRat F) :=
  if M = 0 then none
  else
    let st := polyLoop N M 0 (u % M) 1
    if st.t1.natDegree ≤ D ∧ IsUnit (EuclideanDomain.gcd st.t1 M) then
      let c := st.t1.leadingCoeff⁻¹
      some ⟨Polynomial.C c * st.r1, Polynomial.C c * st.t1⟩
    else
      none

private theorem initial_polyStepInv {M : F[X]} (hM : M ≠ 0) (u : F[X]) :
    PolyStepInv M u M 0 (u % M) 1 := by
  refine
    { r0_ne := hM
      r1_lt := Polynomial.degree_mod_lt u hM
      mod0 := by simp
      mod1 := ?_
      t_deg := by simp
      t1_ne := one_ne_zero
      bezout := ⟨1, rfl, by simp⟩ }
  rw [one_mul, EuclideanDomain.mod_eq_sub_mul_div u M, sub_sub_cancel_left]
  exact dvd_neg.mpr (dvd_mul_right M _)

open Classical in
/-- Soundness of `PolyRat.reconstruct`. -/
theorem reconstruct_eq_some {M u : F[X]} {N D : ℕ} {p : PolyRat F}
    (hp : reconstruct M u N D = some p) :
    M ≠ 0 ∧ p.den.Monic ∧ p.num.degree ≤ N ∧ p.den.natDegree ≤ D ∧
      IsCoprime p.num p.den ∧ IsCoprime p.den M ∧ M ∣ p.num - p.den * u := by
  rw [reconstruct] at hp
  by_cases hM : M = 0
  · simp [hM] at hp
  · simp only [hM, ↓reduceIte] at hp
    let st := polyLoop N M 0 (u % M) 1
    change (if st.t1.natDegree ≤ D ∧ IsUnit (EuclideanDomain.gcd st.t1 M) then
      some ⟨Polynomial.C st.t1.leadingCoeff⁻¹ * st.r1,
        Polynomial.C st.t1.leadingCoeff⁻¹ * st.t1⟩ else none) = some p at hp
    split_ifs at hp with hcond
    rcases hcond with ⟨htD, hgcd⟩
    have hpeq : (⟨Polynomial.C st.t1.leadingCoeff⁻¹ * st.r1,
        Polynomial.C st.t1.leadingCoeff⁻¹ * st.t1⟩ : PolyRat F) = p := Option.some.inj hp
    have hspec := polyLoop_spec (M := M) (u := u) (N := N) (initial_polyStepInv hM u)
    change PolyStepInv M u st.r0 st.t0 st.r1 st.t1 ∧ st.r1.degree ≤ (N : WithBot ℕ) ∧ _ at hspec
    rcases hspec with ⟨hinv, hrN, _⟩
    have hc_ne : st.t1.leadingCoeff⁻¹ ≠ 0 :=
      inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hinv.t1_ne)
    have hCunit : IsUnit (Polynomial.C st.t1.leadingCoeff⁻¹) :=
      Polynomial.isUnit_C.mpr (Ne.isUnit hc_ne)
    have hmonic : (Polynomial.C st.t1.leadingCoeff⁻¹ * st.t1).Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff_C_mul_of_isUnit (Ne.isUnit hc_ne),
        inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hinv.t1_ne)]
    have hcop_tM : IsCoprime st.t1 M := EuclideanDomain.gcd_isUnit_iff.mp hgcd
    have hcop_rt : IsCoprime st.r1 st.t1 := by
      rcases hcop_tM with ⟨a, b, hab⟩
      rcases hinv.bezout with ⟨s, hs1, hs2⟩
      have hMs : (s : F[X]) * (st.r0 * st.t1 - st.r1 * st.t0) = M := by
        rw [hs2, ← mul_assoc]
        have : ((s * s : ℤ) : F[X]) = 1 := by rw [hs1]; simp
        calc
          (s : F[X]) * (s : F[X]) * M = ((s * s : ℤ) : F[X]) * M := by push_cast; rfl
          _ = M := by rw [this, one_mul]
      refine ⟨-(b * (s : F[X]) * st.t0), a + b * (s : F[X]) * st.r0, ?_⟩
      calc
        -(b * (s : F[X]) * st.t0) * st.r1 + (a + b * (s : F[X]) * st.r0) * st.t1
            = a * st.t1 + b * ((s : F[X]) * (st.r0 * st.t1 - st.r1 * st.t0)) := by ring
        _ = a * st.t1 + b * M := by rw [hMs]
        _ = 1 := hab
    rw [← hpeq]
    refine ⟨hM, hmonic, ?_, ?_, ?_, ?_, ?_⟩
    · refine le_trans (Polynomial.degree_mul_le _ _) ?_
      simpa only [Polynomial.degree_C hc_ne, zero_add] using hrN
    · simpa only [Polynomial.natDegree_C_mul hc_ne] using htD
    · exact ((isCoprime_mul_unit_left_left hCunit st.r1
          (Polynomial.C st.t1.leadingCoeff⁻¹ * st.t1)).mpr
        ((isCoprime_mul_unit_left_left hCunit st.t1 st.r1).mpr hcop_rt.symm).symm)
    · exact (isCoprime_mul_unit_left_left hCunit _ _).mpr hcop_tM
    · have hsub : Polynomial.C st.t1.leadingCoeff⁻¹ * st.r1 -
          Polynomial.C st.t1.leadingCoeff⁻¹ * st.t1 * u =
          Polynomial.C st.t1.leadingCoeff⁻¹ * (st.r1 - st.t1 * u) := by ring
      rw [hsub]
      exact dvd_mul_of_dvd_right hinv.mod1 _

open Classical in
/-- Completeness of `PolyRat.reconstruct`: recovers `some p` whenever `N + D < M.natDegree`,
`p.den.Monic`, `IsCoprime p.num p.den`, `IsCoprime p.den M`, `p.num.degree ≤ N`,
`p.den.natDegree ≤ D`, and `M ∣ p.num - p.den * u`. -/
theorem reconstruct_of_eq {M u : F[X]} {N D : ℕ} {p : PolyRat F}
    (hMp : p.den.Monic) (hcp : IsCoprime p.num p.den) (hcM : IsCoprime p.den M)
    (hpn : p.num.degree ≤ N) (hpd : p.den.natDegree ≤ D) (hMdeg : N + D < M.natDegree)
    (hmod : M ∣ p.num - p.den * u) : reconstruct M u N D = some p := by
  have hM : M ≠ 0 := fun h0 => by simp [h0] at hMdeg
  rw [reconstruct]
  simp only [hM, ↓reduceIte]
  let st := polyLoop N M 0 (u % M) 1
  change (if st.t1.natDegree ≤ D ∧ IsUnit (EuclideanDomain.gcd st.t1 M) then
    some ⟨Polynomial.C st.t1.leadingCoeff⁻¹ * st.r1,
      Polynomial.C st.t1.leadingCoeff⁻¹ * st.t1⟩ else none) = some p
  have hspec := polyLoop_spec (M := M) (u := u) (N := N) (initial_polyStepInv hM u)
  change PolyStepInv M u st.r0 st.t0 st.r1 st.t1 ∧ st.r1.degree ≤ (N : WithBot ℕ) ∧
    ((st.r0 = M ∧ st.t0 = 0 ∧ st.r1 = u % M ∧ st.t1 = 1) ∨
      (N : WithBot ℕ) < st.r0.degree) at hspec
  rcases hspec with ⟨hinv, hrN, hcase⟩
  have hmod_rt : M ∣ p.num * st.t1 - p.den * st.r1 := by
    have heq : p.num * st.t1 - p.den * st.r1 =
        (p.num - p.den * u) * st.t1 - p.den * (st.r1 - st.t1 * u) := by ring
    rw [heq]
    exact dvd_sub (dvd_mul_of_dvd_left hmod _) (dvd_mul_of_dvd_right hinv.mod1 _)
  have hMdeg_lt : (N : WithBot ℕ) + (D : WithBot ℕ) < M.degree := by
    rw [Polynomial.degree_eq_natDegree hM]
    exact_mod_cast hMdeg
  have hpd' : p.den.degree ≤ D := by
    rw [Polynomial.degree_eq_natDegree hMp.ne_zero]
    exact_mod_cast hpd
  have hrel : ∃ y : F[X], p.num = y * st.r1 ∧ p.den = y * st.t1 := by
    rcases hcase with ⟨_, _, _, ht1_eq⟩ | hr0_gt
    · have hdeg_lt : (p.num * st.t1 - p.den * st.r1).degree < M.degree := by
        refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
        · rw [ht1_eq, mul_one]
          exact lt_of_le_of_lt (le_trans hpn (le_add_of_nonneg_right
            (by exact_mod_cast Nat.zero_le D))) hMdeg_lt
        · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
          exact lt_of_le_of_lt (add_le_add hpd' hrN)
            (by rw [add_comm (D : WithBot ℕ)]; exact hMdeg_lt)
      have hzero : p.num * st.t1 = p.den * st.r1 := by
        by_contra hne
        exact absurd (Polynomial.degree_le_of_dvd hmod_rt (sub_ne_zero.mpr hne))
          (not_le_of_gt hdeg_lt)
      rw [ht1_eq, mul_one] at hzero
      have hden_u : IsUnit p.den := by
        have hd : p.den ∣ p.num := ⟨st.r1, hzero⟩
        rcases hcp with ⟨a, b, hab⟩
        obtain ⟨k, hk⟩ := hd
        exact isUnit_iff_exists_inv.mpr ⟨a * k + b, by linear_combination hab - a * hk⟩
      have hp1 : p.den = 1 := Polynomial.eq_of_monic_of_associated hMp Polynomial.monic_one
        (associated_one_iff_isUnit.mpr hden_u)
      rw [hp1, one_mul] at hzero
      exact ⟨1, by rw [one_mul, hzero], by rw [one_mul, hp1, ht1_eq]⟩
    · rcases hinv.bezout with ⟨s, hs1, hs2⟩
      have hmod0 : M ∣ p.den * st.r0 - p.num * st.t0 := by
        have heq : p.den * st.r0 - p.num * st.t0 =
            p.den * (st.r0 - st.t0 * u) - (p.num - p.den * u) * st.t0 := by ring
        rw [heq]
        exact dvd_sub (dvd_mul_of_dvd_right hinv.mod0 _) (dvd_mul_of_dvd_left hmod _)
      rcases dvd_mul_of_dvd_right hmod_rt (s : F[X]) with ⟨x, hx⟩
      rcases dvd_mul_of_dvd_right hmod0 (s : F[X]) with ⟨y, hy⟩
      have hss : ((s * s : ℤ) : F[X]) = 1 := by rw [hs1]; simp
      have hcramer : ∀ {a e0 e1 : F[X]},
          (s : F[X]) * a * (st.r0 * st.t1 - st.r1 * st.t0) =
            ((s : F[X]) * (p.num * st.t1 - p.den * st.r1)) * e0 +
              ((s : F[X]) * (p.den * st.r0 - p.num * st.t0)) * e1 →
          M * a = M * (x * e0 + y * e1) := fun {a e0 e1} hlin => by
        calc
          M * a = ((s * s : ℤ) : F[X]) * M * a := by rw [hss, one_mul]
          _ = (s : F[X]) * a * ((s : F[X]) * M) := by push_cast; ring
          _ = (s : F[X]) * a * (st.r0 * st.t1 - st.r1 * st.t0) := by rw [hs2]
          _ = ((s : F[X]) * (p.num * st.t1 - p.den * st.r1)) * e0 +
              ((s : F[X]) * (p.den * st.r0 - p.num * st.t0)) * e1 := hlin
          _ = (M * x) * e0 + (M * y) * e1 := by rw [← hx, ← hy]
          _ = M * (x * e0 + y * e1) := by ring
      have ha_eq : p.num = x * st.r0 + y * st.r1 := mul_left_cancel₀ hM (hcramer (by ring))
      have hb_eq : p.den = x * st.t0 + y * st.t1 := mul_left_cancel₀ hM (hcramer (by ring))
      have hx0 : x = 0 := by
        by_contra hxne
        have hxr0_deg : (N : WithBot ℕ) < (x * st.r0).degree := by
          rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree hxne,
            Polynomial.degree_eq_natDegree hinv.r0_ne]
          have h0 := hr0_gt
          rw [Polynomial.degree_eq_natDegree hinv.r0_ne] at h0
          have hn : N < st.r0.natDegree := by exact_mod_cast h0
          exact_mod_cast (by omega : N < x.natDegree + st.r0.natDegree)
        have hdeg_yr1 : (x * st.r0).degree = (y * st.r1).degree := by
          by_contra hne_deg
          rcases lt_or_gt_of_ne hne_deg with hlt_deg | hlt_deg
          · have hdeg := Polynomial.degree_add_eq_right_of_degree_lt hlt_deg
            rw [← ha_eq] at hdeg
            exact absurd (lt_trans hxr0_deg hlt_deg) (not_lt_of_ge (hdeg ▸ hpn))
          · have hdeg := Polynomial.degree_add_eq_left_of_degree_lt hlt_deg
            rw [← ha_eq] at hdeg
            exact absurd hxr0_deg (not_lt_of_ge (hdeg ▸ hpn))
        have hyne : y ≠ 0 := by
          intro hy0
          rw [hy0, zero_mul, Polynomial.degree_zero] at hdeg_yr1
          have : (x * st.r0).degree ≠ ⊥ :=
            Polynomial.degree_ne_bot.mpr (mul_ne_zero hxne hinv.r0_ne)
          exact this hdeg_yr1
        have hr1_ne : st.r1 ≠ 0 := by
          intro hr10
          rw [hr10, mul_zero, Polynomial.degree_zero] at hdeg_yr1
          have : (x * st.r0).degree ≠ ⊥ :=
            Polynomial.degree_ne_bot.mpr (mul_ne_zero hxne hinv.r0_ne)
          exact this hdeg_yr1
        have hxy_nat : x.natDegree < y.natDegree := by
          rw [Polynomial.degree_mul, Polynomial.degree_mul,
            Polynomial.degree_eq_natDegree hxne, Polynomial.degree_eq_natDegree hyne,
            Polynomial.degree_eq_natDegree hinv.r0_ne,
            Polynomial.degree_eq_natDegree hr1_ne] at hdeg_yr1
          have heq_nat : x.natDegree + st.r0.natDegree = y.natDegree + st.r1.natDegree := by
            exact_mod_cast hdeg_yr1
          have h1 := hinv.r1_lt
          rw [Polynomial.degree_eq_natDegree hinv.r0_ne,
            Polynomial.degree_eq_natDegree hr1_ne] at h1
          have h1' : st.r1.natDegree < st.r0.natDegree := by exact_mod_cast h1
          omega
        have ht_lt : (x * st.t0).degree < (y * st.t1).degree := by
          by_cases ht0 : st.t0 = 0
          · rw [ht0, mul_zero, Polynomial.degree_zero,
              Polynomial.degree_eq_natDegree (mul_ne_zero hyne hinv.t1_ne)]
            exact WithBot.bot_lt_coe _
          · have ht_nat : st.t0.natDegree < st.t1.natDegree := by
              have h1 := hinv.t_deg
              rw [Polynomial.degree_eq_natDegree ht0,
                Polynomial.degree_eq_natDegree hinv.t1_ne] at h1
              exact_mod_cast h1
            rw [Polynomial.degree_mul, Polynomial.degree_mul,
              Polynomial.degree_eq_natDegree hxne, Polynomial.degree_eq_natDegree hyne,
              Polynomial.degree_eq_natDegree ht0, Polynomial.degree_eq_natDegree hinv.t1_ne]
            exact_mod_cast
              (by omega : x.natDegree + st.t0.natDegree < y.natDegree + st.t1.natDegree)
        have hden_deg : p.den.degree = (y * st.t1).degree := by
          rw [hb_eq]
          exact Polynomial.degree_add_eq_right_of_degree_lt ht_lt
        have ht1_le_den : st.t1.degree ≤ p.den.degree := by
          rw [hden_deg, Polynomial.degree_mul, Polynomial.degree_eq_natDegree hyne,
            Polynomial.degree_eq_natDegree hinv.t1_ne]
          exact_mod_cast (Nat.le_add_left st.t1.natDegree y.natDegree)
        have hbound : (p.num * st.t1 - p.den * st.r1).degree < M.degree := by
          refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
          · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
            exact lt_of_le_of_lt (add_le_add hpn (le_trans ht1_le_den hpd')) hMdeg_lt
          · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
            exact lt_of_le_of_lt (add_le_add hpd' hrN)
              (by rw [add_comm (D : WithBot ℕ)]; exact hMdeg_lt)
        have hmul_ne : p.num * st.t1 - p.den * st.r1 ≠ 0 := by
          intro hzero
          have hxz : M * x = 0 := by rw [← hx, hzero, mul_zero]
          exact hxne ((mul_eq_zero.mp hxz).resolve_left hM)
        exact absurd (Polynomial.degree_le_of_dvd hmod_rt hmul_ne) (not_le_of_gt hbound)
      rw [hx0, zero_mul, zero_add] at ha_eq hb_eq
      exact ⟨y, ha_eq, hb_eq⟩
  rcases hrel with ⟨y, ha_eq, hb_eq⟩
  have hy_unit : IsUnit y := by
    rcases hcp with ⟨a, b, hab⟩
    refine isUnit_iff_exists_inv.mpr ⟨a * st.r1 + b * st.t1, ?_⟩
    calc
      y * (a * st.r1 + b * st.t1) = a * (y * st.r1) + b * (y * st.t1) := by ring
      _ = a * p.num + b * p.den := by rw [← ha_eq, ← hb_eq]
      _ = 1 := hab
  rcases Polynomial.isUnit_iff.mp hy_unit with ⟨c, hc_u, hyc⟩
  have hc_ne : c ≠ 0 := hc_u.ne_zero
  subst hyc
  have ht1_deg : st.t1.natDegree ≤ D := by
    have heq : st.t1.natDegree = p.den.natDegree := by
      rw [hb_eq, Polynomial.natDegree_C_mul hc_ne]
    exact heq ▸ hpd
  have htM_cop : IsCoprime st.t1 M := by
    rw [hb_eq] at hcM
    exact hcM.of_mul_left_right
  have hgcd_unit : IsUnit (EuclideanDomain.gcd st.t1 M) :=
    EuclideanDomain.gcd_isUnit_iff.mpr htM_cop
  have hcond : st.t1.natDegree ≤ D ∧ IsUnit (EuclideanDomain.gcd st.t1 M) := ⟨ht1_deg, hgcd_unit⟩
  simp only [hcond, and_self, ↓reduceIte]
  congr 1
  have hlead : c * st.t1.leadingCoeff = 1 := by
    have hm := hMp.leadingCoeff
    rw [hb_eq, Polynomial.leadingCoeff_C_mul_of_isUnit (Ne.isUnit hc_ne)] at hm
    exact hm
  have hc_inv : st.t1.leadingCoeff⁻¹ = c :=
    inv_eq_of_mul_eq_one_right (by rw [mul_comm, hlead])
  rw [hc_inv, ← ha_eq, ← hb_eq]

end EuclideanReconstruction

section CauchyAndFiniteField

variable {F : Type*} [Field F]

open Classical in
/-- Cauchy rational-function interpolation from evaluations `vals : F → F` at nodes `s : Finset F`
via `Lagrange.interpolate` and `PolyRat.reconstruct`. -/
def cauchy (s : Finset F) (vals : F → F) (N D : ℕ) : Option (PolyRat F) :=
  reconstruct (∏ a ∈ s, (X - C a)) (Lagrange.interpolate s id vals) N D

open scoped Function in
open Classical in
private theorem dvd_prod_X_sub_C_iff {s : Finset F} {f : F[X]} :
    (∏ a ∈ s, (X - C a)) ∣ f ↔ ∀ a ∈ s, f.eval a = 0 := by
  refine ⟨fun hdvd a ha => Polynomial.dvd_iff_isRoot.mp
    (dvd_trans (Finset.dvd_prod_of_mem (fun x => X - C x) ha) hdvd), fun h => ?_⟩
  exact Finset.prod_dvd_of_coprime
    ((Polynomial.pairwise_coprime_X_sub_C Function.injective_id).set_pairwise _)
    fun a ha => Polynomial.dvd_iff_isRoot.mpr (h a ha)

open Classical in
private theorem isCoprime_prod_X_sub_C_iff {s : Finset F} {b : F[X]} :
    IsCoprime b (∏ a ∈ s, (X - C a)) ↔ ∀ a ∈ s, b.eval a ≠ 0 := by
  rw [IsCoprime.prod_right_iff]
  refine forall₂_congr fun a _ => ?_
  constructor
  · rintro ⟨u, v, huv⟩ ha0
    have hev := congrArg (Polynomial.eval a) huv
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, ha0, sub_self, mul_zero, add_zero, Polynomial.eval_one] at hev
    exact one_ne_zero hev.symm
  · intro ha0
    refine ⟨C (b.eval a)⁻¹, (1 - C (b.eval a)⁻¹ * b) / (X - C a), ?_⟩
    have hdvd : (X - C a) ∣ 1 - C (b.eval a)⁻¹ * b := by
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_one,
        Polynomial.eval_mul, Polynomial.eval_C, inv_mul_cancel₀ ha0, sub_self]
    have hdiv := EuclideanDomain.mul_div_cancel' (Polynomial.X_sub_C_ne_zero a) hdvd
    rw [mul_comm (X - C a)] at hdiv
    linear_combination hdiv

open Classical in
/-- Soundness of `PolyRat.cauchy`: any output `p` satisfies `p.den.Monic`, `p.num.degree ≤ N`,
`p.den.natDegree ≤ D`, `p.den.eval a ≠ 0` and `p.num.eval a / p.den.eval a = vals a` for all
`a ∈ s`. -/
theorem cauchy_eq_some {s : Finset F} {vals : F → F} {N D : ℕ} {p : PolyRat F}
    (hp : cauchy s vals N D = some p) :
    p.den.Monic ∧ p.num.degree ≤ N ∧ p.den.natDegree ≤ D ∧ IsCoprime p.num p.den ∧
      ∀ a ∈ s, p.den.eval a ≠ 0 ∧ p.num.eval a / p.den.eval a = vals a := by
  rcases reconstruct_eq_some hp with ⟨_, hmonic, hdegN, hdegD, hcop, hcM, hmod⟩
  refine ⟨hmonic, hdegN, hdegD, hcop, fun a ha => ?_⟩
  have hda : p.den.eval a ≠ 0 := isCoprime_prod_X_sub_C_iff.mp hcM a ha
  have hev := dvd_prod_X_sub_C_iff.mp hmod a ha
  have hlag : (Lagrange.interpolate s id vals).eval a = vals a :=
    Lagrange.eval_interpolate_at_node vals Function.injective_id.injOn ha
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, sub_eq_zero] at hev
  rw [hlag] at hev
  exact ⟨hda, by rw [hev, mul_div_cancel_left₀ _ hda]⟩

open Classical in
/-- Completeness of `PolyRat.cauchy`: if `N + D < s.card`, `p.den.Monic`, `IsCoprime p.num p.den`,
`p.num.degree ≤ N`, `p.den.natDegree ≤ D`, and `p.den.eval a ≠ 0` with
`p.num.eval a / p.den.eval a = vals a` on all `a ∈ s`, then `cauchy s vals N D = some p`. -/
theorem cauchy_of_eq {s : Finset F} {vals : F → F} {N D : ℕ} {p : PolyRat F}
    (hMp : p.den.Monic) (hcp : IsCoprime p.num p.den) (hpn : p.num.degree ≤ N)
    (hpd : p.den.natDegree ≤ D) (hs : N + D < s.card)
    (heval : ∀ a ∈ s, p.den.eval a ≠ 0 ∧ p.num.eval a / p.den.eval a = vals a) :
    cauchy s vals N D = some p := by
  have hcM : IsCoprime p.den (∏ a ∈ s, (X - C a)) :=
    isCoprime_prod_X_sub_C_iff.mpr fun a ha => (heval a ha).1
  have hmod : (∏ a ∈ s, (X - C a)) ∣ p.num - p.den * Lagrange.interpolate s id vals := by
    rw [dvd_prod_X_sub_C_iff]
    intro a ha
    rcases heval a ha with ⟨hda, hdiv⟩
    have hlag : (Lagrange.interpolate s id vals).eval a = vals a :=
      Lagrange.eval_interpolate_at_node vals Function.injective_id.injOn ha
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, sub_eq_zero]
    rw [hlag, mul_comm (p.den.eval a), ← div_eq_iff hda]
    exact hdiv
  have hdegM : (∏ a ∈ s, (X - C a)).natDegree = s.card := by
    rw [Polynomial.natDegree_prod_of_monic (f := fun a => X - C a) (s := s)
      fun a _ => Polynomial.monic_X_sub_C a]
    simp
  exact reconstruct_of_eq hMp hcp hcM hpn hpd (by rw [hdegM]; exact hs) hmod

/-- Finite-field specialization of `PolyRat.reconstruct` over `(ZMod p)[X]` for prime `p`. -/
theorem reconstruct_zmod_of_eq {p : ℕ} [Fact p.Prime] {M u : (ZMod p)[X]} {N D : ℕ}
    {q : PolyRat (ZMod p)} (hMq : q.den.Monic) (hcq : IsCoprime q.num q.den)
    (hcM : IsCoprime q.den M) (hqn : q.num.degree ≤ N) (hqd : q.den.natDegree ≤ D)
    (hMdeg : N + D < M.natDegree) (hmod : M ∣ q.num - q.den * u) :
    reconstruct M u N D = some q :=
  reconstruct_of_eq hMq hcq hcM hqn hqd hMdeg hmod

end CauchyAndFiniteField

end

end PolyRat

end Polynomial
