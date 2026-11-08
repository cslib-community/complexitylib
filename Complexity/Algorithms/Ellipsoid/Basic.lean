/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Analysis.Convex.Ellipsoid

/-!
# The central-cut ellipsoid method with a strong separation oracle

Khachiyan's ellipsoid method [Khachiyan1979] for a set `P ⊆ ℝⁿ` given by a strong separation
oracle [GrotschelLovaszSchrijver1988, Section 2.1]. Starting from an ellipsoid `E(A₀, c₀) ⊇ P`,
each step queries the oracle at the current center. If the oracle certifies the center is in `P`
the method stops (the state no longer changes). Otherwise it returns a hyperplane through the
center with `P` strictly on one side, and the method replaces the ellipsoid by the central-cut
ellipsoid `Matrix.centralCutShape`/`Matrix.centralCutCenter` containing that half
[GrotschelLovaszSchrijver1988, Section 3.1], [BertsimasTsitsiklis1997, Section 8.2]. This is the
exact-arithmetic method of those sections; the finite-precision central-cut method of
[GrotschelLovaszSchrijver1988, Section 3.2], with rounding and its larger constants, is not
formalized here.

Since each cut shrinks the volume by the factor `exp (-1 / (2 (n + 1)))`
(`Matrix.volume_ellipsoid_centralCut_lt`), after `N` steps either the current center is in `P` or
`vol P ≤ exp (-N / (2 (n + 1))) · vol E(A₀, c₀)`.

Arithmetic is exact over `ℝ`: the square root in the update is computed exactly and nothing is
rounded. Finite-precision ellipsoids, the bit complexity of the method, and its use for rational
linear programming (a volume lower bound for full-dimensional rational polytopes and the
reduction of feasibility to that case) are not formalized here.

## Main definitions

* `Cslib.Algorithms.Ellipsoid.IsStrongSeparationOracle`: the oracle contract.
* `Cslib.Algorithms.Ellipsoid.step`, `Cslib.Algorithms.Ellipsoid.run`: one step and `N` steps of
  the method.

## Main results

* `Cslib.Algorithms.Ellipsoid.posDef_run_shape`, `Cslib.Algorithms.Ellipsoid.subset_ellipsoid_run`:
  every shape is positive definite and every ellipsoid contains `P`.
* `Cslib.Algorithms.Ellipsoid.center_mem_or_volume_le`: after `N` steps the center is in `P` or
  `vol P ≤ exp (-N / (2 (n + 1))) · vol E(A₀, c₀)`.
* `Cslib.Algorithms.Ellipsoid.center_mem_or_volume_lt`: the same with
  `N > 2 (n + 1) ln (vol E(A₀, c₀) / v)` and conclusion `vol P < v`.
* `Cslib.Algorithms.Ellipsoid.center_mem_of_ball_subset`: if `P` contains a ball of radius `r` and
  lies in the ball of radius `R` about `c₀`, the method started from the latter ball has its center
  in `P` after any `N > 2 n (n + 1) ln (R / r)` steps.

## References

* [BertsimasTsitsiklis1997], Section 8.2
* [GrotschelLovaszSchrijver1988], Sections 2.1 and 3.1
* [Khachiyan1979]
-/

public section

namespace Cslib.Algorithms.Ellipsoid

open Matrix MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- `sep` is a *strong separation oracle* for `P` [GrotschelLovaszSchrijver1988, Section 2.1]: on a
query `z` it either answers `none`, certifying `z ∈ P`, or returns a nonzero vector `a` with
`a ⬝ᵥ x < a ⬝ᵥ z` for every `x ∈ P`, i.e. a hyperplane strictly separating `z` from `P`.

Grötschel, Lovász and Schrijver pose the strong separation problem for convex sets, with a
normalized cut vector given in binary. Here `P` is an arbitrary set, any nonzero real `a` is
allowed and no encoding or output size is involved, so for convex `P` this is the real-number
content of that problem up to scaling of `a`. -/
structure IsStrongSeparationOracle (P : Set (ι → ℝ)) (sep : (ι → ℝ) → Option (ι → ℝ)) : Prop where
  mem_of_eq_none {z : ι → ℝ} : sep z = none → z ∈ P
  ne_zero_of_eq_some {z a : ι → ℝ} : sep z = some a → a ≠ 0
  separates {z a : ι → ℝ} : sep z = some a → ∀ x ∈ P, a ⬝ᵥ x < a ⬝ᵥ z

namespace IsStrongSeparationOracle

variable {P : Set (ι → ℝ)} {sep : (ι → ℝ) → Option (ι → ℝ)}

/-- A strong separation oracle decides membership: it answers `none` exactly on `P`. -/
theorem eq_none_iff (h : IsStrongSeparationOracle P sep) {z : ι → ℝ} : sep z = none ↔ z ∈ P := by
  refine ⟨h.mem_of_eq_none, fun hz => ?_⟩
  cases hs : sep z with
  | none => rfl
  | some a => exact absurd (h.separates hs z hz) (lt_irrefl _)

end IsStrongSeparationOracle

/-- The state of the ellipsoid method: the current ellipsoid `ellipsoid shape center`. -/
structure State (ι : Type*) where
  /-- The shape matrix `A` of the current ellipsoid `E(A, c)`. -/
  shape : Matrix ι ι ℝ
  /-- The center `c` of the current ellipsoid `E(A, c)`. -/
  center : ι → ℝ

/-- One step of the central-cut ellipsoid method: query the oracle at the center; if it answers
`none` the center lies in `P` and the state is kept, otherwise cut through the center with the
returned normal [GrotschelLovaszSchrijver1988, Section 3.1]. -/
noncomputable def step (sep : (ι → ℝ) → Option (ι → ℝ)) (s : State ι) : State ι :=
  match sep s.center with
  | none => s
  | some a => ⟨centralCutShape s.shape a, centralCutCenter s.shape s.center a⟩

/-- `N` steps of the central-cut ellipsoid method started from `E(A₀, c₀)`. -/
noncomputable def run (sep : (ι → ℝ) → Option (ι → ℝ)) (A₀ : Matrix ι ι ℝ) (c₀ : ι → ℝ) :
    ℕ → State ι
  | 0 => ⟨A₀, c₀⟩
  | N + 1 => step sep (run sep A₀ c₀ N)

variable {sep : (ι → ℝ) → Option (ι → ℝ)}

theorem step_of_eq_none {s : State ι} (h : sep s.center = none) : step sep s = s := by
  simp [step, h]

theorem step_of_eq_some {s : State ι} {a : ι → ℝ} (h : sep s.center = some a) :
    step sep s = ⟨centralCutShape s.shape a, centralCutCenter s.shape s.center a⟩ := by
  simp [step, h]

@[simp]
theorem run_zero (A₀ : Matrix ι ι ℝ) (c₀ : ι → ℝ) : run sep A₀ c₀ 0 = ⟨A₀, c₀⟩ := by
  rw [run]

theorem run_succ (A₀ : Matrix ι ι ℝ) (c₀ : ι → ℝ) (N : ℕ) :
    run sep A₀ c₀ (N + 1) = step sep (run sep A₀ c₀ N) := by
  rw [run]

variable {P : Set (ι → ℝ)}

/-- Every shape produced by the method is positive definite. -/
theorem posDef_run_shape (hsep : IsStrongSeparationOracle P sep) {A₀ : Matrix ι ι ℝ}
    (hA₀ : A₀.PosDef) (c₀ : ι → ℝ) (N : ℕ) : (run sep A₀ c₀ N).shape.PosDef := by
  induction N with
  | zero => exact hA₀
  | succ N ih =>
    rw [run_succ]
    cases hs : sep (run sep A₀ c₀ N).center with
    | none => rwa [step_of_eq_none hs]
    | some a => rw [step_of_eq_some hs]; exact ih.centralCutShape (hsep.ne_zero_of_eq_some hs)

variable [DecidableEq ι]

/-- Every ellipsoid produced by the method contains `P`, if the initial one does. -/
theorem subset_ellipsoid_run (hsep : IsStrongSeparationOracle P sep) {A₀ : Matrix ι ι ℝ}
    (hA₀ : A₀.PosDef) {c₀ : ι → ℝ} (hP : P ⊆ ellipsoid A₀ c₀) (N : ℕ) :
    P ⊆ ellipsoid (run sep A₀ c₀ N).shape (run sep A₀ c₀ N).center := by
  induction N with
  | zero => exact hP
  | succ N ih =>
    rw [run_succ]
    cases hs : sep (run sep A₀ c₀ N).center with
    | none => rwa [step_of_eq_none hs]
    | some a =>
      rw [step_of_eq_some hs]
      exact fun x hx => ellipsoid_inter_halfspace_subset (posDef_run_shape hsep hA₀ c₀ N)
        (hsep.ne_zero_of_eq_some hs) _ ⟨ih hx, (hsep.separates hs x hx).le⟩

/-- **Volume decrease of the ellipsoid method**: after `N` steps either the current center lies in
`P` or the current ellipsoid has volume at most `exp (-N / (2 (n + 1)))` times the initial one,
where `n = card ι` [GrotschelLovaszSchrijver1988, Section 3.1], [BertsimasTsitsiklis1997,
Section 8.2]. -/
theorem center_mem_or_volume_ellipsoid_run_le (hsep : IsStrongSeparationOracle P sep)
    {A₀ : Matrix ι ι ℝ} (hA₀ : A₀.PosDef) (c₀ : ι → ℝ) (N : ℕ) :
    (run sep A₀ c₀ N).center ∈ P ∨
      volume (ellipsoid (run sep A₀ c₀ N).shape (run sep A₀ c₀ N).center) ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) / (2 * ((Fintype.card ι : ℝ) + 1)))) *
          volume (ellipsoid A₀ c₀) := by
  induction N with
  | zero => right; simp
  | succ N ih =>
    rw [run_succ]
    cases hs : sep (run sep A₀ c₀ N).center with
    | none => left; rw [step_of_eq_none hs]; exact hsep.mem_of_eq_none hs
    | some a =>
      right
      rw [step_of_eq_some hs]
      have hc : (run sep A₀ c₀ N).center ∉ P := fun h =>
        absurd (hsep.separates hs _ h) (lt_irrefl _)
      refine (volume_ellipsoid_centralCut_lt (posDef_run_shape hsep hA₀ c₀ N)
        (hsep.ne_zero_of_eq_some hs) _).le.trans ?_
      refine (mul_le_mul_right (ih.resolve_left hc) _).trans_eq ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 3
      push_cast
      ring

/-- **The ellipsoid method with a strong separation oracle**: if `P ⊆ E(A₀, c₀)`, then after `N`
steps either the current center lies in `P` or
`vol P ≤ exp (-N / (2 (n + 1))) · vol E(A₀, c₀)` [GrotschelLovaszSchrijver1988, Section 3.1],
[BertsimasTsitsiklis1997, Section 8.2]. Arithmetic is exact over `ℝ`. -/
theorem center_mem_or_volume_le (hsep : IsStrongSeparationOracle P sep) {A₀ : Matrix ι ι ℝ}
    (hA₀ : A₀.PosDef) {c₀ : ι → ℝ} (hP : P ⊆ ellipsoid A₀ c₀) (N : ℕ) :
    (run sep A₀ c₀ N).center ∈ P ∨
      volume P ≤
        ENNReal.ofReal (Real.exp (-(N : ℝ) / (2 * ((Fintype.card ι : ℝ) + 1)))) *
          volume (ellipsoid A₀ c₀) :=
  (center_mem_or_volume_ellipsoid_run_le hsep hA₀ c₀ N).imp_right
    ((measure_mono (subset_ellipsoid_run hsep hA₀ hP N)).trans)

/-- **Iteration bound**: if `P ⊆ E(A₀, c₀)`, `0 < v` and `N > 2 (n + 1) ln (vol E(A₀, c₀) / v)`,
then after `N` steps either the current center lies in `P` or `vol P < v`
[GrotschelLovaszSchrijver1988, Section 3.1], [BertsimasTsitsiklis1997, Section 8.2]. -/
theorem center_mem_or_volume_lt (hsep : IsStrongSeparationOracle P sep) {A₀ : Matrix ι ι ℝ}
    (hA₀ : A₀.PosDef) {c₀ : ι → ℝ} (hP : P ⊆ ellipsoid A₀ c₀) {v : ℝ} (hv : 0 < v) {N : ℕ}
    (hN : 2 * ((Fintype.card ι : ℝ) + 1) *
      Real.log ((volume (ellipsoid A₀ c₀)).toReal / v) < N) :
    (run sep A₀ c₀ N).center ∈ P ∨ volume P < ENNReal.ofReal v := by
  refine (center_mem_or_volume_le hsep hA₀ hP N).imp_right fun h => h.trans_lt ?_
  set V := (volume (ellipsoid A₀ c₀)).toReal with hV
  have hV0 : 0 < V := ENNReal.toReal_pos (volume_ellipsoid_pos hA₀ c₀).ne'
    (volume_ellipsoid_lt_top hA₀ c₀).ne
  have hn : (0 : ℝ) < 2 * ((Fintype.card ι : ℝ) + 1) := by positivity
  rw [← ENNReal.ofReal_toReal (volume_ellipsoid_lt_top hA₀ c₀).ne, ← hV,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_lt_ofReal_iff hv,
    ← lt_div_iff₀ hV0, ← Real.lt_log_iff_exp_lt (div_pos hv hV0), Real.log_div hv.ne' hV0.ne',
    neg_div, neg_lt, neg_sub, lt_div_iff₀ hn, ← Real.log_div hV0.ne' hv.ne']
  linarith

/-- **Ball sandwich**: if `P` contains a ball of radius `r > 0` and lies in the ball of radius `R`
about `c₀`, the method started from that ball finds a point of `P` within any
`N > 2 n (n + 1) ln (R / r)` steps [GrotschelLovaszSchrijver1988, Section 3.1],
[BertsimasTsitsiklis1997, Section 8.2]. -/
theorem center_mem_of_ball_subset (hsep : IsStrongSeparationOracle P sep) {r R : ℝ} (hr : 0 < r)
    (hR : 0 < R) {z c₀ : ι → ℝ} (hzP : {x | (x - z) ⬝ᵥ (x - z) ≤ r ^ 2} ⊆ P)
    (hPc : P ⊆ {x | (x - c₀) ⬝ᵥ (x - c₀) ≤ R ^ 2}) {N : ℕ}
    (hN : 2 * (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1) * Real.log (R / r) < N) :
    (run sep ((R ^ 2) • (1 : Matrix ι ι ℝ)) c₀ N).center ∈ P := by
  rw [← ellipsoid_sq_smul_one hr.ne'] at hzP
  rw [← ellipsoid_sq_smul_one hR.ne'] at hPc
  refine (center_mem_or_volume_le hsep (PosDef.sq_smul_one hR.ne') hPc N).resolve_right
    fun h => ?_
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have h1 := (measure_mono hzP).trans h
  rw [volume_ellipsoid_sq_smul_one hr, volume_ellipsoid_sq_smul_one hR, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le] at h1
  have h2 := (ENNReal.mul_le_mul_iff_left volume_ellipsoid_one_zero_pos.ne'
    volume_ellipsoid_one_zero_lt_top.ne).mp h1
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow,
    Real.log_pow] at h3
  have hn1 : (0 : ℝ) < 2 * (n + 1) := by positivity
  have h4 : (N : ℝ) ≤ 2 * (n + 1) * (Fintype.card ι * (Real.log R - Real.log r)) := by
    rw [neg_div, ← sub_eq_neg_add, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hn1] at h3
    linarith
  rw [Real.log_div hR.ne' hr.ne'] at hN
  rw [← hn_def] at h4
  linarith

end Cslib.Algorithms.Ellipsoid
