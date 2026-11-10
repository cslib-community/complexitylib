/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Moments/Variance.lean` and
-- `Mathlib/Probability/Independence/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
import Mathlib.Data.Set.Card
import Mathlib.Probability.Moments.Covariance

/-!
# Second-moment concentration for counts of locally dependent events

Let `Y` count the events `A k`, `k ∈ F`, of a probability space, and let `G` be a *dependency
relation*: events `A k` and `A l` with `¬ G k l` are independent. Then:

* the indicators of `A k` and `A l` have covariance zero when `¬ G k l`, and at most one always,
  so `Var Y ≤ |F| D` when each `k ∈ F` is related to at most `D` indices of `F`
  (`ProbabilityTheory.variance_sum_indicator_le`);
* by Chebyshev's inequality, `Y` deviates from its mean `∑ k, P(A k)` by at least `c > 0` with
  probability at most `|F| D / c ^ 2`
  (`ProbabilityTheory.measureReal_le_abs_sum_indicator_sub_le`).

The motivating dependency relation comes from product spaces. Under a product of probability
measures, functions of disjoint sets of coordinates are independent
(`ProbabilityTheory.indepFun_pi_of_dependsOn`), so events determined by the coordinates in sets
`S k` (in the sense of `DependsOn`) are independent whenever their sets are disjoint
(`ProbabilityTheory.indepSet_pi_of_dependsOn`). Counts of such *local* events concentrate when each
`S k` meets few of the others (`ProbabilityTheory.measureReal_pi_le_abs_sum_indicator_sub_le`).

## Main results

* `ProbabilityTheory.ncard_eq_sum_indicator`: the number of events that occur is the sum of their
  indicators.
* `ProbabilityTheory.ncard_lt_of_not_le_abs`: deviation bound on the number of events that occur.
* `ProbabilityTheory.variance_sum_indicator_le`: the variance of a count of events with a
  dependency relation.
* `ProbabilityTheory.measureReal_le_abs_sum_indicator_sub_le`: the corresponding deviation bound.
* `ProbabilityTheory.integral_sum_indicator_one`: the expected number of events that occur.
* `ProbabilityTheory.measureReal_nonpos_le_variance_div_sq`: the second moment method,
  `P(X ≤ 0) ≤ Var X / (E X) ^ 2` for square integrable `X` with `E X > 0`.
* `ProbabilityTheory.measureReal_forall_notMem_le`: the second moment method for a count of
  measurable events with positive mean `S`, stated through the pair probabilities `P(A k ∩ A l)`.
* `ProbabilityTheory.exists_measurable_comp_restrict`: a measurable function of finitely many
  coordinates factors measurably through the restriction to them.
* `ProbabilityTheory.indepFun_pi_of_dependsOn`, `ProbabilityTheory.indepSet_pi_of_dependsOn`:
  functions and events of disjoint sets of coordinates are independent under a product measure.
* `ProbabilityTheory.measureReal_pi_le_abs_sum_indicator_sub_le`: the deviation bound for local
  events in a product space.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Section 4.3][AlonSpencer2016]
-/

@[expose] public section

open MeasureTheory Finset

namespace ProbabilityTheory

section General

variable {Ω κ : Type*}

/-- The number of events that occur is the sum of their indicators. -/
theorem ncard_eq_sum_indicator [Fintype κ] (A : κ → Set Ω) (ω : Ω) :
    ({k | ω ∈ A k}.ncard : ℝ) = ∑ k, (A k).indicator (1 : Ω → ℝ) ω := by
  classical
  simp only [Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole, ← Set.ncard_coe_finset, Finset.coe_filter_univ]

/-- Outside the event that the number of events that occur deviates from `m` by at least `c`,
this number is below `m + c`. -/
theorem ncard_lt_of_not_le_abs [Fintype κ] {A : κ → Set Ω} {ω : Ω} {m c : ℝ}
    (h : ¬c ≤ |∑ k, (A k).indicator (1 : Ω → ℝ) ω - m|) : ({k | ω ∈ A k}.ncard : ℝ) < m + c := by
  rw [ncard_eq_sum_indicator]
  linarith [le_abs_self (∑ k, (A k).indicator (1 : Ω → ℝ) ω - m), not_le.mp h]

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The unit indicator of a measurable set is square integrable under a finite measure. -/
private theorem memLp_indicator_one {s : Set Ω} (hs : MeasurableSet s) :
    MemLp (s.indicator (1 : Ω → ℝ)) 2 P :=
  memLp_indicator_const 2 hs.nullMeasurableSet 1 (Or.inr (measure_ne_top P s))

/-- The covariance of the indicators of two events is `P(s ∩ t) - P(s) P(t)`. -/
private theorem covariance_indicator_one {s t : Set Ω} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    cov[s.indicator (1 : Ω → ℝ), t.indicator (1 : Ω → ℝ); P] =
      P.real (s ∩ t) - P.real s * P.real t := by
  rw [covariance_eq_sub (memLp_indicator_one hs) (memLp_indicator_one ht),
    ← Set.inter_indicator_one, integral_indicator_one (hs.inter ht), integral_indicator_one hs,
    integral_indicator_one ht]

/-- The expected number of events `A k`, `k ∈ F`, that occur is `∑ k ∈ F, P(A k)`. -/
theorem integral_sum_indicator_one (F : Finset κ) {A : κ → Set Ω}
    (hA : ∀ k ∈ F, MeasurableSet (A k)) :
    ∫ ω, ∑ k ∈ F, (A k).indicator (1 : Ω → ℝ) ω ∂P = ∑ k ∈ F, P.real (A k) := by
  rw [integral_finsetSum _ fun k hk => (memLp_indicator_one (hA k hk)).integrable one_le_two]
  exact sum_congr rfl fun k hk => integral_indicator_one (hA k hk)

/-- **The variance of a count of events.** If events `A k` and `A l` with `¬ G k l` are
independent, and each `k ∈ F` is related by `G` to at most `D` indices of `F`, then the number of
events `A k`, `k ∈ F`, that occur has variance at most `|F| D`. -/
theorem variance_sum_indicator_le (F : Finset κ) {A : κ → Set Ω}
    (hA : ∀ k ∈ F, MeasurableSet (A k)) (G : κ → κ → Prop) [DecidableRel G]
    (hG : ∀ k ∈ F, ∀ l ∈ F, ¬ G k l → IndepSet (A k) (A l) P) {D : ℕ}
    (hD : ∀ k ∈ F, #{l ∈ F | G k l} ≤ D) :
    Var[fun ω => ∑ k ∈ F, (A k).indicator (1 : Ω → ℝ) ω; P] ≤ #F * D := by
  rw [variance_fun_sum' fun k hk => memLp_indicator_one (hA k hk)]
  calc ∑ k ∈ F, ∑ l ∈ F, cov[(A k).indicator 1, (A l).indicator 1; P]
      ≤ ∑ k ∈ F, ∑ l ∈ F, if G k l then (1 : ℝ) else 0 := by
        refine sum_le_sum fun k hk => sum_le_sum fun l hl => ?_
        rw [covariance_indicator_one (hA k hk) (hA l hl)]
        split_ifs with hkl
        · have h₁ : P.real (A k ∩ A l) ≤ 1 := measureReal_le_one
          nlinarith [measureReal_nonneg (μ := P) (s := A k),
            measureReal_nonneg (μ := P) (s := A l)]
        · rw [measureReal_def, (hG k hk l hl hkl).measure_inter_eq_mul, ENNReal.toReal_mul,
            measureReal_def, measureReal_def, sub_self]
    _ = ∑ k ∈ F, (#{l ∈ F | G k l} : ℝ) := by
        simp only [sum_boole]
    _ ≤ ∑ _k ∈ F, (D : ℝ) := sum_le_sum fun k hk => by exact_mod_cast hD k hk
    _ = #F * D := by simp

/-- **Second-moment concentration.** If events `A k` and `A l` with `¬ G k l` are independent,
and each `k ∈ F` is related by `G` to at most `D` indices of `F`, then the number of events
`A k`, `k ∈ F`, that occur deviates from its mean by at least `c > 0` with probability at most
`|F| D / c ^ 2`. -/
theorem measureReal_le_abs_sum_indicator_sub_le (F : Finset κ) {A : κ → Set Ω}
    (hA : ∀ k ∈ F, MeasurableSet (A k)) (G : κ → κ → Prop) [DecidableRel G]
    (hG : ∀ k ∈ F, ∀ l ∈ F, ¬ G k l → IndepSet (A k) (A l) P) {D : ℕ}
    (hD : ∀ k ∈ F, #{l ∈ F | G k l} ≤ D) {c : ℝ} (hc : 0 < c) :
    P.real {ω | c ≤ |∑ k ∈ F, (A k).indicator (1 : Ω → ℝ) ω - ∑ k ∈ F, P.real (A k)|} ≤
      #F * D / c ^ 2 := by
  have hY : MemLp (fun ω => ∑ k ∈ F, (A k).indicator (1 : Ω → ℝ) ω) 2 P :=
    memLp_finsetSum F fun k hk => memLp_indicator_one (hA k hk)
  have hmean := integral_sum_indicator_one (P := P) F hA
  have cheb := meas_ge_le_variance_div_sq hY hc
  rw [hmean] at cheb
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (cheb.trans ?_)
  exact ENNReal.ofReal_le_ofReal
    (by gcongr; exact variance_sum_indicator_le F hA G hG hD)

/-- **The second moment method** [Alon and Spencer, Section 4.3][AlonSpencer2016]: under a
probability measure, a square integrable random variable `X` with `E X > 0` is nonpositive with
probability at most `Var X / (E X) ^ 2`. -/
theorem measureReal_nonpos_le_variance_div_sq {X : Ω → ℝ} (hX : MemLp X 2 P) (hX₀ : 0 < P[X]) :
    P.real {ω | X ω ≤ 0} ≤ Var[X; P] / P[X] ^ 2 := by
  have hsub : {ω | X ω ≤ 0} ⊆ {ω | P[X] ≤ |X ω - P[X]|} := fun ω hω => by
    rw [Set.mem_ofPred_eq] at hω ⊢
    rw [abs_sub_comm]
    exact le_abs.2 (Or.inl (by linarith))
  calc P.real {ω | X ω ≤ 0} ≤ P.real {ω | P[X] ≤ |X ω - P[X]|} := measureReal_mono hsub
    _ ≤ Var[X; P] / P[X] ^ 2 := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))
        (meas_ge_le_variance_div_sq hX hX₀)

/-- **The second moment method for a count of events**
[Alon and Spencer, Section 4.3][AlonSpencer2016]. Under a probability measure, if the events `A k`
are measurable and `S = ∑ k ∈ F, P(A k) > 0`, then the probability that none of the events `A k`,
`k ∈ F`, occurs is at most `(∑ k ∈ F, ∑ l ∈ F, P(A k ∩ A l) - S ^ 2) / S ^ 2`: the variance of
the number of events that occur, divided by the square of its mean. -/
theorem measureReal_forall_notMem_le (F : Finset κ) {A : κ → Set Ω}
    (hA : ∀ k ∈ F, MeasurableSet (A k)) (hS : 0 < ∑ k ∈ F, P.real (A k)) :
    P.real {ω | ∀ k ∈ F, ω ∉ A k} ≤
      (∑ k ∈ F, ∑ l ∈ F, P.real (A k ∩ A l) - (∑ k ∈ F, P.real (A k)) ^ 2) /
        (∑ k ∈ F, P.real (A k)) ^ 2 := by
  set Y : Ω → ℝ := fun ω => ∑ k ∈ F, (A k).indicator (1 : Ω → ℝ) ω with hYdef
  have hY : MemLp Y 2 P := memLp_finsetSum F fun k hk => memLp_indicator_one (hA k hk)
  have hmean : P[Y] = ∑ k ∈ F, P.real (A k) := integral_sum_indicator_one F hA
  have hvar : Var[Y; P] =
      ∑ k ∈ F, ∑ l ∈ F, P.real (A k ∩ A l) - (∑ k ∈ F, P.real (A k)) ^ 2 := by
    rw [hYdef, variance_fun_sum' fun k hk => memLp_indicator_one (hA k hk), sq, sum_mul_sum,
      ← sum_sub_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun l hl => covariance_indicator_one (hA k hk) (hA l hl)
  have hsub : {ω | ∀ k ∈ F, ω ∉ A k} ⊆ {ω | Y ω ≤ 0} := fun ω hω => by
    rw [Set.mem_ofPred_eq] at hω ⊢
    change ∑ k ∈ F, (A k).indicator (1 : Ω → ℝ) ω ≤ 0
    rw [sum_eq_zero fun k hk => Set.indicator_of_notMem (hω k hk) _]
  calc P.real {ω | ∀ k ∈ F, ω ∉ A k} ≤ P.real {ω | Y ω ≤ 0} := measureReal_mono hsub
    _ ≤ Var[Y; P] / P[Y] ^ 2 := measureReal_nonpos_le_variance_div_sq hY (hmean ▸ hS)
    _ = _ := by rw [hvar, hmean]

end General

section Pi

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {μ : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]

omit [Fintype ι] in
/-- A measurable function of the coordinates in a finite set `S` factors measurably through the
restriction to `S`: freeze the other coordinates at `ω₀`. -/
theorem exists_measurable_comp_restrict {β : Type*} [MeasurableSpace β]
    {f : (Π i, Ω i) → β} (hf : Measurable f) {S : Finset ι} (hfS : DependsOn f (S : Set ι))
    (ω₀ : Π i, Ω i) : ∃ g : (Π i : S, Ω i) → β, Measurable g ∧ f = g ∘ fun ω (i : S) => ω i := by
  classical
  refine ⟨fun y => f (Function.updateFinset ω₀ S y), hf.comp measurable_updateFinset, ?_⟩
  funext ω
  exact (hfS fun i hi => by simp [Function.updateFinset, Finset.mem_coe.1 hi]).symm

/-- **Functions of disjoint sets of coordinates are independent** under a product of probability
measures. -/
theorem indepFun_pi_of_dependsOn {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {f : (Π i, Ω i) → β} {g : (Π i, Ω i) → γ}
    {S T : Set ι} (hfS : DependsOn f S) (hgT : DependsOn g T) (hST : Disjoint S T) :
    IndepFun f g (Measure.pi μ) := by
  classical
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure (Measure.pi μ)
  let e := MeasurableEquiv.piEquivPiSubtypeProd Ω (· ∈ S)
  let ν₁ : Measure (Π i : {i // i ∈ S}, Ω i) := Measure.pi fun i => μ i.1
  let ν₂ : Measure (Π i : {i // i ∉ S}, Ω i) := Measure.pi fun i => μ i.1
  have he : MeasurePreserving e (Measure.pi μ) (ν₁.prod ν₂) :=
    measurePreserving_piEquivPiSubtypeProd μ (· ∈ S)
  let y₀ : Π i : {i // i ∉ S}, Ω i := fun i => ω₀ i.1
  let x₀ : Π i : {i // i ∈ S}, Ω i := fun i => ω₀ i.1
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B _ _
  let C : Set (Π i : {i // i ∈ S}, Ω i) := {x | f (e.symm (x, y₀)) ∈ A}
  let D : Set (Π i : {i // i ∉ S}, Ω i) := {y | g (e.symm (x₀, y)) ∈ B}
  have hf_eq : ∀ ω, f ω = f (e.symm ((e ω).1, y₀)) := by
    intro ω
    refine hfS fun i hi => ?_
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  have hg_eq : ∀ ω, g ω = g (e.symm (x₀, (e ω).2)) := by
    intro ω
    refine hgT fun i hi => ?_
    have hiS : i ∉ S := Set.disjoint_right.1 hST hi
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply, hiS]
  have hpreA : f ⁻¹' A = e ⁻¹' (C ×ˢ Set.univ) := by
    ext ω
    simp [C, hf_eq ω]
  have hpreB : g ⁻¹' B = e ⁻¹' (Set.univ ×ˢ D) := by
    ext ω
    simp [D, hg_eq ω]
  have hpreAB : f ⁻¹' A ∩ g ⁻¹' B = e ⁻¹' (C ×ˢ D) := by
    ext ω
    simp [C, D, hf_eq ω, hg_eq ω]
  rw [hpreAB, hpreA, hpreB, he.measure_preimage_equiv, he.measure_preimage_equiv,
    he.measure_preimage_equiv, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    measure_univ, measure_univ, mul_one, one_mul]

/-- **Events of disjoint sets of coordinates are independent** under a product of probability
measures. -/
theorem indepSet_pi_of_dependsOn {A B : Set (Π i, Ω i)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) {S T : Set ι} (hAS : DependsOn (· ∈ A) S) (hBT : DependsOn (· ∈ B) T)
    (hST : Disjoint S T) : IndepSet A B (Measure.pi μ) := by
  have h := (indepFun_pi_of_dependsOn (μ := μ) hAS
    hBT hST).measure_inter_preimage_eq_mul {True} {True} (measurableSet_singleton _)
      (measurableSet_singleton _)
  have hpre : ∀ C : Set (Π i, Ω i), (· ∈ C) ⁻¹' {True} = C := fun C => by
    ext
    simp
  rw [hpre, hpre] at h
  exact (indepSet_iff_measure_inter_eq_mul hA hB _).2 h

/-- **Second-moment concentration for local events.** Under a product of probability measures,
let each event `A k` depend only on the coordinates in `S k`, where `S k` and `S l` are disjoint
unless `G k l`, and let each `k ∈ F` be related by `G` to at most `D` indices of `F`. Then the
number of events `A k`, `k ∈ F`, that occur deviates from its mean by at least `c > 0` with
probability at most `|F| D / c ^ 2`. -/
theorem measureReal_pi_le_abs_sum_indicator_sub_le {κ : Type*} (F : Finset κ)
    {A : κ → Set (Π i, Ω i)} (hA : ∀ k ∈ F, MeasurableSet (A k)) (S : κ → Set ι)
    (hAS : ∀ k ∈ F, DependsOn (· ∈ A k) (S k)) (G : κ → κ → Prop) [DecidableRel G]
    (hG : ∀ k ∈ F, ∀ l ∈ F, ¬ G k l → Disjoint (S k) (S l)) {D : ℕ}
    (hD : ∀ k ∈ F, #{l ∈ F | G k l} ≤ D) {c : ℝ} (hc : 0 < c) :
    (Measure.pi μ).real {ω | c ≤ |∑ k ∈ F, (A k).indicator (1 : (Π i, Ω i) → ℝ) ω -
        ∑ k ∈ F, (Measure.pi μ).real (A k)|} ≤ #F * D / c ^ 2 :=
  measureReal_le_abs_sum_indicator_sub_le F hA G (fun k hk l hl hkl =>
    indepSet_pi_of_dependsOn (hA k hk) (hA l hl) (hAS k hk) (hAS l hl) (hG k hk l hl hkl)) hD hc

end Pi

end ProbabilityTheory
