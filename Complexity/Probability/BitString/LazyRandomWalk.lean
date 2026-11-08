/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.MarkovChain.Coupling
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Map
import Complexity.Probability.PMF.ToReal
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.PMF.EventBind

/-!
# The lazy random walk on the hypercube

The lazy random walk on `{0,1}^ι` (`Cslib.BitString.lazyRandomWalk`) picks a coordinate `i` and a
fair bit `b` uniformly and independently and overwrites coordinate `i` by `b`
([LevinPeres2017], Sections 2.3 and 5.3.1). It is reversible with respect to the uniform
distribution.

The coordinate-refresh coupling (`Cslib.BitString.lazyRandomWalkCoupling`) uses the same
coordinate and the same bit in both copies, so once coordinate `i` has been chosen the copies
agree there forever. A fixed coordinate is never chosen in `t` steps with probability
`(1 - 1/n)^t`, where `n = |ι|`. The union bound over the coordinates is the coupon-collector tail
bound of [LevinPeres2017], Proposition 2.4, and with the coupling bound
(Corollary 5.5) gives

* `d(t) ≤ n (1 - 1/n)^t ≤ n e^{-t/n}` (`Cslib.BitString.distToStationary_lazyRandomWalk_le`,
  `Cslib.BitString.distToStationary_lazyRandomWalk_le_exp`), and
* `t_mix(ε) ≤ ⌈n log n + n log ε⁻¹⌉` for every `ε > 0`
  (`Cslib.BitString.mixingTime_lazyRandomWalk_le`).

The last bound is [LevinPeres2017], (5.6), with a ceiling: (5.6) is printed as
`t_mix(ε) ≤ n log n + log(1/ε) n`, which fails without rounding up for `n = 1` and `ε = 2/5`, where
`t_mix(ε) = 1 > log (5/2)`. The ceiling is what Proposition 2.4 gives; the library's Markov chain
tests check this instance.

## Main definitions

* `Cslib.BitString.lazyRandomWalk`: the lazy random walk on `ι → Bool`.
* `Cslib.BitString.lazyRandomWalkCoupling`: the coordinate-refresh coupling.

## Main results

* `Cslib.BitString.isReversible_lazyRandomWalk`, `Cslib.BitString.isStationary_lazyRandomWalk`:
  the uniform distribution is reversible and stationary.
* `Cslib.BitString.isMarkovianCoupling_lazyRandomWalkCoupling`,
  `Cslib.BitString.isSticky_lazyRandomWalkCoupling`: the coupling is Markovian and sticky.
* `Cslib.BitString.distToStationary_lazyRandomWalk_le`,
  `Cslib.BitString.distToStationary_lazyRandomWalk_le_exp`: `d(t) ≤ n (1 - 1/n)^t ≤ n e^{-t/n}`.
* `Cslib.BitString.mixingTime_lazyRandomWalk_le`: `t_mix(ε) ≤ ⌈n log n + n log ε⁻¹⌉`.

## References

* [LevinPeres2017], Sections 2.2, 2.3 and 5.3.1.
-/

public section

open scoped ENNReal Cslib.Probability.PMF

namespace Cslib.BitString

open Cslib.Probability Cslib.Probability.PMF Cslib.Probability.MarkovChain

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The lazy random walk on the hypercube `ι → Bool`: overwrite a uniformly random coordinate by
a fair bit ([LevinPeres2017], Sections 2.3 and 5.3.1). -/
noncomputable def lazyRandomWalk : MarkovChain (ι → Bool) :=
  ⟨fun x => (PMF.uniformOfFintype (ι × Bool)).map fun ib => Function.update x ib.1 ib.2⟩

/-- The coordinate-refresh coupling of two lazy random walks on the hypercube: both copies
overwrite the same uniformly random coordinate by the same fair bit
([LevinPeres2017], Section 5.3.1). -/
noncomputable def lazyRandomWalkCoupling : MarkovChain ((ι → Bool) × (ι → Bool)) :=
  ⟨fun z => (PMF.uniformOfFintype (ι × Bool)).map fun ib =>
    (Function.update z.1 ib.1 ib.2, Function.update z.2 ib.1 ib.2)⟩

variable {ι}

/-- The lazy random walk has a symmetric transition matrix. -/
theorem lazyRandomWalk_apply_comm (x y : ι → Bool) :
    lazyRandomWalk ι x y = lazyRandomWalk ι y x := by
  change ((PMF.uniformOfFintype (ι × Bool)).map _) y = ((PMF.uniformOfFintype (ι × Bool)).map _) x
  rw [uniformOfFintype_map_apply, uniformOfFintype_map_apply]
  congr 2
  refine Nat.card_congr
    { toFun := fun p => ⟨(p.1.1, x p.1.1), ?_⟩
      invFun := fun p => ⟨(p.1.1, y p.1.1), ?_⟩
      left_inv := fun p => ?_
      right_inv := fun p => ?_ } <;>
  · obtain ⟨⟨i, b⟩, hp⟩ := p
    simp only at hp ⊢
    subst hp
    simp

/-- The lazy random walk is reversible with respect to the uniform distribution. -/
theorem isReversible_lazyRandomWalk :
    (lazyRandomWalk ι).IsReversible (PMF.uniformOfFintype _) := by
  intro x y
  rw [PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, lazyRandomWalk_apply_comm]

/-- The uniform distribution is stationary for the lazy random walk. -/
theorem isStationary_lazyRandomWalk :
    (lazyRandomWalk ι).IsStationary (PMF.uniformOfFintype _) :=
  isReversible_lazyRandomWalk.isStationary

/-- Each copy of the coordinate-refresh coupling is a lazy random walk. -/
theorem isMarkovianCoupling_lazyRandomWalkCoupling :
    (lazyRandomWalk ι).IsMarkovianCoupling (lazyRandomWalkCoupling ι) where
  map_fst _ := PMF.map_comp _ _ _
  map_snd _ := PMF.map_comp _ _ _

/-- The coordinate-refresh coupling is sticky. -/
theorem isSticky_lazyRandomWalkCoupling : IsSticky (lazyRandomWalkCoupling ι) := by
  intro x w hw
  change w ∈ (PMF.map _ _).support at hw
  rw [PMF.support_map] at hw
  obtain ⟨_, -, rfl⟩ := hw
  rfl

/-- One step of the coordinate-refresh coupling leaves an unmatched coordinate unmatched with
probability `(n - 1)/n` and never unmatches a matched coordinate. -/
theorem lazyRandomWalkCoupling_toOuterMeasure_ne (i : ι) (z : (ι → Bool) × (ι → Bool)) :
    (lazyRandomWalkCoupling ι z).toOuterMeasure {w | w.1 i ≠ w.2 i} =
      if z.1 i ≠ z.2 i then ((Fintype.card ι - 1 : ℕ) : ℝ≥0∞) / Fintype.card ι else 0 := by
  change ((PMF.uniformOfFintype (ι × Bool)).map _).toOuterMeasure _ = _
  rw [PMF.toOuterMeasure_map_apply]
  have hpre : (fun ib : ι × Bool =>
      (Function.update z.1 ib.1 ib.2, Function.update z.2 ib.1 ib.2)) ⁻¹'
        {w | w.1 i ≠ w.2 i} = {ib | ib.1 ≠ i ∧ z.1 i ≠ z.2 i} := by
    ext ⟨j, b⟩
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Function.update_of_ne (Ne.symm hj), hj]
  rw [hpre]
  split_ifs with hz
  · have hfst : {ib : ι × Bool | ib.1 ≠ i ∧ z.1 i ≠ z.2 i} = Prod.fst ⁻¹' {j | j ≠ i} := by
      ext ⟨j, b⟩
      simp [hz]
    rw [hfst, ← PMF.toOuterMeasure_map_apply, uniformOfFintype_prod_map_fst,
      toOuterMeasure_uniformOfFintype, div_eq_mul_inv]
    congr 2
    have hfin : Finset.univ.filter (· ∈ {j : ι | j ≠ i}) = Finset.univ.erase i := by
      ext j
      simp
    rw [hfin, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  · simp only [hz, and_false, Set.ofPred_false, PMF.toOuterMeasure_apply_eq_zero_iff,
      Set.disjoint_empty]

/-- After `t` steps of the coordinate-refresh coupling, a fixed coordinate is still unmatched with
probability at most `(1 - 1/n)^t`. -/
theorem lazyRandomWalkCoupling_pow_toOuterMeasure_ne_le (i : ι) (t : ℕ)
    (z : (ι → Bool) × (ι → Bool)) :
    (((lazyRandomWalkCoupling ι ^ t) z).toOuterMeasure {w | w.1 i ≠ w.2 i}).toReal ≤
      (1 - (Fintype.card ι : ℝ)⁻¹) ^ t := by
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hstep : ((((Fintype.card ι - 1 : ℕ) : ℝ≥0∞) / Fintype.card ι)).toReal =
      1 - (Fintype.card ι : ℝ)⁻¹ := by
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      Nat.cast_sub Fintype.card_pos, Nat.cast_one]
    field_simp
  induction t generalizing z with
  | zero =>
    rw [pow_zero]
    exact toOuterMeasure_toReal_le_one _ _
  | succ t ih =>
    rw [pow_succ_apply]
    have hle := toOuterMeasure_bind_le_mul_ennreal ((lazyRandomWalkCoupling ι ^ t) z)
      (lazyRandomWalkCoupling ι) {w | w.1 i ≠ w.2 i} {w | w.1 i ≠ w.2 i} le_rfl
      (q₂ := ((Fintype.card ι - 1 : ℕ) : ℝ≥0∞) / Fintype.card ι)
      (fun a _ ha => by
        have ha' : a.1 i ≠ a.2 i := ha
        rw [lazyRandomWalkCoupling_toOuterMeasure_ne, ite_eq_left ha'])
      (fun a _ ha => by
        have ha' : ¬a.1 i ≠ a.2 i := ha
        rw [lazyRandomWalkCoupling_toOuterMeasure_ne, ite_eq_right ha'])
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (toOuterMeasure_ne_top _ _)
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp))) hle).trans ?_
    rw [ENNReal.toReal_mul, hstep, pow_succ]
    exact mul_le_mul_of_nonneg_right (ih z) (by linarith [inv_le_one_of_one_le₀ hn])

/-- After `t` steps of the coordinate-refresh coupling, the copies differ with probability at most
`n (1 - 1/n)^t` (union bound over coordinates, [LevinPeres2017], Proposition 2.4). -/
theorem lazyRandomWalkCoupling_pow_toOuterMeasure_le (t : ℕ) (z : (ι → Bool) × (ι → Bool)) :
    (((lazyRandomWalkCoupling ι ^ t) z).toOuterMeasure {w | w.1 ≠ w.2}).toReal ≤
      Fintype.card ι * (1 - (Fintype.card ι : ℝ)⁻¹) ^ t := by
  have hsub : {w : (ι → Bool) × (ι → Bool) | w.1 ≠ w.2} = ⋃ i, {w | w.1 i ≠ w.2 i} := by
    ext w
    simp [Function.ne_iff]
  rw [hsub]
  calc (((lazyRandomWalkCoupling ι ^ t) z).toOuterMeasure (⋃ i, {w | w.1 i ≠ w.2 i})).toReal
      ≤ (∑ i, ((lazyRandomWalkCoupling ι ^ t) z).toOuterMeasure {w | w.1 i ≠ w.2 i}).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun _ _ => toOuterMeasure_ne_top _ _)
          (MeasureTheory.measure_iUnion_fintype_le _ _)
    _ = ∑ i, (((lazyRandomWalkCoupling ι ^ t) z).toOuterMeasure {w | w.1 i ≠ w.2 i}).toReal :=
        ENNReal.toReal_sum fun _ _ => toOuterMeasure_ne_top _ _
    _ ≤ ∑ _i : ι, (1 - (Fintype.card ι : ℝ)⁻¹) ^ t :=
        Finset.sum_le_sum fun i _ => lazyRandomWalkCoupling_pow_toOuterMeasure_ne_le i t z
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `d(t) ≤ n (1 - 1/n)^t` for the lazy random walk on the hypercube. -/
theorem distToStationary_lazyRandomWalk_le (t : ℕ) :
    (lazyRandomWalk ι).distToStationary (PMF.uniformOfFintype _) t ≤
      Fintype.card ι * (1 - (Fintype.card ι : ℝ)⁻¹) ^ t :=
  distToStationary_le_of_coupling isStationary_lazyRandomWalk
    (fun _ _ => lazyRandomWalkCoupling ι) (fun _ _ => isMarkovianCoupling_lazyRandomWalkCoupling)
    (fun x y => lazyRandomWalkCoupling_pow_toOuterMeasure_le t (x, y))

/-- `d(t) ≤ n e^{-t/n}` for the lazy random walk on the hypercube
([LevinPeres2017], Section 5.3.1). -/
theorem distToStationary_lazyRandomWalk_le_exp (t : ℕ) :
    (lazyRandomWalk ι).distToStationary (PMF.uniformOfFintype _) t ≤
      Fintype.card ι * Real.exp (-(t / Fintype.card ι)) := by
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine (distToStationary_lazyRandomWalk_le t).trans ?_
  gcongr
  calc (1 - (Fintype.card ι : ℝ)⁻¹) ^ t ≤ Real.exp (-(Fintype.card ι : ℝ)⁻¹) ^ t := by
        refine pow_le_pow_left₀ (by linarith [inv_le_one_of_one_le₀ hn]) ?_ t
        linarith [Real.add_one_le_exp (-(Fintype.card ι : ℝ)⁻¹)]
    _ = Real.exp (-(t / Fintype.card ι)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- **Mixing time of the lazy hypercube walk** ([LevinPeres2017], (5.6), with the ceiling
made explicit): `t_mix(ε) ≤ ⌈n log n + n log ε⁻¹⌉` for every `ε > 0`, where `n = |ι|`. -/
theorem mixingTime_lazyRandomWalk_le {ε : ℝ} (hε : 0 < ε) :
    (lazyRandomWalk ι).mixingTime (PMF.uniformOfFintype _) ε ≤
      (⌈Fintype.card ι * Real.log (Fintype.card ι) +
        Fintype.card ι * Real.log ε⁻¹⌉₊ : ℕ) := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
  set t := ⌈n * Real.log n + n * Real.log ε⁻¹⌉₊
  refine mixingTime_le_of_distToStationary_le ?_
  refine (distToStationary_lazyRandomWalk_le_exp t).trans ?_
  have ht : n * Real.log n + n * Real.log ε⁻¹ ≤ t := Nat.le_ceil _
  have hdiv : Real.log n + Real.log ε⁻¹ ≤ t / n := by
    rw [le_div_iff₀ hn]
    linarith
  calc n * Real.exp (-(t / n)) ≤ n * Real.exp (-(Real.log n + Real.log ε⁻¹)) := by
        gcongr
    _ = ε := by
        rw [Real.exp_neg, Real.exp_add, Real.exp_log hn, Real.exp_log (inv_pos.mpr hε)]
        field_simp

end Cslib.BitString
