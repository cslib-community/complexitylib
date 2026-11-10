/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Resizable.Clocked
import CslibFrontier.Foundations.Analysis.ENNRealTsum

/-!
# Geometric `while`-loop exit distributions on the Resizable Word RAM

Iteration and limiting exit distributions (`loopStepRPMF`, `loopIterRPMF`, `loopExitRPMF`) and
state invariants (`RLoopStateInv`) on `RData r` for randomized Las Vegas `while` loops over the
word-granular **Resizable Word RAM** (`Cslib.WordRAM.Resizable`), mirroring the fixed-memory
absorbing `while`-loop exit calculus in `Cslib.WordRAM.Randomized.Expected` on `RData r` (including
the dynamic word frontier `frontier`).

## Main definitions

* `Cslib.WordRAM.Resizable.loopStepRPMF`, `Cslib.WordRAM.Resizable.loopIterRPMF`: single-step and
  `K`-step `while`-loop distributions on `RData r`.
* `Cslib.WordRAM.Resizable.RLoopStateInv`: combined active/exit loop invariant on `RData r`.
* `Cslib.WordRAM.Resizable.loopExitRPMF`: limiting exit distribution of a geometric `while` loop.

## Main results

* `Cslib.WordRAM.Resizable.hasSum_loopExitRDensity`: total exit probability equals `1` whenever
  each active step exits with probability bounded below by `p_exit > 0`.
* `Cslib.WordRAM.Resizable.loopExitRPMF_of_holds`,
  `Cslib.WordRAM.Resizable.loopExitRPMF_of_not_holds`,
  `Cslib.WordRAM.Resizable.mem_support_loopExitRPMF`: fixed-point unfolding and support invariant
  for `loopExitRPMF`.

## References

* [MitzenmacherUpfal2017] Michael Mitzenmacher and Eli Upfal, *Probability and Computing*, 2nd ed.,
  Cambridge University Press, 2017, Sections 2.1, 2.3, and 2.4.
-/

@[expose] public section

open scoped ENNReal

namespace Cslib.WordRAM.Resizable

variable {r : ℕ}

/-- One step of a `while` loop distribution on `RData r`. -/
noncomputable def loopStepRPMF (cond : Cond r) (μ_body : RData r → PMF (RData r)) (x : RData r) :
    PMF (RData r) :=
  open Classical in if cond.Holds x.toData then μ_body x else PMF.pure x

theorem loopStepRPMF_of_holds {cond : Cond r} {μ_body : RData r → PMF (RData r)} {x : RData r}
    (hc : cond.Holds x.toData) : loopStepRPMF cond μ_body x = μ_body x := by
  classical simp [loopStepRPMF, hc]

theorem loopStepRPMF_of_not_holds {cond : Cond r} {μ_body : RData r → PMF (RData r)} {x : RData r}
    (hc : ¬cond.Holds x.toData) : loopStepRPMF cond μ_body x = PMF.pure x := by
  classical simp [loopStepRPMF, hc]

/-- `K`-step iterate of `loopStepRPMF`. -/
noncomputable def loopIterRPMF (cond : Cond r) (μ_body : RData r → PMF (RData r)) :
    ℕ → RData r → PMF (RData r)
  | 0, x => PMF.pure x
  | K + 1, x => (loopStepRPMF cond μ_body x).bind (loopIterRPMF cond μ_body K)

@[simp] theorem loopIterRPMF_zero (cond : Cond r) (μ_body : RData r → PMF (RData r)) (x : RData r) :
    loopIterRPMF cond μ_body 0 x = PMF.pure x := rfl

theorem loopIterRPMF_succ (cond : Cond r) (μ_body : RData r → PMF (RData r)) (K : ℕ)
    (x : RData r) :
    loopIterRPMF cond μ_body (K + 1) x =
      (loopStepRPMF cond μ_body x).bind (loopIterRPMF cond μ_body K) := rfl

theorem loopIterRPMF_of_not_holds {cond : Cond r} {μ_body : RData r → PMF (RData r)} {x : RData r}
    (hc : ¬cond.Holds x.toData) (K : ℕ) :
    loopIterRPMF cond μ_body K x = PMF.pure x := by
  induction K with
  | zero => rfl
  | succ K ih => rw [loopIterRPMF_succ, loopStepRPMF_of_not_holds hc, PMF.pure_bind, ih]

theorem loopIterRPMF_succ_right (cond : Cond r) (μ_body : RData r → PMF (RData r)) (K : ℕ)
    (x : RData r) :
    loopIterRPMF cond μ_body (K + 1) x =
      (loopIterRPMF cond μ_body K x).bind (loopStepRPMF cond μ_body) := by
  induction K generalizing x with
  | zero => simp [loopIterRPMF]
  | succ K ih =>
    rw [loopIterRPMF_succ (K := K), PMF.bind_bind]
    exact congrArg ((loopStepRPMF cond μ_body x).bind ·) (funext ih)

theorem loopIterRPMF_indicator_mono (cond : Cond r) (μ_body : RData r → PMF (RData r))
    (x y : RData r) :
    Monotone fun K => Set.indicator {z : RData r | ¬cond.Holds z.toData}
      (loopIterRPMF cond μ_body K x) y := by
  intro K₁ K₂ hK
  dsimp only
  by_cases hy : y ∈ {z : RData r | ¬cond.Holds z.toData}
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    refine monotone_nat_of_le_succ (f := fun K => loopIterRPMF cond μ_body K x y) (fun K => ?_) hK
    rw [loopIterRPMF_succ_right, PMF.bind_apply]
    calc
      loopIterRPMF cond μ_body K x y
        = loopIterRPMF cond μ_body K x y * loopStepRPMF cond μ_body y y := by
          rw [loopStepRPMF_of_not_holds hy, PMF.pure_apply_self, mul_one]
      _ ≤ ∑' z, loopIterRPMF cond μ_body K x z * loopStepRPMF cond μ_body z y :=
          le_tsum
            (f := fun z => loopIterRPMF cond μ_body K x z * loopStepRPMF cond μ_body z y) y
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

/-- Combined active/exit state invariant for `while` loops on `RData r`. -/
def RLoopStateInv (cond : Cond r) (I Q : RData r → Prop) (x : RData r) : Prop :=
  (cond.Holds x.toData ∧ I x) ∨ (¬cond.Holds x.toData ∧ Q x)

theorem loopIterRPMF_support_inv {cond : Cond r} {I Q : RData r → Prop}
    {μ_body : RData r → PMF (RData r)}
    (hinv : ∀ x, I x → cond.Holds x.toData → ∀ y ∈ (μ_body x).support, RLoopStateInv cond I Q y)
    (K : ℕ) {x : RData r} (hx : RLoopStateInv cond I Q x) :
    ∀ y ∈ (loopIterRPMF cond μ_body K x).support, RLoopStateInv cond I Q y := by
  induction K generalizing x with
  | zero =>
    intro y hy
    rw [loopIterRPMF_zero, PMF.support_pure, Set.mem_singleton_iff] at hy
    rwa [hy]
  | succ K ih =>
    intro y hy
    rw [loopIterRPMF_succ, PMF.mem_support_bind_iff] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    rcases hx with ⟨hcx, hIx⟩ | ⟨hcx, hQx⟩
    · rw [loopStepRPMF_of_holds hcx] at hz
      exact ih (hinv x hIx hcx z hz) y hyz
    · rw [loopStepRPMF_of_not_holds hcx, PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ih (Or.inr ⟨hcx, hQx⟩) y hyz

private theorem pmf_rdata_compl_add (μ : PMF (RData r)) (cond : Cond r) :
    μ.toOuterMeasure {y : RData r | ¬cond.Holds y.toData} +
      μ.toOuterMeasure {y : RData r | cond.Holds y.toData} = 1 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
  convert μ.tsum_coe using 1
  congr 1; funext y; by_cases hc : cond.Holds y.toData <;> simp [hc]

theorem pmf_rdata_step_drift_bound (μ : PMF (RData r)) (cond : Cond r)
    {C p_exit : ℝ≥0∞} (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hp_exit : p_exit ≤ μ.toOuterMeasure {y : RData r | ¬cond.Holds y.toData}) :
    C + ∑' y, μ y * (if cond.Holds y.toData then C / p_exit else 0) ≤ C / p_exit := by
  set M := C / p_exit
  have hC : C = p_exit * M := by rw [mul_comm, ENNReal.div_mul_cancel hp_pos.ne' hp_top]
  have hact : (∑' y, μ y * (if cond.Holds y.toData then M else 0)) =
      μ.toOuterMeasure {y : RData r | cond.Holds y.toData} * M := by
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun y => by by_cases hc : cond.Holds y.toData <;> simp [hc]
  calc
    C + ∑' y, μ y * (if cond.Holds y.toData then M else 0)
      = p_exit * M + μ.toOuterMeasure {y : RData r | cond.Holds y.toData} * M := by rw [hC, hact]
    _ ≤ μ.toOuterMeasure {y : RData r | ¬cond.Holds y.toData} * M +
          μ.toOuterMeasure {y : RData r | cond.Holds y.toData} * M := by gcongr
    _ = (μ.toOuterMeasure {y : RData r | ¬cond.Holds y.toData} +
          μ.toOuterMeasure {y : RData r | cond.Holds y.toData}) * M := by rw [← add_mul]
    _ = M := by rw [pmf_rdata_compl_add, one_mul]

private noncomputable def loopActiveRSteps (cond : Cond r) (μ_body : RData r → PMF (RData r))
    (N : ℕ) (x : RData r) : ℝ≥0∞ :=
  ∑ K ∈ Finset.range N,
    (loopIterRPMF cond μ_body K x).toOuterMeasure {y : RData r | cond.Holds y.toData}

private theorem loopActiveRSteps_le {cond : Cond r} {I Q : RData r → Prop}
    {μ_body : RData r → PMF (RData r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x.toData → ∀ y ∈ (μ_body x).support, RLoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x.toData →
      p_exit ≤ (μ_body x).toOuterMeasure {y : RData r | ¬cond.Holds y.toData})
    (N : ℕ) {x : RData r} (hx : RLoopStateInv cond I Q x) :
    loopActiveRSteps cond μ_body N x ≤ if cond.Holds x.toData then 1 / p_exit else 0 := by
  induction N generalizing x with
  | zero => simp [loopActiveRSteps]
  | succ N ih =>
    rcases hx with ⟨hcx, hIx⟩ | ⟨hcx, _⟩
    · simp only [hcx, ↓reduceIte]
      have hrec : loopActiveRSteps cond μ_body (N + 1) x =
          1 + ∑' z, μ_body x z * loopActiveRSteps cond μ_body N z := by
        rw [loopActiveRSteps, Finset.sum_range_succ']
        have hzero : (loopIterRPMF cond μ_body 0 x).toOuterMeasure
            {y : RData r | cond.Holds y.toData} = 1 := by
          simp [PMF.toOuterMeasure_pure_apply, hcx]
        rw [hzero, add_comm]
        congr 1
        have hsucc : ∀ K : ℕ, (loopIterRPMF cond μ_body (K + 1) x).toOuterMeasure
            {y : RData r | cond.Holds y.toData} =
            ∑' z, μ_body x z *
              (loopIterRPMF cond μ_body K z).toOuterMeasure
                {y : RData r | cond.Holds y.toData} := fun K => by
          rw [loopIterRPMF_succ, loopStepRPMF_of_holds hcx, PMF.toOuterMeasure_bind_apply]
        simp only [hsucc]
        rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
        simp only [loopActiveRSteps, Finset.mul_sum]
      rw [hrec]
      refine (add_le_add le_rfl (tsum_le_tsum fun z => ?_)).trans
        (pmf_rdata_step_drift_bound (μ_body x) cond hp_pos hp_top (hp_exit x hIx hcx))
      by_cases hz : z ∈ (μ_body x).support
      · exact mul_le_mul_right (ih (hinv x hIx hcx z hz)) _
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hz, zero_mul, zero_mul]
    · simp only [hcx, ↓reduceIte, nonpos_iff_eq_zero, loopActiveRSteps]
      refine Finset.sum_eq_zero fun K _ => ?_
      rw [loopIterRPMF_of_not_holds hcx, PMF.toOuterMeasure_pure_apply]
      simp [hcx]

theorem hasSum_loopExitRDensity {cond : Cond r} {I Q : RData r → Prop}
    {μ_body : RData r → PMF (RData r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x.toData → ∀ y ∈ (μ_body x).support, RLoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x.toData →
      p_exit ≤ (μ_body x).toOuterMeasure {y : RData r | ¬cond.Holds y.toData})
    {x : RData r} (hx : RLoopStateInv cond I Q x) :
    HasSum (fun y => ⨆ K : ℕ,
      Set.indicator {z : RData r | ¬cond.Holds z.toData} (loopIterRPMF cond μ_body K x) y) 1 := by
  rw [CompleteLattice.summable.hasSum_iff,
    ENNReal.tsum_iSup_of_monotone (loopIterRPMF_indicator_mono cond μ_body x)]
  simp_rw [← PMF.toOuterMeasure_apply]
  set b := ⨆ K : ℕ,
    (loopIterRPMF cond μ_body K x).toOuterMeasure {z : RData r | ¬cond.Holds z.toData}
  have hb_le : b ≤ 1 := iSup_le fun K => Cslib.Probability.PMF.toOuterMeasure_le_one _ _
  have hsub_zero : 1 - b = 0 := by
    by_contra hne
    have hN_bound : ∀ N : ℕ, (N : ℝ≥0∞) * (1 - b) ≤ 1 / p_exit := fun N => by
      have hterm : ∀ K : ℕ, 1 - b ≤
          (loopIterRPMF cond μ_body K x).toOuterMeasure
            {z : RData r | cond.Holds z.toData} := fun K => by
        refine tsub_le_iff_left.mpr ?_
        rw [← pmf_rdata_compl_add (loopIterRPMF cond μ_body K x) cond]
        exact add_le_add (le_iSup
          (fun J => (loopIterRPMF cond μ_body J x).toOuterMeasure
            {z : RData r | ¬cond.Holds z.toData}) K) le_rfl
      calc
        (N : ℝ≥0∞) * (1 - b) = ∑ _K ∈ Finset.range N, (1 - b) := by simp
        _ ≤ ∑ K ∈ Finset.range N,
              (loopIterRPMF cond μ_body K x).toOuterMeasure
                {z : RData r | cond.Holds z.toData} := Finset.sum_le_sum fun K _ => hterm K
        _ ≤ if cond.Holds x.toData then 1 / p_exit else 0 :=
            loopActiveRSteps_le hp_pos hp_top hinv hp_exit N hx
        _ ≤ 1 / p_exit := by split_ifs <;> simp
    have htop : (⊤ : ℝ≥0∞) ≤ 1 / p_exit := by
      rw [← ENNReal.top_mul hne, ← ENNReal.iSup_natCast, ENNReal.iSup_mul]
      exact iSup_le hN_bound
    exact ENNReal.div_ne_top ENNReal.one_ne_top hp_pos.ne' (top_le_iff.mp htop)
  exact le_antisymm hb_le (tsub_eq_zero_iff_le.mp hsub_zero)

/-- Limiting exit distribution of `RCode.loop cond body` from `x` under `μ_body`. -/
noncomputable def loopExitRPMF (cond : Cond r) (μ_body : RData r → PMF (RData r)) (x : RData r) :
    PMF (RData r) :=
  open Classical in
  if h : HasSum (fun y => ⨆ K : ℕ,
      Set.indicator {z : RData r | ¬cond.Holds z.toData} (loopIterRPMF cond μ_body K x) y) 1 then
    ⟨_, h⟩
  else PMF.pure x

theorem loopExitRPMF_apply_of_hasSum {cond : Cond r} {μ_body : RData r → PMF (RData r)}
    {x : RData r}
    (h : HasSum (fun y => ⨆ K : ℕ,
      Set.indicator {z : RData r | ¬cond.Holds z.toData} (loopIterRPMF cond μ_body K x) y) 1)
    (y : RData r) :
    loopExitRPMF cond μ_body x y =
      ⨆ K : ℕ, Set.indicator {z : RData r | ¬cond.Holds z.toData}
        (loopIterRPMF cond μ_body K x) y := by
  classical simp only [loopExitRPMF, h, ↓reduceDIte]; rfl

theorem loopExitRPMF_of_not_holds {cond : Cond r} {μ_body : RData r → PMF (RData r)} {x : RData r}
    (hc : ¬cond.Holds x.toData) : loopExitRPMF cond μ_body x = PMF.pure x := by
  have hfun : (fun y => ⨆ K : ℕ, Set.indicator {z : RData r | ¬cond.Holds z.toData}
      (loopIterRPMF cond μ_body K x) y) = PMF.pure x := by
    funext y
    have hK : ∀ K : ℕ, Set.indicator {z : RData r | ¬cond.Holds z.toData}
        (loopIterRPMF cond μ_body K x) y = PMF.pure x y := fun K => by
      rw [loopIterRPMF_of_not_holds hc]
      by_cases hyx : y = x
      · subst hyx; simp [hc]
      · simp [PMF.pure_apply, hyx]
    simp [hK]
  ext y
  rw [loopExitRPMF_apply_of_hasSum (hfun ▸ (PMF.pure x).2), congrFun hfun y]

theorem loopExitRPMF_of_holds {cond : Cond r} {I Q : RData r → Prop}
    {μ_body : RData r → PMF (RData r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x.toData → ∀ y ∈ (μ_body x).support, RLoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x.toData →
      p_exit ≤ (μ_body x).toOuterMeasure {y : RData r | ¬cond.Holds y.toData})
    {x : RData r} (hIx : I x) (hcx : cond.Holds x.toData) :
    loopExitRPMF cond μ_body x = (μ_body x).bind (loopExitRPMF cond μ_body) := by
  ext y
  have hx : RLoopStateInv cond I Q x := Or.inl ⟨hcx, hIx⟩
  rw [loopExitRPMF_apply_of_hasSum (hasSum_loopExitRDensity hp_pos hp_top hinv hp_exit hx),
    PMF.bind_apply]
  have hzero : Set.indicator {z : RData r | ¬cond.Holds z.toData} (PMF.pure x) y = 0 := by
    by_cases hy : ¬cond.Holds y.toData
    · have hyx : y ≠ x := fun h => hy (h ▸ hcx)
      simp [hy, PMF.pure_apply, hyx]
    · simp [Set.indicator_of_notMem, hy]
  have hiSup_shift :
      (⨆ K : ℕ, Set.indicator {z : RData r | ¬cond.Holds z.toData}
        (loopIterRPMF cond μ_body K x) y) =
        ⨆ K : ℕ, Set.indicator {z : RData r | ¬cond.Holds z.toData}
          (loopIterRPMF cond μ_body (K + 1) x) y := by
    refine le_antisymm (iSup_le fun K => ?_) (iSup_le fun K =>
      le_iSup (fun J => Set.indicator {z : RData r | ¬cond.Holds z.toData}
        (loopIterRPMF cond μ_body J x) y) (K + 1))
    cases K with
    | zero => rw [loopIterRPMF_zero, hzero]; exact zero_le
    | succ K =>
      exact le_iSup (fun J => Set.indicator {z : RData r | ¬cond.Holds z.toData}
        (loopIterRPMF cond μ_body (J + 1) x) y) K
  rw [hiSup_shift]
  have hstep : ∀ K : ℕ,
      Set.indicator {z : RData r | ¬cond.Holds z.toData}
        (loopIterRPMF cond μ_body (K + 1) x) y =
        ∑' z, μ_body x z * Set.indicator {w' : RData r | ¬cond.Holds w'.toData}
          (loopIterRPMF cond μ_body K z) y := fun K => by
    rw [loopIterRPMF_succ, loopStepRPMF_of_holds hcx]
    by_cases hy : ¬cond.Holds y.toData
    · simp [Set.indicator_of_mem, hy, PMF.bind_apply]
    · simp [Set.indicator_of_notMem, hy]
  simp_rw [hstep]
  rw [← ENNReal.tsum_iSup_of_monotone
    (f := fun K z => μ_body x z * Set.indicator {w' : RData r | ¬cond.Holds w'.toData}
      (loopIterRPMF cond μ_body K z) y)
    (fun z _ _ hK =>
      mul_le_mul_right (loopIterRPMF_indicator_mono cond μ_body z y hK) (μ_body x z))]
  refine tsum_congr fun z => ?_
  by_cases hz : z ∈ (μ_body x).support
  · rw [← ENNReal.mul_iSup,
      loopExitRPMF_apply_of_hasSum
        (hasSum_loopExitRDensity hp_pos hp_top hinv hp_exit (hinv x hIx hcx z hz))]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr hz, zero_mul]; simp

theorem mem_support_loopExitRPMF {cond : Cond r} {I Q : RData r → Prop}
    {μ_body : RData r → PMF (RData r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x.toData → ∀ y ∈ (μ_body x).support, RLoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x.toData →
      p_exit ≤ (μ_body x).toOuterMeasure {y : RData r | ¬cond.Holds y.toData})
    {x : RData r} (hx : RLoopStateInv cond I Q x)
    {y : RData r} (hy : y ∈ (loopExitRPMF cond μ_body x).support) :
    (¬cond.Holds y.toData ∧ Q y) ∧ ∃ K, y ∈ (loopIterRPMF cond μ_body K x).support := by
  rw [PMF.mem_support_iff,
    loopExitRPMF_apply_of_hasSum (hasSum_loopExitRDensity hp_pos hp_top hinv hp_exit hx)] at hy
  have ⟨K, hK⟩ : ∃ K : ℕ, Set.indicator {z : RData r | ¬cond.Holds z.toData}
      (loopIterRPMF cond μ_body K x) y ≠ 0 := by
    by_contra! h; exact hy (by simp [h])
  have hnc : ¬cond.Holds y.toData := by
    by_contra hc; exact hK (by simp [Set.indicator_of_notMem, hc])
  rw [Set.indicator_of_mem hnc, ← PMF.mem_support_iff] at hK
  rcases loopIterRPMF_support_inv hinv K hx y hK with ⟨hcy, _⟩ | ⟨_, hQy⟩
  · exact absurd hcy hnc
  · exact ⟨⟨hnc, hQy⟩, K, hK⟩


end Cslib.WordRAM.Resizable
