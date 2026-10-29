/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.Randomized.Structured
public import Complexity.Languages.Probabilistic.Expect
public import Complexity.Probability.PMF.Bind
public import Complexity.Probability.PMF.Event

/-!
# Expected running time for randomized word RAMs

Expected instruction counts for flat (`Program`) and structured (`Code`) randomized word RAM
programs, valued in the extended nonnegative reals `ℝ≥0∞` so expectations are total without
summability side conditions; nonsummable running-probability tails have value `⊤`.

For a flat program `p` starting at state `s`, the expected running time is defined via the
discrete tail-sum formula over clocked horizons:
`expectedTime w p s = ∑' t : ℕ, (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u}`.
Because `.halted` and `.faulted` are absorbing, each horizon `t` contributes the probability that
execution is still running before either halt or fault after `t` steps. Summing over `t : ℕ` yields
the exact 1-step Bellman equation `expectedStepsFrom_running`, connects directly to structured
`ExecRand` trees via
`ExecRand.expectedTime_program`, reduces to a finite sum under `RandHaltsWithin`
(`RandHaltsWithin.expectedTime_eq_sum`, `expectedTime_le_of_randHaltsWithin`), and recovers exact
deterministic step counts (`Executes.expectedTime_eq`).

For structured `Code B r` programs, `expectedCodeTime` measures the expected instruction count of
`codeComp w c x` when a finite, fault-free `ExecRand` tree exists, and is `⊤` otherwise. Thus
unbounded almost-surely terminating loops can receive a conservative infinite structured cost.
It satisfies exact sequential
additivity (`expectedCodeTime_seq`), branch laws (`expectedCodeTime_branch_pos`,
`expectedCodeTime_branch_neg`, `expectedCodeTime_branch_le`), and a potential/drift bound for
`while` loops (`expectedCodeTime_loop_le_of_drift`).

## Main definitions

* `Cslib.WordRAM.AlmostSurelyHalts`: zero faults at all horizons and supremum halting probability
  equal to `1`.
* `Cslib.WordRAM.expectedStepsFrom`, `Cslib.WordRAM.expectedTime`: `ℝ≥0∞`-valued expected
  remaining instructions from a `RandCfg r` or initial `State r`.
* `Cslib.WordRAM.expectedCodeTime`: `ℝ≥0∞`-valued expected instruction count of a structured
  `Code B r`.

## Main results

* `Cslib.WordRAM.expectedStepsFrom_running`: 1-step Bellman equation for `expectedStepsFrom`.
* `Cslib.WordRAM.RandHaltsWithin.almostSurelyHalts`,
  `Cslib.WordRAM.AlmostSurelyHalts.of_expectedTime_ne_top`: sufficient conditions for almost-sure
  halting.
* `Cslib.WordRAM.RandHaltsWithin.expectedTime_eq_sum`,
  `Cslib.WordRAM.expectedTime_le_of_randHaltsWithin`: finite-horizon reduction under
  `RandHaltsWithin`.
* `Cslib.WordRAM.Executes.expectedTime_eq`: deterministic halting runs have `expectedTime = n`.
* `Cslib.WordRAM.ExecRand.expectedTime_program`: exact bridge between compiled `c.program out` and
  `expectedCodeTime`.
* `Cslib.WordRAM.expectedCodeTime_seq`, `Cslib.WordRAM.expectedCodeTime_branch_le`,
  `Cslib.WordRAM.expectedCodeTime_loop_le_of_drift`: compositional expected-time rules for
  structured `Code`.

Discrete and conditional expectation principles are classical background; see
[MitzenmacherUpfal2017], Sections 2.1 and 2.3. The particular native tail-sum/Bellman definitions,
finite structured-execution-tree bridge and ranked-loop expected-cost formalization are original
library constructions in this module.

## References

* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017],
  Sections 2.1 and 2.3.
-/

@[expose] public section

open scoped ENNReal

namespace Cslib

/-! ## Almost-sure halting and `ℝ≥0∞`-valued expected running time -/

namespace WordRAM

variable {B : Basis} {r : ℕ}

/-- Set of active (`.running`) configurations. -/
def RandCfg.runningSet (r : ℕ) : Set (RandCfg r) := {cfg | ∃ u, cfg = .running u}

/-- Set of cleanly halted (`.halted`) configurations. -/
def RandCfg.haltedSet (r : ℕ) : Set (RandCfg r) := {cfg | ∃ v d, cfg = .halted v d}

@[simp]
theorem RandCfg.mem_runningSet_iff {cfg : RandCfg r} :
    cfg ∈ RandCfg.runningSet r ↔ ∃ u, cfg = .running u :=
  Iff.rfl

@[simp]
theorem RandCfg.mem_haltedSet_iff {cfg : RandCfg r} :
    cfg ∈ RandCfg.haltedSet r ↔ ∃ v d, cfg = .halted v d :=
  Iff.rfl

/-- Starting from `s`, `p` never faults and halts with probability tending to `1`. -/
def AlmostSurelyHalts (w : ℕ) (p : Program B r) (s : State r) : Prop :=
  RandFaultFree w p s ∧
    (⨆ T : ℕ, (evalRand w p T s).toOuterMeasure (RandCfg.haltedSet r)) = 1

/-- Halting probability is monotone in the horizon `T` because `.halted` is absorbing. -/
theorem evalRand_haltedSet_mono (w : ℕ) (p : Program B r) (s : State r) :
    Monotone fun T => (evalRand w p T s).toOuterMeasure (RandCfg.haltedSet r) := by
  refine monotone_nat_of_le_succ fun T => ?_
  have hstep : evalRand w p (T + 1) s =
      (evalRand w p T s).bind (fun cfg => (stepRand w p cfg).eval) := by
    rw [evalRand, runRand_add w p T 1, ProbComp.eval_bind]
    simp only [evalRand, runRand_succ, runRand_zero, bind_pure]
  rw [hstep, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine tsum_le_tsum fun cfg => ?_
  by_cases hcfg : cfg ∈ RandCfg.haltedSet r
  · have hmem := hcfg
    obtain ⟨v, d, rfl⟩ := hcfg
    have h1 : (stepRand w p (.halted v d)).eval.toOuterMeasure (RandCfg.haltedSet r) = 1 := by
      simp [stepRand_halted, PMF.toOuterMeasure_pure_apply, hmem]
    rw [Set.indicator_of_mem hmem, h1, mul_one]
  · simp [Set.indicator_of_notMem hcfg]

/-- Any worst-case bounded execution halts almost surely. -/
theorem RandHaltsWithin.almostSurelyHalts {w T : ℕ} {p : Program B r} {s : State r}
    (h : RandHaltsWithin w p s T) : AlmostSurelyHalts w p s := by
  refine ⟨h.randFaultFree,
    le_antisymm (iSup_le fun _ => Cslib.Probability.PMF.toOuterMeasure_le_one _ _)
      (le_iSup_of_le T ?_)⟩
  have hcompl : (evalRand w p T s).toOuterMeasure (RandCfg.haltedSet r)ᶜ = 0 := by
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    intro cfg hmem hnot
    rw [support_evalRand] at hmem
    exact hnot (h cfg hmem)
  have hsum : (evalRand w p T s).toOuterMeasure (RandCfg.haltedSet r) +
      (evalRand w p T s).toOuterMeasure (RandCfg.haltedSet r)ᶜ = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
    convert (evalRand w p T s).tsum_coe using 1
    congr 1
    funext cfg
    by_cases hc : cfg ∈ RandCfg.haltedSet r <;> simp [hc]
  rw [hcompl, add_zero] at hsum
  exact hsum.ge

/-- Expected number of remaining instructions starting from configuration `cfg`, defined via the
tail sum of active-configuration probabilities. -/
noncomputable def expectedStepsFrom (w : ℕ) (p : Program B r) (cfg : RandCfg r) : ℝ≥0∞ :=
  ∑' t : ℕ, (runRand w p t cfg).eval.toOuterMeasure {cfg' | ∃ u, cfg' = .running u}

/-- Expected running time of `p` at word size `w` from initial state `s`, valued in `ℝ≥0∞`. -/
noncomputable def expectedTime (w : ℕ) (p : Program B r) (s : State r) : ℝ≥0∞ :=
  ∑' t : ℕ, (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u}

theorem expectedTime_eq_expectedStepsFrom (w : ℕ) (p : Program B r) (s : State r) :
    expectedTime w p s = expectedStepsFrom w p (.running s) :=
  rfl

@[simp]
theorem expectedStepsFrom_halted (w : ℕ) (p : Program B r) (v : ℕ) (d : Data r) :
    expectedStepsFrom w p (.halted v d) = 0 := by
  simp [expectedStepsFrom, PMF.toOuterMeasure_pure_apply]

@[simp]
theorem expectedStepsFrom_faulted (w : ℕ) (p : Program B r) :
    expectedStepsFrom w p .faulted = 0 := by
  simp [expectedStepsFrom, PMF.toOuterMeasure_pure_apply]

private theorem tsum_nat_eq_zero_add (g : ℕ → ℝ≥0∞) :
    ∑' t : ℕ, g t = g 0 + ∑' t : ℕ, g (t + 1) := by
  rw [tsum_eq_add_tsum_ite (f := g) 0]
  congr 1
  have hsh := Function.Injective.tsum_eq Nat.succ_injective
    (f := fun t => if t = 0 then 0 else g t) fun t ht => by
      cases t with
      | zero => simp at ht
      | succ k => exact ⟨k, rfl⟩
  exact (tsum_congr fun x => by split_ifs <;> rfl).trans hsh.symm

/-- 1-step Bellman equation: an active state `s` incurs `1` immediate step plus the expected
remaining steps from `stepRand w p (.running s)`. -/
theorem expectedStepsFrom_running (w : ℕ) (p : Program B r) (s : State r) :
    expectedStepsFrom w p (.running s) =
      1 + ProbComp.expect (stepRand w p (.running s)) (expectedStepsFrom w p) := by
  rw [expectedStepsFrom, tsum_nat_eq_zero_add]
  have hzero : (runRand w p 0 (.running s)).eval.toOuterMeasure
      {cfg' | ∃ u, cfg' = .running u} = 1 := by
    simp [PMF.toOuterMeasure_pure_apply]
  rw [hzero]
  congr 1
  have hsucc : ∀ t : ℕ, (runRand w p (t + 1) (.running s)).eval.toOuterMeasure
      {cfg' | ∃ u, cfg' = .running u} =
      ∑' cfg, (stepRand w p (.running s)).eval cfg *
        (runRand w p t cfg).eval.toOuterMeasure {cfg' | ∃ u, cfg' = .running u} := by
    intro t
    rw [runRand_succ, ProbComp.eval_bind, PMF.toOuterMeasure_bind_apply]
  simp only [hsucc]
  rw [tsum_comm]
  simp only [ProbComp.expect, expectedStepsFrom, ENNReal.tsum_mul_left]

/-- Under `RandFaultFree`, every horizon partitions probability `1` between `.running` and
`.halted`. -/
theorem RandFaultFree.running_add_halted_eq_one {w : ℕ} {p : Program B r} {s : State r}
    (hf : RandFaultFree w p s) (t : ℕ) :
    (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u} +
      (evalRand w p t s).toOuterMeasure (RandCfg.haltedSet r) = 1 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
  convert (evalRand w p t s).tsum_coe using 1
  congr 1
  funext cfg
  cases cfg with
  | running u => simp [RandCfg.haltedSet]
  | halted v d => simp [RandCfg.haltedSet]
  | faulted =>
    simp [RandCfg.haltedSet, hf.evalRand_faulted_eq_zero t]

/-- A fault-free execution with finite expected running time halts almost surely. -/
theorem AlmostSurelyHalts.of_expectedTime_ne_top {w : ℕ} {p : Program B r} {s : State r}
    (hf : RandFaultFree w p s) (htop : expectedTime w p s ≠ ⊤) :
    AlmostSurelyHalts w p s := by
  refine ⟨hf, le_antisymm (iSup_le fun _ => Cslib.Probability.PMF.toOuterMeasure_le_one _ _) ?_⟩
  by_contra hlt
  have hlt1 : (⨆ t : ℕ, (evalRand w p t s).toOuterMeasure (RandCfg.haltedSet r)) < 1 :=
    lt_of_not_ge hlt
  set supH := ⨆ t : ℕ, (evalRand w p t s).toOuterMeasure (RandCfg.haltedSet r)
  have hpos : 0 < 1 - supH := tsub_pos_of_lt hlt1
  have hle_run : ∀ t : ℕ,
      1 - supH ≤ (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u} := by
    intro t
    have hpart := hf.running_add_halted_eq_one t
    have hle_sup : (evalRand w p t s).toOuterMeasure (RandCfg.haltedSet r) ≤ supH :=
      le_iSup (fun k => (evalRand w p k s).toOuterMeasure (RandCfg.haltedSet r)) t
    refine tsub_le_iff_right.mpr ?_
    calc
      1 = (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u} +
            (evalRand w p t s).toOuterMeasure (RandCfg.haltedSet r) := hpart.symm
      _ ≤ (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u} + supH := by gcongr
  have hinf : (⊤ : ℝ≥0∞) ≤ expectedTime w p s := by
    calc
      (⊤ : ℝ≥0∞) = ∑' _ : ℕ, (1 - supH) := (ENNReal.tsum_const_eq_top_of_ne_zero hpos.ne').symm
      _ ≤ expectedTime w p s := tsum_le_tsum hle_run
  exact htop (top_unique hinf)

/-- Under `RandHaltsWithin w p s T`, the active-configuration tail sum vanishes from `T` onward and
reduces to a finite sum over `Finset.range T`. -/
theorem RandHaltsWithin.expectedTime_eq_sum {w T : ℕ} {p : Program B r} {s : State r}
    (h : RandHaltsWithin w p s T) :
    expectedTime w p s =
      ∑ t ∈ Finset.range T,
        (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u} := by
  rw [expectedTime, tsum_eq_sum (s := Finset.range T)]
  intro t ht
  have hT : T ≤ t := Nat.le_of_not_lt (Finset.mem_range.not.mp ht)
  rw [evalRand_eq_of_randHaltsWithin h hT, PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro cfg hmem hrun
  obtain ⟨u, rfl⟩ := hrun
  rw [support_evalRand] at hmem
  obtain ⟨v, d, hvd⟩ := h _ hmem
  cases hvd

/-- A worst-case step bound `RandHaltsWithin w p s T` immediately bounds `expectedTime` by `T`. -/
theorem expectedTime_le_of_randHaltsWithin {w T : ℕ} {p : Program B r} {s : State r}
    (h : RandHaltsWithin w p s T) :
    expectedTime w p s ≤ T := by
  rw [h.expectedTime_eq_sum]
  calc
    ∑ t ∈ Finset.range T, (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u}
      ≤ ∑ _t ∈ Finset.range T, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun _ _ => Cslib.Probability.PMF.toOuterMeasure_le_one _ _
    _ = T := by simp

/-- Along any deterministic `Runs` of length `m`, `expectedStepsFrom` adds `m` to the expected
remaining steps at the destination state. -/
theorem Runs.expectedStepsFrom_eq {w m : ℕ} {p : Program B r} {s t : State r}
    (hrun : Runs w p s t m) :
    expectedStepsFrom w p (.running s) = m + expectedStepsFrom w p (.running t) := by
  induction hrun using Relation.RelatesInSteps.head_induction_on with
  | hrefl => simp
  | @hhead s u m' hsc _ ih =>
    rw [expectedStepsFrom_running, stepRand_of_step_eq_next hsc, ProbComp.expect_pure, ih,
      Nat.cast_add, Nat.cast_one, add_comm (m' : ℝ≥0∞) 1, add_assoc]

/-- Any deterministic halting execution `Executes w p s v n` has exact expected running time `n`. -/
theorem Executes.expectedTime_eq {w n : ℕ} {p : Program B r} {s : State r} {v : ℕ}
    (h : Executes w p s v n) :
    expectedTime w p s = n := by
  obtain ⟨t, m, hrun, hhalt, rfl⟩ := h
  rw [expectedTime_eq_expectedStepsFrom, hrun.expectedStepsFrom_eq, expectedStepsFrom_running,
    stepRand_of_step_eq_halt hhalt, ProbComp.expect_pure, expectedStepsFrom_halted, add_zero,
    Nat.cast_add, Nat.cast_one]

/-! ## Structured `expectedCodeTime` and compilation bridge -/

/-- Along an assembled structured execution `ExecRand w c x m` inside `p`, the expected remaining
steps from `⟨pc, x⟩` equal the expected step count of `m` plus the expected continuation steps from
`⟨pc + c.size, y⟩`. -/
theorem ExecRand.expectedStepsFrom_assemble {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) :
    expectedStepsFrom w p (.running ⟨pc, x⟩) =
      ProbComp.expect m (fun z =>
        (z.2 : ℝ≥0∞) + expectedStepsFrom w p (.running ⟨pc + c.size, z.1⟩)) := by
  induction h generalizing pc with
  | op ho =>
    rw [expectedStepsFrom_running, stepRand_op hp.head ho, ProbComp.expect_pure,
      ProbComp.expect_pure]
    simp [Code.size]
  | @rand dst src x hfit =>
    rw [expectedStepsFrom_running, stepRand_rand_of_fits hp.head hfit, ProbComp.expect_bind,
      ProbComp.expect_bind]
    simp only [ProbComp.expect_pure, Code.size, Nat.cast_one]
    rw [ProbComp.expect_add, ProbComp.expect_const]
  | @seq c₁ c₂ x m₁ m₂ _ _ ih₁ ih₂ =>
    have hc₂ : p.Contains (pc + c₁.size) (c₂.assemble (pc + c₁.size)) := by
      simpa [Code.length_assemble] using hp.append_right
    rw [ih₁ hp.append_left, ProbComp.expect_bind]
    refine ProbComp.expect_congr_on_support fun z₁ hz₁ => ?_
    rw [ih₂ z₁ hz₁ hc₂, ProbComp.expect_bind,
      ← ProbComp.expect_const (m₂ z₁.1) (z₁.2 : ℝ≥0∞), ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z₂ _ => ?_
    simp only [ProbComp.expect_pure, Code.size, Nat.cast_add, add_assoc]
  | @branch_pos cond pos neg x m hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    rw [expectedStepsFrom_running, stepRand_branch hbr]
    simp only [hc, ↓reduceIte, ProbComp.expect_pure]
    have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
    rw [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'
    rw [ih hc', ProbComp.expect_map, ← ProbComp.expect_const m 1, ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z _ => ?_
    simp only [Code.size, Nat.cast_add, Nat.cast_one]
    rw [show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
    ac_rfl
  | @branch_neg cond pos neg x m hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    rw [expectedStepsFrom_running, stepRand_branch hbr]
    simp only [hc, ↓reduceIte, ProbComp.expect_pure]
    rw [ih hp.cons_tail.append_left, ProbComp.expect_map,
      ← ProbComp.expect_const m 1, ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z _ => ?_
    have hj : p[pc + 1 + neg.size]? = some (.jump (pc + neg.size + pos.size + 2)) := by
      simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head
    rw [expectedStepsFrom_running, stepRand_jump hj, ProbComp.expect_pure]
    simp only [Code.size, Nat.cast_add, Nat.cast_ofNat]
    rw [show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
    set E := expectedStepsFrom w p (.running ⟨pc + (neg.size + pos.size + 2), z.1⟩)
    calc
      1 + ((z.2 : ℝ≥0∞) + (1 + E)) = (z.2 : ℝ≥0∞) + (1 + 1) + E := by ac_rfl
      _ = (z.2 : ℝ≥0∞) + 2 + E := by rw [one_add_one_eq_two]
  | @loop_exit cond body x hc =>
    have hbr : p[pc]? = some (.branch cond (pc + 2)) := hp.head
    have hj : p[pc + 1]? = some (.jump (pc + body.size + 3)) := hp.cons_tail.head
    rw [expectedStepsFrom_running, stepRand_branch hbr]
    simp only [hc, ↓reduceIte, ProbComp.expect_pure]
    rw [expectedStepsFrom_running, stepRand_jump hj, ProbComp.expect_pure]
    simp only [Code.size, Nat.cast_ofNat]
    rw [← add_assoc, one_add_one_eq_two, show pc + body.size + 3 = pc + (body.size + 3) by omega]
  | @loop_iter cond body x mb ml hc _ _ ihb ihl =>
    have hbr : p[pc]? = some (.branch cond (pc + 2)) := hp.head
    have hbody_contains : p.Contains (pc + 2) (body.assemble (pc + 2)) := by
      simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left
    have hj : p[pc + 2 + body.size]? = some (.jump pc) := by
      simpa using hp.cons_tail.cons_tail.append_right.head
    rw [expectedStepsFrom_running, stepRand_branch hbr]
    simp only [hc, ↓reduceIte, ProbComp.expect_pure]
    rw [ihb hbody_contains, ProbComp.expect_bind, ← ProbComp.expect_const mb 1,
      ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z₁ hz₁ => ?_
    rw [expectedStepsFrom_running, stepRand_jump hj, ProbComp.expect_pure, ihl z₁ hz₁ hp,
      ProbComp.expect_bind]
    have hconst : (1 : ℝ≥0∞) + ((z₁.2 : ℝ≥0∞) +
        (1 + ProbComp.expect (ml z₁.1) fun z =>
          (z.2 : ℝ≥0∞) + expectedStepsFrom w p (.running ⟨pc + (Code.loop cond body).size, z.1⟩))) =
        ProbComp.expect (ml z₁.1) (fun _ => (z₁.2 : ℝ≥0∞) + 2) +
          ProbComp.expect (ml z₁.1) (fun z =>
            (z.2 : ℝ≥0∞) +
              expectedStepsFrom w p (.running ⟨pc + (Code.loop cond body).size, z.1⟩)) := by
      rw [ProbComp.expect_const, ← one_add_one_eq_two]
      ac_rfl
    rw [hconst, ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z₂ _ => ?_
    simp only [ProbComp.expect_pure, Nat.cast_add, Nat.cast_ofNat]
    rw [← add_assoc ((z₁.2 : ℝ≥0∞) + 2) (z₂.2 : ℝ≥0∞), add_right_comm (z₁.2 : ℝ≥0∞) 2]

/-- Exact bridge: compiling `c` with `c.program out` adds `1` (for the final `halt out`
instruction) to the expected step count of `ExecRand w c x m`. -/
theorem ExecRand.expectedTime_program {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) (out : Fin r) :
    expectedTime w (c.program out) ⟨0, x⟩ =
      ProbComp.expect m (fun z => (z.2 : ℝ≥0∞)) + 1 := by
  rw [expectedTime_eq_expectedStepsFrom,
    h.expectedStepsFrom_assemble (Program.Contains.self (c.program out)).append_left,
    ← ProbComp.expect_const m 1, ← ProbComp.expect_add]
  refine ProbComp.expect_congr_on_support fun z _ => ?_
  have hhalt : (c.program out)[0 + c.size]? = some (.halt out) := by
    simp [Code.program]
  rw [expectedStepsFrom_running, stepRand_halt (s := ⟨0 + c.size, z.1⟩) hhalt,
    ProbComp.expect_pure, expectedStepsFrom_halted, add_zero]

/-- When some `ExecRand w c x m` exists, `codeComp w c x` satisfies `ExecRand`. -/
theorem codeComp_execRand {w : ℕ} {c : Code B r} {x : Data r}
    (hex : ∃ m, ExecRand w c x m) : ExecRand w c x (codeComp w c x) := by
  obtain ⟨m, hm⟩ := hex
  rwa [hm.codeComp_eq]

/-- Expected instruction count of a structured program `c` from data `x` at word size `w`, or `⊤`
if `c` can fault or diverge on some path from `x`. -/
noncomputable def expectedCodeTime (w : ℕ) (c : Code B r) (x : Data r) : ℝ≥0∞ :=
  open Classical in
  if ∃ m, ExecRand w c x m then
    ProbComp.expect (codeComp w c x) (fun z => (z.2 : ℝ≥0∞))
  else ⊤

theorem ExecRand.expectedCodeTime_eq {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) :
    expectedCodeTime w c x = ProbComp.expect m (fun z => (z.2 : ℝ≥0∞)) := by
  classical
  have hex : ∃ m', ExecRand w c x m' := ⟨m, h⟩
  simp only [expectedCodeTime, hex, ↓reduceIte, h.codeComp_eq]

theorem expectedCodeTime_eq_top {w : ℕ} {c : Code B r} {x : Data r}
    (h : ¬∃ m, ExecRand w c x m) : expectedCodeTime w c x = ⊤ := by
  classical
  simp only [expectedCodeTime, h, ↓reduceIte]

theorem Exec.expectedCodeTime_eq {w n : ℕ} {c : Code B r} {x y : Data r}
    (h : Exec w c x y n) :
    expectedCodeTime w c x = n := by
  rw [h.execRand.expectedCodeTime_eq, ProbComp.expect_pure]

theorem expectedCodeTime_program {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) (out : Fin r) :
    expectedTime w (c.program out) ⟨0, x⟩ = expectedCodeTime w c x + 1 := by
  rw [h.expectedTime_program, h.expectedCodeTime_eq]

@[simp]
theorem expectedCodeTime_op {w : ℕ} {o : Op B r} {x y : Data r} (ho : o.eval w x = some y) :
    expectedCodeTime w (.op o) x = 1 := by
  simpa only [Nat.cast_one] using (Exec.op ho).expectedCodeTime_eq

@[simp]
theorem expectedCodeTime_rand {w : ℕ} {dst src : Fin r} {x : Data r} (h : Fits w (x.regs src)) :
    expectedCodeTime (B := B) w (.rand dst src) x = 1 := by
  rw [(ExecRand.rand (B := B) (dst := dst) h).expectedCodeTime_eq, ProbComp.expect_bind]
  simp only [ProbComp.expect_pure, Nat.cast_one, ProbComp.expect_const]

/-- Sequential additivity of `expectedCodeTime`: when `c₁` executes via `m₁`, the expected time of
`Code.seq c₁ c₂` equals the expected time of `c₁` plus the `m₁`-expected time of `c₂`. -/
theorem expectedCodeTime_seq {w : ℕ} {c₁ c₂ : Code B r} {x : Data r}
    {m₁ : ProbComp (Data r × ℕ)} (h₁ : ExecRand w c₁ x m₁) :
    expectedCodeTime w (.seq c₁ c₂) x =
      expectedCodeTime w c₁ x + ProbComp.expect m₁ (fun z => expectedCodeTime w c₂ z.1) := by
  classical
  by_cases h₂ : ∀ z ∈ m₁.support, ∃ m₂, ExecRand w c₂ z.1 m₂
  · have h₂_comp : ∀ z ∈ m₁.support, ExecRand w c₂ z.1 (codeComp w c₂ z.1) :=
      fun z hz => codeComp_execRand (h₂ z hz)
    rw [(h₁.seq h₂_comp).expectedCodeTime_eq, h₁.expectedCodeTime_eq, ProbComp.expect_bind,
      ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z hz => ?_
    rw [ProbComp.expect_bind, (h₂_comp z hz).expectedCodeTime_eq,
      ← ProbComp.expect_const (codeComp w c₂ z.1) (z.2 : ℝ≥0∞), ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z₂ _ => ?_
    simp only [ProbComp.expect_pure, Nat.cast_add]
  · simp only [not_forall] at h₂
    obtain ⟨z₀, hz₀, hnot₂⟩ := h₂
    have hnot_seq : ¬∃ m, ExecRand w (.seq c₁ c₂) x m := by
      rintro ⟨m, hm⟩
      cases hm with
      | seq h₁' h₂' =>
        obtain rfl := h₁.unique h₁'
        exact hnot₂ (Exists.intro _ (h₂' z₀ hz₀))
    rw [expectedCodeTime_eq_top hnot_seq,
      ProbComp.expect_eq_top_of_mem_support hz₀ (expectedCodeTime_eq_top hnot₂), add_top]

/-- Sequential additivity after a deterministic prefix `Exec w c₁ x y n₁`. -/
theorem expectedCodeTime_seq_of_exec {w n₁ : ℕ} {c₁ c₂ : Code B r} {x y : Data r}
    (h₁ : Exec w c₁ x y n₁) :
    expectedCodeTime w (.seq c₁ c₂) x = n₁ + expectedCodeTime w c₂ y := by
  rw [expectedCodeTime_seq h₁.execRand, h₁.expectedCodeTime_eq, ProbComp.expect_pure]

theorem expectedCodeTime_branch_pos {w : ℕ} {cond : Cond r} {pos neg : Code B r} {x : Data r}
    (hc : cond.Holds x) :
    expectedCodeTime w (.branch cond pos neg) x = expectedCodeTime w pos x + 1 := by
  classical
  by_cases hp : ∃ m, ExecRand w pos x m
  · obtain ⟨m, hm⟩ := hp
    rw [(hm.branch_pos hc).expectedCodeTime_eq, hm.expectedCodeTime_eq, ProbComp.expect_map,
      ← ProbComp.expect_const m 1, ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z _ => ?_
    simp only [Nat.cast_add, Nat.cast_one]
  · have hnot : ¬∃ m, ExecRand w (.branch cond pos neg) x m := by
      rintro ⟨m, hm⟩
      cases hm with
      | branch_pos _ h => exact hp (Exists.intro _ h)
      | branch_neg hc' _ => exact hc' hc
    simp only [expectedCodeTime, hnot, hp, ↓reduceIte, top_add]

theorem expectedCodeTime_branch_neg {w : ℕ} {cond : Cond r} {pos neg : Code B r} {x : Data r}
    (hc : ¬cond.Holds x) :
    expectedCodeTime w (.branch cond pos neg) x = expectedCodeTime w neg x + 2 := by
  classical
  by_cases hn : ∃ m, ExecRand w neg x m
  · obtain ⟨m, hm⟩ := hn
    rw [(hm.branch_neg hc).expectedCodeTime_eq, hm.expectedCodeTime_eq, ProbComp.expect_map,
      ← ProbComp.expect_const m 2, ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z _ => ?_
    simp only [Nat.cast_add, Nat.cast_ofNat]
  · have hnot : ¬∃ m, ExecRand w (.branch cond pos neg) x m := by
      rintro ⟨m, hm⟩
      cases hm with
      | branch_pos hc' _ => exact hc hc'
      | branch_neg _ h => exact hn (Exists.intro _ h)
    simp only [expectedCodeTime, hnot, hn, ↓reduceIte, top_add]

/-- Branch convexity / uniform upper bound on `expectedCodeTime (.branch cond pos neg)`. -/
theorem expectedCodeTime_branch_le {w : ℕ} {cond : Cond r} {pos neg : Code B r} {x : Data r}
    {B_steps : ℝ≥0∞}
    (hpos : cond.Holds x → expectedCodeTime w pos x + 1 ≤ B_steps)
    (hneg : ¬cond.Holds x → expectedCodeTime w neg x + 2 ≤ B_steps) :
    expectedCodeTime w (.branch cond pos neg) x ≤ B_steps := by
  by_cases hc : cond.Holds x
  · rw [expectedCodeTime_branch_pos hc]
    exact hpos hc
  · rw [expectedCodeTime_branch_neg hc]
    exact hneg hc

/-- Convex combination of branch expected times under a random input distribution `m`. -/
theorem expect_expectedCodeTime_branch {w : ℕ} {cond : Cond r} {pos neg : Code B r}
    (m : ProbComp (Data r)) :
    ProbComp.expect m (fun x => expectedCodeTime w (.branch cond pos neg) x) =
      ProbComp.expect m (fun x =>
        open Classical in
        if cond.Holds x then expectedCodeTime w pos x + 1 else expectedCodeTime w neg x + 2) := by
  refine ProbComp.expect_congr_on_support fun x _ => ?_
  by_cases hc : cond.Holds x
  · simp [hc, expectedCodeTime_branch_pos hc]
  · simp [hc, expectedCodeTime_branch_neg hc]

theorem expectedCodeTime_loop_exit {w : ℕ} {cond : Cond r} {body : Code B r} {x : Data r}
    (hc : ¬cond.Holds x) :
    expectedCodeTime w (.loop cond body) x = 2 := by
  rw [(ExecRand.loop_exit (body := body) hc).expectedCodeTime_eq, ProbComp.expect_pure]
  rfl

theorem expectedCodeTime_loop_iter {w : ℕ} {cond : Cond r} {body : Code B r} {x : Data r}
    {mb : ProbComp (Data r × ℕ)} (hc : cond.Holds x) (hb : ExecRand w body x mb) :
    expectedCodeTime w (.loop cond body) x =
      expectedCodeTime w body x + 2 +
        ProbComp.expect mb (fun z => expectedCodeTime w (.loop cond body) z.1) := by
  classical
  by_cases hl : ∀ z ∈ mb.support, ∃ ml, ExecRand w (.loop cond body) z.1 ml
  · have hl_comp : ∀ z ∈ mb.support,
        ExecRand w (.loop cond body) z.1 (codeComp w (.loop cond body) z.1) :=
      fun z hz => codeComp_execRand (hl z hz)
    rw [(ExecRand.loop_iter hc hb hl_comp).expectedCodeTime_eq, hb.expectedCodeTime_eq,
      ProbComp.expect_bind, ← ProbComp.expect_const mb 2, ← ProbComp.expect_add,
      ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z hz => ?_
    rw [ProbComp.expect_bind, (hl_comp z hz).expectedCodeTime_eq,
      ← ProbComp.expect_const (codeComp w (.loop cond body) z.1) ((z.2 : ℝ≥0∞) + 2),
      ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z₂ _ => ?_
    simp only [ProbComp.expect_pure, Nat.cast_add, Nat.cast_ofNat]
    ac_rfl
  · simp only [not_forall] at hl
    obtain ⟨z₀, hz₀, hnot_l⟩ := hl
    have hnot_loop : ¬∃ m, ExecRand w (.loop cond body) x m := by
      rintro ⟨m, hm⟩
      cases hm with
      | loop_exit hc' => exact hc' hc
      | loop_iter _ hb' hl' =>
        obtain rfl := hb.unique hb'
        exact hnot_l (Exists.intro _ (hl' z₀ hz₀))
    rw [expectedCodeTime_eq_top hnot_loop,
      ProbComp.expect_eq_top_of_mem_support hz₀ (expectedCodeTime_eq_top hnot_l), add_top]

/-- Potential/drift bound for `Code.loop`: if an invariant `I` holds, every iteration decreases a
well-founded `ℕ` ranking `Φ`, and the expected single-iteration cost `(z.2 : ℝ≥0∞) + 2` plus next
potential `Ψ z.1` is at most `Ψ s`, then the loop executes cleanly (`∃ m, ExecRand ...`) and its
`expectedCodeTime` is at most `Ψ x + 2` (accounting for the final `2`-step loop exit). -/
theorem expectedCodeTime_loop_le_of_drift {w : ℕ} {cond : Cond r} {body : Code B r}
    (I : Data r → Prop) (Φ : Data r → ℕ) (Ψ : Data r → ℝ≥0∞) {x : Data r}
    (hx : I x)
    (hstep : ∀ s, I s → cond.Holds s →
      ∃ mb, ExecRand w body s mb ∧
        (∀ z ∈ mb.support, I z.1 ∧ Φ z.1 < Φ s) ∧
        ProbComp.expect mb (fun z => (z.2 : ℝ≥0∞) + 2 + Ψ z.1) ≤ Ψ s) :
    (∃ m, ExecRand w (.loop cond body) x m) ∧
      expectedCodeTime w (.loop cond body) x ≤ Ψ x + 2 := by
  suffices ∀ k s, I s → Φ s ≤ k →
      (∃ m, ExecRand w (.loop cond body) s m) ∧
        expectedCodeTime w (.loop cond body) s ≤ Ψ s + 2 from
    this (Φ x) x hx le_rfl
  intro k
  induction k with
  | zero =>
    intro s hs hΦ
    by_cases hc : cond.Holds s
    · obtain ⟨mb, _, hsup, _⟩ := hstep s hs hc
      obtain ⟨z₀, hz₀⟩ := ProbComp.support_nonempty mb
      have := (hsup z₀ hz₀).2
      omega
    · exact ⟨Exists.intro _ (ExecRand.loop_exit hc),
        by rw [expectedCodeTime_loop_exit hc]; exact le_add_self⟩
  | succ k ih =>
    intro s hs hΦ
    by_cases hc : cond.Holds s
    · obtain ⟨mb, hb, hsup, hdrift⟩ := hstep s hs hc
      have hrec : ∀ z ∈ mb.support,
          (∃ m, ExecRand w (.loop cond body) z.1 m) ∧
            expectedCodeTime w (.loop cond body) z.1 ≤ Ψ z.1 + 2 :=
        fun z hz => ih z.1 (hsup z hz).1 (by have := (hsup z hz).2; omega)
      have hl_comp : ∀ z ∈ mb.support,
          ExecRand w (.loop cond body) z.1 (codeComp w (.loop cond body) z.1) :=
        fun z hz => codeComp_execRand (hrec z hz).1
      refine ⟨Exists.intro _ (ExecRand.loop_iter hc hb hl_comp), ?_⟩
      rw [expectedCodeTime_loop_iter hc hb, hb.expectedCodeTime_eq]
      calc
        ProbComp.expect mb (fun z => (z.2 : ℝ≥0∞)) + 2 +
            ProbComp.expect mb (fun z => expectedCodeTime w (.loop cond body) z.1)
          ≤ ProbComp.expect mb (fun z => (z.2 : ℝ≥0∞)) + 2 +
              ProbComp.expect mb (fun z => Ψ z.1 + 2) := by
            gcongr
            exact ProbComp.expect_mono_on_support fun z hz => (hrec z hz).2
        _ = ProbComp.expect mb (fun z => (z.2 : ℝ≥0∞) + 2 + Ψ z.1) + 2 := by
            rw [add_right_comm _ 2 _, ← ProbComp.expect_add]
            congr 1
            refine ProbComp.expect_congr_on_support fun z _ => ?_
            ac_rfl
        _ ≤ Ψ s + 2 := by gcongr
    · exact ⟨Exists.intro _ (ExecRand.loop_exit hc),
        by rw [expectedCodeTime_loop_exit hc]; exact le_add_self⟩

end WordRAM

end Cslib
