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
import Complexity.Foundations.Analysis.ENNRealTsum
import Complexity.Probability.PMF.Expect

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
* `Cslib.WordRAM.ExecCodeDist`: compositional structured execution certificate pairing an output
  distribution `μ : PMF (Data r)` with an expected step bound `T : ℝ≥0∞`, closed under unbounded
  almost-surely terminating geometric `while` loops (`ExecCodeDist.loop_geometric`).

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
* `Cslib.WordRAM.ExecCodeDist.loop_geometric`,
  `Cslib.WordRAM.expectedStepsFrom_loop_le_of_geometric`,
  `Cslib.WordRAM.ExecCodeDist.program_halts`: expected-time and almost-sure halting rules for
  geometric Las Vegas `while` loops and structured programs.

Discrete and conditional expectation principles are classical background; see
[MitzenmacherUpfal2017], Sections 2.1, 2.3, and 2.4. The particular native tail-sum/Bellman
definitions, finite structured-execution-tree bridge and ranked-loop expected-cost formalization are
original library constructions in this module.

## References

* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017],
  Sections 2.1, 2.3, and 2.4.
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

/-! ## Distributional structured execution (`ExecCodeDist`) and geometric Las Vegas loops -/

/-- Non-faulting structured randomized executions transfer instruction-for-instruction along any
defined-evaluation basis simulation `ψ : B.Simulates B'`. -/
theorem ExecRand.mapSimulates {B' : Basis} (ψ : B.Simulates B') {w : ℕ} {c : Code B r}
    {x : Data r} {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) :
    ExecRand w (c.mapSimulates ψ) x m := by
  induction h with
  | op ho => exact .op (Op.eval_mapSimulates_of_some ψ ho)
  | rand hfit => exact .rand hfit
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_exit hc => exact .loop_exit hc
  | loop_iter hc _ _ ihb ihl => exact .loop_iter hc ihb ihl

/-- Pointwise halting probability at `.halted v d` is monotone in the horizon `T`. -/
theorem evalRand_halted_mono (w : ℕ) (p : Program B r) (s : State r) (v : ℕ) (d : Data r) :
    Monotone fun T => evalRand w p T s (.halted v d) := by
  refine monotone_nat_of_le_succ fun T => ?_
  have hstep : evalRand w p (T + 1) s =
      (evalRand w p T s).bind (fun cfg => (stepRand w p cfg).eval) := by
    rw [evalRand, runRand_add w p T 1, ProbComp.eval_bind]
    simp only [evalRand, runRand_succ, runRand_zero, bind_pure]
  rw [hstep, PMF.bind_apply]
  calc
    evalRand w p T s (.halted v d)
      = evalRand w p T s (.halted v d) * (stepRand w p (.halted v d)).eval (.halted v d) := by
        simp [stepRand_halted]
    _ ≤ ∑' cfg, evalRand w p T s cfg * (stepRand w p cfg).eval (.halted v d) :=
        le_tsum
          (f := fun cfg => evalRand w p T s cfg * (stepRand w p cfg).eval (.halted v d))
          (RandCfg.halted v d)

/-- Finite-horizon approximation of `expectedStepsFrom`: expected number of active (`.running`)
steps within the first `N` steps starting from configuration `cfg`. -/
noncomputable def expectedStepsWithin (w : ℕ) (p : Program B r) (N : ℕ) (cfg : RandCfg r) :
    ℝ≥0∞ :=
  ∑ t ∈ Finset.range N, (runRand w p t cfg).eval.toOuterMeasure {cfg' | ∃ u, cfg' = .running u}

@[simp]
theorem expectedStepsWithin_zero (w : ℕ) (p : Program B r) (cfg : RandCfg r) :
    expectedStepsWithin w p 0 cfg = 0 := by
  simp [expectedStepsWithin]

@[simp]
theorem expectedStepsWithin_halted (w : ℕ) (p : Program B r) (N v : ℕ) (d : Data r) :
    expectedStepsWithin w p N (.halted v d) = 0 := by
  simp [expectedStepsWithin, PMF.toOuterMeasure_pure_apply]

@[simp]
theorem expectedStepsWithin_faulted (w : ℕ) (p : Program B r) (N : ℕ) :
    expectedStepsWithin w p N .faulted = 0 := by
  simp [expectedStepsWithin, PMF.toOuterMeasure_pure_apply]

theorem expectedStepsWithin_mono (w : ℕ) (p : Program B r) (cfg : RandCfg r) :
    Monotone fun N => expectedStepsWithin w p N cfg := by
  intro N₁ N₂ hN
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hN)

theorem iSup_expectedStepsWithin (w : ℕ) (p : Program B r) (cfg : RandCfg r) :
    (⨆ N : ℕ, expectedStepsWithin w p N cfg) = expectedStepsFrom w p cfg :=
  (ENNReal.tsum_eq_iSup_nat).symm

theorem expectedStepsWithin_le_expectedStepsFrom (w : ℕ) (p : Program B r) (N : ℕ)
    (cfg : RandCfg r) :
    expectedStepsWithin w p N cfg ≤ expectedStepsFrom w p cfg := by
  rw [← iSup_expectedStepsWithin]
  exact le_iSup (fun K => expectedStepsWithin w p K cfg) N

/-- 1-step horizon recursion for `expectedStepsWithin`: at horizon `N + 1`, an active state `s`
incurs `1` step plus the `N`-step continuation expectation. -/
theorem expectedStepsWithin_running_succ (w : ℕ) (p : Program B r) (N : ℕ) (s : State r) :
    expectedStepsWithin w p (N + 1) (.running s) =
      1 + ProbComp.expect (stepRand w p (.running s)) (expectedStepsWithin w p N) := by
  rw [expectedStepsWithin, Finset.sum_range_succ']
  have hzero : (runRand w p 0 (.running s)).eval.toOuterMeasure
      {cfg' | ∃ u, cfg' = .running u} = 1 := by
    simp [PMF.toOuterMeasure_pure_apply]
  rw [hzero, add_comm]
  congr 1
  have hsucc : ∀ t : ℕ, (runRand w p (t + 1) (.running s)).eval.toOuterMeasure
      {cfg' | ∃ u, cfg' = .running u} =
      ∑' cfg, (stepRand w p (.running s)).eval cfg *
        (runRand w p t cfg).eval.toOuterMeasure {cfg' | ∃ u, cfg' = .running u} := by
    intro t
    rw [runRand_succ, ProbComp.eval_bind, PMF.toOuterMeasure_bind_apply]
  simp only [hsucc]
  rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
  simp only [ProbComp.expect, expectedStepsWithin, Finset.mul_sum]

theorem expectedStepsWithin_running_le (w : ℕ) (p : Program B r) (N : ℕ) (s : State r) :
    expectedStepsWithin w p N (.running s) ≤
      1 + ProbComp.expect (stepRand w p (.running s)) (expectedStepsWithin w p N) := by
  cases N with
  | zero => simp
  | succ N =>
    rw [expectedStepsWithin_running_succ]
    gcongr
    exact ProbComp.expect_mono fun cfg => expectedStepsWithin_mono w p cfg (Nat.le_succ N)

theorem ExecRand.expectedStepsWithin_assemble {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) (N : ℕ) :
    expectedStepsWithin w p N (.running ⟨pc, x⟩) ≤
      ProbComp.expect m (fun z =>
        (z.2 : ℝ≥0∞) + expectedStepsWithin w p N (.running ⟨pc + c.size, z.1⟩)) := by
  induction h generalizing pc with
  | @op o x y ho =>
    refine (expectedStepsWithin_running_le w p N ⟨pc, x⟩).trans ?_
    rw [stepRand_op (s := ⟨pc, x⟩) hp.head ho, ProbComp.expect_pure, ProbComp.expect_pure]
    simp [Code.size]
  | @rand dst src x hfit =>
    refine (expectedStepsWithin_running_le w p N ⟨pc, x⟩).trans ?_
    rw [stepRand_rand_of_fits (s := ⟨pc, x⟩) hp.head hfit, ProbComp.expect_bind,
      ProbComp.expect_bind]
    simp only [ProbComp.expect_pure, Code.size, Nat.cast_one]
    rw [ProbComp.expect_add, ProbComp.expect_const]
  | @seq c₁ c₂ x m₁ m₂ _ _ ih₁ ih₂ =>
    have hc₂ : p.Contains (pc + c₁.size) (c₂.assemble (pc + c₁.size)) := by
      simpa [Code.length_assemble] using hp.append_right
    refine (ih₁ hp.append_left).trans ?_
    rw [ProbComp.expect_bind]
    refine ProbComp.expect_mono_on_support fun z₁ hz₁ => ?_
    refine (add_le_add le_rfl (ih₂ z₁ hz₁ hc₂)).trans (le_of_eq ?_)
    rw [ProbComp.expect_bind,
      ← ProbComp.expect_const (m₂ z₁.1) (z₁.2 : ℝ≥0∞), ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z₂ _ => ?_
    simp only [ProbComp.expect_pure, Code.size, Nat.cast_add, add_assoc]
  | @branch_pos cond pos neg x m hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    refine (expectedStepsWithin_running_le w p N ⟨pc, x⟩).trans ?_
    rw [stepRand_branch (s := ⟨pc, x⟩) hbr]
    simp only [hc, ↓reduceIte, ProbComp.expect_pure]
    have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
    rw [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'
    refine (add_le_add le_rfl (ih hc')).trans (le_of_eq ?_)
    rw [ProbComp.expect_map, ← ProbComp.expect_const m 1, ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z _ => ?_
    simp only [Code.size, Nat.cast_add, Nat.cast_one]
    rw [show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
    ac_rfl
  | @branch_neg cond pos neg x m hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    refine (expectedStepsWithin_running_le w p N ⟨pc, x⟩).trans ?_
    rw [stepRand_branch (s := ⟨pc, x⟩) hbr]
    simp only [hc, ↓reduceIte, ProbComp.expect_pure]
    refine (add_le_add le_rfl (ih hp.cons_tail.append_left)).trans ?_
    rw [ProbComp.expect_map, ← ProbComp.expect_const m 1, ← ProbComp.expect_add]
    refine ProbComp.expect_mono_on_support fun z _ => ?_
    have hj : p[pc + 1 + neg.size]? = some (.jump (pc + neg.size + pos.size + 2)) := by
      simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head
    refine (add_le_add le_rfl
      (add_le_add le_rfl (expectedStepsWithin_running_le w p N ⟨pc + 1 + neg.size, z.1⟩))).trans
      (le_of_eq ?_)
    rw [stepRand_jump (s := ⟨pc + 1 + neg.size, z.1⟩) hj, ProbComp.expect_pure]
    simp only [Code.size, Nat.cast_add, Nat.cast_ofNat]
    rw [show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
    set E := expectedStepsWithin w p N (.running ⟨pc + (neg.size + pos.size + 2), z.1⟩)
    calc
      1 + ((z.2 : ℝ≥0∞) + (1 + E)) = (z.2 : ℝ≥0∞) + (1 + 1) + E := by ac_rfl
      _ = (z.2 : ℝ≥0∞) + 2 + E := by rw [one_add_one_eq_two]
  | @loop_exit cond body x hc =>
    have hbr : p[pc]? = some (.branch cond (pc + 2)) := hp.head
    have hj : p[pc + 1]? = some (.jump (pc + body.size + 3)) := hp.cons_tail.head
    refine (expectedStepsWithin_running_le w p N ⟨pc, x⟩).trans ?_
    rw [stepRand_branch (s := ⟨pc, x⟩) hbr]
    simp only [hc, ↓reduceIte, ProbComp.expect_pure]
    refine (add_le_add le_rfl (expectedStepsWithin_running_le w p N ⟨pc + 1, x⟩)).trans
      (le_of_eq ?_)
    rw [stepRand_jump (s := ⟨pc + 1, x⟩) hj, ProbComp.expect_pure]
    simp only [Code.size, Nat.cast_ofNat]
    rw [← add_assoc, one_add_one_eq_two, show pc + body.size + 3 = pc + (body.size + 3) by omega]
  | @loop_iter cond body x mb ml hc _ _ ihb ihl =>
    have hbr : p[pc]? = some (.branch cond (pc + 2)) := hp.head
    have hbody_contains : p.Contains (pc + 2) (body.assemble (pc + 2)) := by
      simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left
    have hj : p[pc + 2 + body.size]? = some (.jump pc) := by
      simpa using hp.cons_tail.cons_tail.append_right.head
    refine (expectedStepsWithin_running_le w p N ⟨pc, x⟩).trans ?_
    rw [stepRand_branch (s := ⟨pc, x⟩) hbr]
    simp only [hc, ↓reduceIte, ProbComp.expect_pure]
    refine (add_le_add le_rfl (ihb hbody_contains)).trans ?_
    rw [ProbComp.expect_bind, ← ProbComp.expect_const mb 1, ← ProbComp.expect_add]
    refine ProbComp.expect_mono_on_support fun z₁ hz₁ => ?_
    have hjump_le : expectedStepsWithin w p N (.running ⟨pc + 2 + body.size, z₁.1⟩) ≤
        1 + ProbComp.expect (ml z₁.1) (fun z =>
          (z.2 : ℝ≥0∞) +
            expectedStepsWithin w p N (.running ⟨pc + (Code.loop cond body).size, z.1⟩)) := by
      refine (expectedStepsWithin_running_le w p N ⟨pc + 2 + body.size, z₁.1⟩).trans ?_
      rw [stepRand_jump (s := ⟨pc + 2 + body.size, z₁.1⟩) hj, ProbComp.expect_pure]
      exact add_le_add le_rfl (ihl z₁ hz₁ hp)
    refine (add_le_add le_rfl (add_le_add le_rfl hjump_le)).trans (le_of_eq ?_)
    rw [ProbComp.expect_bind]
    have hconst : (1 : ℝ≥0∞) + ((z₁.2 : ℝ≥0∞) +
        (1 + ProbComp.expect (ml z₁.1) fun z =>
          (z.2 : ℝ≥0∞) +
            expectedStepsWithin w p N (.running ⟨pc + (Code.loop cond body).size, z.1⟩))) =
        ProbComp.expect (ml z₁.1) (fun _ => (z₁.2 : ℝ≥0∞) + 2) +
          ProbComp.expect (ml z₁.1) (fun z =>
            (z.2 : ℝ≥0∞) +
              expectedStepsWithin w p N (.running ⟨pc + (Code.loop cond body).size, z.1⟩)) := by
      rw [ProbComp.expect_const, ← one_add_one_eq_two]
      ac_rfl
    rw [hconst, ← ProbComp.expect_add]
    refine ProbComp.expect_congr_on_support fun z₂ _ => ?_
    simp only [ProbComp.expect_pure, Nat.cast_add, Nat.cast_ofNat]
    rw [← add_assoc ((z₁.2 : ℝ≥0∞) + 2) (z₂.2 : ℝ≥0∞), add_right_comm (z₁.2 : ℝ≥0∞) 2]

/-- Along `ExecRand w c x m`, if no continuation from `⟨pc + c.size, y⟩` faults within `T` steps
for any supported outcome `y`, then running `p` from `⟨pc, x⟩` does not fault within `T` steps. -/
theorem ExecRand.evalRand_faulted_eq_zero {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) {p : Program B r} {pc T : ℕ}
    (hp : p.Contains pc (c.assemble pc))
    (hcont : ∀ z ∈ m.support, ∀ t ≤ T, evalRand w p t ⟨pc + c.size, z.1⟩ .faulted = 0) :
    ∀ t ≤ T, evalRand w p t ⟨pc, x⟩ .faulted = 0 := by
  induction h generalizing pc T with
  | @op o x y ho =>
    intro t ht
    cases t with
    | zero => simp [evalRand]
    | succ k =>
      rw [evalRand, runRand_succ, stepRand_op (s := ⟨pc, x⟩) hp.head ho, pure_bind]
      simpa [evalRand, Code.size] using hcont (y, 1) rfl k (by omega)
  | @rand dst src x hfit =>
    intro t ht
    cases t with
    | zero => simp [evalRand]
    | succ k =>
      rw [evalRand, runRand_succ, stepRand_rand_of_fits (s := ⟨pc, x⟩) hp.head hfit, bind_assoc,
        ProbComp.eval_bind, PMF.bind_apply, tsum_eq_zero_iff]
      intro sample
      have hmem : (x.set dst sample.val, 1) ∈
          (ProbComp.unifFin (x.regs src) >>= fun s => pure (x.set dst s.val, 1)).support :=
        OracleComp.mem_supportWith_bind_iff.mpr ⟨sample, ProbComp.mem_support_unifFin _ sample, rfl⟩
      have hzero := hcont _ hmem k (by omega)
      simp only [pure_bind]
      exact mul_eq_zero_of_right _ hzero
  | @seq c₁ c₂ x m₁ m₂ _ _ ih₁ ih₂ =>
    have hc₂ : p.Contains (pc + c₁.size) (c₂.assemble (pc + c₁.size)) := by
      simpa [Code.length_assemble] using hp.append_right
    refine ih₁ hp.append_left fun z₁ hz₁ t ht => ?_
    refine ih₂ z₁ hz₁ hc₂ (T := t) (fun z₂ hz₂ t' ht' => ?_) t le_rfl
    have hmem : (z₂.1, z₁.2 + z₂.2) ∈
        (m₁ >>= fun z₁ => m₂ z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2)).support :=
      OracleComp.mem_supportWith_bind_iff.mpr
        ⟨z₁, hz₁, OracleComp.mem_supportWith_bind_iff.mpr ⟨z₂, hz₂, rfl⟩⟩
    simpa [Code.size, Nat.add_assoc] using hcont _ hmem t' (ht'.trans ht)
  | @branch_pos cond pos neg x m hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
    rw [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'
    intro t ht
    cases t with
    | zero => simp [evalRand]
    | succ k =>
      rw [evalRand, runRand_succ, stepRand_branch (s := ⟨pc, x⟩) hbr]
      simp only [hc, ↓reduceIte, pure_bind]
      refine ih hc' (T := k) (fun z hz t' ht' => ?_) k le_rfl
      have hmem : (z.1, z.2 + 1) ∈ ((fun z : Data r × ℕ => (z.1, z.2 + 1)) <$> m).support :=
        OracleComp.mem_supportWith_map_iff.mpr ⟨z, hz, rfl⟩
      simpa [Code.size, show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
        using hcont _ hmem t' (by omega)
  | @branch_neg cond pos neg x m hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hj : p[pc + 1 + neg.size]? = some (.jump (pc + neg.size + pos.size + 2)) := by
      simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head
    intro t ht
    cases t with
    | zero => simp [evalRand]
    | succ k =>
      rw [evalRand, runRand_succ, stepRand_branch (s := ⟨pc, x⟩) hbr]
      simp only [hc, ↓reduceIte, pure_bind]
      refine ih hp.cons_tail.append_left (T := k) (fun z hz t' ht' => ?_) k le_rfl
      cases t' with
      | zero => simp [evalRand]
      | succ k' =>
        rw [evalRand, runRand_succ, stepRand_jump (s := ⟨pc + 1 + neg.size, z.1⟩) hj, pure_bind]
        have hmem : (z.1, z.2 + 2) ∈ ((fun z : Data r × ℕ => (z.1, z.2 + 2)) <$> m).support :=
          OracleComp.mem_supportWith_map_iff.mpr ⟨z, hz, rfl⟩
        simpa [evalRand, Code.size,
          show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
          using hcont _ hmem k' (by omega)
  | @loop_exit cond body x hc =>
    have hbr : p[pc]? = some (.branch cond (pc + 2)) := hp.head
    have hj : p[pc + 1]? = some (.jump (pc + body.size + 3)) := hp.cons_tail.head
    intro t ht
    cases t with
    | zero => simp [evalRand]
    | succ k =>
      rw [evalRand, runRand_succ, stepRand_branch (s := ⟨pc, x⟩) hbr]
      simp only [hc, ↓reduceIte, pure_bind]
      cases k with
      | zero => simp
      | succ k' =>
        rw [runRand_succ, stepRand_jump (s := ⟨pc + 1, x⟩) hj, pure_bind]
        simpa [evalRand, Code.size, show pc + body.size + 3 = pc + (body.size + 3) by omega]
          using hcont (x, 2) rfl k' (by omega)
  | @loop_iter cond body x mb ml hc _ _ ihb ihl =>
    have hbr : p[pc]? = some (.branch cond (pc + 2)) := hp.head
    have hbody_contains : p.Contains (pc + 2) (body.assemble (pc + 2)) := by
      simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left
    have hj : p[pc + 2 + body.size]? = some (.jump pc) := by
      simpa using hp.cons_tail.cons_tail.append_right.head
    intro t ht
    cases t with
    | zero => simp [evalRand]
    | succ k =>
      rw [evalRand, runRand_succ, stepRand_branch (s := ⟨pc, x⟩) hbr]
      simp only [hc, ↓reduceIte, pure_bind]
      refine ihb hbody_contains (T := k) (fun z₁ hz₁ t' ht' => ?_) k le_rfl
      cases t' with
      | zero => simp [evalRand]
      | succ k' =>
        rw [evalRand, runRand_succ, stepRand_jump (s := ⟨pc + 2 + body.size, z₁.1⟩) hj, pure_bind]
        refine ihl z₁ hz₁ hp (T := k') (fun z₂ hz₂ t'' ht'' => ?_) k' le_rfl
        have hmem : (z₂.1, z₁.2 + z₂.2 + 2) ∈
            (mb >>= fun z₁ => ml z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2 + 2)).support :=
          OracleComp.mem_supportWith_bind_iff.mpr
            ⟨z₁, hz₁, OracleComp.mem_supportWith_bind_iff.mpr ⟨z₂, hz₂, rfl⟩⟩
        exact hcont _ hmem t'' (by omega)

private theorem iSup_evalRand_halted_le_of_step {w : ℕ} {p : Program B r} {s s' : State r}
    (hstep : stepRand w p (.running s) = pure (.running s')) (v : ℕ) (d : Data r) :
    (⨆ T : ℕ, evalRand w p T s' (.halted v d)) ≤ ⨆ T : ℕ, evalRand w p T s (.halted v d) := by
  refine iSup_le fun T => le_iSup_of_le (T + 1) ?_
  simp only [evalRand, runRand_succ, hstep, pure_bind, le_rfl]

/-- Along `ExecRand w c x m`, the expected supremum halting probability from `⟨pc + c.size, y⟩` is a
lower bound on the supremum halting probability from `⟨pc, x⟩`. -/
theorem ExecRand.le_iSup_evalRand_halted {w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) (v : ℕ) (d : Data r) :
    ProbComp.expect m (fun z => ⨆ T : ℕ, evalRand w p T ⟨pc + c.size, z.1⟩ (.halted v d)) ≤
      ⨆ T : ℕ, evalRand w p T ⟨pc, x⟩ (.halted v d) := by
  induction h generalizing pc with
  | @op o x y ho =>
    rw [ProbComp.expect_pure]
    simpa [Code.size] using
      iSup_evalRand_halted_le_of_step (stepRand_op (s := ⟨pc, x⟩) hp.head ho) v d
  | @rand dst src x hfit =>
    rw [ProbComp.expect_bind]
    simp only [ProbComp.expect_pure, Code.size]
    change (∑' sample : Fin (x.regs src + 1),
        (ProbComp.unifFin (x.regs src)).eval sample *
          ⨆ T : ℕ, evalRand w p T ⟨pc + 1, x.set dst sample.val⟩ (.halted v d)) ≤
      ⨆ T : ℕ, evalRand w p T ⟨pc, x⟩ (.halted v d)
    simp_rw [ENNReal.mul_iSup]
    rw [ENNReal.tsum_iSup_of_monotone fun sample T₁ T₂ hT =>
      mul_le_mul_right (evalRand_halted_mono w p ⟨pc + 1, x.set dst sample.val⟩ v d hT) _]
    refine iSup_le fun T => le_iSup_of_le (T + 1) ?_
    rw [evalRand, runRand_succ, stepRand_rand_of_fits (s := ⟨pc, x⟩) hp.head hfit, bind_assoc,
      ProbComp.eval_bind, PMF.bind_apply]
    refine le_of_eq (tsum_congr fun sample => ?_)
    simp [evalRand]
  | @seq c₁ c₂ x m₁ m₂ _ _ ih₁ ih₂ =>
    have hc₂ : p.Contains (pc + c₁.size) (c₂.assemble (pc + c₁.size)) := by
      simpa [Code.length_assemble] using hp.append_right
    rw [ProbComp.expect_bind]
    refine (ProbComp.expect_mono_on_support fun z₁ hz₁ => ?_).trans (ih₁ hp.append_left)
    rw [ProbComp.expect_bind]
    refine (ProbComp.expect_mono_on_support fun z₂ _ => ?_).trans (ih₂ z₁ hz₁ hc₂)
    simp only [ProbComp.expect_pure, Code.size, Nat.add_assoc, le_rfl]
  | @branch_pos cond pos neg x m hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
    rw [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'
    have hstep : stepRand w p (.running ⟨pc, x⟩) = pure (.running ⟨pc + neg.size + 2, x⟩) := by
      rw [stepRand_branch (s := ⟨pc, x⟩) hbr]
      simp [hc]
    rw [ProbComp.expect_map]
    refine (ProbComp.expect_mono_on_support fun z _ => ?_).trans
      ((ih hc').trans (iSup_evalRand_halted_le_of_step hstep v d))
    simp only [Code.size,
      show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega, le_rfl]
  | @branch_neg cond pos neg x m hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hj : p[pc + 1 + neg.size]? = some (.jump (pc + neg.size + pos.size + 2)) := by
      simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head
    have hstep : stepRand w p (.running ⟨pc, x⟩) = pure (.running ⟨pc + 1, x⟩) := by
      rw [stepRand_branch (s := ⟨pc, x⟩) hbr]
      simp [hc]
    rw [ProbComp.expect_map]
    refine (ProbComp.expect_mono_on_support fun z _ => ?_).trans
      ((ih hp.cons_tail.append_left).trans (iSup_evalRand_halted_le_of_step hstep v d))
    simpa [Code.size, show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
      using iSup_evalRand_halted_le_of_step
        (stepRand_jump (s := ⟨pc + 1 + neg.size, z.1⟩) hj) v d
  | @loop_exit cond body x hc =>
    have hbr : p[pc]? = some (.branch cond (pc + 2)) := hp.head
    have hj : p[pc + 1]? = some (.jump (pc + body.size + 3)) := hp.cons_tail.head
    have hstep : stepRand w p (.running ⟨pc, x⟩) = pure (.running ⟨pc + 1, x⟩) := by
      rw [stepRand_branch (s := ⟨pc, x⟩) hbr]
      simp [hc]
    rw [ProbComp.expect_pure]
    simpa [Code.size, show pc + body.size + 3 = pc + (body.size + 3) by omega] using
      (iSup_evalRand_halted_le_of_step (stepRand_jump (s := ⟨pc + 1, x⟩) hj) v d).trans
        (iSup_evalRand_halted_le_of_step hstep v d)
  | @loop_iter cond body x mb ml hc _ _ ihb ihl =>
    have hbr : p[pc]? = some (.branch cond (pc + 2)) := hp.head
    have hbody_contains : p.Contains (pc + 2) (body.assemble (pc + 2)) := by
      simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left
    have hj : p[pc + 2 + body.size]? = some (.jump pc) := by
      simpa using hp.cons_tail.cons_tail.append_right.head
    have hstep : stepRand w p (.running ⟨pc, x⟩) = pure (.running ⟨pc + 2, x⟩) := by
      rw [stepRand_branch (s := ⟨pc, x⟩) hbr]
      simp [hc]
    rw [ProbComp.expect_bind]
    refine (ProbComp.expect_mono_on_support fun z₁ hz₁ => ?_).trans
      ((ihb hbody_contains).trans (iSup_evalRand_halted_le_of_step hstep v d))
    rw [ProbComp.expect_bind]
    refine (ProbComp.expect_mono_on_support fun z₂ _ => ?_).trans
      ((ihl z₁ hz₁ hp).trans
        (iSup_evalRand_halted_le_of_step (stepRand_jump (s := ⟨pc + 2 + body.size, z₁.1⟩) hj) v d))
    simp only [ProbComp.expect_pure, le_rfl]

/-! ### Absorbing Markov chain for geometric Las Vegas loops -/

/-- One step of the stopped loop Markov kernel on `Data r`: active states (`cond.Holds x`) step
according to `μ_body x`, while exiting states (`¬cond.Holds x`) are absorbing. -/
noncomputable def loopStepPMF (cond : Cond r) (μ_body : Data r → PMF (Data r)) (x : Data r) :
    PMF (Data r) :=
  open Classical in
  if cond.Holds x then μ_body x else PMF.pure x

theorem loopStepPMF_of_holds {cond : Cond r} {μ_body : Data r → PMF (Data r)} {x : Data r}
    (hc : cond.Holds x) :
    loopStepPMF cond μ_body x = μ_body x := by
  classical
  simp [loopStepPMF, hc]

theorem loopStepPMF_of_not_holds {cond : Cond r} {μ_body : Data r → PMF (Data r)} {x : Data r}
    (hc : ¬cond.Holds x) :
    loopStepPMF cond μ_body x = PMF.pure x := by
  classical
  simp [loopStepPMF, hc]

/-- `K`-step iterate of `loopStepPMF`. -/
noncomputable def loopIterPMF (cond : Cond r) (μ_body : Data r → PMF (Data r)) :
    ℕ → Data r → PMF (Data r)
  | 0, x => PMF.pure x
  | K + 1, x => (loopStepPMF cond μ_body x).bind (loopIterPMF cond μ_body K)

@[simp]
theorem loopIterPMF_zero (cond : Cond r) (μ_body : Data r → PMF (Data r)) (x : Data r) :
    loopIterPMF cond μ_body 0 x = PMF.pure x := rfl

theorem loopIterPMF_succ (cond : Cond r) (μ_body : Data r → PMF (Data r)) (K : ℕ) (x : Data r) :
    loopIterPMF cond μ_body (K + 1) x =
      (loopStepPMF cond μ_body x).bind (loopIterPMF cond μ_body K) := rfl

theorem loopIterPMF_of_not_holds {cond : Cond r} {μ_body : Data r → PMF (Data r)} {x : Data r}
    (hc : ¬cond.Holds x) (K : ℕ) :
    loopIterPMF cond μ_body K x = PMF.pure x := by
  induction K with
  | zero => rfl
  | succ K ih => rw [loopIterPMF_succ, loopStepPMF_of_not_holds hc, PMF.pure_bind, ih]

theorem loopIterPMF_succ_right (cond : Cond r) (μ_body : Data r → PMF (Data r)) (K : ℕ)
    (x : Data r) :
    loopIterPMF cond μ_body (K + 1) x =
      (loopIterPMF cond μ_body K x).bind (loopStepPMF cond μ_body) := by
  induction K generalizing x with
  | zero => simp [loopIterPMF]
  | succ K ih =>
    rw [loopIterPMF_succ (K := K), PMF.bind_bind]
    exact congrArg ((loopStepPMF cond μ_body x).bind ·) (funext ih)

theorem loopIterPMF_mono_of_not_holds (cond : Cond r) (μ_body : Data r → PMF (Data r))
    (x : Data r) {y : Data r} (hy : ¬cond.Holds y) :
    Monotone fun K => loopIterPMF cond μ_body K x y := by
  refine monotone_nat_of_le_succ fun K => ?_
  rw [loopIterPMF_succ_right, PMF.bind_apply]
  calc
    loopIterPMF cond μ_body K x y
      = loopIterPMF cond μ_body K x y * loopStepPMF cond μ_body y y := by
        rw [loopStepPMF_of_not_holds hy, PMF.pure_apply_self, mul_one]
    _ ≤ ∑' z, loopIterPMF cond μ_body K x z * loopStepPMF cond μ_body z y :=
        le_tsum
          (f := fun z => loopIterPMF cond μ_body K x z * loopStepPMF cond μ_body z y) y

theorem loopIterPMF_indicator_mono (cond : Cond r) (μ_body : Data r → PMF (Data r))
    (x y : Data r) :
    Monotone fun K => Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y := by
  intro K₁ K₂ hK
  dsimp only
  by_cases hy : y ∈ {z | ¬cond.Holds z}
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    exact loopIterPMF_mono_of_not_holds cond μ_body x hy hK
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

/-- Combined loop state invariant: either active (`cond.Holds x ∧ I x`) or exited
(`¬cond.Holds x ∧ Q x`). -/
def LoopStateInv (cond : Cond r) (I Q : Data r → Prop) (x : Data r) : Prop :=
  (cond.Holds x ∧ I x) ∨ (¬cond.Holds x ∧ Q x)

theorem loopIterPMF_support_inv {cond : Cond r} {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)}
    (hinv : ∀ x, I x → cond.Holds x → ∀ y ∈ (μ_body x).support, LoopStateInv cond I Q y)
    (K : ℕ) {x : Data r} (hx : LoopStateInv cond I Q x) :
    ∀ y ∈ (loopIterPMF cond μ_body K x).support, LoopStateInv cond I Q y := by
  induction K generalizing x with
  | zero =>
    intro y hy
    rw [loopIterPMF_zero, PMF.support_pure, Set.mem_singleton_iff] at hy
    rwa [hy]
  | succ K ih =>
    intro y hy
    rw [loopIterPMF_succ, PMF.mem_support_bind_iff] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    rcases hx with ⟨hcx, hIx⟩ | ⟨hcx, hQx⟩
    · rw [loopStepPMF_of_holds hcx] at hz
      exact ih (hinv x hIx hcx z hz) y hyz
    · rw [loopStepPMF_of_not_holds hcx, PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ih (Or.inr ⟨hcx, hQx⟩) y hyz

private theorem pmf_toOuterMeasure_compl_add (μ : PMF (Data r)) (cond : Cond r) :
    μ.toOuterMeasure {y | ¬cond.Holds y} + μ.toOuterMeasure {y | cond.Holds y} = 1 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
  convert μ.tsum_coe using 1
  congr 1
  funext y
  by_cases hc : cond.Holds y <;> simp [hc]

private theorem pmf_step_drift_bound (μ : PMF (Data r)) (cond : Cond r)
    {C p_exit : ℝ≥0∞} (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hp_exit : p_exit ≤ μ.toOuterMeasure {y | ¬cond.Holds y}) :
    C + ∑' y, μ y * (if cond.Holds y then C / p_exit else 0) ≤ C / p_exit := by
  set M := C / p_exit
  have hC : C = p_exit * M := by
    rw [mul_comm, ENNReal.div_mul_cancel hp_pos.ne' hp_top]
  have hact : (∑' y, μ y * (if cond.Holds y then M else 0)) =
      μ.toOuterMeasure {y | cond.Holds y} * M := by
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun y => ?_
    by_cases hc : cond.Holds y <;> simp [hc]
  calc
    C + ∑' y, μ y * (if cond.Holds y then M else 0)
      = p_exit * M + μ.toOuterMeasure {y | cond.Holds y} * M := by rw [hC, hact]
    _ ≤ μ.toOuterMeasure {y | ¬cond.Holds y} * M +
          μ.toOuterMeasure {y | cond.Holds y} * M := by gcongr
    _ = (μ.toOuterMeasure {y | ¬cond.Holds y} +
          μ.toOuterMeasure {y | cond.Holds y}) * M := by rw [← add_mul]
    _ = M := by rw [pmf_toOuterMeasure_compl_add, one_mul]

/-- Expected number of active loop iterations within the first `N` steps of `loopIterPMF`. -/
private noncomputable def loopActiveSteps (cond : Cond r) (μ_body : Data r → PMF (Data r))
    (N : ℕ) (x : Data r) : ℝ≥0∞ :=
  ∑ K ∈ Finset.range N, (loopIterPMF cond μ_body K x).toOuterMeasure {y | cond.Holds y}

private theorem loopActiveSteps_of_not_holds {cond : Cond r} {μ_body : Data r → PMF (Data r)}
    {x : Data r} (hc : ¬cond.Holds x) (N : ℕ) :
    loopActiveSteps cond μ_body N x = 0 := by
  unfold loopActiveSteps
  refine Finset.sum_eq_zero fun K _ => ?_
  rw [loopIterPMF_of_not_holds hc, PMF.toOuterMeasure_pure_apply]
  simp [hc]

private theorem loopActiveSteps_succ_of_holds {cond : Cond r} {μ_body : Data r → PMF (Data r)}
    {x : Data r} (hc : cond.Holds x) (N : ℕ) :
    loopActiveSteps cond μ_body (N + 1) x =
      1 + ∑' z, μ_body x z * loopActiveSteps cond μ_body N z := by
  rw [loopActiveSteps, Finset.sum_range_succ']
  have hzero : (loopIterPMF cond μ_body 0 x).toOuterMeasure {y | cond.Holds y} = 1 := by
    simp [PMF.toOuterMeasure_pure_apply, hc]
  rw [hzero, add_comm]
  congr 1
  have hsucc : ∀ K : ℕ, (loopIterPMF cond μ_body (K + 1) x).toOuterMeasure {y | cond.Holds y} =
      ∑' z, μ_body x z * (loopIterPMF cond μ_body K z).toOuterMeasure {y | cond.Holds y} := by
    intro K
    rw [loopIterPMF_succ, loopStepPMF_of_holds hc, PMF.toOuterMeasure_bind_apply]
  simp only [hsucc]
  rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
  simp only [loopActiveSteps, Finset.mul_sum]

private theorem loopActiveSteps_le {cond : Cond r} {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x → ∀ y ∈ (μ_body x).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x → p_exit ≤ (μ_body x).toOuterMeasure {y | ¬cond.Holds y})
    (N : ℕ) {x : Data r} (hx : LoopStateInv cond I Q x) :
    loopActiveSteps cond μ_body N x ≤ if cond.Holds x then 1 / p_exit else 0 := by
  induction N generalizing x with
  | zero => simp [loopActiveSteps]
  | succ N ih =>
    rcases hx with ⟨hcx, hIx⟩ | ⟨hcx, _⟩
    · simp only [hcx, ↓reduceIte]
      rw [loopActiveSteps_succ_of_holds hcx]
      refine (add_le_add le_rfl (tsum_le_tsum fun z => ?_)).trans
        (pmf_step_drift_bound (μ_body x) cond hp_pos hp_top (hp_exit x hIx hcx))
      by_cases hz : z ∈ (μ_body x).support
      · exact mul_le_mul_right (ih (hinv x hIx hcx z hz)) _
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hz, zero_mul, zero_mul]
    · simp [loopActiveSteps_of_not_holds hcx, hcx]

theorem hasSum_loopExitDensity {cond : Cond r} {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x → ∀ y ∈ (μ_body x).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x → p_exit ≤ (μ_body x).toOuterMeasure {y | ¬cond.Holds y})
    {x : Data r} (hx : LoopStateInv cond I Q x) :
    HasSum (fun y => ⨆ K : ℕ,
      Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y) 1 := by
  rw [CompleteLattice.summable.hasSum_iff,
    ENNReal.tsum_iSup_of_monotone (loopIterPMF_indicator_mono cond μ_body x)]
  simp_rw [← PMF.toOuterMeasure_apply]
  set b := ⨆ K : ℕ, (loopIterPMF cond μ_body K x).toOuterMeasure {z | ¬cond.Holds z}
  have hb_le : b ≤ 1 := iSup_le fun K => Cslib.Probability.PMF.toOuterMeasure_le_one _ _
  have hsub_zero : 1 - b = 0 := by
    by_contra hne
    have hN_bound : ∀ N : ℕ, (N : ℝ≥0∞) * (1 - b) ≤ 1 / p_exit := by
      intro N
      have hterm : ∀ K : ℕ, 1 - b ≤
          (loopIterPMF cond μ_body K x).toOuterMeasure {z | cond.Holds z} := by
        intro K
        refine tsub_le_iff_left.mpr ?_
        rw [← pmf_toOuterMeasure_compl_add (loopIterPMF cond μ_body K x) cond]
        exact add_le_add
          (le_iSup (fun J => (loopIterPMF cond μ_body J x).toOuterMeasure {z | ¬cond.Holds z}) K)
          le_rfl
      calc
        (N : ℝ≥0∞) * (1 - b)
          = ∑ _K ∈ Finset.range N, (1 - b) := by simp
        _ ≤ ∑ K ∈ Finset.range N,
              (loopIterPMF cond μ_body K x).toOuterMeasure {z | cond.Holds z} :=
            Finset.sum_le_sum fun K _ => hterm K
        _ ≤ if cond.Holds x then 1 / p_exit else 0 :=
            loopActiveSteps_le hp_pos hp_top hinv hp_exit N hx
        _ ≤ 1 / p_exit := by split_ifs <;> simp
    have htop : (⊤ : ℝ≥0∞) ≤ 1 / p_exit := by
      rw [← ENNReal.top_mul hne, ← ENNReal.iSup_natCast, ENNReal.iSup_mul]
      exact iSup_le hN_bound
    exact ENNReal.div_ne_top ENNReal.one_ne_top hp_pos.ne' (top_le_iff.mp htop)
  exact le_antisymm hb_le (tsub_eq_zero_iff_le.mp hsub_zero)

/-- Limiting exit distribution of `Code.loop cond body` starting from `x` under one-step body
distribution family `μ_body`. -/
noncomputable def loopExitPMF (cond : Cond r) (μ_body : Data r → PMF (Data r)) (x : Data r) :
    PMF (Data r) :=
  open Classical in
  if h : HasSum (fun y => ⨆ K : ℕ,
      Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y) 1 then
    ⟨_, h⟩
  else
    PMF.pure x

theorem loopExitPMF_apply_of_hasSum {cond : Cond r} {μ_body : Data r → PMF (Data r)} {x : Data r}
    (h : HasSum (fun y => ⨆ K : ℕ,
      Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y) 1)
    (y : Data r) :
    loopExitPMF cond μ_body x y =
      ⨆ K : ℕ, Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y := by
  classical
  simp only [loopExitPMF, h, ↓reduceDIte]
  rfl

theorem loopExitPMF_of_not_holds {cond : Cond r} {μ_body : Data r → PMF (Data r)} {x : Data r}
    (hc : ¬cond.Holds x) :
    loopExitPMF cond μ_body x = PMF.pure x := by
  have hfun : (fun y => ⨆ K : ℕ,
      Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y) = PMF.pure x := by
    funext y
    have hK : ∀ K : ℕ,
        Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y = PMF.pure x y := by
      intro K
      rw [loopIterPMF_of_not_holds hc]
      by_cases hyx : y = x
      · subst hyx
        simp [hc]
      · simp [PMF.pure_apply, hyx]
    simp [hK]
  ext y
  rw [loopExitPMF_apply_of_hasSum (hfun ▸ (PMF.pure x).2), congrFun hfun y]

theorem loopExitPMF_of_holds {cond : Cond r} {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x → ∀ y ∈ (μ_body x).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x → p_exit ≤ (μ_body x).toOuterMeasure {y | ¬cond.Holds y})
    {x : Data r} (hIx : I x) (hcx : cond.Holds x) :
    loopExitPMF cond μ_body x = (μ_body x).bind (loopExitPMF cond μ_body) := by
  ext y
  have hx : LoopStateInv cond I Q x := Or.inl ⟨hcx, hIx⟩
  rw [loopExitPMF_apply_of_hasSum (hasSum_loopExitDensity hp_pos hp_top hinv hp_exit hx),
    PMF.bind_apply]
  have hzero : Set.indicator {z | ¬cond.Holds z} (PMF.pure x) y = 0 := by
    by_cases hy : ¬cond.Holds y
    · have hyx : y ≠ x := fun h => hy (h ▸ hcx)
      simp [hy, PMF.pure_apply, hyx]
    · simp [Set.indicator_of_notMem, hy]
  have hiSup_shift :
      (⨆ K : ℕ, Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y) =
        ⨆ K : ℕ, Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body (K + 1) x) y := by
    refine le_antisymm (iSup_le fun K => ?_) (iSup_le fun K =>
      le_iSup (fun J => Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body J x) y) (K + 1))
    cases K with
    | zero =>
      rw [loopIterPMF_zero, hzero]
      exact zero_le
    | succ K =>
      exact le_iSup
        (fun J => Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body (J + 1) x) y) K
  rw [hiSup_shift]
  have hstep : ∀ K : ℕ,
      Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body (K + 1) x) y =
        ∑' z, μ_body x z *
          Set.indicator {w' | ¬cond.Holds w'} (loopIterPMF cond μ_body K z) y := by
    intro K
    rw [loopIterPMF_succ, loopStepPMF_of_holds hcx]
    by_cases hy : ¬cond.Holds y
    · simp [Set.indicator_of_mem, hy, PMF.bind_apply]
    · simp [Set.indicator_of_notMem, hy]
  simp_rw [hstep]
  rw [← ENNReal.tsum_iSup_of_monotone
    (f := fun K z => μ_body x z *
      Set.indicator {w' | ¬cond.Holds w'} (loopIterPMF cond μ_body K z) y)
    (fun z _ _ hK => mul_le_mul_right (loopIterPMF_indicator_mono cond μ_body z y hK) _)]
  refine tsum_congr fun z => ?_
  by_cases hz : z ∈ (μ_body x).support
  · rw [← ENNReal.mul_iSup,
      loopExitPMF_apply_of_hasSum
        (hasSum_loopExitDensity hp_pos hp_top hinv hp_exit (hinv x hIx hcx z hz))]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr hz, zero_mul]
    simp

theorem mem_support_loopExitPMF {cond : Cond r} {I Q : Data r → Prop}
    {μ_body : Data r → PMF (Data r)} {p_exit : ℝ≥0∞}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hinv : ∀ x, I x → cond.Holds x → ∀ y ∈ (μ_body x).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ x, I x → cond.Holds x → p_exit ≤ (μ_body x).toOuterMeasure {y | ¬cond.Holds y})
    {x : Data r} (hx : LoopStateInv cond I Q x)
    {y : Data r} (hy : y ∈ (loopExitPMF cond μ_body x).support) :
    (¬cond.Holds y ∧ Q y) ∧ ∃ K, y ∈ (loopIterPMF cond μ_body K x).support := by
  rw [PMF.mem_support_iff,
    loopExitPMF_apply_of_hasSum (hasSum_loopExitDensity hp_pos hp_top hinv hp_exit hx)] at hy
  have ⟨K, hK⟩ : ∃ K : ℕ,
      Set.indicator {z | ¬cond.Holds z} (loopIterPMF cond μ_body K x) y ≠ 0 := by
    by_contra! h
    exact hy (by simp [h])
  have hnc : ¬cond.Holds y := by
    by_contra hc
    exact hK (by simp [Set.indicator_of_notMem, hc])
  rw [Set.indicator_of_mem hnc, ← PMF.mem_support_iff] at hK
  rcases loopIterPMF_support_inv hinv K hx y hK with ⟨hcy, _⟩ | ⟨_, hQy⟩
  · exact absurd hcy hnc
  · exact ⟨⟨hnc, hQy⟩, K, hK⟩

/-! ### Compositional distributional execution (`ExecCodeDist`) -/

/-- `ExecCodeDist w c x μ T`: at word size `w`, running structured program `c` from data `x`
terminates almost surely without faulting, realizes exit distribution `μ : PMF (Data r)` at the
fallthrough address `pc + c.size` of any containing flat program, and uses at most `T : ℝ≥0∞`
expected instructions.

Unlike `ExecRand`, which requires a finite-depth computation tree, `ExecCodeDist` includes
unbounded Las Vegas `while` loops whose each active iteration exits with probability bounded below
by `p_exit > 0` (`ExecCodeDist.loop_geometric`). -/
inductive ExecCodeDist {B : Basis} {r : ℕ} (w : ℕ) : Code B r → Data r → PMF (Data r) →
    ℝ≥0∞ → Prop where
  | of_execRand {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)} :
      ExecRand w c x m →
      ExecCodeDist w c x (Prod.fst <$> m).eval (ProbComp.expect m fun z => (z.2 : ℝ≥0∞))
  | mono {c : Code B r} {x : Data r} {μ : PMF (Data r)} {T T' : ℝ≥0∞} :
      ExecCodeDist w c x μ T → T ≤ T' → ExecCodeDist w c x μ T'
  | seq {c₁ c₂ : Code B r} {x : Data r} {μ₁ : PMF (Data r)}
      {μ₂ : Data r → PMF (Data r)} {T₁ : ℝ≥0∞} {T₂ : Data r → ℝ≥0∞} :
      ExecCodeDist w c₁ x μ₁ T₁ →
      (∀ y ∈ μ₁.support, ExecCodeDist w c₂ y (μ₂ y) (T₂ y)) →
      ExecCodeDist w (.seq c₁ c₂) x (μ₁.bind μ₂) (T₁ + ∑' y, μ₁ y * T₂ y)
  | branch_pos {cond : Cond r} {pos neg : Code B r} {x : Data r}
      {μ : PMF (Data r)} {T : ℝ≥0∞} :
      cond.Holds x → ExecCodeDist w pos x μ T →
      ExecCodeDist w (.branch cond pos neg) x μ (T + 1)
  | branch_neg {cond : Cond r} {pos neg : Code B r} {x : Data r}
      {μ : PMF (Data r)} {T : ℝ≥0∞} :
      ¬cond.Holds x → ExecCodeDist w neg x μ T →
      ExecCodeDist w (.branch cond pos neg) x μ (T + 2)
  | loop_geometric {cond : Cond r} {body : Code B r}
      (I Q : Data r → Prop) {μ_body : Data r → PMF (Data r)} {T_body : Data r → ℝ≥0∞}
      {B_body p_exit : ℝ≥0∞} {x : Data r} :
      0 < p_exit → p_exit ≠ ⊤ →
      (∀ z, I z → cond.Holds z → ExecCodeDist w body z (μ_body z) (T_body z)) →
      (∀ z, I z → cond.Holds z → T_body z ≤ B_body) →
      (∀ z, I z → cond.Holds z →
        ∀ y ∈ (μ_body z).support, LoopStateInv cond I Q y) →
      (∀ z, I z → cond.Holds z →
        p_exit ≤ (μ_body z).toOuterMeasure {y | ¬cond.Holds y}) →
      LoopStateInv cond I Q x →
      ExecCodeDist w (.loop cond body) x (loopExitPMF cond μ_body x)
        ((B_body + 2) / p_exit + 2)

namespace ExecCodeDist

variable {w : ℕ} {c c₁ c₂ pos neg body : Code B r} {cond : Cond r} {x y : Data r}
  {μ μ₁ μ' : PMF (Data r)} {T T' T₁ T₂ : ℝ≥0∞}

theorem congr_dist (h : ExecCodeDist w c x μ T) (hμ : μ = μ') (hT : T ≤ T') :
    ExecCodeDist w c x μ' T' := by
  subst hμ
  exact h.mono hT

/-- Every deterministic `Exec w c x y n` gives `ExecCodeDist w c x (PMF.pure y) n`. -/
theorem of_exec {n : ℕ} (h : Exec w c x y n) :
    ExecCodeDist w c x (PMF.pure y) n := by
  simpa [ProbComp.expect_pure] using of_execRand h.execRand

/-- Every deterministic `ExecWithin w c x y n` gives `ExecCodeDist w c x (PMF.pure y) n`. -/
theorem of_execWithin {n : ℕ} (h : ExecWithin w c x y n) :
    ExecCodeDist w c x (PMF.pure y) n := by
  obtain ⟨m, hm, he⟩ := h
  exact (of_exec he).mono (Nat.cast_le.mpr hm)

/-- Single deterministic operation instruction. -/
theorem op {o : Op B r} (ho : o.eval w x = some y) :
    ExecCodeDist w (.op o) x (PMF.pure y) 1 := by
  simpa using of_exec (Exec.op ho)

/-- Single `rand dst src` instruction. -/
theorem rand {dst src : Fin r} (hfit : Fits w (x.regs src)) :
    ExecCodeDist (B := B) w (.rand dst src) x
      ((ProbComp.unifFin (x.regs src)).eval.map fun k => x.set dst k.val) 1 := by
  have h := of_execRand (ExecRand.rand (B := B) (dst := dst) (src := src) hfit)
  refine h.congr_dist ?_ ?_
  · ext z
    simp [ProbComp.eval_map, PMF.map_apply]
  · simp [ProbComp.expect_map, ProbComp.expect_const]

/-- Exiting a loop immediately when `¬cond.Holds x` takes `2` steps and leaves `x` unchanged. -/
theorem loop_exit (hc : ¬cond.Holds x) :
    ExecCodeDist w (.loop cond body) x (PMF.pure x) 2 := by
  simpa using of_exec (Exec.loop_exit hc)

/-- Sequencing with a uniform continuation step bound `T₂`. -/
theorem seq_const {μ₂ : Data r → PMF (Data r)} {T₂ : Data r → ℝ≥0∞} {B₂ : ℝ≥0∞}
    (h₁ : ExecCodeDist w c₁ x μ₁ T₁)
    (h₂ : ∀ y ∈ μ₁.support, ExecCodeDist w c₂ y (μ₂ y) (T₂ y))
    (hB₂ : ∀ y ∈ μ₁.support, T₂ y ≤ B₂) :
    ExecCodeDist w (.seq c₁ c₂) x (μ₁.bind μ₂) (T₁ + B₂) := by
  refine (h₁.seq h₂).mono (add_le_add le_rfl ?_)
  calc
    (∑' y, μ₁ y * T₂ y)
      ≤ ∑' y, μ₁ y * B₂ := by
        refine tsum_le_tsum fun y => ?_
        by_cases hy : y ∈ μ₁.support
        · exact mul_le_mul_right (hB₂ y hy) _
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hy, zero_mul, zero_mul]
    _ = B₂ := by rw [ENNReal.tsum_mul_right, μ₁.tsum_coe, one_mul]

/-- Sequencing after a deterministic first stage (`PMF.pure y`). -/
theorem seq_pure (h₁ : ExecCodeDist w c₁ x (PMF.pure y) T₁)
    (h₂ : ExecCodeDist w c₂ y μ T₂) :
    ExecCodeDist w (.seq c₁ c₂) x μ (T₁ + T₂) := by
  classical
  have h := h₁.seq (c₂ := c₂) (μ₂ := fun z => if z = y then μ else PMF.pure z)
    (T₂ := fun z => if z = y then T₂ else 0) fun z hz => by
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simpa only [↓reduceIte] using h₂
  refine h.congr_dist ?_ ?_
  · simp
  · rw [tsum_eq_single y]
    · simp
    · intro z hz
      simp [PMF.pure_apply, hz]

/-- Every state in the support of `μ` preserves `Data.Bounded w` when `x.Bounded w`. -/
theorem bounded (h : ExecCodeDist w c x μ T) (hx : x.Bounded w) :
    ∀ y ∈ μ.support, y.Bounded w := by
  induction h with
  | @of_execRand c x m hm =>
    intro y hy
    rw [ProbComp.eval_map, PMF.mem_support_map_iff] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [ProbComp.support_eval] at hz
    exact hm.bounded hx hz
  | mono _ _ ih => exact ih hx
  | seq _ _ ih₁ ih₂ =>
    intro y hy
    rw [PMF.mem_support_bind_iff] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    exact ih₂ z hz (ih₁ hx z hz) y hyz
  | branch_pos _ _ ih => exact ih hx
  | branch_neg _ _ ih => exact ih hx
  | @loop_geometric cond body I Q μ_body T_body B_body p_exit x
      hp_pos hp_top _ _ hinv hp_exit hx_inv ih_body =>
    intro y hy
    obtain ⟨_, K, hK⟩ := mem_support_loopExitPMF hp_pos hp_top hinv hp_exit hx_inv hy
    have hK_bdd : ∀ K : ℕ, ∀ x₀ : Data r, LoopStateInv cond I Q x₀ → x₀.Bounded w →
        ∀ z ∈ (loopIterPMF cond μ_body K x₀).support, z.Bounded w := by
      intro K
      induction K with
      | zero =>
        intro x₀ _ hx₀ z hz
        rw [loopIterPMF_zero, PMF.support_pure, Set.mem_singleton_iff] at hz
        rwa [hz]
      | succ K ihK =>
        intro x₀ hx₀_inv hx₀ z hz
        rw [loopIterPMF_succ, PMF.mem_support_bind_iff] at hz
        obtain ⟨u, hu, hzu⟩ := hz
        rcases hx₀_inv with ⟨hcx₀, hIx₀⟩ | ⟨hcx₀, hQx₀⟩
        · rw [loopStepPMF_of_holds hcx₀] at hu
          exact ihK u (hinv x₀ hIx₀ hcx₀ u hu) (ih_body x₀ hIx₀ hcx₀ hx₀ u hu) z hzu
        · rw [loopStepPMF_of_not_holds hcx₀, PMF.support_pure, Set.mem_singleton_iff] at hu
          rw [hu] at hzu
          exact ihK x₀ (Or.inr ⟨hcx₀, hQx₀⟩) hx₀ z hzu
    exact hK_bdd K x hx_inv hx y hK

/-- Any register `i` not written by `c` (`c.Preserves i`) is preserved across the support of `μ`. -/
theorem regs_eq {i : Fin r} (h : ExecCodeDist w c x μ T) (hi : c.Preserves i) :
    ∀ y ∈ μ.support, y.regs i = x.regs i := by
  induction h with
  | @of_execRand c x m hm =>
    intro y hy
    rw [ProbComp.eval_map, PMF.mem_support_map_iff] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [ProbComp.support_eval] at hz
    exact hm.regs_eq hi hz
  | mono _ _ ih => exact ih hi
  | seq _ _ ih₁ ih₂ =>
    intro y hy
    rw [PMF.mem_support_bind_iff] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    exact (ih₂ z hz hi.2 y hyz).trans (ih₁ hi.1 z hz)
  | branch_pos _ _ ih => exact ih hi.1
  | branch_neg _ _ ih => exact ih hi.2
  | @loop_geometric cond body I Q μ_body T_body B_body p_exit x
      hp_pos hp_top _ _ hinv hp_exit hx_inv ih_body =>
    intro y hy
    obtain ⟨_, K, hK⟩ := mem_support_loopExitPMF hp_pos hp_top hinv hp_exit hx_inv hy
    have hK_eq : ∀ K : ℕ, ∀ x₀ : Data r, LoopStateInv cond I Q x₀ →
        ∀ z ∈ (loopIterPMF cond μ_body K x₀).support, z.regs i = x₀.regs i := by
      intro K
      induction K with
      | zero =>
        intro x₀ _ z hz
        rw [loopIterPMF_zero, PMF.support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
      | succ K ihK =>
        intro x₀ hx₀_inv z hz
        rw [loopIterPMF_succ, PMF.mem_support_bind_iff] at hz
        obtain ⟨u, hu, hzu⟩ := hz
        rcases hx₀_inv with ⟨hcx₀, hIx₀⟩ | ⟨hcx₀, hQx₀⟩
        · rw [loopStepPMF_of_holds hcx₀] at hu
          exact (ihK u (hinv x₀ hIx₀ hcx₀ u hu) z hzu).trans (ih_body x₀ hIx₀ hcx₀ hi u hu)
        · rw [loopStepPMF_of_not_holds hcx₀, PMF.support_pure, Set.mem_singleton_iff] at hu
          rw [hu] at hzu
          exact ihK x₀ (Or.inr ⟨hcx₀, hQx₀⟩) z hzu
    exact hK_eq K x hx_inv y hK

/-- Distributional executions transfer along any defined-evaluation basis simulation
`ψ : B.Simulates B'`. -/
theorem mapSimulates {B' : Basis} (ψ : B.Simulates B') (h : ExecCodeDist w c x μ T) :
    ExecCodeDist w (c.mapSimulates ψ) x μ T := by
  induction h with
  | of_execRand hm => exact of_execRand (hm.mapSimulates ψ)
  | mono _ hle ih => exact ih.mono hle
  | seq _ _ ih₁ ih₂ => exact ih₁.seq ih₂
  | branch_pos hc _ ih => exact branch_pos hc ih
  | branch_neg hc _ ih => exact branch_neg hc ih
  | loop_geometric I Q hp_pos hp_top _ hB hinv hp_exit hx ih_body =>
    exact loop_geometric I Q hp_pos hp_top ih_body hB hinv hp_exit hx

private theorem extend_left_injective {r' : ℕ} {f : Fin r → Fin r'} (hf : f.Injective)
    (x : Data r') : Function.Injective (fun y : Data r => y.extend f x) := by
  intro y₁ y₂ h
  have h' := congrArg (Data.comap f) h
  simpa [Data.comap_extend hf] using h'

private theorem pmf_map_apply_injective {α β : Type*} (p : PMF α) {g : α → β}
    (hg : g.Injective) (a : α) :
    p.map g (g a) = p a := by
  rw [PMF.map_apply, tsum_eq_single a]
  · simp
  · intro a' ha'
    have hne : g a ≠ g a' := hg.ne ha'.symm
    simp [hne]

private theorem pmf_map_apply_not_mem_range {α β : Type*} (p : PMF α) (g : α → β) {b : β}
    (hb : b ∉ Set.range g) :
    p.map g b = 0 := by
  rw [PMF.map_apply, tsum_eq_zero_iff]
  intro a
  have hne : b ≠ g a := fun h => hb ⟨a, h.symm⟩
  simp [hne]

private theorem loopIterPMF_rename {r' : ℕ} {f : Fin r → Fin r'} (hf : f.Injective)
    (cond : Cond r) (μ_body : Data r → PMF (Data r)) (x : Data r') (K : ℕ) (u : Data r) :
    loopIterPMF (cond.rename f) (fun x' => (μ_body (x'.comap f)).map (fun y => y.extend f x))
      K (u.extend f x) =
      (loopIterPMF cond μ_body K u).map (fun y => y.extend f x) := by
  induction K generalizing u with
  | zero => simp [loopIterPMF]
  | succ K ih =>
    rw [loopIterPMF_succ, loopIterPMF_succ]
    by_cases hc : cond.Holds u
    · have hc' : (cond.rename f).Holds (u.extend f x) := by
        rw [Cond.holds_rename, Data.comap_extend hf]
        exact hc
      rw [loopStepPMF_of_holds hc', loopStepPMF_of_holds hc, Data.comap_extend hf,
        PMF.bind_map, PMF.map_bind]
      refine congrArg ((μ_body u).bind ·) (funext fun z => ih z)
    · have hc' : ¬(cond.rename f).Holds (u.extend f x) := by
        rw [Cond.holds_rename, Data.comap_extend hf]
        exact hc
      rw [loopStepPMF_of_not_holds hc', loopStepPMF_of_not_holds hc, PMF.pure_bind,
        PMF.pure_bind, ih]

/-- Renaming a distributional execution along an injective register map `f : Fin r → Fin r'`
transforms the output distribution via `Data.extend f x` and preserves the expected step bound. -/
theorem rename {r' : ℕ} {f : Fin r → Fin r'} (hf : f.Injective) {x : Data r'}
    (h : ExecCodeDist w c (x.comap f) μ T) :
    ExecCodeDist w (c.rename f) x (μ.map fun y => y.extend f x) T := by
  generalize hx₀ : x.comap f = x₀ at h
  induction h generalizing x with
  | @of_execRand c _ m hm =>
    subst hx₀
    have hm' := of_execRand (hm.rename hf)
    refine hm'.congr_dist ?_ ?_
    · rw [Functor.map_map, ProbComp.eval_map, ProbComp.eval_map, PMF.map_comp]
      rfl
    · rw [ProbComp.expect_map]
  | mono _ hle ih =>
    exact (ih hx₀).mono hle
  | @seq c₁ c₂ _ μ₁ μ₂ T₁ T₂ _ _ ih₁ ih₂ =>
    subst hx₀
    have h₁' := ih₁ rfl
    have hseq := h₁'.seq
      (μ₂ := fun y' => (μ₂ (y'.comap f)).map fun z => z.extend f x)
      (T₂ := fun y' => T₂ (y'.comap f))
      fun y' hy' => by
        rw [PMF.mem_support_map_iff] at hy'
        obtain ⟨y₁, hy₁, rfl⟩ := hy'
        have h₂' := ih₂ y₁ hy₁ (x := y₁.extend f x) (Data.comap_extend hf y₁ x)
        simpa only [Data.comap_extend hf, Data.extend_extend hf] using h₂'
    refine hseq.congr_dist ?_ ?_
    · rw [PMF.map_bind, PMF.bind_map]
      refine congrArg (μ₁.bind ·) (funext fun y₁ => ?_)
      simp [Data.comap_extend hf]
    · refine add_le_add le_rfl ?_
      rw [Cslib.Probability.PMF.tsum_map_mul]
      simp [Data.comap_extend hf]
  | branch_pos hc _ ih =>
    subst hx₀
    exact branch_pos ((Cond.holds_rename _ _).2 hc) (ih rfl)
  | branch_neg hc _ ih =>
    subst hx₀
    exact branch_neg (fun h => hc ((Cond.holds_rename _ _).1 h)) (ih rfl)
  | @loop_geometric cond body I Q μ_body T_body B_body p_exit _
      hp_pos hp_top _ hB hinv hp_exit hx_inv ih_body =>
    subst hx₀
    let g : Data r → Data r' := fun y => y.extend f x
    have hg : g.Injective := extend_left_injective hf x
    let I' : Data r' → Prop := fun x' => ∃ u, I u ∧ x' = g u
    let Q' : Data r' → Prop := fun x' => ∃ u, Q u ∧ x' = g u
    let μ_body' : Data r' → PMF (Data r') := fun x' => (μ_body (x'.comap f)).map g
    let T_body' : Data r' → ℝ≥0∞ := fun x' => T_body (x'.comap f)
    have hinv' : ∀ z', I' z' → (cond.rename f).Holds z' →
        ∀ y' ∈ (μ_body' z').support, LoopStateInv (cond.rename f) I' Q' y' := by
      rintro z' ⟨u, hIu, rfl⟩ hcz' y' hy'
      have hcu : cond.Holds u := by
        simpa [g, Cond.holds_rename, Data.comap_extend hf] using hcz'
      simp only [μ_body', g, Data.comap_extend hf, PMF.mem_support_map_iff] at hy'
      obtain ⟨y, hy, rfl⟩ := hy'
      rcases hinv u hIu hcu y hy with ⟨hcy, hIy⟩ | ⟨hcy, hQy⟩
      · exact Or.inl ⟨by simpa [g, Cond.holds_rename, Data.comap_extend hf] using hcy,
          ⟨y, hIy, rfl⟩⟩
      · exact Or.inr ⟨by simpa [g, Cond.holds_rename, Data.comap_extend hf] using hcy,
          ⟨y, hQy, rfl⟩⟩
    have hp_exit' : ∀ z', I' z' → (cond.rename f).Holds z' →
        p_exit ≤ (μ_body' z').toOuterMeasure {y' | ¬(cond.rename f).Holds y'} := by
      rintro z' ⟨u, hIu, rfl⟩ hcz'
      have hcu : cond.Holds u := by
        simpa [g, Cond.holds_rename, Data.comap_extend hf] using hcz'
      simp only [μ_body', g, Data.comap_extend hf, PMF.toOuterMeasure_map_apply]
      have hset : ((fun y : Data r => y.extend f x) ⁻¹' {y' | ¬(cond.rename f).Holds y'}) =
          {y | ¬cond.Holds y} := by
        ext y
        simp [Cond.holds_rename, Data.comap_extend hf]
      rw [hset]
      exact hp_exit u hIu hcu
    have hx_inv' : LoopStateInv (cond.rename f) I' Q' x := by
      rcases hx_inv with ⟨hcx, hIx⟩ | ⟨hcx, hQx⟩
      · exact Or.inl ⟨(Cond.holds_rename _ _).2 hcx,
          ⟨x.comap f, hIx, (Data.extend_comap hf x).symm⟩⟩
      · exact Or.inr ⟨fun h => hcx ((Cond.holds_rename _ _).1 h),
          ⟨x.comap f, hQx, (Data.extend_comap hf x).symm⟩⟩
    have hloop := loop_geometric (cond := cond.rename f) (body := body.rename f)
      I' Q' hp_pos hp_top
      (μ_body := μ_body') (T_body := T_body') (B_body := B_body) (x := x)
      (fun z' ⟨u, hIu, hzu⟩ hcz' => by
        subst hzu
        have hcu : cond.Holds u := by
          simpa [g, Cond.holds_rename, Data.comap_extend hf] using hcz'
        have hb' := ih_body u hIu hcu (x := g u) (Data.comap_extend hf u x)
        simpa only [μ_body', T_body', g, Data.comap_extend hf, Data.extend_extend hf] using hb')
      (fun z' ⟨u, hIu, hzu⟩ hcz' => by
        subst hzu
        have hcu : cond.Holds u := by
          simpa [g, Cond.holds_rename, Data.comap_extend hf] using hcz'
        simpa only [T_body', g, Data.comap_extend hf] using hB u hIu hcu)
      hinv' hp_exit' hx_inv'
    refine hloop.congr_dist ?_ le_rfl
    ext y'
    rw [loopExitPMF_apply_of_hasSum (hasSum_loopExitDensity hp_pos hp_top hinv' hp_exit' hx_inv')]
    have hx_eq : x = g (x.comap f) := (Data.extend_comap hf x).symm
    by_cases hy' : y' ∈ Set.range g
    · obtain ⟨y, rfl⟩ := hy'
      rw [pmf_map_apply_injective _ hg,
        loopExitPMF_apply_of_hasSum (hasSum_loopExitDensity hp_pos hp_top hinv hp_exit hx_inv)]
      refine iSup_congr fun K => ?_
      have hiter : loopIterPMF (cond.rename f) μ_body' K x =
          (loopIterPMF cond μ_body K (x.comap f)).map g := by
        conv_lhs => rw [hx_eq]
        exact loopIterPMF_rename hf cond μ_body x K (x.comap f)
      rw [hiter]
      by_cases hcy : ¬cond.Holds y
      · have hcy' : ¬(cond.rename f).Holds (g y) := by
          simpa [g, Cond.holds_rename, Data.comap_extend hf] using hcy
        simp [Set.indicator_of_mem, hcy, hcy', pmf_map_apply_injective _ hg]
      · have hcy' : ¬¬(cond.rename f).Holds (g y) := by
          simpa [g, Cond.holds_rename, Data.comap_extend hf] using hcy
        simp [Set.indicator_of_notMem, hcy, hcy']
    · rw [pmf_map_apply_not_mem_range _ g hy']
      refine le_antisymm (iSup_le fun K => ?_) zero_le
      have hiter : loopIterPMF (cond.rename f) μ_body' K x =
          (loopIterPMF cond μ_body K (x.comap f)).map g := by
        conv_lhs => rw [hx_eq]
        exact loopIterPMF_rename hf cond μ_body x K (x.comap f)
      rw [hiter]
      by_cases hcy' : ¬(cond.rename f).Holds y'
      · simp [Set.indicator_of_mem, hcy', pmf_map_apply_not_mem_range _ g hy']
      · simp [Set.indicator_of_notMem, hcy']

/-! ### Compilation of `ExecCodeDist` to flat `Program` semantics -/

/-- Finite-horizon Bellman inequality for `ExecCodeDist` inside any containing flat program `p`. -/
theorem expectedStepsWithin_assemble (h : ExecCodeDist w c x μ T) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) (N : ℕ) :
    expectedStepsWithin w p N (.running ⟨pc, x⟩) ≤
      T + ∑' y, μ y * expectedStepsWithin w p N (.running ⟨pc + c.size, y⟩) := by
  induction h generalizing pc N with
  | @of_execRand c x m hm =>
    refine (hm.expectedStepsWithin_assemble hp N).trans (le_of_eq ?_)
    rw [ProbComp.expect_add,
      ← ProbComp.expect_map Prod.fst m (fun y =>
        expectedStepsWithin w p N (.running ⟨pc + c.size, y⟩))]
    rfl
  | mono _ hle ih =>
    exact (ih hp N).trans (add_le_add hle le_rfl)
  | @seq c₁ c₂ x μ₁ μ₂ T₁ T₂ _ _ ih₁ ih₂ =>
    have hc₂ : p.Contains (pc + c₁.size) (c₂.assemble (pc + c₁.size)) := by
      simpa [Code.length_assemble] using hp.append_right
    refine (ih₁ hp.append_left N).trans ?_
    have hstep : (∑' y, μ₁ y * expectedStepsWithin w p N (.running ⟨pc + c₁.size, y⟩)) ≤
        (∑' y, μ₁ y * T₂ y) +
          ∑' z, (μ₁.bind μ₂) z *
            expectedStepsWithin w p N (.running ⟨pc + (c₁.seq c₂).size, z⟩) := by
      calc
        (∑' y, μ₁ y * expectedStepsWithin w p N (.running ⟨pc + c₁.size, y⟩))
          ≤ ∑' y, μ₁ y * (T₂ y +
              ∑' z, (μ₂ y) z *
                expectedStepsWithin w p N (.running ⟨pc + c₁.size + c₂.size, z⟩)) := by
            refine tsum_le_tsum fun y => ?_
            by_cases hy : y ∈ μ₁.support
            · exact mul_le_mul_right (ih₂ y hy hc₂ N) _
            · rw [(PMF.apply_eq_zero_iff _ _).mpr hy, zero_mul, zero_mul]
        _ = (∑' y, μ₁ y * T₂ y) +
              ∑' y, μ₁ y * ∑' z, (μ₂ y) z *
                expectedStepsWithin w p N (.running ⟨pc + c₁.size + c₂.size, z⟩) := by
            simp_rw [mul_add, tsum_add]
        _ = (∑' y, μ₁ y * T₂ y) +
              ∑' z, (μ₁.bind μ₂) z *
                expectedStepsWithin w p N (.running ⟨pc + (c₁.seq c₂).size, z⟩) := by
            congr 1
            simp only [Code.size, Nat.add_assoc]
            exact (Cslib.Probability.PMF.tsum_bind_mul μ₁ μ₂ _).symm
    calc
      T₁ + ∑' y, μ₁ y * expectedStepsWithin w p N (.running ⟨pc + c₁.size, y⟩)
        ≤ T₁ + ((∑' y, μ₁ y * T₂ y) +
            ∑' z, (μ₁.bind μ₂) z *
              expectedStepsWithin w p N (.running ⟨pc + (c₁.seq c₂).size, z⟩)) :=
          add_le_add le_rfl hstep
      _ = (T₁ + ∑' y, μ₁ y * T₂ y) +
            ∑' z, (μ₁.bind μ₂) z *
              expectedStepsWithin w p N (.running ⟨pc + (c₁.seq c₂).size, z⟩) := by
          rw [add_assoc]
  | @branch_pos cond pos neg x μ T hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
    rw [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'
    refine (expectedStepsWithin_running_le w p N ⟨pc, x⟩).trans ?_
    rw [stepRand_branch (s := ⟨pc, x⟩) hbr]
    simp only [hc, ↓reduceIte, ProbComp.expect_pure]
    refine (add_le_add le_rfl (ih hc' N)).trans (le_of_eq ?_)
    simp only [Code.size,
      show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
    ac_rfl
  | @branch_neg cond pos neg x μ T hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hj : p[pc + 1 + neg.size]? = some (.jump (pc + neg.size + pos.size + 2)) := by
      simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head
    refine (expectedStepsWithin_running_le w p N ⟨pc, x⟩).trans ?_
    rw [stepRand_branch (s := ⟨pc, x⟩) hbr]
    simp only [hc, ↓reduceIte, ProbComp.expect_pure]
    refine (add_le_add le_rfl (ih hp.cons_tail.append_left N)).trans ?_
    have hjump : (∑' y, μ y * expectedStepsWithin w p N (.running ⟨pc + 1 + neg.size, y⟩)) ≤
        1 + ∑' y, μ y *
          expectedStepsWithin w p N (.running ⟨pc + (neg.size + pos.size + 2), y⟩) := by
      calc
        (∑' y, μ y * expectedStepsWithin w p N (.running ⟨pc + 1 + neg.size, y⟩))
          ≤ ∑' y, μ y * (1 +
              expectedStepsWithin w p N (.running ⟨pc + (neg.size + pos.size + 2), y⟩)) := by
            refine tsum_le_tsum fun y => mul_le_mul_right ?_ _
            refine (expectedStepsWithin_running_le w p N ⟨pc + 1 + neg.size, y⟩).trans (le_of_eq ?_)
            rw [stepRand_jump (s := ⟨pc + 1 + neg.size, y⟩) hj, ProbComp.expect_pure,
              show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
        _ = 1 + ∑' y, μ y *
              expectedStepsWithin w p N (.running ⟨pc + (neg.size + pos.size + 2), y⟩) := by
            simp_rw [mul_add, tsum_add, mul_one, μ.tsum_coe]
    calc
      1 + (T + ∑' y, μ y * expectedStepsWithin w p N (.running ⟨pc + 1 + neg.size, y⟩))
        ≤ 1 + (T + (1 + ∑' y, μ y *
            expectedStepsWithin w p N (.running ⟨pc + (neg.size + pos.size + 2), y⟩))) :=
          add_le_add le_rfl (add_le_add le_rfl hjump)
      _ = (T + (1 + 1)) + ∑' y, μ y *
            expectedStepsWithin w p N (.running ⟨pc + (Code.branch cond pos neg).size, y⟩) := by
          simp only [Code.size]
          ac_rfl
      _ = (T + 2) + ∑' y, μ y *
            expectedStepsWithin w p N (.running ⟨pc + (Code.branch cond pos neg).size, y⟩) := by
          rw [one_add_one_eq_two]
  | @loop_geometric cond body I Q μ_body T_body B_body p_exit x
      hp_pos hp_top _ hB hinv hp_exit hx_inv ih_body =>
    have hj_exit : p[pc + 1]? = some (.jump (pc + body.size + 3)) := hp.cons_tail.head
    have hbody_contains : p.Contains (pc + 2) (body.assemble (pc + 2)) := by
      simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left
    have hj_back : p[pc + 2 + body.size]? = some (.jump pc) := by
      simpa using hp.cons_tail.cons_tail.append_right.head
    set K_cont : Data r → ℝ≥0∞ := fun y =>
      expectedStepsWithin w p N (.running ⟨pc + (Code.loop cond body).size, y⟩)
    set M := (B_body + 2) / p_exit
    have hmain : ∀ n ≤ N, ∀ z : Data r, LoopStateInv cond I Q z →
        expectedStepsWithin w p n (.running ⟨pc, z⟩) ≤
          (if cond.Holds z then M else 0) + 2 +
            ∑' y, loopExitPMF cond μ_body z y * K_cont y := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn =>
        intro hn z hz_inv
        rcases hz_inv with ⟨hcz, hIz⟩ | ⟨hcz, _⟩
        · simp only [hcz, ↓reduceIte]
          rw [expectedStepsWithin_running_succ, stepRand_branch (s := ⟨pc, z⟩) hp.head]
          simp only [hcz, ↓reduceIte, ProbComp.expect_pure]
          have hbody_step := (ih_body z hIz hcz hbody_contains n).trans
            (add_le_add (hB z hIz hcz) le_rfl)
          have hback_step :
              (∑' u, μ_body z u * expectedStepsWithin w p n (.running ⟨pc + 2 + body.size, u⟩)) ≤
                1 + ∑' u, μ_body z u * expectedStepsWithin w p n (.running ⟨pc, u⟩) := by
            calc
              (∑' u, μ_body z u * expectedStepsWithin w p n (.running ⟨pc + 2 + body.size, u⟩))
                ≤ ∑' u, μ_body z u * (1 + expectedStepsWithin w p n (.running ⟨pc, u⟩)) := by
                  refine tsum_le_tsum fun u => mul_le_mul_right ?_ _
                  refine (expectedStepsWithin_running_le w p n ⟨pc + 2 + body.size, u⟩).trans
                    (le_of_eq ?_)
                  rw [stepRand_jump (s := ⟨pc + 2 + body.size, u⟩) hj_back, ProbComp.expect_pure]
              _ = 1 + ∑' u, μ_body z u * expectedStepsWithin w p n (.running ⟨pc, u⟩) := by
                  simp_rw [mul_add, tsum_add, mul_one, (μ_body z).tsum_coe]
          have hbind_k :
              (∑' u, μ_body z u * ∑' y, loopExitPMF cond μ_body u y * K_cont y) =
                ∑' y, loopExitPMF cond μ_body z y * K_cont y := by
            rw [loopExitPMF_of_holds hp_pos hp_top hinv hp_exit hIz hcz]
            exact (Cslib.Probability.PMF.tsum_bind_mul (μ_body z)
              (loopExitPMF cond μ_body) K_cont).symm
          have hih_step :
              (∑' u, μ_body z u * expectedStepsWithin w p n (.running ⟨pc, u⟩)) ≤
                (∑' u, μ_body z u * (if cond.Holds u then M else 0)) + 2 +
                  ∑' y, loopExitPMF cond μ_body z y * K_cont y := by
            calc
              (∑' u, μ_body z u * expectedStepsWithin w p n (.running ⟨pc, u⟩))
                ≤ ∑' u, μ_body z u * ((if cond.Holds u then M else 0) + 2 +
                    ∑' y, loopExitPMF cond μ_body u y * K_cont y) := by
                  refine tsum_le_tsum fun u => ?_
                  by_cases hu : u ∈ (μ_body z).support
                  · exact mul_le_mul_right
                      (ihn (Nat.le_of_succ_le hn) u (hinv z hIz hcz u hu)) _
                  · rw [(PMF.apply_eq_zero_iff _ _).mpr hu, zero_mul, zero_mul]
              _ = (∑' u, μ_body z u * (if cond.Holds u then M else 0)) + 2 +
                    ∑' u, μ_body z u * ∑' y, loopExitPMF cond μ_body u y * K_cont y := by
                  simp_rw [mul_add, tsum_add, ENNReal.tsum_mul_right, (μ_body z).tsum_coe,
                    one_mul]
              _ = (∑' u, μ_body z u * (if cond.Holds u then M else 0)) + 2 +
                    ∑' y, loopExitPMF cond μ_body z y * K_cont y := by
                  rw [hbind_k]
          have hdrift := pmf_step_drift_bound (μ_body z) cond (C := B_body + 2)
            hp_pos hp_top (hp_exit z hIz hcz)
          calc
            1 + expectedStepsWithin w p n (.running ⟨pc + 2, z⟩)
              ≤ 1 + (B_body + (1 + ∑' u, μ_body z u *
                  expectedStepsWithin w p n (.running ⟨pc, u⟩))) :=
                add_le_add le_rfl (hbody_step.trans (add_le_add le_rfl hback_step))
            _ = (B_body + (1 + 1)) + ∑' u, μ_body z u *
                  expectedStepsWithin w p n (.running ⟨pc, u⟩) := by ac_rfl
            _ = (B_body + 2) + ∑' u, μ_body z u *
                  expectedStepsWithin w p n (.running ⟨pc, u⟩) := by rw [one_add_one_eq_two]
            _ ≤ (B_body + 2) + ((∑' u, μ_body z u * (if cond.Holds u then M else 0)) + 2 +
                  ∑' y, loopExitPMF cond μ_body z y * K_cont y) :=
                add_le_add le_rfl hih_step
            _ = ((B_body + 2) + ∑' u, μ_body z u * (if cond.Holds u then M else 0)) + 2 +
                  ∑' y, loopExitPMF cond μ_body z y * K_cont y := by ac_rfl
            _ ≤ M + 2 + ∑' y, loopExitPMF cond μ_body z y * K_cont y :=
                add_le_add (add_le_add hdrift le_rfl) le_rfl
        · simp only [hcz, ↓reduceIte, zero_add]
          rw [loopExitPMF_of_not_holds hcz, tsum_eq_single z
            (fun y hy => by simp [PMF.pure_apply, hy])]
          simp only [PMF.pure_apply_self, one_mul]
          rw [expectedStepsWithin_running_succ, stepRand_branch (s := ⟨pc, z⟩) hp.head]
          simp only [hcz, ↓reduceIte, ProbComp.expect_pure]
          refine (add_le_add le_rfl (expectedStepsWithin_running_le w p n ⟨pc + 1, z⟩)).trans ?_
          rw [stepRand_jump (s := ⟨pc + 1, z⟩) hj_exit, ProbComp.expect_pure, ← add_assoc,
            one_add_one_eq_two]
          refine add_le_add le_rfl ?_
          simpa [K_cont, Code.size, show pc + body.size + 3 = pc + (body.size + 3) by omega]
            using expectedStepsWithin_mono w p
              (.running ⟨pc + (body.size + 3), z⟩) (Nat.le_of_succ_le hn)
    refine (hmain N le_rfl x hx_inv).trans ?_
    refine add_le_add (add_le_add ?_ le_rfl) le_rfl
    split_ifs <;> simp

/-- Full-horizon Bellman inequality for `ExecCodeDist` inside any containing flat program `p`. -/
theorem expectedStepsFrom_assemble (h : ExecCodeDist w c x μ T) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) :
    expectedStepsFrom w p (.running ⟨pc, x⟩) ≤
      T + ∑' y, μ y * expectedStepsFrom w p (.running ⟨pc + c.size, y⟩) := by
  rw [← iSup_expectedStepsWithin w p (.running ⟨pc, x⟩)]
  refine iSup_le fun N => (h.expectedStepsWithin_assemble hp N).trans ?_
  refine add_le_add le_rfl (tsum_le_tsum fun y => mul_le_mul_right ?_ _)
  exact expectedStepsWithin_le_expectedStepsFrom w p N (.running ⟨pc + c.size, y⟩)

/-- Continuation upper-bound form of `expectedStepsFrom_assemble`. -/
theorem expectedStepsFrom_le (h : ExecCodeDist w c x μ T) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) {k : Data r → ℝ≥0∞}
    (hk : ∀ y ∈ μ.support, expectedStepsFrom w p (.running ⟨pc + c.size, y⟩) ≤ k y) :
    expectedStepsFrom w p (.running ⟨pc, x⟩) ≤ T + ∑' y, μ y * k y := by
  refine (h.expectedStepsFrom_assemble hp).trans
    (add_le_add le_rfl (tsum_le_tsum fun y => ?_))
  by_cases hy : y ∈ μ.support
  · exact mul_le_mul_right (hk y hy) _
  · rw [(PMF.apply_eq_zero_iff _ _).mpr hy, zero_mul, zero_mul]

/-- Along `ExecCodeDist w c x μ T`, if no continuation from `⟨pc + c.size, y⟩` faults within
`T_hor` steps for any supported `y ∈ μ.support`, then running `p` from `⟨pc, x⟩` does not fault
within `T_hor` steps. -/
theorem evalRand_faulted_eq_zero (h : ExecCodeDist w c x μ T) {p : Program B r} {pc T_hor : ℕ}
    (hp : p.Contains pc (c.assemble pc))
    (hcont : ∀ y ∈ μ.support, ∀ t ≤ T_hor, evalRand w p t ⟨pc + c.size, y⟩ .faulted = 0) :
    ∀ t ≤ T_hor, evalRand w p t ⟨pc, x⟩ .faulted = 0 := by
  induction h generalizing pc T_hor with
  | @of_execRand c x m hm =>
    refine hm.evalRand_faulted_eq_zero hp fun z hz t ht => ?_
    apply hcont z.1
    · rw [ProbComp.eval_map, PMF.mem_support_map_iff]
      refine ⟨z, ?_, rfl⟩
      rwa [ProbComp.support_eval]
    · exact ht
  | mono _ _ ih => exact ih hp hcont
  | @seq c₁ c₂ x μ₁ μ₂ T₁ T₂ _ _ ih₁ ih₂ =>
    have hc₂ : p.Contains (pc + c₁.size) (c₂.assemble (pc + c₁.size)) := by
      simpa [Code.length_assemble] using hp.append_right
    refine ih₁ hp.append_left fun y₁ hy₁ => ih₂ y₁ hy₁ hc₂ fun y₂ hy₂ t ht => ?_
    have hmem : y₂ ∈ (μ₁.bind μ₂).support :=
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨y₁, hy₁, hy₂⟩
    simpa [Code.size, Nat.add_assoc] using hcont y₂ hmem t ht
  | @branch_pos cond pos neg x μ T hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
    rw [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'
    intro t ht
    cases t with
    | zero => simp [evalRand]
    | succ k =>
      rw [evalRand, runRand_succ, stepRand_branch (s := ⟨pc, x⟩) hbr]
      simp only [hc, ↓reduceIte, pure_bind]
      refine ih hc' (T_hor := k) (fun y hy t' ht' => ?_) k le_rfl
      simpa [Code.size, show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
        using hcont y hy t' (by omega)
  | @branch_neg cond pos neg x μ T hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hj : p[pc + 1 + neg.size]? = some (.jump (pc + neg.size + pos.size + 2)) := by
      simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head
    intro t ht
    cases t with
    | zero => simp [evalRand]
    | succ k =>
      rw [evalRand, runRand_succ, stepRand_branch (s := ⟨pc, x⟩) hbr]
      simp only [hc, ↓reduceIte, pure_bind]
      refine ih hp.cons_tail.append_left (T_hor := k) (fun y hy t' ht' => ?_) k le_rfl
      cases t' with
      | zero => simp [evalRand]
      | succ k' =>
        rw [evalRand, runRand_succ, stepRand_jump (s := ⟨pc + 1 + neg.size, y⟩) hj, pure_bind]
        simpa [evalRand, Code.size,
          show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
          using hcont y hy k' (by omega)
  | @loop_geometric cond body I Q μ_body T_body B_body p_exit x
      hp_pos hp_top _ _ hinv hp_exit hx_inv ih_body =>
    have hj_exit : p[pc + 1]? = some (.jump (pc + body.size + 3)) := hp.cons_tail.head
    have hbody_contains : p.Contains (pc + 2) (body.assemble (pc + 2)) := by
      simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left
    have hj_back : p[pc + 2 + body.size]? = some (.jump pc) := by
      simpa using hp.cons_tail.cons_tail.append_right.head
    have hmain : ∀ n ≤ T_hor, ∀ z : Data r, LoopStateInv cond I Q z →
        (∀ y ∈ (loopExitPMF cond μ_body z).support, ∀ t ≤ T_hor,
          evalRand w p t ⟨pc + (Code.loop cond body).size, y⟩ .faulted = 0) →
        evalRand w p n ⟨pc, z⟩ .faulted = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ihn =>
        intro hn z hz_inv hcont_z
        cases n with
        | zero => simp [evalRand]
        | succ k =>
          rcases hz_inv with ⟨hcz, hIz⟩ | ⟨hcz, _⟩
          · rw [evalRand, runRand_succ, stepRand_branch (s := ⟨pc, z⟩) hp.head]
            simp only [hcz, ↓reduceIte, pure_bind]
            refine ih_body z hIz hcz hbody_contains (T_hor := k) (fun u hu t' ht' => ?_) k le_rfl
            cases t' with
            | zero => simp [evalRand]
            | succ k' =>
              rw [evalRand, runRand_succ, stepRand_jump (s := ⟨pc + 2 + body.size, u⟩) hj_back,
                pure_bind]
              refine ihn k' (by omega) (by omega) u (hinv z hIz hcz u hu) fun y hy t'' ht'' => ?_
              apply hcont_z y _ t'' ht''
              rw [loopExitPMF_of_holds hp_pos hp_top hinv hp_exit hIz hcz, PMF.mem_support_bind_iff]
              exact ⟨u, hu, hy⟩
          · rw [evalRand, runRand_succ, stepRand_branch (s := ⟨pc, z⟩) hp.head]
            simp only [hcz, ↓reduceIte, pure_bind]
            cases k with
            | zero => simp
            | succ k' =>
              rw [runRand_succ, stepRand_jump (s := ⟨pc + 1, z⟩) hj_exit, pure_bind]
              have hz_mem : z ∈ (loopExitPMF cond μ_body z).support := by
                simp [loopExitPMF_of_not_holds hcz]
              simpa [evalRand, Code.size, show pc + body.size + 3 = pc + (body.size + 3) by omega]
                using hcont_z z hz_mem k' (by omega)
    intro t ht
    exact hmain t ht x hx_inv hcont

/-- If every continuation from `⟨pc + c.size, y⟩` (`y ∈ μ.support`) is fault-free at all horizons,
then running `p` from `⟨pc, x⟩` is fault-free at all horizons. -/
theorem randFaultFree_assemble (h : ExecCodeDist w c x μ T) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc))
    (hcont : ∀ y ∈ μ.support, RandFaultFree w p ⟨pc + c.size, y⟩) :
    RandFaultFree w p ⟨pc, x⟩ := by
  intro T_hor
  rw [← support_evalRand, ← PMF.apply_eq_zero_iff]
  exact h.evalRand_faulted_eq_zero hp
    (fun y hy t _ => (hcont y hy).evalRand_faulted_eq_zero t)
    T_hor le_rfl

/-- Along `ExecCodeDist w c x μ T`, the `μ`-weighted supremum halting probability from
`⟨pc + c.size, y⟩` is a lower bound on the supremum halting probability from `⟨pc, x⟩`. -/
theorem le_iSup_evalRand_halted (h : ExecCodeDist w c x μ T) {p : Program B r} {pc : ℕ}
    (hp : p.Contains pc (c.assemble pc)) (v : ℕ) (d : Data r) :
    (∑' y, μ y * ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc + c.size, y⟩ (.halted v d)) ≤
      ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc, x⟩ (.halted v d) := by
  induction h generalizing pc with
  | @of_execRand c x m hm =>
    refine (le_of_eq ?_).trans (hm.le_iSup_evalRand_halted hp v d)
    exact ProbComp.expect_map Prod.fst m
      (fun y => ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc + c.size, y⟩ (.halted v d))
  | mono _ _ ih => exact ih hp
  | @seq c₁ c₂ x μ₁ μ₂ T₁ T₂ _ _ ih₁ ih₂ =>
    have hc₂ : p.Contains (pc + c₁.size) (c₂.assemble (pc + c₁.size)) := by
      simpa [Code.length_assemble] using hp.append_right
    have hbind :
        (∑' y, (μ₁.bind μ₂) y *
            ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc + (c₁.seq c₂).size, y⟩ (.halted v d)) =
          ∑' y₁, μ₁ y₁ * ∑' y, (μ₂ y₁) y *
            ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc + c₁.size + c₂.size, y⟩ (.halted v d) := by
      simp only [Code.size, Nat.add_assoc]
      exact Cslib.Probability.PMF.tsum_bind_mul μ₁ μ₂ _
    rw [hbind]
    refine (tsum_le_tsum fun y₁ => ?_).trans (ih₁ hp.append_left)
    by_cases hy₁ : y₁ ∈ μ₁.support
    · exact mul_le_mul_right (ih₂ y₁ hy₁ hc₂) _
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hy₁, zero_mul, zero_mul]
  | @branch_pos cond pos neg x μ T hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
    rw [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'
    have hstep : stepRand w p (.running ⟨pc, x⟩) = pure (.running ⟨pc + neg.size + 2, x⟩) := by
      rw [stepRand_branch (s := ⟨pc, x⟩) hbr]
      simp [hc]
    refine (le_of_eq ?_).trans ((ih hc').trans (iSup_evalRand_halted_le_of_step hstep v d))
    refine tsum_congr fun y => ?_
    simp [Code.size, show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
  | @branch_neg cond pos neg x μ T hc _ ih =>
    have hbr : p[pc]? = some (.branch cond (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hj : p[pc + 1 + neg.size]? = some (.jump (pc + neg.size + pos.size + 2)) := by
      simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head
    have hstep : stepRand w p (.running ⟨pc, x⟩) = pure (.running ⟨pc + 1, x⟩) := by
      rw [stepRand_branch (s := ⟨pc, x⟩) hbr]
      simp [hc]
    refine (tsum_le_tsum fun y => mul_le_mul_right ?_ _).trans
      ((ih hp.cons_tail.append_left).trans (iSup_evalRand_halted_le_of_step hstep v d))
    simpa [Code.size, show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
      using iSup_evalRand_halted_le_of_step
        (stepRand_jump (s := ⟨pc + 1 + neg.size, y⟩) hj) v d
  | @loop_geometric cond body I Q μ_body T_body B_body p_exit x
      hp_pos hp_top _ _ hinv hp_exit hx_inv ih_body =>
    have hj_exit : p[pc + 1]? = some (.jump (pc + body.size + 3)) := hp.cons_tail.head
    have hbody_contains : p.Contains (pc + 2) (body.assemble (pc + 2)) := by
      simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left
    have hj_back : p[pc + 2 + body.size]? = some (.jump pc) := by
      simpa using hp.cons_tail.cons_tail.append_right.head
    set H_loop : Data r → ℝ≥0∞ := fun z => ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc, z⟩ (.halted v d)
    set H_exit : Data r → ℝ≥0∞ := fun z =>
      ⨆ T_hor : ℕ, evalRand w p T_hor ⟨pc + (Code.loop cond body).size, z⟩ (.halted v d)
    have hexit_le : ∀ z : Data r, ¬cond.Holds z → H_exit z ≤ H_loop z := by
      intro z hcz
      have hbr : stepRand w p (.running ⟨pc, z⟩) = pure (.running ⟨pc + 1, z⟩) := by
        rw [stepRand_branch (s := ⟨pc, z⟩) hp.head]
        simp [hcz]
      simpa [H_exit, H_loop, Code.size, show pc + body.size + 3 = pc + (body.size + 3) by omega]
        using (iSup_evalRand_halted_le_of_step
          (stepRand_jump (s := ⟨pc + 1, z⟩) hj_exit) v d).trans
            (iSup_evalRand_halted_le_of_step hbr v d)
    have hstep_le : ∀ z : Data r, I z → cond.Holds z →
        (∑' u, μ_body z u * H_loop u) ≤ H_loop z := by
      intro z hIz hcz
      have hbr : stepRand w p (.running ⟨pc, z⟩) = pure (.running ⟨pc + 2, z⟩) := by
        rw [stepRand_branch (s := ⟨pc, z⟩) hp.head]
        simp [hcz]
      refine (tsum_le_tsum fun u => mul_le_mul_right ?_ _).trans
        ((ih_body z hIz hcz hbody_contains).trans (iSup_evalRand_halted_le_of_step hbr v d))
      exact iSup_evalRand_halted_le_of_step
        (stepRand_jump (s := ⟨pc + 2 + body.size, u⟩) hj_back) v d
    have hiter_le : ∀ K : ℕ, ∀ z : Data r, LoopStateInv cond I Q z →
        (∑' y, loopIterPMF cond μ_body K z y * H_loop y) ≤ H_loop z := by
      intro K
      induction K with
      | zero =>
        intro z _
        rw [tsum_eq_single z (fun y hy => by simp [loopIterPMF_zero, PMF.pure_apply, hy])]
        simp [H_loop]
      | succ K ihK =>
        intro z hz_inv
        rcases hz_inv with ⟨hcz, hIz⟩ | ⟨hcz, _⟩
        · rw [loopIterPMF_succ, loopStepPMF_of_holds hcz]
          have hbind : (∑' y, ((μ_body z).bind (loopIterPMF cond μ_body K)) y * H_loop y) =
              ∑' u, μ_body z u * ∑' y, loopIterPMF cond μ_body K u y * H_loop y :=
            Cslib.Probability.PMF.tsum_bind_mul (μ_body z) (loopIterPMF cond μ_body K) H_loop
          rw [hbind]
          refine (tsum_le_tsum fun u => ?_).trans (hstep_le z hIz hcz)
          by_cases hu : u ∈ (μ_body z).support
          · exact mul_le_mul_right (ihK u (hinv z hIz hcz u hu)) _
          · rw [(PMF.apply_eq_zero_iff _ _).mpr hu, zero_mul, zero_mul]
        · rw [loopIterPMF_of_not_holds hcz,
            tsum_eq_single z (fun y hy => by simp [PMF.pure_apply, hy])]
          simp
    have hrewrite_sum :
        (∑' y, loopExitPMF cond μ_body x y * H_exit y) =
          ⨆ K : ℕ, ∑' y,
            Set.indicator {w' | ¬cond.Holds w'} (loopIterPMF cond μ_body K x) y * H_exit y := by
      simp_rw [loopExitPMF_apply_of_hasSum
        (hasSum_loopExitDensity hp_pos hp_top hinv hp_exit hx_inv), ENNReal.iSup_mul]
      exact ENNReal.tsum_iSup_of_monotone fun y K₁ K₂ hK =>
        mul_le_mul_left (loopIterPMF_indicator_mono cond μ_body x y hK) (H_exit y)
    rw [hrewrite_sum]
    refine iSup_le fun K => (tsum_le_tsum fun y => ?_).trans (hiter_le K x hx_inv)
    by_cases hcy : ¬cond.Holds y
    · rw [Set.indicator_of_mem hcy]
      exact mul_le_mul_right (hexit_le y hcy) _
    · simp [Set.indicator_of_notMem, hcy]

/-- Compiling `ExecCodeDist w c x μ T` with `c.program out` yields:
1. `expectedTime w (c.program out) ⟨0, x⟩ ≤ T + 1`,
2. `RandFaultFree w (c.program out) ⟨0, x⟩`,
3. `AlmostSurelyHalts w (c.program out) ⟨0, x⟩` whenever `T ≠ ⊤`, and
4. for every `y : Data r`,
   `μ y ≤ ⨆ T_hor : ℕ, evalRand w (c.program out) T_hor ⟨0, x⟩ (.halted (y.regs out) y)`. -/
theorem program_halts (h : ExecCodeDist w c x μ T) (out : Fin r) :
    expectedTime w (c.program out) ⟨0, x⟩ ≤ T + 1 ∧
    RandFaultFree w (c.program out) ⟨0, x⟩ ∧
    (T ≠ ⊤ → AlmostSurelyHalts w (c.program out) ⟨0, x⟩) ∧
    ∀ y : Data r,
      μ y ≤ ⨆ T_hor : ℕ, evalRand w (c.program out) T_hor ⟨0, x⟩ (.halted (y.regs out) y) := by
  have hp : (c.program out).Contains 0 (c.assemble 0) :=
    (Program.Contains.self (c.program out)).append_left
  have hhalt : (c.program out)[0 + c.size]? = some (.halt out) := by
    simp [Code.program]
  have hexp : expectedTime w (c.program out) ⟨0, x⟩ ≤ T + 1 := by
    rw [expectedTime_eq_expectedStepsFrom]
    refine (h.expectedStepsFrom_le (k := fun _ => 1) hp fun y _ => ?_).trans ?_
    · rw [expectedStepsFrom_running, stepRand_halt (s := ⟨0 + c.size, y⟩) hhalt,
        ProbComp.expect_pure, expectedStepsFrom_halted, add_zero]
    · simp [μ.tsum_coe]
  have hff : RandFaultFree w (c.program out) ⟨0, x⟩ := by
    refine h.randFaultFree_assemble hp fun y _ t => ?_
    rw [← support_evalRand, ← PMF.apply_eq_zero_iff]
    cases t with
    | zero => simp [evalRand]
    | succ k =>
      rw [evalRand, runRand_succ, stepRand_halt (s := ⟨0 + c.size, y⟩) hhalt, pure_bind,
        runRand_halted]
      simp [PMF.pure_apply]
  refine ⟨hexp, hff, fun hT => ?_, fun y => ?_⟩
  · refine AlmostSurelyHalts.of_expectedTime_ne_top hff ?_
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hT, ENNReal.one_ne_top⟩) hexp
  · have hle := h.le_iSup_evalRand_halted hp (y.regs out) y
    refine (le_trans ?_
      (le_tsum
        (f := fun z => μ z *
          ⨆ T_hor : ℕ, evalRand w (c.program out) T_hor ⟨0 + c.size, z⟩
            (.halted (y.regs out) y)) y)).trans hle
    have h1 : (1 : ℝ≥0∞) ≤
        ⨆ T_hor : ℕ, evalRand w (c.program out) T_hor ⟨0 + c.size, y⟩ (.halted (y.regs out) y) := by
      refine le_iSup_of_le 1 ?_
      rw [evalRand, runRand_succ, stepRand_halt (s := ⟨0 + c.size, y⟩) hhalt, pure_bind,
        runRand_zero, ProbComp.eval_pure, PMF.pure_apply_self]
    simpa using mul_le_mul_right h1 (μ y)

end ExecCodeDist

/-- Geometric Las Vegas loop expected-step bound inside any flat program `p` containing
`(Code.loop cond body).assemble pc`. -/
theorem expectedStepsFrom_loop_le_of_geometric {w : ℕ} {cond : Cond r} {body : Code B r}
    (I Q : Data r → Prop) {μ_body : Data r → PMF (Data r)} {T_body : Data r → ℝ≥0∞}
    {B_body p_exit : ℝ≥0∞} {x : Data r}
    (hp_pos : 0 < p_exit) (hp_top : p_exit ≠ ⊤)
    (hbody : ∀ z, I z → cond.Holds z → ExecCodeDist w body z (μ_body z) (T_body z))
    (hB : ∀ z, I z → cond.Holds z → T_body z ≤ B_body)
    (hinv : ∀ z, I z → cond.Holds z →
      ∀ y ∈ (μ_body z).support, LoopStateInv cond I Q y)
    (hp_exit : ∀ z, I z → cond.Holds z →
      p_exit ≤ (μ_body z).toOuterMeasure {y | ¬cond.Holds y})
    (hx_inv : LoopStateInv cond I Q x)
    {p : Program B r} {pc : ℕ} (hp : p.Contains pc ((Code.loop cond body).assemble pc))
    {k : Data r → ℝ≥0∞}
    (hk : ∀ y, ¬cond.Holds y → Q y →
      expectedStepsFrom w p (.running ⟨pc + (Code.loop cond body).size, y⟩) ≤ k y) :
    expectedStepsFrom w p (.running ⟨pc, x⟩) ≤
      ((B_body + 2) / p_exit + 2) + ∑' y, loopExitPMF cond μ_body x y * k y := by
  have hloop := ExecCodeDist.loop_geometric I Q hp_pos hp_top hbody hB hinv hp_exit hx_inv
  refine hloop.expectedStepsFrom_le hp fun y hy => ?_
  obtain ⟨⟨hcy, hQy⟩, _⟩ := mem_support_loopExitPMF hp_pos hp_top hinv hp_exit hx_inv hy
  exact hk y hcy hQy

end Cslib.WordRAM

end
