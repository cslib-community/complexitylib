/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.Resizable.Basic
public import Complexity.Languages.Probabilistic.Expect
public import Complexity.Probability.PMF.Bind
public import Complexity.Probability.PMF.Event
import Complexity.Foundations.Analysis.ENNRealTsum
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map

/-!
# Clocked randomized execution and adaptive-adversary expected time on the Resizable Word RAM

Clocked probabilistic operational semantics, adaptive-adversary fault-freedom, every-step peak
hardware-frontier bounds (`PeakFrontierLe`), `ℝ≥0∞`-valued expected running time
(`expectedTimeDemonic`), and flat-program halting-distribution specifications (`ExecRProgramDist`)
for the word-granular **Resizable Word RAM** (`Cslib.WordRAM.Resizable`).

When a flat program `p : RProgram B r` executes `.grow dst kReg`, a time- and state-adaptive
adversary `adv : RAdv r` (`ℕ → RState r → ℕ → ℕ`), observing the step index `t` and the full
current machine state `s : RState r`, chooses arbitrary `w`-bit initial words in
`[s.data.frontier, s.data.frontier + k)` (`advGrowMem`). Every flat-program specification
quantifies universally (or takes the supremum in `ℝ≥0∞`) over all `adv : RAdv r`.

## Main definitions

* `Cslib.WordRAM.Resizable.RAdv`, `Cslib.WordRAM.Resizable.advGrowMem`: time- and state-adaptive
  adversary for newly grown words on `.grow`.
* `Cslib.WordRAM.Resizable.stepRandResizable`, `Cslib.WordRAM.Resizable.runRandResizable`,
  `Cslib.WordRAM.Resizable.evalRandDemonic`: single-step and clocked `t`-step probabilistic
  execution in `ProbComp` and `PMF`.
* `Cslib.WordRAM.Resizable.RDemonicFaultFree`, `Cslib.WordRAM.Resizable.PeakFrontierLe`,
  `Cslib.WordRAM.Resizable.AlmostSurelyHaltsDemonic`,
  `Cslib.WordRAM.Resizable.expectedTimeDemonic`: fault-freedom, every-step peak hardware-frontier
  bound, almost-sure halting, and supremum expected instruction count across all adaptive
  adversaries.
* `Cslib.WordRAM.Resizable.ExecRProgramDist`: flat-program execution certificate coupling fault
  freedom, `PeakFrontierLe`, `expectedTimeDemonic ≤ T`, and exact halting-state distribution `μ`.

## Main results

* `Cslib.WordRAM.Resizable.ExecRProgramDist.iSup_evalRandDemonic_halted_eq`: `ExecRProgramDist`
  pins the limiting halting probability of every state `y` to `μ y` under every adversary `adv`.
* `Cslib.WordRAM.Resizable.ExecRProgramDist.almostSurelyHaltsDemonic`: every `ExecRProgramDist`
  halts almost surely across all adaptive adversaries.
* `Cslib.WordRAM.Resizable.not_execRProgramDist_halt`: a 1-instruction `[.halt out]` program cannot
  satisfy `ExecRProgramDist` for any target distribution assigning positive mass outside `x`.

## References

* [KuszmaulLiangZhou2026] William Kuszmaul, Jingxun Liang, and Renfei Zhou, *Succinct Dynamic
  Rank/Select: Bypassing the Tree-Structure Bottleneck*, SODA 2026 (`arXiv:2510.19175v1`,
  Section 5.1, PDF p. 16 / printed p. 15).
* [MitzenmacherUpfal2017] Michael Mitzenmacher and Eli Upfal, *Probability and Computing*, 2nd ed.,
  Cambridge University Press, 2017, Sections 2.1, 2.3, and 2.4.
-/
@[expose] public section

open scoped ENNReal

namespace Cslib.WordRAM.Resizable

variable {B B' : Basis} {r : ℕ}

/-! ## Adaptive adversary and clocked randomized execution -/

/-- Time- and state-adaptive adversary choosing initial word contents on `.grow` instructions as a
function of step index `t : ℕ`, active machine state `s : RState r`, and word address `a : ℕ`. -/
abbrev RAdv (r : ℕ) : Type := ℕ → RState r → ℕ → ℕ

/-- Shift an adaptive adversary forward by `d` execution steps. -/
def RAdv.shift (d : ℕ) (adv : RAdv r) : RAdv r := fun t s a => adv (t + d) s a

@[simp] theorem RAdv.shift_zero (adv : RAdv r) : adv.shift 0 = adv := rfl

theorem RAdv.shift_shift (d₁ d₂ : ℕ) (adv : RAdv r) :
    (adv.shift d₁).shift d₂ = adv.shift (d₁ + d₂) := by
  funext t s a; dsimp only [RAdv.shift]; congr 1; omega

/-- Prepend a single-step initializer `f` before `adv` so `(adv.prepend f).shift 1 = adv`. -/
def RAdv.prepend (f : RState r → ℕ → ℕ) (adv : RAdv r) : RAdv r
  | 0, s, a => f s a
  | t + 1, s, a => adv t s a

@[simp] theorem RAdv.prepend_zero (f : RState r → ℕ → ℕ) (adv : RAdv r) :
    (adv.prepend f) 0 = f := rfl

@[simp] theorem RAdv.shift_one_prepend (f : RState r → ℕ → ℕ) (adv : RAdv r) :
    (adv.prepend f).shift 1 = adv := by
  funext t s a; simp [RAdv.shift, RAdv.prepend]

/-- Adversarial memory initializer for `.grow`: preserves `mem a` for `a < L`, writes
`init a % 2 ^ w` in `[L, L + k)`, and zeroes `a ≥ L + k`. -/
def advGrowMem (w : ℕ) (init : ℕ → ℕ) (L k : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  fun a => if a < L then mem a else if a < L + k then init a % 2 ^ w else 0

/-- Every `advGrowMem` instance satisfies `DemonicGrow`. -/
theorem demonicGrow_advGrowMem (w : ℕ) (init : ℕ → ℕ) (L k : ℕ) (mem : ℕ → ℕ) :
    DemonicGrow w L k mem (advGrowMem w init L k mem) := by
  refine ⟨fun a ha => by simp [advGrowMem, ha], fun a hlo hhi => ?_, fun a ha => ?_⟩
  · have hnot : ¬a < L := by omega
    simp only [advGrowMem, hnot, ↓reduceIte, hhi]
    exact Nat.mod_lt _ (Nat.two_pow_pos w)
  · have h1 : ¬a < L := by omega
    have h2 : ¬a < L + k := by omega
    simp [advGrowMem, h1, h2]

/-- Single step of randomized execution of `p : RProgram B r` at word width `w` under single-step
growth initializer `advStep : RState r → ℕ → ℕ`. Halted and faulted configurations are absorbing. -/
def stepRandResizable (w : ℕ) (advStep : RState r → ℕ → ℕ) (p : RProgram B r) :
    RCfg r → ProbComp (RCfg r)
  | .running s =>
    match p[s.pc]? with
    | none => pure .faulted
    | some (.op o) =>
      match evalResizable w o s.data with
      | some x => pure (.running ⟨s.pc + 1, x⟩)
      | none => pure .faulted
    | some (.jump target) => pure (.running ⟨target, s.data⟩)
    | some (.branch c target) =>
      pure (.running ⟨if c.Holds s.data.toData then target else s.pc + 1, s.data⟩)
    | some (.halt i) => pure (.halted (s.data.regs i) s.data)
    | some (.rand dst src) =>
      if Fits w (s.data.regs src) then do
        let k ← ProbComp.unifFin (s.data.regs src)
        pure (.running ⟨s.pc + 1, s.data.set dst k.val⟩)
      else pure .faulted
    | some (.grow dst kReg) =>
      let k := s.data.regs kReg
      if Fits w (s.data.frontier + k) then
        let mem' := advGrowMem w (advStep s) s.data.frontier k s.data.mem
        pure (.running ⟨s.pc + 1,
          ⟨Function.update s.data.regs dst s.data.frontier, mem', s.data.frontier + k⟩⟩)
      else pure .faulted
    | some (.shrink kReg) =>
      let k := s.data.regs kReg
      if k ≤ s.data.frontier then
        pure (.running ⟨s.pc + 1,
          ⟨s.data.regs, clear s.data.mem (s.data.frontier - k) k, s.data.frontier - k⟩⟩)
      else pure .faulted
  | cfg => pure cfg

section StepLemmas

variable {w : ℕ} {advStep : RState r → ℕ → ℕ} {p : RProgram B r} {s : RState r}

@[simp] theorem stepRandResizable_halted (v : ℕ) (d : RData r) :
    stepRandResizable w advStep p (.halted v d) = pure (.halted v d) := rfl

@[simp] theorem stepRandResizable_faulted :
    stepRandResizable w advStep p .faulted = pure .faulted := rfl

theorem stepRandResizable_op {o : Op B r} {y : RData r} (hp : p[s.pc]? = some (.op o))
    (he : evalResizable w o s.data = some y) :
    stepRandResizable w advStep p (.running s) = pure (.running ⟨s.pc + 1, y⟩) := by
  simp [stepRandResizable, hp, he]

theorem stepRandResizable_jump {t : ℕ} (hp : p[s.pc]? = some (.jump t)) :
    stepRandResizable w advStep p (.running s) = pure (.running ⟨t, s.data⟩) := by
  simp [stepRandResizable, hp]

theorem stepRandResizable_branch {c : Cond r} {t : ℕ} (hp : p[s.pc]? = some (.branch c t)) :
    stepRandResizable w advStep p (.running s) =
      pure (.running ⟨if c.Holds s.data.toData then t else s.pc + 1, s.data⟩) := by
  simp [stepRandResizable, hp]

theorem stepRandResizable_branch_pos {c : Cond r} {t : ℕ} (hp : p[s.pc]? = some (.branch c t))
    (hc : c.Holds s.data.toData) :
    stepRandResizable w advStep p (.running s) = pure (.running ⟨t, s.data⟩) := by
  rw [stepRandResizable_branch hp]; simp [hc]

theorem stepRandResizable_branch_neg {c : Cond r} {t : ℕ} (hp : p[s.pc]? = some (.branch c t))
    (hc : ¬c.Holds s.data.toData) :
    stepRandResizable w advStep p (.running s) = pure (.running ⟨s.pc + 1, s.data⟩) := by
  rw [stepRandResizable_branch hp]; simp [hc]

theorem stepRandResizable_halt {i : Fin r} (hp : p[s.pc]? = some (.halt i)) :
    stepRandResizable w advStep p (.running s) = pure (.halted (s.data.regs i) s.data) := by
  simp [stepRandResizable, hp]

theorem stepRandResizable_rand_of_fits {dst src : Fin r} (hp : p[s.pc]? = some (.rand dst src))
    (hf : Fits w (s.data.regs src)) :
    stepRandResizable w advStep p (.running s) = (do
      let k ← ProbComp.unifFin (s.data.regs src)
      pure (.running ⟨s.pc + 1, s.data.set dst k.val⟩)) := by
  simp [stepRandResizable, hp, hf]

theorem stepRandResizable_grow_of_fits {dst kReg : Fin r} (hp : p[s.pc]? = some (.grow dst kReg))
    (hf : Fits w (s.data.frontier + s.data.regs kReg)) :
    stepRandResizable w advStep p (.running s) =
      pure (.running ⟨s.pc + 1, ⟨Function.update s.data.regs dst s.data.frontier,
        advGrowMem w (advStep s) s.data.frontier (s.data.regs kReg) s.data.mem,
        s.data.frontier + s.data.regs kReg⟩⟩) := by
  simp [stepRandResizable, hp, hf]

theorem stepRandResizable_shrink_of_le {kReg : Fin r} (hp : p[s.pc]? = some (.shrink kReg))
    (hk : s.data.regs kReg ≤ s.data.frontier) :
    stepRandResizable w advStep p (.running s) =
      pure (.running ⟨s.pc + 1, ⟨s.data.regs,
        clear s.data.mem (s.data.frontier - s.data.regs kReg) (s.data.regs kReg),
        s.data.frontier - s.data.regs kReg⟩⟩) := by
  simp [stepRandResizable, hp, hk]

end StepLemmas

/-- Clocked `t`-step randomized execution of `p : RProgram B r` under adaptive adversary `adv`. -/
def runRandResizable (w : ℕ) (adv : RAdv r) (p : RProgram B r) :
    ℕ → RCfg r → ProbComp (RCfg r)
  | 0, cfg => pure cfg
  | t + 1, cfg => do
    let cfg' ← stepRandResizable w (adv 0) p cfg
    runRandResizable w (adv.shift 1) p t cfg'

@[simp] theorem runRandResizable_zero (w : ℕ) (adv : RAdv r) (p : RProgram B r) (cfg : RCfg r) :
    runRandResizable w adv p 0 cfg = pure cfg := rfl

theorem runRandResizable_succ (w : ℕ) (adv : RAdv r) (p : RProgram B r) (t : ℕ) (cfg : RCfg r) :
    runRandResizable w adv p (t + 1) cfg = (do
      let cfg' ← stepRandResizable w (adv 0) p cfg
      runRandResizable w (adv.shift 1) p t cfg') := rfl

@[simp] theorem runRandResizable_halted (w : ℕ) (adv : RAdv r) (p : RProgram B r) (t v : ℕ)
    (d : RData r) : runRandResizable w adv p t (.halted v d) = pure (.halted v d) := by
  induction t generalizing adv with
  | zero => rfl
  | succ t ih => simp [runRandResizable, ih]

@[simp] theorem runRandResizable_faulted (w : ℕ) (adv : RAdv r) (p : RProgram B r) (t : ℕ) :
    runRandResizable w adv p t .faulted = pure .faulted := by
  induction t generalizing adv with
  | zero => rfl
  | succ t ih => simp [runRandResizable, ih]

theorem runRandResizable_add (w : ℕ) (adv : RAdv r) (p : RProgram B r) (t₁ t₂ : ℕ)
    (cfg : RCfg r) :
    runRandResizable w adv p (t₁ + t₂) cfg = (do
      let cfg' ← runRandResizable w adv p t₁ cfg
      runRandResizable w (adv.shift t₁) p t₂ cfg') := by
  induction t₁ generalizing adv cfg with
  | zero => simp [runRandResizable]
  | succ t₁ ih =>
    rw [Nat.succ_add, runRandResizable_succ, runRandResizable_succ, bind_assoc]
    refine congrArg (stepRandResizable w (adv 0) p cfg >>= ·) (funext fun cfg' => ?_)
    rw [ih, RAdv.shift_shift, Nat.add_comm 1 t₁]

/-- Configuration distribution after `t` steps from `.running s` under adaptive adversary `adv`. -/
noncomputable def evalRandDemonic (w : ℕ) (adv : RAdv r) (p : RProgram B r) (t : ℕ)
    (s : RState r) : PMF (RCfg r) :=
  (runRandResizable w adv p t (.running s)).eval

/-- Set of active (`.running`) configurations. -/
def RCfg.runningSet (r : ℕ) : Set (RCfg r) := {cfg | ∃ u, cfg = .running u}

/-- Set of cleanly halted (`.halted`) configurations. -/
def RCfg.haltedSet (r : ℕ) : Set (RCfg r) := {cfg | ∃ v d, cfg = .halted v d}

@[simp] theorem RCfg.mem_runningSet_iff {cfg : RCfg r} :
    cfg ∈ RCfg.runningSet r ↔ ∃ u, cfg = .running u := Iff.rfl

@[simp] theorem RCfg.mem_haltedSet_iff {cfg : RCfg r} :
    cfg ∈ RCfg.haltedSet r ↔ ∃ v d, cfg = .halted v d := Iff.rfl

/-- Pointwise halting probability at `.halted v d` is monotone in the horizon `t`. -/
theorem evalRandDemonic_halted_mono (w : ℕ) (adv : RAdv r) (p : RProgram B r) (s : RState r)
    (v : ℕ) (d : RData r) :
    Monotone fun t => evalRandDemonic w adv p t s (.halted v d) := by
  refine monotone_nat_of_le_succ fun t => ?_
  have hstep : evalRandDemonic w adv p (t + 1) s =
      (evalRandDemonic w adv p t s).bind
        (fun cfg => (stepRandResizable w ((adv.shift t) 0) p cfg).eval) := by
    simp only [evalRandDemonic, runRandResizable_add w adv p t 1, ProbComp.eval_bind,
      runRandResizable_succ, runRandResizable_zero, bind_pure]
  rw [hstep, PMF.bind_apply]
  calc
    evalRandDemonic w adv p t s (.halted v d)
      = evalRandDemonic w adv p t s (.halted v d) *
          (stepRandResizable w ((adv.shift t) 0) p (.halted v d)).eval (.halted v d) := by
        simp [stepRandResizable_halted]
    _ ≤ ∑' cfg, evalRandDemonic w adv p t s cfg *
          (stepRandResizable w ((adv.shift t) 0) p cfg).eval (.halted v d) :=
        le_tsum
          (f := fun cfg => evalRandDemonic w adv p t s cfg *
            (stepRandResizable w ((adv.shift t) 0) p cfg).eval (.halted v d))
          (.halted v d)

/-- Any deterministic transition `stepRandResizable w (adv 0) p (.running s) = pure (.running s')`
transports supremum halting probabilities from `(adv.shift 1, s')` to `(adv, s)`. -/
theorem iSup_evalRandDemonic_halted_le_of_step {w : ℕ} {adv : RAdv r} {p : RProgram B r}
    {s s' : RState r}
    (hstep : stepRandResizable w (adv 0) p (.running s) = pure (.running s'))
    (v : ℕ) (d : RData r) :
    (⨆ T_hor : ℕ, evalRandDemonic w (adv.shift 1) p T_hor s' (.halted v d)) ≤
      ⨆ T_hor : ℕ, evalRandDemonic w adv p T_hor s (.halted v d) := by
  refine iSup_le fun T_hor => le_iSup_of_le (T_hor + 1) ?_
  simp [evalRandDemonic, runRandResizable_succ, hstep]

/-! ## Fault-freedom, `PeakFrontierLe`, expected time, and `ExecRProgramDist` -/

/-- Configuration hardware-frontier upper bound (`≤ L_peak`). -/
def RCfg.FrontierLe (L_peak : ℕ) : RCfg r → Prop
  | .running s => s.data.frontier ≤ L_peak
  | .halted _ d => d.frontier ≤ L_peak
  | .faulted => True

/-- Joint non-faulting and frontier-bounded configuration invariant. -/
def RCfg.SafeBounded (L_peak : ℕ) : RCfg r → Prop
  | .running s => s.data.frontier ≤ L_peak
  | .halted _ d => d.frontier ≤ L_peak
  | .faulted => False

theorem RCfg.SafeBounded.ne_faulted {L_peak : ℕ} {cfg : RCfg r} (h : cfg.SafeBounded L_peak) :
    cfg ≠ .faulted := by
  rintro rfl; exact h

theorem RCfg.SafeBounded.frontierLe {L_peak : ℕ} {cfg : RCfg r} (h : cfg.SafeBounded L_peak) :
    cfg.FrontierLe L_peak := by
  cases cfg with
  | running _ | halted _ _ => exact h
  | faulted => exact h.elim

theorem RCfg.SafeBounded.mono {L₁ L₂ : ℕ} {cfg : RCfg r} (hL : L₁ ≤ L₂)
    (h : cfg.SafeBounded L₁) : cfg.SafeBounded L₂ := by
  cases cfg with
  | running _ | halted _ _ => exact h.trans hL
  | faulted => exact h

/-- Zero-fault invariant across all adaptive adversaries `adv : RAdv r` and all horizons `t : ℕ`. -/
def RDemonicFaultFree (w : ℕ) (p : RProgram B r) (s : RState r) : Prop :=
  ∀ (adv : RAdv r) (t : ℕ), evalRandDemonic w adv p t s .faulted = 0

/-- Every-step peak hardware-frontier bound: across every adaptive adversary `adv : RAdv r`, every
horizon `t : ℕ`, and every reachable configuration `cfg` (`.running` or `.halted`), the active
hardware word frontier never exceeds `L_peak`. -/
def PeakFrontierLe (w L_peak : ℕ) (p : RProgram B r) (s : RState r) : Prop :=
  ∀ (adv : RAdv r) (t : ℕ) (cfg : RCfg r),
    cfg ∈ (evalRandDemonic w adv p t s).support → cfg.FrontierLe L_peak

theorem PeakFrontierLe.mono {w L₁ L₂ : ℕ} {p : RProgram B r} {s : RState r}
    (hL : L₁ ≤ L₂) (h : PeakFrontierLe w L₁ p s) : PeakFrontierLe w L₂ p s := by
  intro adv t cfg hcfg
  have h1 := h adv t cfg hcfg
  cases cfg with
  | running _ | halted _ _ => exact h1.trans hL
  | faulted => trivial

/-- Almost-sure halting across all adaptive adversaries `adv : RAdv r`. -/
def AlmostSurelyHaltsDemonic (w : ℕ) (p : RProgram B r) (s : RState r) : Prop :=
  RDemonicFaultFree w p s ∧
    ∀ adv : RAdv r, (⨆ t : ℕ, (evalRandDemonic w adv p t s).toOuterMeasure (RCfg.haltedSet r)) = 1

/-- Finite-horizon expected active steps under a fixed adaptive adversary `adv`. -/
noncomputable def expectedStepsWithinAdv (w : ℕ) (adv : RAdv r) (p : RProgram B r) (N : ℕ)
    (cfg : RCfg r) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range N,
    (runRandResizable w adv p t cfg).eval.toOuterMeasure (RCfg.runningSet r)

/-- Supremum finite-horizon expected active steps across all adaptive adversaries `adv`. -/
noncomputable def supExpectedStepsWithin (w : ℕ) (p : RProgram B r) (N : ℕ) (cfg : RCfg r) :
    ℝ≥0∞ :=
  ⨆ adv : RAdv r, expectedStepsWithinAdv w adv p N cfg

/-- Expected remaining active steps from `cfg` under a fixed adaptive adversary `adv`. -/
noncomputable def expectedStepsFromAdv (w : ℕ) (adv : RAdv r) (p : RProgram B r) (cfg : RCfg r) :
    ℝ≥0∞ :=
  ∑' t : ℕ, (runRandResizable w adv p t cfg).eval.toOuterMeasure (RCfg.runningSet r)

/-- Supremum expected remaining active steps from `cfg` across all adaptive adversaries `adv`. -/
noncomputable def expectedStepsFromDemonic (w : ℕ) (p : RProgram B r) (cfg : RCfg r) : ℝ≥0∞ :=
  ⨆ adv : RAdv r, expectedStepsFromAdv w adv p cfg

/-- Worst-case adaptive-adversary expected running time of `p` from `s` at word width `w`. -/
noncomputable def expectedTimeDemonic (w : ℕ) (p : RProgram B r) (s : RState r) : ℝ≥0∞ :=
  expectedStepsFromDemonic w p (.running s)

@[simp] theorem expectedStepsWithinAdv_zero (w : ℕ) (adv : RAdv r) (p : RProgram B r)
    (cfg : RCfg r) : expectedStepsWithinAdv w adv p 0 cfg = 0 := by
  simp [expectedStepsWithinAdv]

@[simp] theorem supExpectedStepsWithin_zero (w : ℕ) (p : RProgram B r) (cfg : RCfg r) :
    supExpectedStepsWithin w p 0 cfg = 0 := by
  simp [supExpectedStepsWithin]

@[simp] theorem expectedStepsFromAdv_halted (w : ℕ) (adv : RAdv r) (p : RProgram B r) (v : ℕ)
    (d : RData r) : expectedStepsFromAdv w adv p (.halted v d) = 0 := by
  simp [expectedStepsFromAdv, RCfg.runningSet, PMF.toOuterMeasure_pure_apply]

@[simp] theorem expectedStepsFromDemonic_halted (w : ℕ) (p : RProgram B r) (v : ℕ) (d : RData r) :
    expectedStepsFromDemonic w p (.halted v d) = 0 := by
  simp [expectedStepsFromDemonic]

theorem expectedStepsWithinAdv_mono (w : ℕ) (adv : RAdv r) (p : RProgram B r) (cfg : RCfg r) :
    Monotone fun N => expectedStepsWithinAdv w adv p N cfg :=
  fun _ _ hN => Finset.sum_le_sum_of_subset (Finset.range_mono hN)

theorem supExpectedStepsWithin_mono (w : ℕ) (p : RProgram B r) (cfg : RCfg r) :
    Monotone fun N => supExpectedStepsWithin w p N cfg :=
  fun _ _ hN => iSup_mono fun adv => expectedStepsWithinAdv_mono w adv p cfg hN

theorem iSup_supExpectedStepsWithin (w : ℕ) (p : RProgram B r) (cfg : RCfg r) :
    (⨆ N : ℕ, supExpectedStepsWithin w p N cfg) = expectedStepsFromDemonic w p cfg := by
  simp only [supExpectedStepsWithin, expectedStepsFromDemonic, expectedStepsFromAdv]
  rw [iSup_comm]
  exact iSup_congr fun adv => ENNReal.tsum_eq_iSup_nat.symm

theorem supExpectedStepsWithin_le_expectedStepsFromDemonic (w : ℕ) (p : RProgram B r) (N : ℕ)
    (cfg : RCfg r) :
    supExpectedStepsWithin w p N cfg ≤ expectedStepsFromDemonic w p cfg := by
  rw [← iSup_supExpectedStepsWithin]
  exact le_iSup (fun K => supExpectedStepsWithin w p K cfg) N

/-- 1-step Bellman equation for `expectedStepsWithinAdv`. -/
theorem expectedStepsWithinAdv_running_succ (w : ℕ) (adv : RAdv r) (p : RProgram B r) (N : ℕ)
    (s : RState r) :
    expectedStepsWithinAdv w adv p (N + 1) (.running s) =
      1 + ProbComp.expect (stepRandResizable w (adv 0) p (.running s))
        (expectedStepsWithinAdv w (adv.shift 1) p N) := by
  rw [expectedStepsWithinAdv, Finset.sum_range_succ']
  have hzero : (runRandResizable w adv p 0 (.running s)).eval.toOuterMeasure
      (RCfg.runningSet r) = 1 := by
    simp [RCfg.runningSet, PMF.toOuterMeasure_pure_apply]
  rw [hzero, add_comm]
  congr 1
  have hsucc : ∀ t : ℕ, (runRandResizable w adv p (t + 1) (.running s)).eval.toOuterMeasure
      (RCfg.runningSet r) =
      ∑' cfg, (stepRandResizable w (adv 0) p (.running s)).eval cfg *
        (runRandResizable w (adv.shift 1) p t cfg).eval.toOuterMeasure (RCfg.runningSet r) := by
    intro t
    rw [runRandResizable_succ, ProbComp.eval_bind, PMF.toOuterMeasure_bind_apply]
  simp only [hsucc]
  rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
  simp only [ProbComp.expect, expectedStepsWithinAdv, Finset.mul_sum]

theorem expectedStepsWithinAdv_running_le (w : ℕ) (adv : RAdv r) (p : RProgram B r) (N : ℕ)
    (s : RState r) :
    expectedStepsWithinAdv w adv p N (.running s) ≤
      1 + ProbComp.expect (stepRandResizable w (adv 0) p (.running s))
        (supExpectedStepsWithin w p N) := by
  cases N with
  | zero => simp
  | succ N =>
    rw [expectedStepsWithinAdv_running_succ]
    refine add_le_add le_rfl (ProbComp.expect_mono fun cfg => ?_)
    exact (expectedStepsWithinAdv_mono w (adv.shift 1) p cfg (Nat.le_succ N)).trans
      (le_iSup (fun adv' => expectedStepsWithinAdv w adv' p (N + 1) cfg) (adv.shift 1))

theorem expectedStepsFromAdv_running (w : ℕ) (adv : RAdv r) (p : RProgram B r) (s : RState r) :
    expectedStepsFromAdv w adv p (.running s) =
      1 + ProbComp.expect (stepRandResizable w (adv 0) p (.running s))
        (expectedStepsFromAdv w (adv.shift 1) p) := by
  let g : ℕ → ℝ≥0∞ := fun t =>
    (runRandResizable w adv p t (.running s)).eval.toOuterMeasure (RCfg.runningSet r)
  have hsplit : ∑' t : ℕ, g t = g 0 + ∑' t : ℕ, g (t + 1) := by
    rw [tsum_eq_add_tsum_ite (f := g) 0]
    congr 1
    have hsh := Function.Injective.tsum_eq Nat.succ_injective
      (f := fun t => if t = 0 then 0 else g t) fun t ht => by
        cases t with
        | zero => simp at ht
        | succ k => exact ⟨k, rfl⟩
    exact (tsum_congr fun x => by split_ifs <;> rfl).trans hsh.symm
  change ∑' t : ℕ, g t = _
  rw [hsplit]
  have hzero : g 0 = 1 := by simp [g, RCfg.runningSet, PMF.toOuterMeasure_pure_apply]
  rw [hzero]
  congr 1
  have hsucc : ∀ t : ℕ, g (t + 1) =
      ∑' cfg, (stepRandResizable w (adv 0) p (.running s)).eval cfg *
        (runRandResizable w (adv.shift 1) p t cfg).eval.toOuterMeasure (RCfg.runningSet r) := by
    intro t
    simp only [g, runRandResizable_succ, ProbComp.eval_bind, PMF.toOuterMeasure_bind_apply]
  simp only [hsucc, ProbComp.expect, expectedStepsFromAdv]
  rw [tsum_comm]
  refine tsum_congr fun cfg => by rw [ENNReal.tsum_mul_left]

/-- **Flat Resizable Word RAM Distributional Execution (`ExecRProgramDist`).**
Starting at `⟨0, x⟩` at word width `w`, `p : RProgram B r` with output register `out : Fin r`:
1. never faults under any adaptive adversary (`RDemonicFaultFree`),
2. keeps the active hardware frontier `≤ L_peak` at every step (`PeakFrontierLe`),
3. runs in at most `T` expected instructions (`expectedTimeDemonic w p ⟨0, x⟩ ≤ T`), and
4. reaches halting distribution `μ : PMF (RData r)` across every adaptive adversary `adv`. -/
structure ExecRProgramDist (w : ℕ) (p : RProgram B r) (out : Fin r) (x : RData r)
    (μ : PMF (RData r)) (T : ℝ≥0∞) (L_peak : ℕ) : Prop where
  /-- Zero faults across all adaptive adversaries and horizons. -/
  faultFree : RDemonicFaultFree w p ⟨0, x⟩
  /-- Hardware frontier stays `≤ L_peak` across all adaptive adversaries and horizons. -/
  peakFrontierLe : PeakFrontierLe w L_peak p ⟨0, x⟩
  /-- Supremum expected step count is at most `T`. -/
  expectedTime_le : expectedTimeDemonic w p ⟨0, x⟩ ≤ T
  /-- Every state `y` is reached at `.halted (y.regs out) y` with probability at least `μ y`. -/
  halted_le : ∀ (adv : RAdv r) (y : RData r),
    μ y ≤ ⨆ t : ℕ, evalRandDemonic w adv p t ⟨0, x⟩ (.halted (y.regs out) y)

namespace ExecRProgramDist

theorem mono {w L₁ L₂ : ℕ} {p : RProgram B r} {out : Fin r} {x : RData r}
    {μ : PMF (RData r)} {T₁ T₂ : ℝ≥0∞}
    (h : ExecRProgramDist w p out x μ T₁ L₁) (hT : T₁ ≤ T₂) (hL : L₁ ≤ L₂) :
    ExecRProgramDist w p out x μ T₂ L₂ :=
  ⟨h.faultFree, h.peakFrontierLe.mono hL, h.expectedTime_le.trans hT, h.halted_le⟩

/-- `ExecRProgramDist` implies `AlmostSurelyHaltsDemonic` and pins the exact limiting halting
probability of every `y : RData r` to `μ y` under every adaptive adversary `adv : RAdv r`. -/
theorem iSup_evalRandDemonic_halted_eq {w L_peak : ℕ} {p : RProgram B r} {out : Fin r}
    {x : RData r} {μ : PMF (RData r)} {T : ℝ≥0∞}
    (h : ExecRProgramDist w p out x μ T L_peak) (adv : RAdv r) (y₀ : RData r) :
    (⨆ t : ℕ, evalRandDemonic w adv p t ⟨0, x⟩ (.halted (y₀.regs out) y₀)) = μ y₀ := by
  classical
  let emb : RData r → RCfg r := fun y => .halted (y.regs out) y
  have hemb : Function.Injective emb := fun _ _ heq => by injection heq with _ hy
  let g : RCfg r → ℝ≥0∞ := fun cfg => ⨆ t : ℕ, evalRandDemonic w adv p t ⟨0, x⟩ cfg
  let f : RData r → ℝ≥0∞ := fun y => g (emb y)
  have htsum_f : ∑' y, f y ≤ 1 := by
    have hind_mono : ∀ cfg : RCfg r, Monotone fun t =>
        Set.indicator (RCfg.haltedSet r) (evalRandDemonic w adv p t ⟨0, x⟩) cfg := by
      intro cfg t₁ t₂ ht
      dsimp only
      by_cases hmem : cfg ∈ RCfg.haltedSet r
      · have hmem' := hmem
        obtain ⟨v, d, rfl⟩ := hmem
        rw [Set.indicator_of_mem hmem', Set.indicator_of_mem hmem']
        exact evalRandDemonic_halted_mono w adv p ⟨0, x⟩ v d ht
      · simp [Set.indicator_of_notMem hmem]
    have hcfg_sum : (∑' cfg, ⨆ t : ℕ,
        Set.indicator (RCfg.haltedSet r) (evalRandDemonic w adv p t ⟨0, x⟩) cfg) ≤ 1 := by
      rw [ENNReal.tsum_iSup_of_monotone hind_mono]
      refine iSup_le fun t => ?_
      rw [← PMF.toOuterMeasure_apply]
      exact Cslib.Probability.PMF.toOuterMeasure_le_one _ _
    refine (tsum_eq_iSup_sum.trans_le (iSup_le fun s => ?_)).trans hcfg_sum
    have himg : (∑ y ∈ s, f y) = ∑ cfg ∈ s.image emb, g cfg :=
      (Finset.sum_image (f := g) fun _ _ _ _ h' => hemb h').symm
    rw [himg]
    let g_ind : RCfg r → ℝ≥0∞ := fun c =>
      ⨆ t : ℕ, Set.indicator (RCfg.haltedSet r) (evalRandDemonic w adv p t ⟨0, x⟩) c
    refine (Finset.sum_le_sum (g := g_ind) fun cfg hcfg => ?_).trans (sum_le_tsum _)
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hcfg
    refine iSup_mono fun t => le_of_eq ?_
    have hmem_y : emb y ∈ RCfg.haltedSet r := ⟨y.regs out, y, rfl⟩
    exact (Set.indicator_of_mem hmem_y _).symm
  refine le_antisymm ?_ (h.halted_le adv y₀)
  set rest_μ := ∑' y, if y = y₀ then (0 : ℝ≥0∞) else μ y
  set rest_f := ∑' y, if y = y₀ then (0 : ℝ≥0∞) else f y
  have hμ_split : μ y₀ + rest_μ = 1 :=
    (tsum_eq_add_tsum_ite (f := μ) y₀).symm.trans μ.tsum_coe
  have hf_split : f y₀ + rest_f ≤ 1 :=
    (tsum_eq_add_tsum_ite (f := f) y₀).symm.trans_le htsum_f
  have hrest_le : rest_μ ≤ rest_f := tsum_le_tsum fun y => by
    split_ifs
    · exact le_rfl
    · exact h.halted_le adv y
  have hrest_ne_top : rest_μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq hμ_split)
  exact (ENNReal.add_le_add_iff_right hrest_ne_top).mp
    ((add_le_add le_rfl hrest_le).trans (hf_split.trans_eq hμ_split.symm))

/-- Every `ExecRProgramDist` halts almost surely under every adaptive adversary. -/
theorem almostSurelyHaltsDemonic {w L_peak : ℕ} {p : RProgram B r} {out : Fin r}
    {x : RData r} {μ : PMF (RData r)} {T : ℝ≥0∞}
    (h : ExecRProgramDist w p out x μ T L_peak) :
    AlmostSurelyHaltsDemonic w p ⟨0, x⟩ := by
  classical
  refine ⟨h.faultFree, fun adv => le_antisymm
    (iSup_le fun _ => Cslib.Probability.PMF.toOuterMeasure_le_one _ _) ?_⟩
  let emb : RData r → RCfg r := fun y => .halted (y.regs out) y
  have hemb : Function.Injective emb := fun _ _ heq => by injection heq with _ hy
  let g_ind : RCfg r → ℝ≥0∞ := fun cfg =>
    ⨆ t : ℕ, Set.indicator (RCfg.haltedSet r) (evalRandDemonic w adv p t ⟨0, x⟩) cfg
  have hind_mono : ∀ cfg : RCfg r, Monotone fun t =>
      Set.indicator (RCfg.haltedSet r) (evalRandDemonic w adv p t ⟨0, x⟩) cfg := by
    intro cfg t₁ t₂ ht
    dsimp only
    by_cases hmem : cfg ∈ RCfg.haltedSet r
    · have hmem' := hmem
      obtain ⟨v, d, rfl⟩ := hmem
      rw [Set.indicator_of_mem hmem', Set.indicator_of_mem hmem']
      exact evalRandDemonic_halted_mono w adv p ⟨0, x⟩ v d ht
    · simp [Set.indicator_of_notMem hmem]
  simp_rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_iSup_of_monotone hind_mono]
  rw [← μ.tsum_coe, tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc
    (∑ y ∈ s, μ y)
      ≤ ∑ y ∈ s, g_ind (emb y) := by
        refine Finset.sum_le_sum fun y _ => (h.halted_le adv y).trans (iSup_mono fun t => ?_)
        have hmem_y : emb y ∈ RCfg.haltedSet r := ⟨y.regs out, y, rfl⟩
        rw [Set.indicator_of_mem hmem_y]
    _ = ∑ cfg ∈ s.image emb, g_ind cfg :=
        (Finset.sum_image (f := g_ind) fun _ _ _ _ h' => hemb h').symm
    _ ≤ ∑' cfg, g_ind cfg := sum_le_tsum _

end ExecRProgramDist

/-- **Soundness Check (`not_execRProgramDist_halt`).**
A 1-instruction `[.halt out]` stub cannot satisfy `ExecRProgramDist` for any target distribution
`μ` whose support contains a state `y ≠ x`. -/
theorem not_execRProgramDist_halt {w L_peak : ℕ} {out : Fin r} {x y : RData r}
    {μ : PMF (RData r)} {T : ℝ≥0∞} (hy : y ∈ μ.support) (hne : y ≠ x) :
    ¬ExecRProgramDist (B := B) w [.halt out] out x μ T L_peak := by
  intro h
  have hle := h.halted_le (fun _ _ _ => 0) y
  have hzero : (⨆ t : ℕ, evalRandDemonic (B := B) w (fun _ _ _ => 0) [.halt out] t ⟨0, x⟩
      (.halted (y.regs out) y)) ≤ 0 := by
    refine iSup_le fun t => le_of_eq ?_
    cases t with
    | zero => simp [evalRandDemonic, PMF.pure_apply]
    | succ k =>
      have hhalt : ([RInstr.halt out] : RProgram B r)[0]? = some (.halt out) := rfl
      rw [evalRandDemonic, runRandResizable_succ, stepRandResizable_halt (s := ⟨0, x⟩) hhalt,
        pure_bind, runRandResizable_halted, ProbComp.eval_pure]
      have hcfg_ne : RCfg.halted (y.regs out) y ≠ RCfg.halted (x.regs out) x := fun heq => by
        injection heq with _ hyx; exact hne hyx
      exact PMF.pure_apply_of_ne _ _ hcfg_ne
  exact (PMF.mem_support_iff _ _).mp hy (nonpos_iff_eq_zero.mp (hle.trans hzero))


/-- Every `evalResizable` step leaves the hardware word frontier unchanged. -/
theorem evalResizable_frontier_eq {w : ℕ} {o : Op B r} {x y : RData r}
    (he : evalResizable w o x = some y) : y.frontier = x.frontier := by
  cases o with
  | const d v =>
    dsimp only [evalResizable, RData.put] at he
    split_ifs at he with hf; injection he with hy; subst hy; rfl
  | copy d s => injection he with hy; subst hy; rfl
  | alu f d args =>
    dsimp only [evalResizable] at he
    obtain ⟨_, _, hput⟩ := Option.bind_eq_some_iff.mp he
    dsimp only [RData.put] at hput
    split_ifs at hput with hf; injection hput with hy; subst hy; rfl
  | load d a | store a d =>
    dsimp only [evalResizable] at he
    split_ifs at he with hlt; injection he with hy; subst hy; rfl

/-- Every `RDemonicExec w L_peak c x n P` witnesses at least one reachable post-state `y`
satisfying `P y` and `y.frontier ≤ L_peak`. -/
theorem RDemonicExec.exists_post_frontier_le {w L_peak n : ℕ} {c : RCode B r} {x : RData r}
    {P : RData r → Prop} (h : RDemonicExec w L_peak c x n P) :
    ∃ y, P y ∧ y.frontier ≤ L_peak := by
  induction h with
  | op hL he hp => exact ⟨_, hp, (evalResizable_frontier_eq he).trans_le hL⟩
  | @grow dst kReg x P hL _ hp =>
    exact ⟨_, hp _ (demonicGrow_advGrowMem w (fun _ => 0) x.frontier (x.regs kReg) x.mem), hL⟩
  | shrink hL _ hp => exact ⟨_, hp, Nat.sub_le _ _ |>.trans hL⟩
  | rand hL _ hp => exact ⟨_, hp 0 (Nat.zero_le _), hL⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨y₁, hy₁, _⟩ := ih₁
    exact ih₂ y₁ hy₁
  | branch_pos _ _ ih | branch_neg _ _ ih | loop_iter _ _ _ ihb ihl =>
    first | exact ih | (obtain ⟨y₁, hy₁, _⟩ := ihb; exact ihl y₁ hy₁)
  | loop_exit hL _ hp => exact ⟨_, hp, hL⟩
  | mono _ _ hPQ ih =>
    obtain ⟨y, hy, hfr⟩ := ih
    exact ⟨y, hPQ y hy, hfr⟩


/-! ## Compilation of `RDemonicExec` and `ExecRCodeDist` to flat `RProgram` -/

/-- Horizon-bounded non-faulting and `≤ L_peak` frontier invariant on `evalRandDemonic`. -/
def DemonicSafeWithin (w L_peak T_hor : ℕ) (p : RProgram B r) (s : RState r) : Prop :=
  ∀ (adv : RAdv r), ∀ t ≤ T_hor, ∀ cfg ∈ (evalRandDemonic w adv p t s).support,
    cfg.SafeBounded L_peak

theorem DemonicSafeWithin.anti {w L_peak T₁ T₂ : ℕ} {p : RProgram B r} {s : RState r}
    (hT : T₁ ≤ T₂) (h : DemonicSafeWithin w L_peak T₂ p s) :
    DemonicSafeWithin w L_peak T₁ p s :=
  fun adv t ht => h adv t (ht.trans hT)

theorem DemonicSafeWithin.mono_peak {w L₁ L₂ T_hor : ℕ} {p : RProgram B r} {s : RState r}
    (hL : L₁ ≤ L₂) (h : DemonicSafeWithin w L₁ T_hor p s) :
    DemonicSafeWithin w L₂ T_hor p s :=
  fun adv t ht cfg hcfg => (h adv t ht cfg hcfg).mono hL

theorem DemonicSafeWithin.frontier_le {w L_peak T_hor : ℕ} {p : RProgram B r} {s : RState r}
    (h : DemonicSafeWithin w L_peak T_hor p s) : s.data.frontier ≤ L_peak :=
  h (fun _ _ _ => 0) 0 (Nat.zero_le _) (.running s) (by simp [evalRandDemonic])

theorem demonicSafeWithin_of_pure {w L_peak T_hor : ℕ} {p : RProgram B r}
    {s : RState r} {s' : (RState r → ℕ → ℕ) → RState r} (hfr : s.data.frontier ≤ L_peak)
    (hstep : ∀ f, stepRandResizable w f p (.running s) = pure (.running (s' f)))
    (hnext : ∀ f k, k + 1 ≤ T_hor → DemonicSafeWithin w L_peak k p (s' f)) :
    DemonicSafeWithin w L_peak T_hor p s := by
  intro adv t ht cfg hcfg
  cases t with
  | zero =>
    rw [evalRandDemonic, runRandResizable_zero, ProbComp.eval_pure,
      PMF.support_pure, Set.mem_singleton_iff] at hcfg
    subst hcfg; exact hfr
  | succ k =>
    rw [evalRandDemonic, runRandResizable_succ, hstep (adv 0), pure_bind] at hcfg
    exact hnext (adv 0) k ht (adv.shift 1) k le_rfl cfg hcfg

theorem demonicSafeWithin_of_rand {w L_peak T_hor : ℕ} {p : RProgram B r}
    {pc : ℕ} {x : RData r} {dst src : Fin r} (hfr : x.frontier ≤ L_peak)
    (hp : p[pc]? = some (.rand dst src)) (hfit : Fits w (x.regs src))
    (hnext : ∀ (j : Fin (x.regs src + 1)) (k : ℕ), k + 1 ≤ T_hor →
      DemonicSafeWithin w L_peak k p ⟨pc + 1, x.set dst j.val⟩) :
    DemonicSafeWithin w L_peak T_hor p ⟨pc, x⟩ := by
  intro adv t ht cfg hcfg
  cases t with
  | zero =>
    rw [evalRandDemonic, runRandResizable_zero, ProbComp.eval_pure,
      PMF.support_pure, Set.mem_singleton_iff] at hcfg
    subst hcfg; exact hfr
  | succ k =>
    rw [evalRandDemonic, runRandResizable_succ,
      stepRandResizable_rand_of_fits (s := ⟨pc, x⟩) hp hfit,
      bind_assoc, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hcfg
    obtain ⟨j, _, hcfg'⟩ := hcfg
    rw [pure_bind] at hcfg'
    exact hnext j k ht (adv.shift 1) k le_rfl cfg hcfg'

theorem supExpectedStepsWithin_le_of_pure {w N : ℕ} {p : RProgram B r}
    {s : RState r} {s' : (RState r → ℕ → ℕ) → RState r}
    (hstep : ∀ f, stepRandResizable w f p (.running s) = pure (.running (s' f))) :
    supExpectedStepsWithin w p N (.running s) ≤
      1 + ⨆ f, supExpectedStepsWithin w p N (.running (s' f)) := by
  refine iSup_le fun adv => (expectedStepsWithinAdv_running_le w adv p N s).trans ?_
  rw [hstep (adv 0), ProbComp.expect_pure]
  exact add_le_add le_rfl
    (le_iSup (fun f => supExpectedStepsWithin w p N (.running (s' f))) (adv 0))

theorem supExpectedStepsWithin_le_of_const {w N : ℕ} {p : RProgram B r}
    {s s₁ : RState r}
    (hstep : ∀ f, stepRandResizable w f p (.running s) = pure (.running s₁)) :
    supExpectedStepsWithin w p N (.running s) ≤
      1 + supExpectedStepsWithin w p N (.running s₁) := by
  refine (supExpectedStepsWithin_le_of_pure hstep).trans ?_
  exact add_le_add le_rfl (iSup_le fun _ => le_rfl)

/-- Worst-case-adversary supremum halting probability at `.halted v d` from `⟨pc, y⟩`. -/
noncomputable def haltedReach (w : ℕ) (p : RProgram B r) (v : ℕ) (d : RData r)
    (pc : ℕ) (y : RData r) : ℝ≥0∞ :=
  ⨅ adv : RAdv r, ⨆ T_hor : ℕ, evalRandDemonic w adv p T_hor ⟨pc, y⟩ (.halted v d)

theorem haltedReach_le_of_pure {w v : ℕ} {p : RProgram B r} {d : RData r}
    {s : RState r} {s' : (RState r → ℕ → ℕ) → RState r}
    (hstep : ∀ f, stepRandResizable w f p (.running s) = pure (.running (s' f))) :
    (⨅ f, haltedReach w p v d (s' f).pc (s' f).data) ≤ haltedReach w p v d s.pc s.data := by
  refine le_iInf fun adv => ?_
  refine (iInf_le _ (adv 0)).trans ((iInf_le _ (adv.shift 1)).trans ?_)
  exact iSup_evalRandDemonic_halted_le_of_step (hstep (adv 0)) v d

theorem haltedReach_le_of_const {w v : ℕ} {p : RProgram B r} {d : RData r}
    {s s₁ : RState r}
    (hstep : ∀ f, stepRandResizable w f p (.running s) = pure (.running s₁)) :
    haltedReach w p v d s₁.pc s₁.data ≤ haltedReach w p v d s.pc s.data :=
  (le_iInf fun _ => le_rfl).trans (haltedReach_le_of_pure hstep)

theorem haltedReach_le_of_rand {w v pc : ℕ} {p : RProgram B r} {d x : RData r}
    {dst src : Fin r} (hp : p[pc]? = some (.rand dst src)) (hfit : Fits w (x.regs src)) :
    (∑' k : Fin (x.regs src + 1), (ProbComp.unifFin (x.regs src)).eval k *
      haltedReach w p v d (pc + 1) (x.set dst k.val)) ≤
      haltedReach w p v d pc x := by
  refine le_iInf fun adv => ?_
  have hstep_sum : ∀ T_hor : ℕ,
      (∑' k : Fin (x.regs src + 1), (ProbComp.unifFin (x.regs src)).eval k *
        evalRandDemonic w (adv.shift 1) p T_hor ⟨pc + 1, x.set dst k.val⟩ (.halted v d)) =
        evalRandDemonic w adv p (T_hor + 1) ⟨pc, x⟩ (.halted v d) := fun T_hor => by
    simp only [evalRandDemonic, runRandResizable_succ,
      stepRandResizable_rand_of_fits (s := ⟨pc, x⟩) hp hfit, bind_assoc, pure_bind,
      ProbComp.eval_bind, PMF.bind_apply]
  calc
    (∑' k, (ProbComp.unifFin (x.regs src)).eval k *
        haltedReach w p v d (pc + 1) (x.set dst k.val))
      ≤ ∑' k, (ProbComp.unifFin (x.regs src)).eval k *
          ⨆ T_hor : ℕ, evalRandDemonic w (adv.shift 1) p T_hor
            ⟨pc + 1, x.set dst k.val⟩ (.halted v d) :=
        tsum_le_tsum fun k => mul_le_mul_right (iInf_le _ (adv.shift 1)) _
    _ = ⨆ T_hor : ℕ, ∑' k, (ProbComp.unifFin (x.regs src)).eval k *
          evalRandDemonic w (adv.shift 1) p T_hor ⟨pc + 1, x.set dst k.val⟩ (.halted v d) := by
        simp_rw [ENNReal.mul_iSup]
        exact ENNReal.tsum_iSup_of_monotone fun k _ _ hT =>
          mul_le_mul_right (evalRandDemonic_halted_mono w (adv.shift 1) p _ v d hT) _
    _ = ⨆ T_hor : ℕ, evalRandDemonic w adv p (T_hor + 1) ⟨pc, x⟩ (.halted v d) := by
        simp_rw [hstep_sum]
    _ ≤ ⨆ T_hor : ℕ, evalRandDemonic w adv p T_hor ⟨pc, x⟩ (.halted v d) :=
        iSup_le fun T_hor => le_iSup
          (fun t => evalRandDemonic w adv p t ⟨pc, x⟩ (.halted v d)) (T_hor + 1)

theorem RDemonicExec.supExpectedStepsWithin_assemble {w L_peak n pc N : ℕ} {c : RCode B r}
    {x : RData r} {P : RData r → Prop} (h : RDemonicExec w L_peak c x n P) {p : RProgram B r}
    (hp : p.Contains pc (c.assemble pc)) :
    supExpectedStepsWithin w p N (.running ⟨pc, x⟩) ≤
      (n : ℝ≥0∞) + ⨆ (y : RData r) (_ : P y),
        supExpectedStepsWithin w p N (.running ⟨pc + c.size, y⟩) := by
  induction h generalizing pc with
  | @op o x y P _ he hp_y =>
    refine (supExpectedStepsWithin_le_of_const fun f =>
      stepRandResizable_op (s := ⟨pc, x⟩) hp.head he).trans ?_
    simp only [RCode.size, Nat.cast_one]
    exact add_le_add le_rfl (le_iSup₂_of_le y hp_y le_rfl)
  | @grow dst kReg x P _ hfit hp_y =>
    refine (supExpectedStepsWithin_le_of_pure fun f =>
      stepRandResizable_grow_of_fits (s := ⟨pc, x⟩) hp.head hfit).trans ?_
    simp only [RCode.size, Nat.cast_one]
    refine add_le_add le_rfl (iSup_le fun f => ?_)
    exact le_iSup₂_of_le _ (hp_y _ (demonicGrow_advGrowMem w (f ⟨pc, x⟩) _ _ _)) le_rfl
  | @shrink kReg x P _ hk hp_y =>
    refine (supExpectedStepsWithin_le_of_const fun f =>
      stepRandResizable_shrink_of_le (s := ⟨pc, x⟩) hp.head hk).trans ?_
    simp only [RCode.size, Nat.cast_one]
    exact add_le_add le_rfl (le_iSup₂_of_le _ hp_y le_rfl)
  | @rand dst src x P _ hfit hp_y =>
    refine iSup_le fun adv => (expectedStepsWithinAdv_running_le w adv p N ⟨pc, x⟩).trans ?_
    rw [stepRandResizable_rand_of_fits (s := ⟨pc, x⟩) hp.head hfit, ProbComp.expect_bind]
    simp only [ProbComp.expect_pure, RCode.size, Nat.cast_one]
    refine add_le_add le_rfl ?_
    set B_sup := ⨆ (y : RData r) (_ : P y),
      supExpectedStepsWithin w p N (.running ⟨pc + 1, y⟩)
    refine (ProbComp.expect_mono (g := fun _ => B_sup) fun k : Fin (x.regs src + 1) =>
      le_iSup₂_of_le (x.set dst k.val) (hp_y k.val (Nat.lt_succ_iff.mp k.isLt)) le_rfl).trans ?_
    rw [ProbComp.expect_const]
  | @seq c₁ c₂ x T₁ T₂ Q P _ _ ih₁ ih₂ =>
    have hc₂ : p.Contains (pc + c₁.size) (c₂.assemble (pc + c₁.size)) := by
      simpa [RCode.length_assemble] using hp.append_right
    refine (ih₁ hp.append_left).trans ?_
    rw [Nat.cast_add, add_assoc]
    refine add_le_add le_rfl (iSup₂_le fun y₁ hy₁ => (ih₂ y₁ hy₁ hc₂).trans ?_)
    simp only [RCode.size, Nat.add_assoc]
    exact le_rfl
  | @branch_pos c pos neg x T P hc _ ih =>
    have hbr : p[pc]? = some (.branch c (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
    rw [RCode.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'
    refine (supExpectedStepsWithin_le_of_const fun _ =>
      stepRandResizable_branch_pos (s := ⟨pc, x⟩) hbr hc).trans ?_
    refine (add_le_add le_rfl (ih hc')).trans (le_of_eq ?_)
    simp only [RCode.size, Nat.cast_add, Nat.cast_one,
      show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
    ac_rfl
  | @branch_neg c pos neg x T P hc _ ih =>
    have hbr : p[pc]? = some (.branch c (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hj : p[pc + 1 + neg.size]? = some (.jump (pc + neg.size + pos.size + 2)) := by
      simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head
    refine (supExpectedStepsWithin_le_of_const fun _ =>
      stepRandResizable_branch_neg (s := ⟨pc, x⟩) hbr hc).trans ?_
    refine (add_le_add le_rfl (ih hp.cons_tail.append_left)).trans ?_
    have hj_le : (⨆ (y : RData r) (_ : P y),
        supExpectedStepsWithin w p N (.running ⟨pc + 1 + neg.size, y⟩)) ≤
        1 + ⨆ (y : RData r) (_ : P y),
          supExpectedStepsWithin w p N (.running ⟨pc + (neg.size + pos.size + 2), y⟩) := by
      refine iSup₂_le fun y hy => ?_
      refine (supExpectedStepsWithin_le_of_const fun f =>
        stepRandResizable_jump (s := ⟨pc + 1 + neg.size, y⟩) hj).trans ?_
      rw [show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
      exact add_le_add le_rfl (le_iSup₂_of_le y hy le_rfl)
    calc
      1 + ((T : ℝ≥0∞) + ⨆ (y : RData r) (_ : P y),
          supExpectedStepsWithin w p N (.running ⟨pc + 1 + neg.size, y⟩))
        ≤ 1 + ((T : ℝ≥0∞) + (1 + ⨆ (y : RData r) (_ : P y),
            supExpectedStepsWithin w p N (.running ⟨pc + (neg.size + pos.size + 2), y⟩))) :=
          add_le_add le_rfl (add_le_add le_rfl hj_le)
      _ = ((T + 2 : ℕ) : ℝ≥0∞) + ⨆ (y : RData r) (_ : P y),
            supExpectedStepsWithin w p N (.running ⟨pc + (RCode.branch c pos neg).size, y⟩) := by
          simp only [RCode.size, Nat.cast_add, Nat.cast_ofNat]
          rw [show (2 : ℝ≥0∞) = 1 + 1 from one_add_one_eq_two.symm]
          ac_rfl
  | @loop_exit c body x P _ hc hp_y =>
    have hj : p[pc + 1]? = some (.jump (pc + body.size + 3)) := hp.cons_tail.head
    refine (supExpectedStepsWithin_le_of_const fun _ =>
      stepRandResizable_branch_neg (s := ⟨pc, x⟩) hp.head hc).trans ?_
    refine (add_le_add le_rfl (supExpectedStepsWithin_le_of_const fun f =>
      stepRandResizable_jump (s := ⟨pc + 1, x⟩) hj)).trans ?_
    rw [← add_assoc (1 : ℝ≥0∞), one_add_one_eq_two,
      show pc + body.size + 3 = pc + (RCode.loop c body).size by simp [RCode.size]; omega]
    exact add_le_add (by norm_num) (le_iSup₂_of_le x hp_y le_rfl)
  | @loop_iter c body x T₁ T₂ Q P hc _ _ ihb ihl =>
    have hbody_c : p.Contains (pc + 2) (body.assemble (pc + 2)) := by
      simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left
    have hj_back : p[pc + 2 + body.size]? = some (.jump pc) := by
      simpa using hp.cons_tail.cons_tail.append_right.head
    refine (supExpectedStepsWithin_le_of_const fun _ =>
      stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.head hc).trans ?_
    refine (add_le_add le_rfl (ihb hbody_c)).trans ?_
    have hback : (⨆ (y : RData r) (_ : Q y),
        supExpectedStepsWithin w p N (.running ⟨pc + 2 + body.size, y⟩)) ≤
        1 + ((T₂ : ℝ≥0∞) + ⨆ (z : RData r) (_ : P z),
          supExpectedStepsWithin w p N (.running ⟨pc + (RCode.loop c body).size, z⟩)) := by
      refine iSup₂_le fun y hy => ?_
      refine (supExpectedStepsWithin_le_of_const fun f =>
        stepRandResizable_jump (s := ⟨pc + 2 + body.size, y⟩) hj_back).trans ?_
      exact add_le_add le_rfl (ihl y hy hp)
    calc
      1 + ((T₁ : ℝ≥0∞) + ⨆ (y : RData r) (_ : Q y),
          supExpectedStepsWithin w p N (.running ⟨pc + 2 + body.size, y⟩))
        ≤ 1 + ((T₁ : ℝ≥0∞) + (1 + ((T₂ : ℝ≥0∞) + ⨆ (z : RData r) (_ : P z),
            supExpectedStepsWithin w p N (.running ⟨pc + (RCode.loop c body).size, z⟩)))) :=
          add_le_add le_rfl (add_le_add le_rfl hback)
      _ = ((T₁ + 2 + T₂ : ℕ) : ℝ≥0∞) + ⨆ (z : RData r) (_ : P z),
            supExpectedStepsWithin w p N (.running ⟨pc + (RCode.loop c body).size, z⟩) := by
          simp only [Nat.cast_add, Nat.cast_ofNat]
          rw [show (2 : ℝ≥0∞) = 1 + 1 from one_add_one_eq_two.symm]
          ac_rfl
  | mono _ hT hPQ ih =>
    refine (ih hp).trans (add_le_add (Nat.cast_le.mpr hT) ?_)
    exact iSup₂_le fun y hy => le_iSup₂_of_le y (hPQ y hy) le_rfl

theorem RDemonicExec.demonicSafeWithin_assemble {w L_peak n pc T_hor : ℕ} {c : RCode B r}
    {x : RData r} {P : RData r → Prop} (h : RDemonicExec w L_peak c x n P) {p : RProgram B r}
    (hp : p.Contains pc (c.assemble pc))
    (hcont : ∀ y, P y → DemonicSafeWithin w L_peak T_hor p ⟨pc + c.size, y⟩) :
    DemonicSafeWithin w L_peak T_hor p ⟨pc, x⟩ := by
  induction h generalizing pc T_hor with
  | @op o x y P hL he hp_y =>
    exact demonicSafeWithin_of_pure hL
      (fun _ => stepRandResizable_op (s := ⟨pc, x⟩) hp.head he)
      fun _ k hk => (hcont y hp_y).anti (by omega)
  | @grow dst kReg x P hL hfit hp_y =>
    exact demonicSafeWithin_of_pure (s := ⟨pc, x⟩) (by dsimp only; omega)
      (fun f => stepRandResizable_grow_of_fits (s := ⟨pc, x⟩) hp.head hfit)
      fun f k hk => (hcont _ (hp_y _ (demonicGrow_advGrowMem w (f ⟨pc, x⟩) _ _ _))).anti (by omega)
  | @shrink kReg x P hL hk hp_y =>
    exact demonicSafeWithin_of_pure hL
      (fun _ => stepRandResizable_shrink_of_le (s := ⟨pc, x⟩) hp.head hk)
      fun _ k hk' => (hcont _ hp_y).anti (by omega)
  | @rand dst src x P hL hfit hp_y =>
    exact demonicSafeWithin_of_rand hL hp.head hfit fun j k hk =>
      (hcont _ (hp_y j.val (Nat.lt_succ_iff.mp j.isLt))).anti (by omega)
  | @seq c₁ c₂ x _ _ Q P _ _ ih₁ ih₂ =>
    have hc₂ : p.Contains (pc + c₁.size) (c₂.assemble (pc + c₁.size)) := by
      simpa [RCode.length_assemble] using hp.append_right
    exact ih₁ hp.append_left fun y₁ hy₁ => ih₂ y₁ hy₁ hc₂ fun y₂ hy₂ => by
      simpa [RCode.size, Nat.add_assoc] using hcont y₂ hy₂
  | @branch_pos c pos neg x _ P hc hpos ih =>
    have hbr : p[pc]? = some (.branch c (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
    rw [RCode.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'
    refine demonicSafeWithin_of_pure hpos.frontier_le
      (fun _ => stepRandResizable_branch_pos (s := ⟨pc, x⟩) hbr hc)
      fun _ k hk => ih hc' fun y hy => ?_
    simpa [RCode.size, show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
      using (hcont y hy).anti (by omega)
  | @branch_neg c pos neg x _ P hc hneg ih =>
    have hbr : p[pc]? = some (.branch c (pc + neg.size + 2)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.head
    have hj : p[pc + 1 + neg.size]? = some (.jump (pc + neg.size + pos.size + 2)) := by
      simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head
    refine demonicSafeWithin_of_pure hneg.frontier_le
      (fun _ => stepRandResizable_branch_neg (s := ⟨pc, x⟩) hbr hc)
      fun _ k hk => ih hp.cons_tail.append_left fun y hy => ?_
    have hy_fr := (hcont y hy).frontier_le
    refine demonicSafeWithin_of_pure hy_fr
      (fun _ => stepRandResizable_jump (s := ⟨pc + 1 + neg.size, y⟩) hj) fun _ k' hk' => ?_
    simpa [RCode.size, show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
      using (hcont y hy).anti (by omega)
  | @loop_exit c body x P hL hc hp_y =>
    have hj : p[pc + 1]? = some (.jump (pc + body.size + 3)) := hp.cons_tail.head
    refine demonicSafeWithin_of_pure hL
      (fun _ => stepRandResizable_branch_neg (s := ⟨pc, x⟩) hp.head hc)
      fun _ k hk => demonicSafeWithin_of_pure hL
        (fun _ => stepRandResizable_jump (s := ⟨pc + 1, x⟩) hj) fun _ k' hk' => ?_
    simpa [RCode.size, show pc + body.size + 3 = pc + (body.size + 3) by omega]
      using (hcont x hp_y).anti (by omega)
  | @loop_iter c body x _ _ Q P hc hbody hloop ihb ihl =>
    have hbody_c : p.Contains (pc + 2) (body.assemble (pc + 2)) := by
      simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left
    have hj_back : p[pc + 2 + body.size]? = some (.jump pc) := by
      simpa using hp.cons_tail.cons_tail.append_right.head
    refine demonicSafeWithin_of_pure hbody.frontier_le
      (fun _ => stepRandResizable_branch_pos (s := ⟨pc, x⟩) hp.head hc)
      fun _ k hk => ihb hbody_c fun y hy => ?_
    refine demonicSafeWithin_of_pure (hloop y hy).frontier_le
      (fun _ => stepRandResizable_jump (s := ⟨pc + 2 + body.size, y⟩) hj_back)
      fun _ k' hk' => ihl y hy hp fun z hz => (hcont z hz).anti (by omega)
  | mono _ _ hPQ ih => exact ih hp fun y hy => hcont y (hPQ y hy)


end Cslib.WordRAM.Resizable
