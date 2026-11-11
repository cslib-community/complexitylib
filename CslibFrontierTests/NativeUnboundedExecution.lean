/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Probabilistic.NativeUnboundedExecution
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# A native selector with no uniformly sufficient instruction clock

A genuine native fair-coin loop waits for heads, queries a stateful oracle, and
halts with its raw proposed bit. The reply, cost and duration are correlated.
Every finite clock leaves positive live mass, but the unbounded stopped law is
derived and has no divergence. A second actual machine diverges surely.
-/

noncomputable section
open Cslib Cslib.Probability Turing
open Turing.MultiTapeMachine (Config Channel)
open NativeOpenExecution
open scoped NNReal ENNReal
namespace CslibFrontierTests.NativeUnboundedExecution

inductive Control | wait | finish deriving DecidableEq

instance : Fintype Control := ⟨{.wait, .finish}, by intro c; cases c <;> simp⟩

def action (next : Option Control) (output : Option Bool := none) : Turing.Action 0 Bool Control :=
  { inputTape := 0, workTapes := Fin.elim0, output, state := next }

/-- Private local waiting has no oracle bill and is excluded from external time. -/
def machine : MultiTapePTM 0 Bool Control Unit where
  initial := .wait
  tr control _ _ answer bit := match control with
    | .wait => if bit then .query () .finish else
        .step (action (some .wait)) (fun _ => none) (fun _ => 0)
    | .finish => .step (action none (answer ())) (fun _ => none) (fun _ => 0)

def reply (u : Bool) : Reply := ⟨[u], if u then 7 else 1, if u then 5 else 2⟩

def env : Environment Unit Bool := fun _ _ =>
  (PMF.uniformOfFintype Bool).map (fun u => (reply u, u))

def start : World 0 Control Unit Bool [] := ⟨machine.initialConfig [], ⟨false, []⟩⟩

def answered (u : Bool) : World 0 Control Unit Bool [] :=
  ⟨start.config.receive () .finish [u], start.memory.record ((), []) (reply u) u⟩

def done (u : Bool) : World 0 Control Unit Bool [] :=
  ⟨(answered u).config.step (action none (some u)) (fun _ => none) (fun _ => 0),
    (answered u).memory⟩

private theorem wait_same : start.config.step (action (some .wait)) (fun _ => none) (fun _ => 0) =
    start.config := by
  simp only [start, machine, action, MultiTapeMachine.initialConfig, Config.step,
    Action.apply, Cfg.init]
  congr 2 <;> funext i <;> exact Fin.elim0 i

/-- Exact actual native one-instruction law: retry locally or issue the query. -/
theorem step_start : step machine env start =
    (PMF.uniformOfFintype Bool).bind (fun bit =>
      if bit then (PMF.uniformOfFintype Bool).map answered else PMF.pure start) := by
  simp only [step, start, machine, MultiTapeMachine.initialConfig, Cfg.init]
  congr 1
  funext bit
  cases bit
  · change PMF.pure (⟨start.config.step (action (some .wait)) (fun _ => none) (fun _ => 0),
      start.memory⟩ : World 0 Control Unit Bool []) = PMF.pure start
    rw [wait_same]
  · simp only [ite_true, env, PMF.map_comp]
    rfl

/-- A returned bit is actually written and the native machine halts. -/
theorem step_answered (u : Bool) : step machine env (answered u) = PMF.pure (done u) := by
  simp [step, answered, done, machine, start, reply, Config.receive, Config.answerSymbols,
    Channel.answerSymbol, Config.step, MultiTapeMachine.initialConfig, action, Action.apply]

example (u : Bool) : NativeUnboundedExecution.halted (done u) := by rfl

abbrev W := World 0 Control Unit Bool []

private def mass (world x : W) : ℝ≥0∞ :=
  StoppedProcess.terminalMass (step machine env) NativeUnboundedExecution.halted world x

private theorem mass_done (u : Bool) (x : W) : mass (done u) x = PMF.pure (done u) x :=
  StoppedProcess.terminalMass_halted _ _ (NativeUnboundedExecution.step_halted machine env)
    (done u) rfl x

private theorem mass_answered (u : Bool) (x : W) :
    mass (answered u) x = PMF.pure (done u) x := by
  unfold mass
  rw [StoppedProcess.terminalMass_unfold _ _
    (NativeUnboundedExecution.step_halted machine env), step_answered]
  simp only [PMF.pure_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq]
  exact mass_done u x

private theorem mass_le_one (x : W) : mass start x ≤ 1 :=
  (le_tsum (mass start) x).trans
    (StoppedProcess.terminalMass_sum_le _ _
      (NativeUnboundedExecution.step_halted machine env) start)

/-- Actual unbounded terminal world law, derived from the native first-step
recurrence rather than an assumed termination or representation contract. -/
theorem mass_start (x : W) : mass start x = (PMF.uniformOfFintype Bool).map done x := by
  have he : mass start x = (2 : ℝ≥0∞)⁻¹ * mass start x +
      (2 : ℝ≥0∞)⁻¹ * (PMF.uniformOfFintype Bool).map done x := by
    have hq : (∑' u, PMF.uniformOfFintype Bool u * mass (answered u) x) =
        (PMF.uniformOfFintype Bool).map done x := by
      simp only [mass_answered]
      rfl
    conv_lhs => unfold mass; rw [StoppedProcess.terminalMass_unfold _ _
      (NativeUnboundedExecution.step_halted machine env)]
    change (∑' next, step machine env start next * mass next x) = _
    rw [step_start, PMF.tsum_bind_mul, tsum_bool]
    simp only [Bool.false_eq_true, ite_false, ite_true, PMF.tsum_map_mul,
      PMF.pure_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq]
    rw [hq]
    norm_num [PMF.uniformOfFintype_apply]
  have hm : mass start x ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (mass_le_one x)
  have hq := ((PMF.uniformOfFintype Bool).map done).apply_ne_top x
  have hr := congrArg ENNReal.toReal he
  have hc : (2 : ℝ≥0∞)⁻¹ ≠ ⊤ := by norm_num
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hc hm) (ENNReal.mul_ne_top hc hq)] at hr
  norm_num only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hr
  apply (ENNReal.toReal_eq_toReal_iff' hm hq).mp
  linarith

/-- The geometric waiting loop terminates almost surely, with the full joint
native world/reply/resource law of the one actual oracle call. -/
theorem terminal_law : NativeUnboundedExecution.terminal machine env start =
    (PMF.uniformOfFintype Bool).map (fun u => some (done u)) := by
  classical
  have hn : NativeUnboundedExecution.terminal machine env start none = 0 := by
    change 1 - (∑' x, mass start x) = 0
    simp only [mass_start, PMF.tsum_coe, tsub_self]
  ext next
  cases next with
  | none => simp [hn, PMF.map_apply]
  | some next =>
    change mass start next = _
    rw [mass_start]
    simp [PMF.map_apply]

private theorem step_retry : (2 : ℝ≥0∞)⁻¹ ≤ step machine env start start := by
  classical
  rw [step_start, PMF.bind_apply]
  simp only [tsum_bool, Bool.false_eq_true, ite_false, ite_true,
    PMF.pure_apply_self, mul_one]
  simpa only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat] using
    le_add_right (le_refl ((2 : ℝ≥0∞)⁻¹))

/-- Every finite native clock leaves genuinely positive live mass. -/
theorem retry_mass (n : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ n ≤ execute machine env n start start := by
  induction n with
  | zero => simp [execute_zero]
  | succ n ih =>
    rw [execute_add, PMF.bind_apply, pow_succ]
    simp only [execute_one]
    exact (mul_le_mul ih step_retry bot_le bot_le).trans
      (le_tsum (fun next => execute machine env n start next * step machine env next start) start)

/-- No fixed clock is sufficient on all positive-probability runs. -/
theorem no_uniform_clock (n : ℕ) :
    ∃ next ∈ (execute machine env n start).support, ¬ NativeUnboundedExecution.halted next := by
  refine ⟨start, ?_, by simp [NativeUnboundedExecution.halted, start,
    MultiTapeMachine.initialConfig, Cfg.init, machine]⟩
  rw [PMF.mem_support_iff]
  have hp : (0 : ℝ≥0∞) < 2⁻¹ := by norm_num
  exact ne_of_gt ((ENNReal.pow_pos hp n).trans_le (retry_mass n))

/-- The oracle cost and physical duration are correlated with its returned bit,
with no integrability/bounded-total-bill hypothesis. -/
theorem expected_terminal_bill :
    (∑' next, NativeUnboundedExecution.terminal machine env start next *
      next.elim 0 (fun w => (tokenBill w.memory.events : ℝ≥0∞))) = 4 := by
  rw [terminal_law, PMF.tsum_map_mul]
  norm_num [done, answered, start, tokenBill, Memory.record, reply, tsum_bool,
    PMF.uniformOfFintype_apply]
  have hc := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
    (show (2 : ℝ≥0)⁻¹ * 7 + 2⁻¹ = 4 by norm_num)
  simpa only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_inv_two, ENNReal.coe_ofNat] using hc

example : NativeUnboundedExecution.terminal machine env start none = 0 := by
  simp [terminal_law, PMF.map_apply]

theorem expected_terminal_duration :
    (∑' next, NativeUnboundedExecution.terminal machine env start next *
      next.elim 0 (fun w => (elapsed w.memory.events : ℝ≥0∞))) = 7 / 2 := by
  rw [terminal_law, PMF.tsum_map_mul]
  norm_num [done, answered, start, elapsed, Memory.record, reply, tsum_bool,
    PMF.uniformOfFintype_apply]
  have hc := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
    (show (2 : ℝ≥0)⁻¹ * 5 + 2⁻¹ * 2 = 7 / 2 by norm_num)
  simpa only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_inv_two, ENNReal.coe_ofNat,
    ENNReal.coe_div (show (2 : ℝ≥0) ≠ 0 by norm_num)] using hc

/-- Termination follows from the actual native clock limit despite the absence
of any uniformly sufficient finite instruction clock. -/
example : (⨆ fuel, NativeUnboundedExecution.haltedMass machine env fuel start) = 1 :=
  (NativeUnboundedExecution.terminal_none_eq_zero machine env start).mp
    (by simp [terminal_law, PMF.map_apply])

/-- The nonnegative stopped-bill clock limit is the actual unbounded expectation. -/
example : (∑' next, NativeUnboundedExecution.terminal machine env start (some next) *
      (tokenBill next.memory.events : ℝ≥0∞)) =
    ⨆ fuel, ∑' next, (if NativeUnboundedExecution.halted next then
      execute machine env fuel start next else 0) * (tokenBill next.memory.events : ℝ≥0∞) :=
  NativeUnboundedExecution.terminal_score machine env start _

def parse (_ : Unit) (_ word : List Bool) : Finset Bool := word.toFinset

def decode (word : List Bool) : Option (Finset Bool) := some word.toFinset

def accept (C : Finset Bool) : Bool := true ∈ C

/-- Admission is proved on actual finite runs for all clocks, not supplied with
a terminal-law or stopping conclusion. Both successful and failed outputs here
are genuine proposals, and success remains correlated with cost and duration. -/
theorem selection_only :
    NativeUnboundedExecution.SelectionOnly machine env parse decode accept start := by
  intro fuel next hn C hc _
  have hh : NativeUnboundedExecution.halted next := by
    by_contra h
    simp only [NativeOpenSelection.result] at hc
    split_ifs at hc with hs
    · exact h (by simpa [NativeUnboundedExecution.halted] using hs)
  have ht := (NativeUnboundedExecution.terminal_support machine env start next).mpr
    ⟨hh, fuel, hn⟩
  rw [terminal_law, PMF.mem_support_map_iff] at ht
  obtain ⟨u, _, he⟩ := ht
  cases he
  have ho : (done u).config.tapes.output = [u] := rfl
  simp only [NativeOpenSelection.result, show (done u).config.tapes.state = none from rfl,
    Option.isNone_none, ite_true, decode, ho, Option.some.injEq] at hc
  subst C
  simp [NativeOpenSelection.proposals, parse, done, answered, start, Memory.record, reply]

example : (NativeUnboundedExecution.terminal machine env start).map
      (Option.map fun next => NativeOpenSelection.outcome accept
        (NativeOpenSelection.view parse decode next)) =
    (NativeUnboundedExecution.terminal machine env start).map
      (Option.map fun next => NativeOpenSelection.outcome accept
        ⟨next.memory.events, next.config.tapes.state.isNone,
          NativeOpenSelection.result decode next⟩) :=
  NativeUnboundedExecution.terminal_normalized machine env parse decode accept start selection_only

/-- The constructed unbounded behavioral selector preserves the actual full
joint native outcome, rather than independently reproducing its marginals. -/
example : (NativeUnboundedExecution.behavioral machine env parse decode start).map
      (Option.map (NativeOpenSelection.outcome accept)) =
    (PMF.uniformOfFintype Bool).map (fun u => some (NativeOpenSelection.outcome accept
      ⟨(done u).memory.events, true, NativeOpenSelection.result decode (done u)⟩)) := by
  rw [NativeUnboundedExecution.behavioral_outcome_law machine env parse decode accept
    start selection_only, terminal_law, PMF.map_comp]
  rfl

/-- An actual finite-control native machine which never issues a query or halts. -/
def diverging : MultiTapePTM 0 Bool Control Unit where
  initial := .wait
  tr _ _ _ _ _ := .step (action (some .wait)) (fun _ => none) (fun _ => 0)

private theorem diverging_step : step diverging env start = PMF.pure start := by
  change (PMF.uniformOfFintype Bool).bind (fun _ => PMF.pure
    (⟨start.config.step (action (some .wait)) (fun _ => none) (fun _ => 0), start.memory⟩ : W)) = _
  rw [wait_same, PMF.bind_const]

private theorem diverging_clock (n : ℕ) : execute diverging env n start = PMF.pure start := by
  induction n with
  | zero => exact execute_zero _ _ _
  | succ n ih =>
    rw [execute_add, ih, PMF.pure_bind, execute_one, diverging_step]

/-- Sure divergence is retained as probability one, not converted to a halted
failure, an accepted empty cover, or a finite clock result. -/
theorem diverging_terminal : NativeUnboundedExecution.terminal diverging env start =
    PMF.pure none := by
  classical
  have hm (next : W) : StoppedProcess.terminalMass (step diverging env)
      NativeUnboundedExecution.halted start next = 0 := by
    simp only [StoppedProcess.terminalMass, StoppedProcess.stopped,
      ← execute_eq_stateLaw, diverging_clock]
    by_cases hh : NativeUnboundedExecution.halted next
    · have hn : start ≠ next := by
        intro he
        subst next
        simp [NativeUnboundedExecution.halted, start, MultiTapeMachine.initialConfig,
          machine, Cfg.init] at hh
      simp [hh, PMF.pure_apply, Ne.symm hn]
    · simp [hh]
  ext next
  cases next with
  | none =>
    change 1 - (∑' next, StoppedProcess.terminalMass (step diverging env)
      NativeUnboundedExecution.halted start next) = _
    simp [hm, PMF.pure_apply]
  | some next =>
    change StoppedProcess.terminalMass (step diverging env)
      NativeUnboundedExecution.halted start next = _
    simp [hm, PMF.pure_apply]

end CslibFrontierTests.NativeUnboundedExecution
