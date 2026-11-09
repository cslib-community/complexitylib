/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontierTests.NativeEpoch
import CslibFrontier.Probability.StochasticOracle.SelectionLowerBound
import Mathlib.Tactic

/-!
# A concrete stopped native epoch instantiates the finite policy API

This is a checked one-opportunity client, not unrestricted Theorems 5/6. The
actual raw request is the empty word on the unit channel: its concrete batch is
one preformed call. The native geometric wait is unbounded, the response carries
a correlated charge/duration, and subsequent native verification is silent.
-/

noncomputable section
open Cslib Cslib.Probability Turing NativeOpenExecution NativeInterface NativeEpoch
open Cslib.Probability.StochasticOracle
open Cslib.Optimization.OneConstraint
open CslibFrontierTests.NativeUnboundedExecution
open CslibFrontierTests.NativeEpoch
open scoped ENNReal NNReal
namespace CslibFrontierTests.NativeEpochPolicy

/-- One actual call opportunity, with a correlated finite raw-response law. -/
def oracle : SelectionPolicy.Oracle Unit Bool Bool where
  respond _ _ := pair true false (1 / 2) (by norm_num) (by norm_num)
  proposed _ _ u := [{u}]
  charge _ _ u := if u then 7 else 1
  duration _ _ u := if u then 5 else 2
  charge_nonneg := by intro _ _ u; cases u <;> norm_num
  duration_nonneg := by intro _ _ u; cases u <;> norm_num

/-- One query, followed by local output extraction; later decisions halt. -/
def policy : SelectionPolicy.Policy Unit Bool Bool where
  choose h := if h = [] then Distribution.pure (some ()) else Distribution.pure none
  output h := Distribution.pure (match h.head? with
    | some (some (_, u)) => {u}
    | _ => ∅)

private theorem fair : (pair true false (1 / 2 : ℝ) (by norm_num) (by norm_num)).toPMF =
    PMF.uniformOfFintype Bool := by
  ext u
  cases u <;> norm_num [Distribution.toPMF, pair, PMF.uniformOfFintype_apply,
    ENNReal.ofReal_div_of_pos]

private theorem policy_law : (SelectionPolicy.law oracle policy []).toPMF =
    (PMF.uniformOfFintype Bool).map (fun u => some ((), u)) := by
  simp only [SelectionPolicy.law, List.not_mem_nil, ite_false, policy, ite_true,
    Distribution.toPMF_bind, Distribution.toPMF_pure, PMF.pure_bind, oracle,
    Distribution.toPMF_map, fair]

/-- Decode the actual one-record response, not a supplied source-law equality. -/
def record (state : Option (World 0 Control Unit Bool [])) : SelectionPolicy.Record Unit Bool :=
  state.bind fun world => world.memory.events.head?.map fun event =>
    (event.operation, event.reply.word.headD false)

/-- True next-query stopping through arbitrary silent waiting induces the
existing quantitative policy's actual response-record law. -/
theorem native_policy_record_law : (nextEpoch machine env start).map record =
    (SelectionPolicy.law oracle policy []).toPMF := by
  rw [first_response, policy_law, PMF.map_comp]
  rfl

/-- The concrete source batch is nonempty and preformed before the response. -/
example : ({()} : Finset Unit).Nonempty ∧
    selectedSignal (some queryCheckpoint) = some (.query [] () []) := by
  exact ⟨by simp, rfl⟩

/-- The single opportunity is not reused by any actual completed native path. -/
example (u : Bool) : ((done u).memory.events.map Event.operation).Nodup ∧
    (done u).memory.events.length = 1 := by
  simp [done, answered, start, Memory.record]

/-- Every response returns within the concrete cutoff; the singleton maximum
latency is its own duration and no unfinished cancellation is omitted. -/
example (u : Bool) : (reply u).duration ≤ 5 ∧
    elapsed (done u).memory.events = (reply u).duration ∧
    tokenBill (done u).memory.events = (reply u).tokens := by
  cases u <;> norm_num [reply, elapsed, tokenBill, done, answered, start, Memory.record]

/-- Native response and silent completion preserve the same actual record,
output family and both resources as the quantitative finite policy. -/
theorem native_policy_joint_law :
    (NativeUnboundedExecution.terminal machine env start).map (fun state => state.map fun world =>
      (record (some world), NativeOpenSelection.result decode world,
        tokenBill world.memory.events, elapsed world.memory.events)) =
      (SelectionPolicy.law oracle policy []).toPMF.map (fun r => r.map fun (_, u) =>
        (r, some ({u} : Finset Bool), (if u then 7 else 1 : ℝ≥0), (if u then 5 else 2 : ℝ≥0))) := by
  rw [← resume_after_epochs machine env 1 start]
  simp only [ObservedProcess.stateLaw, PMF.pure_bind, epochStep, first_response,
    PMF.bind_map, PMF.map_bind]
  have hf (u : Bool) : finish machine env (answered u) = PMF.pure (some (done u)) := by
    rw [finish, native_epoch_equation, nextEpoch, next_halt, PMF.pure_bind]
    simp only [respond, PMF.pure_bind, Option.elim_some]
    exact StoppedProcess.terminal_halted _ _ _ _ rfl
  simp only [Function.comp_def, hf, PMF.pure_map, policy_law, PMF.map_comp]
  congr 1
  funext u
  cases u <;> norm_num [Function.comp_def, record, NativeOpenSelection.result, decode,
    done, answered, start, tokenBill, elapsed, Memory.record, reply,
    MultiTapeMachine.Config.step, MultiTapeMachine.Config.receive, action, Action.apply,
    MultiTapeMachine.initialConfig, machine, Cfg.init]

/-- The expected actual finite-policy bill is derived from its oracle/table;
it equals the native stopped bill, not an assumed resource bound. -/
theorem policy_expected_cost : SelectionPolicy.expectedCost oracle policy 1 = 4 := by
  unfold SelectionPolicy.expectedCost
  simp only [AdaptiveSelection.historyExpectation]
  rw [SelectionPolicy.law_mean _ _ [] _ (by simp)]
  norm_num [policy, Distribution.mean_pure, oracle, pair_mean,
    AdaptiveSelection.accruedBill, SelectionPolicy.bill]

/-- The true proposal covers a singleton ground set; the false proposal is an
empty original set. The feasible dual and true cover both have value one. -/
def coverInstance : PartialCover.Instance Unit Bool where
  ground := {()}
  sets u := if u then {()} else ∅
  sets_subset := by intro u; cases u <;> simp
  weight _ := 1
  weight_nonneg := by intro _; norm_num
  dual _ := 1
  dual_nonneg := by intro _; norm_num
  dual_feasible := by intro u; cases u <;> norm_num

/-- The actual finite policy extracts only its received proposal. -/
theorem admissible : SelectionPolicy.Admissible oracle policy := by
  intro h _ C hC
  have he : C = (match h.head? with | some (some (_, u)) => {u} | _ => ∅) := by
    by_contra he
    simp [policy, Distribution.pure, he] at hC
  subst C
  cases h with
  | nil => simp
  | cons x h =>
    cases x with
    | none => simp
    | some x =>
      rcases x with ⟨⟨⟩, u⟩
      simp [SelectionPolicy.available, SelectionPolicy.proposals, oracle]

/-- Certified deadline success is derived from the actual one-response policy,
not supplied as an admission hypothesis. -/
theorem success_probability : SelectionPolicy.successProbability oracle policy coverInstance 1 5 1 =
    1 / 2 := by
  unfold SelectionPolicy.successProbability
  simp only [AdaptiveSelection.historyExpectation]
  rw [SelectionPolicy.law_mean _ _ [] _ (by simp)]
  norm_num [policy, Distribution.mean_pure, oracle, pair_mean, SelectionPolicy.success,
    PartialCover.Instance.covered, PartialCover.Instance.cost, coverInstance,
    AdaptiveSelection.accruedBill, SelectionPolicy.latency]

/-- Local oracle envelopes hold for every behavioral competitor, derived from
the fixed reply law rather than assumed lower-cost/optimality conclusions. -/
theorem universal : SelectionPolicy.UniversalBounds oracle coverInstance 1 (1 / 2) 4 2 := by
  intro π _
  constructor
  · intro h _ _ a _
    rcases a with ⟨⟩
    have hz : AdaptiveSelection.reveals coverInstance (SelectionPolicy.proposals oracle) h
        (some ((), false)) = false := by
      simp [AdaptiveSelection.reveals, AdaptiveSelection.revealed, SelectionPolicy.proposals,
        oracle, PartialCover.Instance.covered, coverInstance]
    change (pair true false (1 / 2 : ℝ) (by norm_num) (by norm_num)).mean
      (fun x => if AdaptiveSelection.reveals coverInstance (SelectionPolicy.proposals oracle) h
        (some ((), x)) then 1 else 0) ≤ 1 / 2
    rw [pair_mean, hz]
    cases AdaptiveSelection.reveals coverInstance (SelectionPolicy.proposals oracle) h
      (some ((), true)) <;> norm_num
  · intro h _ _ a _ x _
    simpa using Finset.card_le_univ
      (AdaptiveSelection.revealed coverInstance (SelectionPolicy.proposals oracle)
        (some (a, x) :: h) \
        AdaptiveSelection.revealed coverInstance (SelectionPolicy.proposals oracle) h)
  · intro h _ _ a _
    norm_num [oracle, pair_mean]
  · intro h _ _ a _ x _
    cases x <;> norm_num [oracle]

/-- The existing quantitative universal theorem bounds every admissible
one-turn competitor meeting the same success target. The concrete native
waiting policy attains this derived lower bound at expected cost four. -/
theorem all_competitors (π : SelectionPolicy.Policy Unit Bool Bool)
    (hA : SelectionPolicy.Admissible oracle π)
    (hs : (1 / 2 : ℝ) ≤ SelectionPolicy.successProbability oracle π coverInstance 1 5 1) :
    4 ≤ SelectionPolicy.expectedCost oracle π 1 := by
  have h := SelectionPolicy.universal_lower_cost oracle coverInstance 1 1 1
    (by intro k hk; simp only [coverInstance, Finset.card_singleton]; omega)
    (1 / 2) 4 2 1 5 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    universal π hA hs
  norm_num at h
  exact h

/-- The singleton batch's actual concurrent maximum is its own reported
latency. This concrete codec needs no assumed batch-validity parser contract. -/
example (u : Bool) : ({()} : Finset Unit).sup (fun _ => (reply u).duration) =
    (reply u).duration := by simp

/-- Actual native acceptance has exactly the certified deadline success
probability of the finite policy instance. -/
theorem native_success_probability :
    (((NativeUnboundedExecution.terminal machine env start).map (fun state => state.any
      (fun world => NativeOpenSelection.accepted accept (NativeOpenSelection.result decode world))))
        true).toReal = SelectionPolicy.successProbability oracle policy coverInstance 1 5 1 := by
  rw [terminal_law, PMF.map_comp, success_probability]
  norm_num [PMF.map_apply, tsum_bool, PMF.uniformOfFintype_apply, NativeOpenSelection.accepted,
    NativeOpenSelection.result, accept, decode, done, answered, start, action, Action.apply,
    MultiTapeMachine.Config.step, MultiTapeMachine.Config.receive,
    MultiTapeMachine.initialConfig, machine, Cfg.init]

/-- A source-API quantitative comparison for the actual unbounded native
selector: its derived expected stopped bill attains the universal one-turn lower
bound against every admissible finite-policy competitor at success target 1/2. -/
theorem native_attains_comparison (π : SelectionPolicy.Policy Unit Bool Bool)
    (hA : SelectionPolicy.Admissible oracle π)
    (hs : (1 / 2 : ℝ) ≤ SelectionPolicy.successProbability oracle π coverInstance 1 5 1) :
    (∑' next, NativeUnboundedExecution.terminal machine env start next *
      next.elim 0 (fun w => (tokenBill w.memory.events : ℝ≥0∞))).toReal =
        SelectionPolicy.expectedCost oracle policy 1 ∧
    (∑' next, NativeUnboundedExecution.terminal machine env start next *
      next.elim 0 (fun w => (tokenBill w.memory.events : ℝ≥0∞))).toReal ≤
        SelectionPolicy.expectedCost oracle π 1 := by
  rw [expected_terminal_bill, policy_expected_cost]
  constructor
  · norm_num
  · simpa using all_competitors π hA hs

end CslibFrontierTests.NativeEpochPolicy
