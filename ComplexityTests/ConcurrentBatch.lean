/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Probabilistic.NativeBatch
import Complexity.Probability.StochasticOracle.ConcurrentBatch.FiniteOracle
import Mathlib.Basic.NNReal.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# Correlated concurrent batches, deadline cancellation and actual protocol guards

Three labeled opportunities are consumed in two batches. The first contains two
concurrent calls sharing one bit: an early valid proposal does not cancel the
other call, which incurs a positive cutoff bill. The second batch retains that
hidden bit and is clipped by the absolute deadline. Reuse and malformed requests
are rejected without a third source turn. No target cost/latency premise is supplied.
-/

noncomputable section
open Cslib Cslib.Probability NativeOpenExecution NativeInterface
open Cslib.Probability.StochasticOracle.ConcurrentBatch
open Cslib.Optimization.OneConstraint
open scoped NNReal
namespace ComplexityTests.ConcurrentBatch

/-- Two concurrent preformed calls; the third opportunity is reserved for later. -/
def first : Batch 3 := ⟨![some [false], some [true], none], by
  exact ⟨0, by simp [active, Finset.mem_filter]⟩⟩

/-- The remaining opportunity, after both first-batch opportunities are consumed. -/
def second : Batch 3 := ⟨![none, none, some []], by
  exact ⟨2, by simp [active, Finset.mem_filter]⟩⟩

/-- Each opportunity has cutoff five; the sequential deadline is eight. -/
def limits : Limits 3 := ⟨fun _ => 5, by intro _; norm_num, 8, 2⟩

/-- A nonzero cancellation invoice is charged only once time two is reached. -/
def delayedBill (tokens : ℕ) (time : ℝ≥0) : ℕ := if 2 ≤ time then tokens else 0

private theorem delayed_mono (tokens : ℕ) : Monotone (delayedBill tokens) := by
  intro a b hab
  by_cases ha : 2 ≤ a
  · have hb : 2 ≤ b := ha.trans hab
    simp [delayedBill, ha, hb]
  · simp [delayedBill, ha]

/-- Joint trajectories have correlated responses, hidden token counts and return times. -/
def paths (u : Bool) (i : Fin 3) : CallTrace :=
  if i = 0 then
    ⟨some (1, encodeFamily (if u then {0} else (∅ : Finset (Fin 1)))),
      fun _ => if u then 4 else 1, by intro _ _ _; exact le_rfl⟩
  else if i = 1 then
    ⟨some (9, [u]), delayedBill (if u then 7 else 2), delayed_mono _⟩
  else ⟨some (4, [u]), delayedBill (if u then 9 else 3), delayed_mono _⟩

/-- The first receipt waits for both concurrent calls, including cutoff cancellation. -/
def firstReceipt (u : Bool) : Exchange 3 := observe limits 8 first (paths u)

/-- Only three units remain; the later call is canceled by the deadline before its return. -/
def secondReceipt (u : Bool) : Exchange 3 := observe limits 3 second (paths u)

private theorem first_active : active first.slots = {0, 1} := by
  apply Finset.ext
  intro i
  fin_cases i <;> decide

private theorem second_active : active second.slots = {2} := by
  apply Finset.ext
  intro i
  fin_cases i <;> decide

/-- The actual packet is nonempty, preformed and completely decodable. -/
example : decodeBatch 3 (encodeBatch first) = some first := decodeBatch_encode first

/-- Invalid/empty batch packets are rejected before any sampling. -/
example : decodeBatch 3 [] = none ∧ decodeBatch 0 [] = none := by
  simp [decodeBatch, decodeSlots, encodeSlots, active]

/-- Cancellation differs from an actual successful empty response word. -/
example : decodeCall (encodeCall (none, 7)) = some (none, 7) ∧
    decodeCall (encodeCall (some [], 7)) = some (some [], 7) := by
  simp [decodeCall_encode]

/-- Early success never erases the other call's cutoff duration or accrued bill. -/
theorem first_resources (u : Bool) :
    (firstReceipt u).duration = 5 ∧ (firstReceipt u).tokens = (if u then 11 else 3) ∧
      (firstReceipt u).report 1 = some (none, if u then 7 else 2) := by
  dsimp only [firstReceipt, Exchange.duration, Exchange.tokens]
  change (active first.slots).sup _ = _ ∧ (∑ i ∈ active first.slots, _) = _ ∧ _
  rw [first_active]
  cases u <;> norm_num [observe, paths, CallTrace.report, CallTrace.response, CallTrace.stop,
    delayedBill, limits, first, active, Finset.mem_filter]

/-- The second receipt uses the remaining absolute deadline, not a fresh cutoff. -/
theorem second_resources (u : Bool) :
    (secondReceipt u).duration = 3 ∧ (secondReceipt u).tokens = (if u then 9 else 3) ∧
      (secondReceipt u).report 2 = some (none, if u then 9 else 3) := by
  dsimp only [secondReceipt, Exchange.duration, Exchange.tokens]
  change (active second.slots).sup _ = _ ∧ (∑ i ∈ active second.slots, _) = _ ∧ _
  rw [second_active]
  cases u <;> norm_num [observe, paths, CallTrace.report, CallTrace.response, CallTrace.stop,
    delayedBill, limits, second, active, Finset.mem_filter]

/-- Only the completed first call can supply a candidate family. -/
example (u : Bool) : proposals 1 (firstReceipt u).report = [if u then {0} else ∅] := by
  cases u <;> norm_num [proposals, firstReceipt, observe, paths, CallTrace.report,
    CallTrace.response, limits, first, List.ofFn_succ, encodeFamily, decodeFamily,
    Finset.mem_filter, List.filterMap_cons, List.filterMap_nil]

/-- First-batch joint response law, including the private bit shared by later calls. -/
def sample : Sampler 3 Bool := fun s _ =>
  if s.history = [] then (PMF.uniformOfFintype Bool).map fun u => (paths u, u)
  else PMF.pure (paths s.privateState, s.privateState)

/-- Actual state after the first accepted concurrent batch. -/
def afterFirst (u : Bool) : ServerState 3 Bool := commit (initial false) (firstReceipt u) u

/-- Actual state after the second batch; the hidden bit is retained across batches. -/
def afterSecond (u : Bool) : ServerState 3 Bool :=
  commit (afterFirst u) (secondReceipt u) u

private theorem admit_first : admit limits (initial (n := 3) false) (encodeBatch first) =
    some first := by simp [admit, decodeBatch_encode, initial, limits]

private theorem admit_second (u : Bool) :
    admit limits (afterFirst u) (encodeBatch second) = some second := by
  have ht := (first_resources u).1
  norm_num [admit, decodeBatch_encode, afterFirst, commit, initial, ht, limits,
    first_active, second_active]
  change 2 ∉ active first.slots
  simp [first_active]

/-- The first real request samples both call trajectories and private state jointly. -/
theorem first_law : serve limits sample (encodeBatch first) (initial false) =
    (PMF.uniformOfFintype Bool).map fun u => (replyOf (firstReceipt u), afterFirst u) := by
  rw [serve_accepted _ _ _ _ _ admit_first]
  simp only [sample, initial, ite_true, PMF.map_comp]
  simp [limits, firstReceipt, afterFirst, initial, Function.comp_def]

private theorem remaining : (8 : ℝ≥0) - 5 = 3 := by
  apply Subtype.ext
  norm_num [NNReal.coe_sub]

/-- The later request retains the earlier hidden bit, with deadline-truncated charges. -/
theorem second_law (u : Bool) : serve limits sample (encodeBatch second) (afterFirst u) =
    PMF.pure (replyOf (secondReceipt u), afterSecond u) := by
  rw [serve_accepted _ _ _ _ _ (admit_second u)]
  have ht := (first_resources u).1
  norm_num [sample, afterFirst, afterSecond, commit, initial, ht, limits, secondReceipt, remaining]

/-- Both sequential batches have total latency eight and actual correlated bills twenty/six. -/
theorem final_resources (u : Bool) :
    (afterSecond u).elapsed = 8 ∧ (afterSecond u).history.length = 2 ∧
      ((afterSecond u).history.map Exchange.tokens).sum = (if u then 20 else 6) ∧
        (afterSecond u).privateState = u := by
  obtain ⟨h₁, h₂, _⟩ := first_resources u
  obtain ⟨h₃, h₄, _⟩ := second_resources u
  cases u <;> norm_num [afterSecond, afterFirst, commit, initial, h₁, h₂, h₃, h₄] at *

/-- Reuse is rejected even while deadline and turn budget still permit another batch. -/
example (u : Bool) : admit limits (afterFirst u) (encodeBatch first) = none := by
  simp only [admit, decodeBatch_encode]
  have hused : ¬Disjoint (active first.slots) (afterFirst u).used := by
    change ¬Disjoint (active first.slots) (active first.slots ∪ ∅)
    simp [first_active]
  simp [hused]

/-- A call which never returns still incurs the positive cutoff cancellation invoice. -/
example : (CallTrace.report ⟨none, delayedBill 7, delayed_mono 7⟩ 5) = (none, 7) := by
  norm_num [CallTrace.report, CallTrace.response, CallTrace.stop, delayedBill]

/-- A completed word of the wrong family-mask length cannot fabricate a candidate. -/
example : decodeFamily 1 [true, false] = none := by simp [decodeFamily]

/-- Reuse/expired deadline cannot invoke the joint sampler or issue another turn. -/
example (u : Bool) : serve limits sample (encodeBatch first) (afterSecond u) =
    PMF.pure (rejection, afterSecond u) := by
  apply serve_rejected
  simp [admit, decodeBatch_encode, (final_resources u).1, limits]

/-- Source feasibility follows from the actual guard/receipt construction. -/
example (u : Bool) : WellFormed limits (afterSecond u) := by
  have hf := commit_wellFormed limits (initial false) (initial_wellFormed limits false)
    (encodeBatch first) first admit_first (paths u) u
  have hf' : WellFormed limits (afterFirst u) := by
    simpa [afterFirst, firstReceipt, initial, limits] using hf
  have hs := commit_wellFormed limits (afterFirst u) hf' (encodeBatch second) second
    (admit_second u) (paths u) u
  norm_num [afterSecond, secondReceipt, afterFirst, initial, commit, (first_resources u).1,
    limits, remaining] at hs ⊢
  exact hs

/-- Actual finite-scenario conditional batch table, not an assumed law equality. -/
def profile : FiniteProfile 3 Unit Bool where
  request _ _ := first
  law _ _ := pair true false (1 / 2) (by norm_num) (by norm_num)
  paths _ _ := paths

/-- Expected batch cost and concurrent latency are computed from the same correlated table. -/
example : ((oracleAt (m := 1) profile limits 8).respond [] ()).mean
      ((oracleAt (m := 1) profile limits 8).charge [] ()) = 7 ∧
    ((oracleAt (m := 1) profile limits 8).respond [] ()).mean
      ((oracleAt (m := 1) profile limits 8).duration [] ()) = 5 := by
  have ht := first_resources true
  have hf := first_resources false
  simp only [oracleAt, profile, profileReceipt, pair_mean]
  change (1 / 2 * ((firstReceipt true).tokens : ℝ) +
      (1 - 1 / 2) * ((firstReceipt false).tokens : ℝ) = 7) ∧
    (1 / 2 * ((firstReceipt true).duration : ℝ) +
      (1 - 1 / 2) * ((firstReceipt false).duration : ℝ) = 5)
  norm_num [ht.1, ht.2.1, hf.1, hf.2.1]

/-- Zero turns and zero deadline reject the same otherwise well-formed nonempty packet. -/
example : admit { limits with turns := 0 } (initial (n := 3) false) (encodeBatch first) = none ∧
    admit { limits with deadline := 0 } (initial (n := 3) false) (encodeBatch first) = none := by
  simp [admit, decodeBatch_encode, initial]

end ComplexityTests.ConcurrentBatch
