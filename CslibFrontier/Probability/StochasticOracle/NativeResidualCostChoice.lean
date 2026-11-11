/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualMinima
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchOutputObservation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat.Binary

/-!
# Runtime cost-aware native residual selection

The original encoded input contains rational oracle prices and missing-block
probabilities, not a selected strategy or prepared execution state. One fixed
native program performs the exact cost comparison before any query and executes
the chosen adaptive/all-specialist feedback on the original instance.

## Main definitions

* `Entry`, `Prices`, `Input`: explicit finite rational oracle data and original input.
* `adaptive`, `prepare`: executed comparison and fresh runtime initialization.
* `controller`: one native program independent of the runtime prices and instance.

## Main results

* `computable_adaptive`, `computable_prepare`: actual native arithmetic and initialization.
* `native_law`: complete output/oracle-memory agreement with the chosen fixed strategy.
* `Reflects`, `adaptive_iff`: primitive source data and the executed comparison.
* `native_selectionOnly`, `native_certified`: provenance and certified actual tape success.
* `native_expected_cost`, `native_minimal`: attained cost and universal native comparison.
* `native_cost_mem`, `native_optimum`: the same code attains the original native infimum.

[Wang2027], Theorem 6, PDF pp. 12–13. Rational decision data are distinguished
from arbitrary real semantic resource charges; this module does not serialize
arbitrary reals or assume that their exact order is computable.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualCostChoice
open Turing Turing.MultiTapeTM NativeOpenExecution NativeRetention
open Turing.MultiTapeTM.ComputableInPolyTime

/-- One specialist's declared probability and expected price. -/
structure Entry where
  /-- Missing-block probability. -/
  probability : ℚ
  /-- Specialist query price. -/
  price : ℚ
  deriving DecidableEq

/-- Exact finite decision data. Source normalization and positivity are semantic
conditions, rather than a supplied cheaper-strategy bit. -/
structure Prices where
  /-- Near-cover query price. -/
  near : ℚ
  /-- Specialist rows in source role order. -/
  entries : List Entry
  deriving DecidableEq

/-- Framed binary rationals for one probability/price row. -/
enc_structure entryEncoding : Entry where probability : encRatBin, price : encRatBin

/-- The decision table includes all operands of the comparison. -/
enc_structure pricesEncoding : Prices where near : encRatBin, entries : (encList entryEncoding)

/-- Original instance/role metadata and the explicit oracle decision table. -/
structure Input where
  /-- Original unprepared startup input, including known roles but no hidden covers. -/
  data : GuardedStartup.Input
  /-- Runtime rational prices and probabilities. -/
  prices : Prices
  deriving DecidableEq

/-- Price operands are framed before the original role word inside the existing
startup ABI. No prepared state or selected branch is installed. -/
@[expose] def packed (x : Input) : GuardedStartup.Input :=
  { x.data with startup := { x.data.startup with
    privateSelector := frame (pricesEncoding x.prices) ++ x.data.startup.privateSelector } }

private def erasePrices (data : GuardedStartup.Input) : GuardedStartup.Input :=
  { data with startup := { data.startup with
    privateSelector := dropFrame data.startup.privateSelector } }

private theorem erasePrices_packed (x : Input) : erasePrices (packed x) = x.data := by
  simp only [erasePrices, packed, dropFrame_frame_append]

/-- The actual word is the existing original-input ABI, with a price prefix.
The fixed native optimum therefore needs no alternate competitor class. -/
@[expose] def encoding : Input ↪ List Bool :=
  ⟨fun x => GuardedStartup.encoding (packed x), by
    intro a b h
    have he := GuardedStartup.encoding.injective h
    have hd : a.data = b.data := by
      simpa only [erasePrices_packed] using congrArg erasePrices he
    have hp : a.prices = b.prices := pricesEncoding.injective (by
      simpa only [packed, unframe_frame_append] using
        congrArg (fun data => unframe data.startup.privateSelector) he)
    cases a; cases b; cases hd; cases hp; rfl⟩

/-- Exact expected cost of the adaptive source strategy. -/
@[expose] def adaptiveCost (p : Prices) : ℚ :=
  p.near + (p.entries.map fun e => e.probability * e.price).sum

/-- Exact cost of preforming all specialist queries. -/
@[expose] def specialistCost (p : Prices) : ℚ := (p.entries.map Entry.price).sum

/-- Actual decision performed at runtime; ties choose adaptation. -/
@[expose] def adaptive (p : Prices) : Bool := decide (adaptiveCost p ≤ specialistCost p)

private theorem computable_product : ComputableInPolyTime
    (fun e : Entry => e.probability * e.price) entryEncoding encRatBin := by
  have h := ratBin_mul.comp entryEncoding_fields_deg.computableInPolyTime
  dsimp only [Function.comp_def] at h
  exact h

private theorem computable_weighted : ComputableInPolyTime
    (fun p : Prices => (p.entries.map fun e => e.probability * e.price).sum)
    pricesEncoding encRatBin := by
  have h := (ratBin_sum.comp (map computable_product)).comp
    pricesEncoding_fields_deg.computableInPolyTime.snd'
  dsimp only [Function.comp_def] at h
  exact h

private theorem computable_specialistCost :
    ComputableInPolyTime specialistCost pricesEncoding encRatBin := by
  have h := (ratBin_sum.comp (map entryEncoding_fields_deg.computableInPolyTime.snd')).comp
    pricesEncoding_fields_deg.computableInPolyTime.snd'
  dsimp only [Function.comp_def] at h
  exact h

private theorem computable_adaptiveCost :
    ComputableInPolyTime adaptiveCost pricesEncoding encRatBin := by
  have h := ratBin_add.comp
    (pricesEncoding_fields_deg.computableInPolyTime.fst'.prod computable_weighted)
  dsimp only [Function.comp_def] at h
  exact h

/-- Native binary-rational multiplication, sums and comparison over the runtime table. -/
theorem computable_adaptive : ComputableInPolyTime adaptive pricesEncoding encBool := by
  have h := ratBin_le.comp (computable_adaptiveCost.prod computable_specialistCost)
  dsimp only [Function.comp_def] at h
  exact h

/-- Fresh runtime state; prices are consumed by native startup, not preinstalled
as a strategy bit. The private role word and original instance remain intact. -/
@[expose] def prepare (x : Input) : RuntimeControl.State :=
  NativeResidualRouting.initial (adaptive x.prices) x.data

private theorem computable_packed : ComputableInPolyTime packed encoding
    GuardedStartup.encoding := .of_eq fun _ => rfl

private theorem startup_mk : ComputableInPolyTime
    (fun p : NativeRetention.Input × ℕ × ℕ × List Bool =>
      InitialContext.Startup.mk p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encInput (encPair encUnary (encPair encUnary encBits)))
    InitialContext.encoding := .of_eq fun _ => rfl

private theorem guard_mk : ComputableInPolyTime
    (fun p : InitialContext.Startup × ℕ => GuardedStartup.Input.mk p.1 p.2)
    (encPair InitialContext.encoding encUnary) GuardedStartup.encoding := .of_eq fun _ => rfl

private theorem computable_data : ComputableInPolyTime
    (fun x : Input => x.data) encoding GuardedStartup.encoding := by
  have hg := GuardedStartup.fields.comp computable_packed
  have hs := InitialContext.fields.comp hg.fst'
  have hw := ComputableInPolyTime.dropFrame.comp hs.snd'.snd'.snd'
  have h := guard_mk.comp ((startup_mk.comp
    (hs.fst'.prod (hs.snd'.fst'.prod (hs.snd'.snd'.fst'.prod hw)))).prod hg.snd')
  simpa only [Function.comp_def, packed, dropFrame_frame_append] using h

private theorem computable_prices : ComputableInPolyTime
    (fun x : Input => x.prices) encoding pricesEncoding := by
  have hs := (InitialContext.fields.comp (GuardedStartup.fields.comp computable_packed).fst')
  have hw := ComputableInPolyTime.unframe.comp hs.snd'.snd'.snd'
  exact hw.of_enc_eq fun x => by
    change pricesEncoding x.prices = unframe ((packed x).startup.privateSelector)
    simp only [packed, unframe_frame_append]

/-- A single compiled initializer actually computes the cost-dependent branch. -/
theorem computable_prepare : ComputableInPolyTime prepare encoding RuntimeControl.encoding := by
  have h := (computable_adaptive.comp computable_prices).ite
    ((NativeResidualRouting.computable_initial true).comp computable_data)
    ((NativeResidualRouting.computable_initial false).comp computable_data)
  have he : (fun x : Input => if adaptive x.prices then
      NativeResidualRouting.initial true x.data else
      NativeResidualRouting.initial false x.data) = prepare := by
    funext x
    cases hb : adaptive x.prices <;> simp [prepare, hb]
  rw [← he]
  exact h

/-- One finite-control native program, uniform in prices, role counts and instance. -/
structure Controller where
  /-- Ordinary work tapes. -/
  tapes : ℕ
  /-- Native control states. -/
  Controls : Type
  /-- Finite control. -/
  finite : Finite Controls
  /-- Actual native code starting on `encoding`. -/
  program : MultiTapePTM tapes Bool Controls Unit
  /-- Reserved runtime context tape. -/
  context : Fin tapes
  /-- Complete clockless feedback law from blank work tapes. -/
  law : ∀ (P : Type) (env : Environment Unit P) (x : Input) (memory : Memory Unit P),
    (NativeUnboundedExecution.terminal program env
      ⟨program.initialConfig (encoding x), memory⟩).map
        (Option.map (NativeReplyContext.observe context)) =
      (Feedback.run env (prepare x).turns (prepare x)
        (fun _ => ⟨[], [], 0⟩) memory NativeResidualRouting.request).map fun outcome =>
          some (⟨tapeOfList (RuntimeControl.packet outcome.state),
            RuntimeControl.result outcome.state, outcome.memory⟩ : NativeReplyContext.Observation P)

private theorem controller_nonempty : Nonempty Controller := by
  obtain ⟨time, space, _, _, hc⟩ := computable_prepare
  obtain ⟨tapes, R, hR, code, context, hlaw⟩ :=
    Feedback.exists_native_controller_from_state encoding prepare
      (fun x => time (encoding x).length) (fun x => space (encoding x).length)
      hc NativeResidualRouting.request NativeResidualRouting.computable_request
  exact ⟨⟨tapes, R, hR, code, context, hlaw⟩⟩

/-- This one program performs both the comparison and the entire selected strategy. -/
def controller : Controller := Classical.choice controller_nonempty

/-- Derived execution identity for actual tape output and full shared oracle memory.
The compared program on the right is proof instrumentation, not host dispatch of
the program on the left. Hidden state, randomness, divergent mass and joint resources
are retained. -/
theorem native_law (P : Type) (env : Environment Unit P) (x : Input)
    (memory : Memory Unit P) :
    (NativeUnboundedExecution.terminal controller.program env
      ⟨controller.program.initialConfig (encoding x), memory⟩).map
        (Option.map fun world => (world.config.tapes.output, world.memory)) =
    (NativeUnboundedExecution.terminal
      (NativeResidualRouting.controller (adaptive x.prices)).program env
      ⟨(NativeResidualRouting.controller (adaptive x.prices)).program.initialConfig
        (GuardedStartup.encoding x.data), memory⟩).map
          (Option.map fun world => (world.config.tapes.output, world.memory)) := by
  have hleft := congrArg (PMF.map (Option.map fun o : NativeReplyContext.Observation P =>
    (o.output, o.memory))) (controller.law P env x memory)
  have hright := congrArg (PMF.map (Option.map fun o : NativeReplyContext.Observation P =>
    (o.output, o.memory)))
    (NativeResidualRouting.controller_law (adaptive x.prices) P env x.data memory)
  simp only [PMF.map_comp, Function.comp_def, Option.map_map, NativeReplyContext.observe,
    ] at hleft hright
  rw [hleft, hright]
  rfl

open ResidualCover ConcurrentBatch Cslib.Optimization.OneConstraint
open scoped ENNReal

/-- Decision-table entries identify primitive source probabilities and prices,
not a supplied branch, optimum, success or cost conclusion. -/
structure Reflects {z : ℕ} (p : Prices) (P : Parameters z) where
  /-- Rows in the actual specialist order. -/
  rows : Fin z → Entry
  /-- The encoded runtime list is exactly those rows. -/
  entries : p.entries = List.ofFn rows
  /-- Near-cover price agrees with the source. -/
  near : (p.near : ℝ) = P.nearCost
  /-- Probabilities agree with the source residual law. -/
  probability : ∀ j, ((rows j).probability : ℝ) = P.missing.weight j
  /-- Specialist prices agree with the source. -/
  price : ∀ j, ((rows j).price : ℝ) = P.specialistCost j

/-- Exact arithmetic on the encoded table agrees with source expected adaptive cost. -/
theorem adaptiveCost_cast {z : ℕ} (p : Prices) (P : Parameters z) (h : Reflects p P) :
    (adaptiveCost p : ℝ) = P.nearCost + P.missing.mean P.specialistCost := by
  simp only [adaptiveCost, h.entries, List.map_ofFn, List.sum_ofFn, Rat.cast_add,
    Rat.cast_sum, Function.comp_def, Rat.cast_mul, h.near, h.probability, h.price,
    Distribution.mean]

/-- Exact arithmetic on the encoded table agrees with all-specialist source cost. -/
theorem specialistCost_cast {z : ℕ} (p : Prices) (P : Parameters z) (h : Reflects p P) :
    (specialistCost p : ℝ) = ∑ j, P.specialistCost j := by
  simp only [specialistCost, h.entries, List.map_ofFn, List.sum_ofFn,
    Rat.cast_sum, Function.comp_def, h.price]

/-- The bit executed by native startup selects precisely the cheaper source alternative. -/
theorem adaptive_iff {z : ℕ} (p : Prices) (P : Parameters z) (h : Reflects p P) :
    adaptive p = true ↔ P.nearCost + P.missing.mean P.specialistCost ≤ ∑ j, P.specialistCost j := by
  rw [← adaptiveCost_cast p P h, ← specialistCost_cast p P h]
  simp only [adaptive, decide_eq_true_eq, Rat.cast_le]

variable {z n m : ℕ} (T : Fin z → Block)
variable (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

private theorem fixed_terminates (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (b : Bool) :
    NativeUnboundedExecution.terminal (NativeResidualRouting.controller b).program
      (ConcurrentBatch.environment NativeResidualAttainment.limits
        (NativeResidualOracle.sample T points candidates P invoice))
      ⟨(NativeResidualRouting.controller b).program.initialConfig
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
        NativeResidualAttainment.initialMemory⟩ none = 0 := by
  apply (PMF.apply_eq_zero_iff _ _).mpr
  intro hn
  have hm : none ∈ ((NativeUnboundedExecution.terminal (NativeResidualRouting.controller b).program
      (ConcurrentBatch.environment NativeResidualAttainment.limits
        (NativeResidualOracle.sample T points candidates P invoice))
      ⟨(NativeResidualRouting.controller b).program.initialConfig
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
        NativeResidualAttainment.initialMemory⟩).map
          (Option.map fun world => (world.config.tapes.output, world.memory))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨none, hn, rfl⟩
  cases b with
  | false =>
    change none ∈ ((NativeUnboundedExecution.terminal
      (NativeResidualRouting.controller false).program
      (ConcurrentBatch.environment (NativeResidualAll.config 2)
        (NativeResidualOracle.sample T points candidates P invoice))
      ⟨(NativeResidualRouting.controller false).program.initialConfig
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
        NativeResidualAttainment.initialMemory⟩).map
          (Option.map fun world => (world.config.tapes.output, world.memory))).support at hm
    rw [NativeResidualAll.native_law T points candidates P invoice hz 2 (by omega),
      PMF.mem_support_pure_iff] at hm
    cases hm
  | true =>
    rw [NativeResidualAttainment.native_law T points candidates P invoice hz] at hm
    obtain ⟨j, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    cases he

/-- One native program computes the cheaper strategy from original rational data
and attains the source minimum in actual accrued invoices. Termination comes from
the derived compiled law, not an assumption about the cost or successful execution. -/
theorem native_expected_cost (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (p : Prices) (h : Reflects p P)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    NativeBatch.Quantitative.expected NativeResidualAttainment.limits
      (NativeResidualOracle.sample T points candidates P invoice) controller.program
      NativeBatch.Trace.charge 3
      ⟨controller.program.initialConfig
        (encoding ⟨NativeResidualAttainment.input T points candidates, p⟩),
        NativeResidualAttainment.initialMemory⟩ =
      ENNReal.ofReal (min (∑ j, P.specialistCost j)
        (P.nearCost + P.missing.mean P.specialistCost)) := by
  have he := NativeBatch.Quantitative.expected_charge_eq_of_output_memory
    NativeResidualAttainment.limits (NativeResidualOracle.sample T points candidates P invoice)
    controller.program (NativeResidualRouting.controller (adaptive p)).program _ _
    (NativeBatch.initial_invariant NativeResidualAttainment.limits ())
    (NativeBatch.initial_invariant NativeResidualAttainment.limits ()) rfl rfl
    (native_law _ _ ⟨NativeResidualAttainment.input T points candidates, p⟩
      NativeResidualAttainment.initialMemory)
    (fixed_terminates T points candidates P invoice hz (adaptive p))
  change NativeBatch.Quantitative.expected _ _ _ NativeBatch.Trace.charge 3 _ = _ at he
  rw [he]
  by_cases hb : adaptive p = true
  · rw [hb, min_eq_right ((adaptive_iff p P h).mp hb)]
    exact NativeResidualAttainment.native_expected_cost T points candidates P invoice hz hprice
  · have hf : adaptive p = false := Bool.eq_false_iff.mpr hb
    rw [hf, min_eq_left (le_of_not_ge (fun hc => hb ((adaptive_iff p P h).mpr hc)))]
    exact NativeResidualAll.native_expected_cost T points candidates P invoice hz 2
      (by omega) hprice

/-- The cost-aware code has actual native selection-only provenance, derived
from its compiled output/memory law and the admitted fixed strategies. -/
theorem native_selectionOnly (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (p : Prices)
    (accept : Finset
      (Fin (NativeResidualAttainment.input T points candidates).startup.system.rows.length)
      → Bool) :
    NativeUnboundedExecution.SelectionOnly controller.program
      (ConcurrentBatch.environment NativeResidualAttainment.limits
        (NativeResidualOracle.sample T points candidates P invoice))
      (NativeBatch.candidateParser (n := z + 1)
        (NativeResidualAttainment.input T points candidates).startup.system.rows.length)
      (decodeFamily (NativeResidualAttainment.input T points candidates).startup.system.rows.length)
      accept ⟨controller.program.initialConfig
        (encoding ⟨NativeResidualAttainment.input T points candidates, p⟩),
        NativeResidualAttainment.initialMemory⟩ := by
  have hadmit : NativeUnboundedExecution.SelectionOnly
      (NativeResidualRouting.controller (adaptive p)).program
      (ConcurrentBatch.environment NativeResidualAttainment.limits
        (NativeResidualOracle.sample T points candidates P invoice))
      (NativeBatch.candidateParser (n := z + 1)
        (NativeResidualAttainment.input T points candidates).startup.system.rows.length)
      (decodeFamily (NativeResidualAttainment.input T points candidates).startup.system.rows.length)
      accept ⟨(NativeResidualRouting.controller (adaptive p)).program.initialConfig
        (GuardedStartup.encoding (NativeResidualAttainment.input T points candidates)),
        NativeResidualAttainment.initialMemory⟩ := by
    cases he : adaptive p with
    | false =>
      exact NativeResidualAll.native_selectionOnly T points candidates P invoice hz 2
        (by omega) accept
    | true =>
      exact NativeResidualAttainment.native_selectionOnly T points candidates P invoice hz accept
  intro fuel next hn C hc ha
  have hh : NativeUnboundedExecution.halted next := by
    unfold NativeOpenSelection.result at hc
    split_ifs at hc with hs
    exact Option.isNone_iff_eq_none.mp hs
  have ht := (NativeUnboundedExecution.terminal_support _ _ _ _).mpr ⟨hh, fuel, hn⟩
  have hm : some (next.config.tapes.output, next.memory) ∈
      ((NativeUnboundedExecution.terminal controller.program
        (ConcurrentBatch.environment NativeResidualAttainment.limits
          (NativeResidualOracle.sample T points candidates P invoice))
        ⟨controller.program.initialConfig
          (encoding ⟨NativeResidualAttainment.input T points candidates, p⟩),
          NativeResidualAttainment.initialMemory⟩).map
            (Option.map fun w => (w.config.tapes.output, w.memory))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨some next, ht, rfl⟩
  rw [native_law] at hm
  obtain ⟨result, hr, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  cases result with
  | none => cases he
  | some before =>
    obtain ⟨ho, hm⟩ := Prod.mk.inj (Option.some.inj he)
    obtain ⟨hb, t, ht⟩ := (NativeUnboundedExecution.terminal_support _ _ _ before).mp hr
    have hc' : NativeOpenSelection.result
        (decodeFamily
          (NativeResidualAttainment.input T points candidates).startup.system.rows.length)
        before = some C := by
      have hh' : next.config.tapes.state = none := hh
      have hb' : before.config.tapes.state = none := hb
      simpa only [NativeOpenSelection.result, hh', hb', Option.isNone_none, ite_true, ho] using hc
    have hp := hadmit t before ht C hc' ha
    simpa only [hm] using hp

/-- The same single cost-aware program has certified tape success one by the
source oracle deadline. The actual stopped event is transported, not assumed. -/
theorem native_certified (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (p : Prices) :
    ((NativeUnboundedExecution.terminal controller.program
      (ConcurrentBatch.environment NativeResidualAttainment.limits
        (NativeResidualOracle.sample T points candidates P invoice))
      ⟨controller.program.initialConfig
        (encoding ⟨NativeResidualAttainment.input T points candidates, p⟩),
        NativeResidualAttainment.initialMemory⟩).map
      (BatchOutput.certified NativeResidualAttainment.limits
        (NativeResidualAttainment.input T points candidates).startup.system
        (NativeResidualAttainment.valid T points candidates (by omega)))) true = 1 := by
  rw [BatchOutput.terminal_certified, native_law, ← BatchOutput.terminal_certified]
  cases he : adaptive p with
  | false => exact NativeResidualAll.native_certified T points candidates P invoice hz 2 (by omega)
  | true => exact NativeResidualAttainment.native_certified T points candidates P invoice hz

/-- The same cost-aware native code is no dearer than every selection-only native
competitor with sure source-optimal output on this original priced input and oracle.
The competitor's probability-one requirement is the source admission condition;
no success, cost or optimality premise is imposed on the constructed program. -/
theorem native_minimal (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (p : Prices) (h : Reflects p P)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost)
    {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Unit)
    (hadmit : NativeUnboundedExecution.SelectionOnly machine
      (ConcurrentBatch.environment NativeResidualAttainment.limits
        (NativeResidualOracle.sample T points candidates P invoice))
      (NativeBatch.candidateParser (n := z + 1) m) (decodeFamily m)
      (NativeResidualPolicies.optimalAccept T candidates (by omega))
      ⟨machine.initialConfig (encoding ⟨NativeResidualAttainment.input T points candidates, p⟩),
        NativeResidualAttainment.initialMemory⟩)
    (hsuccess : ((NativeUnboundedExecution.terminal machine
      (ConcurrentBatch.environment NativeResidualAttainment.limits
        (NativeResidualOracle.sample T points candidates P invoice))
      ⟨machine.initialConfig (encoding ⟨NativeResidualAttainment.input T points candidates, p⟩),
        NativeResidualAttainment.initialMemory⟩).map fun result =>
        decide (optimalOutput (by omega)
          (NativeResidualPolicies.terminalOutput T candidates result) = 1)) true = 1) :
    NativeBatch.Quantitative.expected NativeResidualAttainment.limits
      (NativeResidualOracle.sample T points candidates P invoice) controller.program
      NativeBatch.Trace.charge 3
      ⟨controller.program.initialConfig
        (encoding ⟨NativeResidualAttainment.input T points candidates, p⟩),
        NativeResidualAttainment.initialMemory⟩ ≤
    NativeBatch.Quantitative.expected NativeResidualAttainment.limits
      (NativeResidualOracle.sample T points candidates P invoice) machine NativeBatch.Trace.charge 3
      ⟨machine.initialConfig (encoding ⟨NativeResidualAttainment.input T points candidates, p⟩),
        NativeResidualAttainment.initialMemory⟩ := by
  rw [native_expected_cost T points candidates P invoice hz p h hprice]
  exact NativeResidualPolicies.native_two_lower T points candidates P
    NativeResidualAttainment.limits invoice machine _
    (NativeBatch.initial_invariant NativeResidualAttainment.limits ()) rfl rfl
    (by omega) hprice hadmit hsuccess

/-- The cost-aware program attains the source minimum in the existing native
competitor class, on the original ABI with explicit price metadata. -/
theorem native_cost_mem (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (p : Prices) (h : Reflects p P)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    ENNReal.ofReal (min (∑ j, P.specialistCost j)
      (P.nearCost + P.missing.mean P.specialistCost)) ∈
    BatchOptimum.costs NativeResidualAttainment.limits
      (NativeResidualOracle.sample T points candidates P invoice)
      (packed ⟨NativeResidualAttainment.input T points candidates, p⟩) ()
      (NativeResidualAttainment.valid T points candidates (by omega)) 1 := by
  exact ⟨controller.tapes, controller.Controls, controller.finite, controller.program,
    native_selectionOnly T points candidates P invoice hz p _,
    (native_certified T points candidates P invoice hz p).ge,
    (native_expected_cost T points candidates P invoice hz p h hprice).symm⟩

/-- Exact original native optimum on the priced runtime input. Its upper witness
is the one cost-aware compiled program, rather than a proof choosing between codes. -/
theorem native_optimum (P : Parameters z) (invoice : Fin (z + 1) → ℕ)
    (hz : 3 ≤ z) (p : Prices) (h : Reflects p P)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    BatchOptimum.optimum NativeResidualAttainment.limits
      (NativeResidualOracle.sample T points candidates P invoice)
      (packed ⟨NativeResidualAttainment.input T points candidates, p⟩) ()
      (NativeResidualAttainment.valid T points candidates (by omega)) 1 =
      ENNReal.ofReal (min (∑ j, P.specialistCost j)
        (P.nearCost + P.missing.mean P.specialistCost)) := by
  apply le_antisymm (sInf_le (native_cost_mem T points candidates P invoice hz p h hprice))
  let c := (finCongr (NativeResidualEncoding.rows_length T points candidates)).trans candidates
  have hdata : (packed ⟨NativeResidualAttainment.input T points candidates, p⟩).startup.system =
      SourceEncoding.toNative (NativeResidualEncoding.source T points c) := by
    rw [NativeResidualEncoding.source_reindex]
    rfl
  have hlower := NativeResidualOptimum.two_lower T points
    (packed ⟨NativeResidualAttainment.input T points candidates, p⟩) c
    P NativeResidualAttainment.limits invoice (by omega)
    (NativeResidualAttainment.valid T points candidates (by omega)) hdata rfl hprice
  dsimp only [c, packed, NativeResidualAttainment.input] at hlower
  rwa [NativeResidualOracle.sample_reindex T points candidates
    (NativeResidualEncoding.rows_length T points candidates)] at hlower

end Cslib.Probability.StochasticOracle.NativeResidualCostChoice
