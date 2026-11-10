/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.UntilBad.ChooseTwo
public import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Event

/-!
# Stateful `ProbOracleComp` identical-until-bad hops and monotone bad-flag combinators

Cryptographic game hops on stateful oracle handlers typically augment a base state `σ` to `σ × Bool`
with a sticky Boolean bad flag (`FlagBad`), proving that two handlers agree on good transitions and
that dropping the flag recovers the unflagged executions. Meanwhile, adversaries with private
randomness (`ProbOracleComp spec`) run against `OracleComp.sumHandler` with stateless uniform coin
draws on the left, which preserve oracle state and never trigger bad events.

This module eliminates both sources of per-proof boilerplate:

1. **All-events `CloseTo` and `sumHandler` lifting for `OracleComp.IdenticalUntilBad`**:
   `IdenticalUntilBad.closeTo_run` upgrades the difference lemma to `CloseTo` on the joint
   result-and-state distribution `PMF (α × σ)`, and `IdenticalUntilBad.sumHandler_lift_left` lifts
   any external `IdenticalUntilBad` across memoryless left calls.
2. **Monotone Boolean bad-flag combinators (`FlagBad`, `IsFlagMonotone`,
   `IdenticalUntilBad.of_flag`, `withBadFlag`)**: `IsFlagMonotone` discharges absorption once for
   any handler that keeps `true` latched; `IdenticalUntilBad.of_flag` reduces `IdenticalUntilBad` to
   latched; `IdenticalUntilBad.of_flag` reduces `IdenticalUntilBad` to agreement on `(s, false)`
   transitions into `(s', false)`; `run_interpret_map_fst_of_flag` drops a flag whose marginal on
   `(a, s')` is independent of the flag bit; and `withBadFlag` packages a per-step `(a, (s', b'))`
   kernel into a monotone flagged handler automatically.
3. **`ProbOracleComp.IdenticalUntilBad` and `ProbOracleComp.runWith` bad-event bounds**: lifts
   `run_apply`, `symm`, `bind_apply_le`, `bad_eq`, `abs_sub_le`, `closeTo_run`, `closeTo_bind`,
   `runWith_map_fst`, `toOuterMeasure_bad_le`, `toOuterMeasure_bad_choose_two_cost_le`, and
   `toOuterMeasure_bad_choose_two_le` directly to `ProbOracleComp.runWith` under external query
   budgets (`ProbOracleComp.IsQueryBounded` / `OracleComp.IsCostBounded`), with no manual `Sum.inl`
   case splits.

## Main definitions

* `Cslib.OracleComp.FlagBad`: the bad-state predicate `st.2 = true` on `σ × Bool`.
* `Cslib.OracleComp.IsFlagMonotone`: Boolean flag monotonicity (`true` transitions stay `true`).
* `Cslib.OracleComp.withBadFlag`: lift a step returning `(a, (s', stepBad))` into a monotone
  `StateT (σ × Bool) PMF` handler via `||`.
* `Cslib.ProbOracleComp.IdenticalUntilBad`: identical-until-bad relation lifted to
  `ProbOracleComp.runWith`.

## Main results

* `Cslib.OracleComp.IdenticalUntilBad.closeTo_run`,
  `Cslib.OracleComp.IdenticalUntilBad.closeTo_bind`: all-events `CloseTo` difference lemmas.
* `Cslib.OracleComp.IdenticalUntilBad.sumHandler_lift_left`: lift `IdenticalUntilBad` across
  memoryless left calls.
* `Cslib.OracleComp.IsFlagMonotone.absorb`, `Cslib.OracleComp.IdenticalUntilBad.of_flag`,
  `Cslib.OracleComp.run_interpret_map_fst_of_flag`: generic monotone-flag constructors and marginal
  projection.
* `Cslib.OracleComp.withBadFlag_false`, `Cslib.OracleComp.isFlagMonotone_withBadFlag`,
  `Cslib.OracleComp.identicalUntilBad_withBadFlag`,
  `Cslib.OracleComp.run_interpret_withBadFlag_map_fst`: `withBadFlag` laws.
* `Cslib.OracleComp.IdenticalUntilBad.probOracleComp`,
  `Cslib.ProbOracleComp.identicalUntilBad_iff`,
  `Cslib.ProbOracleComp.IdenticalUntilBad.run_apply`,
  `Cslib.ProbOracleComp.IdenticalUntilBad.symm`,
  `Cslib.ProbOracleComp.IdenticalUntilBad.bind_apply_le`,
  `Cslib.ProbOracleComp.IdenticalUntilBad.bad_eq`,
  `Cslib.ProbOracleComp.IdenticalUntilBad.abs_sub_le`,
  `Cslib.ProbOracleComp.IdenticalUntilBad.closeTo_run`,
  `Cslib.ProbOracleComp.IdenticalUntilBad.closeTo_bind`,
  `Cslib.ProbOracleComp.IdenticalUntilBad.of_flag`,
  `Cslib.ProbOracleComp.identicalUntilBad_withBadFlag`,
  `Cslib.ProbOracleComp.runWith_map_fst`,
  `Cslib.ProbOracleComp.runWith_withBadFlag_map_fst`: `ProbOracleComp.runWith` difference lemmas and
  flag combinators.
* `Cslib.ProbOracleComp.toOuterMeasure_bad_le`,
  `Cslib.ProbOracleComp.toOuterMeasure_bad_choose_two_cost_le`,
  `Cslib.ProbOracleComp.toOuterMeasure_bad_choose_two_le`: linear and triangular bad-event union
  bounds for `ProbOracleComp.runWith`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Theorem 4.7.
-/

public section

namespace Cslib.OracleComp

open Probability
open scoped ENNReal

section CloseToAndSum

variable {ι σ α β : Type} {spec : ι → Type}
  {first second : (q : ι) → StateT σ PMF (spec q)} {bad : σ → Prop}

/-- **All-events difference lemma**: handlers that agree until `bad` induce joint output-and-state
distributions within `CloseTo` error equal to the probability of reaching a bad state. -/
theorem IdenticalUntilBad.closeTo_run (h : IdenticalUntilBad first second bad)
    (program : OracleComp spec α) (s : σ) :
    CloseTo ((interpret first program).run s) ((interpret second program).run s)
      (((interpret first program).run s).toOuterMeasure {x | bad x.2}) := by
  classical
  intro event
  let test : α × σ → PMF Bool := fun out => PMF.pure (decide (out ∈ event))
  have ht (μ : PMF (α × σ)) : (μ.bind test) true = μ.toOuterMeasure event := by
    change (μ.map (fun out => decide (out ∈ event))) true = _
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 1
    ext out
    simp
  have hb := h.bind_apply_le program s test true
  rwa [ht, ht] at hb

/-- **All-events difference lemma for continuations**: postprocessing two identical-until-bad runs
by a shared randomized continuation `next` preserves `CloseTo` within the bad-event probability. -/
theorem IdenticalUntilBad.closeTo_bind (h : IdenticalUntilBad first second bad)
    (program : OracleComp spec α) (s : σ) (next : α × σ → PMF β) :
    CloseTo (((interpret first program).run s).bind next)
      (((interpret second program).run s).bind next)
      (((interpret first program).run s).toOuterMeasure {x | bad x.2}) :=
  (h.closeTo_run program s).bind_left next

/-- Lifting a memoryless handler on the left of `sumHandler` preserves `IdenticalUntilBad` on the
right. -/
theorem IdenticalUntilBad.sumHandler_lift_left {ι₁ : Type} {spec₁ : ι₁ → Type}
    (left : (q : ι₁) → PMF (spec₁ q)) (h : IdenticalUntilBad first second bad) :
    IdenticalUntilBad
      (sumHandler (fun q => StateT.lift (left q)) first)
      (sumHandler (fun q => StateT.lift (left q)) second) bad where
  agree q s hs a s' hs' := by
    cases q with
    | inl q₁ => rfl
    | inr q₂ => exact h.agree q₂ s hs a s' hs'
  absorb_first q s hs x hx := by
    cases q with
    | inl q₁ =>
      change x ∈ ((left q₁).map (·, s)).support at hx
      obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hs
    | inr q₂ => exact h.absorb_first q₂ s hs x hx
  absorb_second q s hs x hx := by
    cases q with
    | inl q₁ =>
      change x ∈ ((left q₁).map (·, s)).support at hx
      obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hs
    | inr q₂ => exact h.absorb_second q₂ s hs x hx

end CloseToAndSum

/-! ### Monotone Boolean bad-flag combinators -/

section BadFlag

variable {ι σ α : Type} {spec : ι → Type}

/-- Bad-state predicate on an augmented state `σ × Bool` testing whether the Boolean flag is
`true`. -/
abbrev FlagBad {σ : Type} (st : σ × Bool) : Prop := st.2 = true

/-- A stateful handler on `σ × Bool` has a *monotone bad flag* when every supported transition from
`(s, true)` preserves `FlagBad`. -/
@[expose] def IsFlagMonotone (handler : (q : ι) → StateT (σ × Bool) PMF (spec q)) : Prop :=
  ∀ q s, ∀ x ∈ (handler q (s, true)).support, FlagBad x.2

/-- A monotone Boolean flag makes `FlagBad` absorbing on every state. -/
theorem IsFlagMonotone.absorb {handler : (q : ι) → StateT (σ × Bool) PMF (spec q)}
    (h : IsFlagMonotone handler) :
    ∀ q st, FlagBad st → ∀ x ∈ (handler q st).support, FlagBad x.2 := by
  rintro q ⟨s, b⟩ hst x hx
  dsimp only [FlagBad] at hst
  subst hst
  exact h q s x hx

/-- Construct `IdenticalUntilBad` on `σ × Bool` from flag monotonicity of both handlers and
pointwise agreement on `(s, false)` transitions that remain at `(s', false)`. -/
theorem IdenticalUntilBad.of_flag {first second : (q : ι) → StateT (σ × Bool) PMF (spec q)}
    (hfirst : IsFlagMonotone first) (hsecond : IsFlagMonotone second)
    (hagree : ∀ q s a s', first q (s, false) (a, (s', false)) =
      second q (s, false) (a, (s', false))) :
    IdenticalUntilBad first second FlagBad where
  agree := by
    rintro q ⟨s, b⟩ hs a ⟨s', b'⟩ hs'
    have hb : b = false := Bool.eq_false_iff.mpr hs
    have hb' : b' = false := Bool.eq_false_iff.mpr hs'
    subst hb hb'
    exact hagree q s a s'
  absorb_first := hfirst.absorb
  absorb_second := hsecond.absorb

/-- Projecting away the Boolean flag of a handler on `σ × Bool` recovers an unflagged execution
whenever each step's `(a, s')` marginal is independent of the input flag. -/
theorem run_interpret_map_fst_of_flag (flagged : (q : ι) → StateT (σ × Bool) PMF (spec q))
    (unflagged : (q : ι) → StateT σ PMF (spec q))
    (hstep : ∀ q s b, (flagged q (s, b)).map (Prod.map id Prod.fst) = unflagged q s)
    (program : OracleComp spec α) (s : σ) (b : Bool) :
    ((interpret flagged program).run (s, b)).map (Prod.map id Prod.fst) =
      (interpret unflagged program).run s :=
  run_interpret_map_state flagged unflagged Prod.fst (fun q ⟨s', b'⟩ => hstep q s' b') program
    (s, b)

/-- Lift a step kernel `step : (q : ι) → σ → PMF (spec q × (σ × Bool))` returning an answer, next
state, and per-call bad indicator into a stateful handler on `σ × Bool` that latches the flag via
`||`. -/
@[expose] noncomputable def withBadFlag (step : (q : ι) → σ → PMF (spec q × (σ × Bool)))
    (q : ι) : StateT (σ × Bool) PMF (spec q) :=
  fun (s, b) => (step q s).map (Prod.map id (Prod.map id (b || ·)))

/-- Starting from `b = false`, one step of `withBadFlag step` has the exact law `step q s`. -/
@[simp] theorem withBadFlag_false (step : (q : ι) → σ → PMF (spec q × (σ × Bool)))
    (q : ι) (s : σ) :
    withBadFlag step q (s, false) = step q s := by
  have hid : (Prod.map (id : spec q → spec q) (Prod.map (id : σ → σ) (false || ·))) = id := by
    ext ⟨a, s', b'⟩ <;> simp
  simp only [withBadFlag, hid, PMF.map_id]

/-- Every handler built with `withBadFlag` has a monotone Boolean bad flag. -/
theorem isFlagMonotone_withBadFlag (step : (q : ι) → σ → PMF (spec q × (σ × Bool))) :
    IsFlagMonotone (withBadFlag step) := by
  intro q s x hx
  simp only [withBadFlag, Bool.true_or, PMF.mem_support_map_iff] at hx
  obtain ⟨⟨a, s', b'⟩, -, rfl⟩ := hx
  rfl

/-- Two `withBadFlag` handlers are `IdenticalUntilBad` whenever their underlying kernels assign
equal probability to every unflagged outcome `(a, (s', false))`. -/
theorem identicalUntilBad_withBadFlag (step₁ step₂ : (q : ι) → σ → PMF (spec q × (σ × Bool)))
    (hagree : ∀ q s a s', step₁ q s (a, (s', false)) = step₂ q s (a, (s', false))) :
    IdenticalUntilBad (withBadFlag step₁) (withBadFlag step₂) FlagBad :=
  IdenticalUntilBad.of_flag (isFlagMonotone_withBadFlag step₁) (isFlagMonotone_withBadFlag step₂)
    fun q s a s' => by simp only [withBadFlag_false, hagree q s a s']

/-- Dropping the Boolean flag after one step of `withBadFlag` drops the per-step indicator,
independently of the prior flag `b`. -/
@[simp] theorem withBadFlag_map_fst (step : (q : ι) → σ → PMF (spec q × (σ × Bool)))
    (q : ι) (s : σ) (b : Bool) :
    (withBadFlag step q (s, b)).map (Prod.map id Prod.fst) =
      (step q s).map (Prod.map id Prod.fst) := by
  simp only [withBadFlag, PMF.map_comp]
  rfl

/-- Dropping the Boolean flag of an adaptive `withBadFlag` execution recovers the unflagged
execution whenever each step's `(a, s')` marginal matches `unflagged`. -/
theorem run_interpret_withBadFlag_map_fst (step : (q : ι) → σ → PMF (spec q × (σ × Bool)))
    (unflagged : (q : ι) → StateT σ PMF (spec q))
    (hstep : ∀ q s, (step q s).map (Prod.map id Prod.fst) = unflagged q s)
    (program : OracleComp spec α) (s : σ) (b : Bool) :
    ((interpret (withBadFlag step) program).run (s, b)).map (Prod.map id Prod.fst) =
      (interpret unflagged program).run s :=
  run_interpret_map_fst_of_flag (withBadFlag step) unflagged
    (fun q s' b' => (withBadFlag_map_fst step q s' b').trans (hstep q s')) program s b

end BadFlag

end Cslib.OracleComp

namespace Cslib.ProbOracleComp

open Probability OracleComp
open scoped ENNReal

variable {Query State α β : Type} {spec : Query → Type}

/-- Two stateful external handlers agree until `bad` under `ProbOracleComp.runWith`: their lifted
`sumHandler`s with private uniform coin sampling satisfy `OracleComp.IdenticalUntilBad`. -/
@[expose] def IdenticalUntilBad (first second : (q : Query) → StateT State PMF (spec q))
    (bad : State → Prop) : Prop :=
  OracleComp.IdenticalUntilBad
    (sumHandler (fun m => StateT.lift (ProbComp.unifOracle m)) first)
    (sumHandler (fun m => StateT.lift (ProbComp.unifOracle m)) second) bad

/-- Lift `OracleComp.IdenticalUntilBad` on external handlers to `ProbOracleComp.IdenticalUntilBad`
across private uniform sampling. -/
theorem _root_.Cslib.OracleComp.IdenticalUntilBad.probOracleComp
    {first second : (q : Query) → StateT State PMF (spec q)} {bad : State → Prop}
    (h : OracleComp.IdenticalUntilBad first second bad) :
    ProbOracleComp.IdenticalUntilBad first second bad :=
  h.sumHandler_lift_left ProbComp.unifOracle

/-- Restrict `ProbOracleComp.IdenticalUntilBad` back to the external handlers. -/
theorem IdenticalUntilBad.toOracleComp
    {first second : (q : Query) → StateT State PMF (spec q)} {bad : State → Prop}
    (h : ProbOracleComp.IdenticalUntilBad first second bad) :
    OracleComp.IdenticalUntilBad first second bad where
  agree q s hs a s' hs' := h.agree (.inr q) s hs a s' hs'
  absorb_first q s hs x hx := h.absorb_first (.inr q) s hs x hx
  absorb_second q s hs x hx := h.absorb_second (.inr q) s hs x hx

/-- `ProbOracleComp.IdenticalUntilBad` holds if and only if the external handlers satisfy
`OracleComp.IdenticalUntilBad`. -/
theorem identicalUntilBad_iff {first second : (q : Query) → StateT State PMF (spec q)}
    {bad : State → Prop} :
    ProbOracleComp.IdenticalUntilBad first second bad ↔
      OracleComp.IdenticalUntilBad first second bad :=
  ⟨IdenticalUntilBad.toOracleComp, OracleComp.IdenticalUntilBad.probOracleComp⟩

namespace IdenticalUntilBad

variable {first second : (q : Query) → StateT State PMF (spec q)} {bad : State → Prop}

/-- Construct `ProbOracleComp.IdenticalUntilBad` on `State × Bool` from monotone Boolean flags on
both external handlers and agreement on `(s, false) ↦ (a, (s', false))`. -/
theorem of_flag {first second : (q : Query) → StateT (State × Bool) PMF (spec q)}
    (hfirst : IsFlagMonotone first) (hsecond : IsFlagMonotone second)
    (hagree : ∀ q s a s', first q (s, false) (a, (s', false)) =
      second q (s, false) (a, (s', false))) :
    ProbOracleComp.IdenticalUntilBad first second FlagBad :=
  (OracleComp.IdenticalUntilBad.of_flag hfirst hsecond hagree).probOracleComp

/-- Symmetric relation for `ProbOracleComp.IdenticalUntilBad`. -/
theorem symm (h : ProbOracleComp.IdenticalUntilBad first second bad) :
    ProbOracleComp.IdenticalUntilBad second first bad :=
  OracleComp.IdenticalUntilBad.symm h

/-- Equal outcome probabilities at good final states under `ProbOracleComp.runWith`. -/
theorem run_apply (h : ProbOracleComp.IdenticalUntilBad first second bad)
    (program : ProbOracleComp spec α) (s : State) (a : α) (s' : State) (hs' : ¬bad s') :
    runWith first program s (a, s') = runWith second program s (a, s') :=
  OracleComp.IdenticalUntilBad.run_apply h program s a s' hs'

/-- **The difference lemma** ([BonehShoup2023], Theorem 4.7) for `ProbOracleComp.runWith`. -/
theorem bind_apply_le (h : ProbOracleComp.IdenticalUntilBad first second bad)
    (program : ProbOracleComp spec α) (s : State) (next : α × State → PMF β) (b : β) :
    (runWith first program s).bind next b ≤
      (runWith second program s).bind next b +
        (runWith first program s).toOuterMeasure {x | bad x.2} :=
  OracleComp.IdenticalUntilBad.bind_apply_le h program s next b

/-- Both external handlers reach `bad` with equal probability under `ProbOracleComp.runWith`. -/
theorem bad_eq (h : ProbOracleComp.IdenticalUntilBad first second bad)
    (program : ProbOracleComp spec α) (s : State) :
    (runWith first program s).toOuterMeasure {x | bad x.2} =
      (runWith second program s).toOuterMeasure {x | bad x.2} :=
  OracleComp.IdenticalUntilBad.bad_eq h program s

/-- **Two-sided difference lemma** ([BonehShoup2023], Theorem 4.7) for `ProbOracleComp.runWith`. -/
theorem abs_sub_le (h : ProbOracleComp.IdenticalUntilBad first second bad)
    (program : ProbOracleComp spec α) (s : State) (next : α × State → PMF β) (b : β) :
    |((runWith first program s).bind next b).toReal -
        ((runWith second program s).bind next b).toReal| ≤
      ((runWith first program s).toOuterMeasure {x | bad x.2}).toReal :=
  OracleComp.IdenticalUntilBad.abs_sub_le h program s next b

/-- All-events `CloseTo` difference lemma on joint `(α × State)` outcomes of
`ProbOracleComp.runWith`. -/
theorem closeTo_run (h : ProbOracleComp.IdenticalUntilBad first second bad)
    (program : ProbOracleComp spec α) (s : State) :
    CloseTo (runWith first program s) (runWith second program s)
      ((runWith first program s).toOuterMeasure {x | bad x.2}) :=
  OracleComp.IdenticalUntilBad.closeTo_run h program s

/-- All-events `CloseTo` difference lemma across a continuation `next` after
`ProbOracleComp.runWith`. -/
theorem closeTo_bind (h : ProbOracleComp.IdenticalUntilBad first second bad)
    (program : ProbOracleComp spec α) (s : State) (next : α × State → PMF β) :
    CloseTo ((runWith first program s).bind next) ((runWith second program s).bind next)
      ((runWith first program s).toOuterMeasure {x | bad x.2}) :=
  OracleComp.IdenticalUntilBad.closeTo_bind h program s next

end IdenticalUntilBad

/-- Two external `withBadFlag` handlers satisfy `ProbOracleComp.IdenticalUntilBad` whenever their
underlying kernels assign equal mass to unflagged outcomes `(a, (s', false))`. -/
theorem identicalUntilBad_withBadFlag
    (step₁ step₂ : (q : Query) → State → PMF (spec q × (State × Bool)))
    (hagree : ∀ q s a s', step₁ q s (a, (s', false)) = step₂ q s (a, (s', false))) :
    ProbOracleComp.IdenticalUntilBad (withBadFlag step₁) (withBadFlag step₂) FlagBad :=
  (OracleComp.identicalUntilBad_withBadFlag step₁ step₂ hagree).probOracleComp

/-- Projecting away the Boolean flag of an external handler on `State × Bool` recovers the unflagged
`ProbOracleComp.runWith` execution whenever each step's `(a, s')` marginal is independent of `b`. -/
theorem runWith_map_fst (flagged : (q : Query) → StateT (State × Bool) PMF (spec q))
    (unflagged : (q : Query) → StateT State PMF (spec q))
    (hstep : ∀ q s b, (flagged q (s, b)).map (Prod.map id Prod.fst) = unflagged q s)
    (program : ProbOracleComp spec α) (s : State) (b : Bool) :
    (runWith flagged program (s, b)).map (Prod.map id Prod.fst) = runWith unflagged program s :=
  runWith_map_state flagged unflagged Prod.fst (fun q ⟨s', b'⟩ => hstep q s' b') program (s, b)

/-- Projecting away the Boolean flag of `withBadFlag step` under `ProbOracleComp.runWith` recovers
`runWith unflagged` whenever each step's `(a, s')` marginal matches `unflagged`. -/
theorem runWith_withBadFlag_map_fst (step : (q : Query) → State → PMF (spec q × (State × Bool)))
    (unflagged : (q : Query) → StateT State PMF (spec q))
    (hstep : ∀ q s, (step q s).map (Prod.map id Prod.fst) = unflagged q s)
    (program : ProbOracleComp spec α) (s : State) (b : Bool) :
    (runWith (withBadFlag step) program (s, b)).map (Prod.map id Prod.fst) =
      runWith unflagged program s :=
  runWith_map_fst (withBadFlag step) unflagged
    (fun q s' b' => (withBadFlag_map_fst step q s' b').trans (hstep q s')) program s b

/-! ### Bad-event union bounds for `ProbOracleComp.runWith` -/

private theorem toOuterMeasure_lift_unif_bad_eq_zero {bad : State → Prop} {s : State}
    (hs : ¬bad s) (m : ℕ) :
    (StateT.lift (σ := State) (ProbComp.unifOracle m) s).toOuterMeasure
      {x : Fin (m + 1) × State | bad x.2} = 0 := by
  change ((ProbComp.unifOracle m).map (·, s)).toOuterMeasure {x | bad x.2} = 0
  rw [PMF.toOuterMeasure_apply_eq_zero_iff]
  refine Set.disjoint_left.mpr fun x hx hbad => hs ?_
  obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  exact hbad

/-- **Accumulated probability of a bad state under `ProbOracleComp.runWith`.** Let each external
call `q` from a good state turn bad with probability at most `cost q * budget s` and raise `budget`
by at most `δ` (while private coin draws cost nothing and leave state unchanged). Then a program
making at most `n` external queries (`program.IsQueryBounded n`), whose external calls have cost at
most `k`, reaches a bad state from `s` with probability at most `k * (budget s + n * δ)`. -/
theorem toOuterMeasure_bad_le {handler : (q : Query) → StateT State PMF (spec q)}
    {bad : State → Prop} (cost : Query → ℕ) (budget : State → ℝ≥0∞) (δ : ℝ≥0∞)
    (hstep : ∀ q s, ¬bad s → (handler q s).toOuterMeasure {x | bad x.2} ≤ cost q * budget s)
    (hgrow : ∀ q s, ¬bad s → ∀ x ∈ (handler q s).support, ¬bad x.2 →
      budget x.2 ≤ budget s + δ)
    {program : ProbOracleComp spec α} {n k : ℕ} (hn : program.IsQueryBounded n)
    (hk : IsCostBounded (Sum.elim (fun _ => 0) cost) program k) {s : State} (hs : ¬bad s) :
    (runWith handler program s).toOuterMeasure {x | bad x.2} ≤ k * (budget s + n * δ) := by
  have h := OracleComp.toOuterMeasure_bad_le_two
    (handler := sumHandler (fun m => StateT.lift (ProbComp.unifOracle m)) handler) (bad := bad)
    (Sum.elim (fun _ => 0) cost) (Sum.elim (fun _ => 0) (fun _ => 1)) budget 0 δ 0
    (fun q st hst => by
      cases q with
      | inl m => simp [toOuterMeasure_lift_unif_bad_eq_zero hst m]
      | inr q => simpa only [Sum.elim_inr, mul_zero, add_zero] using hstep q st hst)
    (fun q st hst x hx hgood => by
      cases q with
      | inl m =>
        change x ∈ ((ProbComp.unifOracle m).map (·, st)).support at hx
        obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        simp
      | inr q =>
        simpa only [Sum.elim_inr, mul_zero, add_zero, Nat.cast_one, one_mul] using
          hgrow q st hst x hx hgood)
    hk hn hs
  change (runWith handler program s).toOuterMeasure {x | bad x.2} ≤ _ at h
  simpa only [mul_zero, add_zero] using h

/-- **Two-cost triangular bad-state union bound under `ProbOracleComp.runWith`.** When external
calls carry budgets `k₁` for `cost₁` (charging `(cost₁ q * size s) * δ` and growing `size`) and `k₂`
for `cost₂` (growing `size` passively), `runWith handler program s` reaches `bad` with probability
at most `(k₁ * size s + k₁ * k₂ + k₁.choose 2) * δ`. -/
theorem toOuterMeasure_bad_choose_two_cost_le {handler : (q : Query) → StateT State PMF (spec q)}
    {bad : State → Prop} (cost₁ cost₂ : Query → ℕ) (size : State → ℕ) (δ : ℝ≥0∞)
    (hstep : ∀ q s, ¬bad s →
      (handler q s).toOuterMeasure {x | bad x.2} ≤ (cost₁ q * size s : ℕ) * δ)
    (hgrow : ∀ q s, ¬bad s → ∀ x ∈ (handler q s).support, ¬bad x.2 →
      size x.2 ≤ size s + cost₁ q + cost₂ q)
    {program : ProbOracleComp spec α} {k₁ k₂ : ℕ}
    (hk₁ : IsCostBounded (Sum.elim (fun _ => 0) cost₁) program k₁)
    (hk₂ : IsCostBounded (Sum.elim (fun _ => 0) cost₂) program k₂)
    {s : State} (hs : ¬bad s) :
    (runWith handler program s).toOuterMeasure {x | bad x.2} ≤
      (k₁ * size s + k₁ * k₂ + k₁.choose 2 : ℕ) * δ :=
  OracleComp.toOuterMeasure_bad_choose_two_cost_le
    (Sum.elim (fun _ => 0) cost₁) (Sum.elim (fun _ => 0) cost₂) size δ
    (fun q st hst => by
      cases q with
      | inl m => simp [toOuterMeasure_lift_unif_bad_eq_zero hst m]
      | inr q => exact hstep q st hst)
    (fun q st hst x hx hgood => by
      cases q with
      | inl m =>
        change x ∈ ((ProbComp.unifOracle m).map (·, st)).support at hx
        obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        simp
      | inr q => exact hgrow q st hst x hx hgood)
    hk₁ hk₂ hs

/-- **Triangular bad-state union bound under `ProbOracleComp.runWith`.** If each external call from
a good state `s` turns bad with probability at most `size s * δ` and increases `size` by at most
`1`, then a program making at most `n` external queries (`program.IsQueryBounded n`) reaches a bad
state from `s` with probability at most `(n * size s + n.choose 2) * δ`. -/
theorem toOuterMeasure_bad_choose_two_le {handler : (q : Query) → StateT State PMF (spec q)}
    {bad : State → Prop} (size : State → ℕ) (δ : ℝ≥0∞)
    (hstep : ∀ q s, ¬bad s → (handler q s).toOuterMeasure {x | bad x.2} ≤ size s * δ)
    (hgrow : ∀ q s, ¬bad s → ∀ x ∈ (handler q s).support, ¬bad x.2 → size x.2 ≤ size s + 1)
    {program : ProbOracleComp spec α} {n : ℕ} (hn : program.IsQueryBounded n)
    {s : State} (hs : ¬bad s) :
    (runWith handler program s).toOuterMeasure {x | bad x.2} ≤
      (n * size s + n.choose 2 : ℕ) * δ := by
  simpa only [mul_zero, add_zero] using
    toOuterMeasure_bad_choose_two_cost_le (fun _ => 1) (fun _ => 0) size δ
      (fun q s hs => by simpa only [one_mul, Nat.cast_id] using hstep q s hs)
      (fun q s hs x hx hgood => by simpa only [add_zero] using hgrow q s hs x hx hgood)
      hn (IsCostBounded.of_forall_cost_eq_zero (fun q => by cases q <;> rfl) program) hs

end Cslib.ProbOracleComp
