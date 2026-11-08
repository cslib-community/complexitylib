/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.NativeOpenExecution
public import Mathlib.Data.Finset.Union
import Complexity.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Native open selection-only observations and behavioral path laws

[Wang2027], model/selection-only definition, PDF pp. 4--6, Theorem 5/Appendix A.5,
pp. 12,16, and Theorem 6, p. 13. This is original bridge infrastructure toward
those endpoints, not a full source theorem or an oracle-turn compiler.

Actual accepted outputs are observed only after native halting. Source admission
constrains successful outputs only. Normalization removes unproposed failed
families using `none`, preserving accepted empty covers as well as full joint
history/success/bill/duration laws. The behavioral kernels are derived from the
actual native hidden-state path, not supplied as an admission hypothesis.

## Main results

* `normalized_provenance`: every retained family comes from actual responses.
* `normalized_outcome_law`: failure normalization preserves the full stopped joint law.
* `behavioral_outcome_law`: derived native/public path, stopping, success and resource law.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeOpenSelection
open NativeOpenExecution Turing
open scoped NNReal
variable {Operation Private Control J : Type} {k : ℕ} {input : List Bool}
variable [DecidableEq Operation] [DecidableEq J]

/-- Decode valid proposals from each actual raw query/response pair. -/
@[expose] def proposals (parse : Operation → List Bool → List Bool → Finset J)
    (events : List (Event Operation)) : Finset J :=
  events.foldr (fun event found => parse event.operation event.request event.reply.word ∪ found) ∅

/-- Read an actual result only when the native machine has halted. Clock
exhaustion at a live configuration does not turn a partial output into success. -/
@[expose] def result (decode : List Bool → Option (Finset J))
    (world : World k Control Operation Private input) : Option (Finset J) :=
  if world.config.tapes.state.isNone then decode world.config.tapes.output else none

/-- Selection-only normalization uses a failure flag, retaining the distinction
between failure and an accepted empty cover on an empty ground instance. -/
@[expose] def normalized (parse : Operation → List Bool → List Bool → Finset J)
    (decode : List Bool → Option (Finset J)) (world : World k Control Operation Private input) :
    Option (Finset J) :=
  (result decode world).filter (fun C => C ⊆ proposals parse world.memory.events)

omit [DecidableEq Operation] in
/-- Every retained family has actual response provenance, including null paths. -/
theorem normalized_provenance (parse : Operation → List Bool → List Bool → Finset J)
    (decode : List Bool → Option (Finset J)) (world : World k Control Operation Private input)
    (C : Finset J) (h : normalized parse decode world = some C) :
    C ⊆ proposals parse world.memory.events := by
  have hp : result decode world = some C ∧ C ⊆ proposals parse world.memory.events := by
    simpa [normalized] using h
  exact hp.2

/-- Boolean acceptance includes the failure flag explicitly. -/
@[expose] def accepted (accept : Finset J → Bool) (output : Option (Finset J)) : Bool :=
  output.any accept

variable (machine : MultiTapePTM k Bool Control Operation) (env : Environment Operation Private)
variable (parse : Operation → List Bool → List Bool → Finset J)
variable (decode : List Bool → Option (Finset J)) (accept : Finset J → Bool)

/-- Source successful-output-only provenance on the actual native execution.
No joint-law, behavioral-kernel, resource or stopping conclusion is a premise. -/
@[expose] def SelectionOnly (fuel : ℕ) (world : World k Control Operation Private input) : Prop :=
  ∀ next ∈ (execute machine env fuel world).support, ∀ C,
    result decode next = some C → accept C = true → C ⊆ proposals parse next.memory.events

private theorem normalized_acceptance (fuel : ℕ)
    (world next : World k Control Operation Private input)
    (h : SelectionOnly machine env parse decode accept fuel world)
    (hn : next ∈ (execute machine env fuel world).support) :
    accepted accept (normalized parse decode next) = accepted accept (result decode next) := by
  cases hr : result decode next with
  | none => simp [accepted, normalized, hr]
  | some C =>
    by_cases hp : C ⊆ proposals parse next.memory.events
    · simp [accepted, normalized, hr, hp]
    · have ha : accept C = false := by
        cases he : accept C
        · rfl
        · exact False.elim (hp (h next hn C hr he))
      simp [accepted, normalized, hr, hp, ha]

/-- Full public state used for behavioral conditioning. -/
structure View (Operation J : Type) where
  /-- Entire query/response path and all resource observations. -/
  events : List (Event Operation)
  /-- Actual native halting is separate from a missing or failed output. -/
  halted : Bool
  /-- Normalized halted output, or the failure flag. -/
  output : Option (Finset J)

/-- Joint accepted-output and resource observation; resource fields are computed
from the same event path, without an independent cost/duration law. -/
structure Outcome (Operation : Type) where
  /-- Actual query and response history. -/
  events : List (Event Operation)
  /-- Actual native stopping event. -/
  halted : Bool
  /-- Accepted-output event. -/
  success : Bool
  /-- Accumulated issued tokens. -/
  tokens : ℝ≥0
  /-- Accumulated external physical duration. -/
  duration : ℝ≥0

/-- The normalized public view does not expose private work tapes or oracle state. -/
@[expose] def view (world : World k Control Operation Private input) : View Operation J :=
  ⟨world.memory.events, world.config.tapes.state.isNone, normalized parse decode world⟩

/-- Read acceptance and both resources from a public view. -/
@[expose] def outcome (v : View Operation J) : Outcome Operation :=
  ⟨v.events, v.halted, accepted accept v.output, tokenBill v.events, elapsed v.events⟩

/-- The entire native joint event/resource law survives failure normalization. -/
theorem normalized_outcome_law (fuel : ℕ) (world : World k Control Operation Private input)
    (h : SelectionOnly machine env parse decode accept fuel world) :
    (execute machine env fuel world).map (fun next => outcome accept (view parse decode next)) =
      (execute machine env fuel world).map
        (fun next => outcome accept
          ⟨next.memory.events, next.config.tapes.state.isNone, result decode next⟩) := by
  simp only [PMF.map]
  apply PMF.bind_congr_on_support
  intro next hn
  have he := normalized_acceptance machine env parse decode accept fuel world next h hn
  exact congrArg PMF.pure (by simp only [outcome, view, he])

/-- Constructed complete-public-history kernels preserve the actual native joint
path/stopping/success/bill/duration law. The time index counts native instructions, so
silent local steps have not been collapsed into oracle turns. -/
theorem behavioral_outcome_law (fuel : ℕ) (world : World k Control Operation Private input)
    (h : SelectionOnly machine env parse decode accept fuel world) :
    (ObservedProcess.publicLaw (step machine env) (view parse decode) fuel world).map
        (fun history => outcome accept (history.headD (view parse decode world))) =
      (execute machine env fuel world).map
        (fun next => outcome accept
          ⟨next.memory.events, next.config.tapes.state.isNone, result decode next⟩) := by
  have he := ObservedProcess.public_current (step machine env) (view parse decode) fuel world
  rw [← execute_eq_stateLaw machine env] at he
  have he' := congrArg (PMF.map (outcome accept)) he
  simp only [PMF.map_comp, Function.comp_def] at he'
  exact he'.trans (normalized_outcome_law machine env parse decode accept fuel world h)

end Cslib.Probability.NativeOpenSelection
