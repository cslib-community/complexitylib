/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomOracle.Sum
import CslibFrontier.Languages.Probabilistic.Semantics
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Probability.Product.Split

/-!
# Lazy random oracles behind a represented state

A game usually keeps its random-oracle tables in its own state: association lists, several caches
in a record, or caches for several oracles at once. When each call of such a handler, read through
a map `rep` from the game state to a `RandomOracle.Cache`, is a lazy `RandomOracle.answer`, the
game has the law of completing the represented cache once and answering every call from the
completed table (`eval_run_interpret_eq_complete_bind`). The per-call hypothesis is the only
game-specific step of an eager/lazy argument.

Several oracles are one oracle on the sum of their interfaces. `RandomOracle.Cache.sum`, re-exported
here, joins their caches, so that one represented state serves them all, and `bind_complete_sum`
splits the completed table back into one table per oracle.

## Main results

* `Cslib.RandomOracle.run_interpret_eq_complete_bind`,
  `Cslib.RandomOracle.eval_run_interpret_eq_complete_bind`: a handler that is a lazy random oracle
  on a represented cache has the law of the completed table.
* `Cslib.RandomOracle.run_interpret_bind_complete`,
  `Cslib.RandomOracle.eval_run_interpret_bind_complete`: the joint law of its result and the
  completion of its final represented cache, the relation an approximate simulation
  (`OracleComp.closeTo_run_interpret_simulation`) is stated against.
* `Cslib.RandomOracle.bind_complete_sum`: completing a joined cache completes each side
  independently.
-/

public section

namespace Cslib.RandomOracle

open Probability
open scoped Cslib

section Represented

variable {Query State α : Type} {Response : Query → Type} [DecidableEq Query] [Fintype Query]
  [∀ q, Finite (Response q)]

/-- A stateful handler that, read through `rep`, answers every call as the lazy random oracle
`answer distribution` has the joint law of its result and the completion of its represented final
cache: completing the represented initial cache, answering every call from the completed table, and
keeping that table. -/
theorem run_interpret_bind_complete (distribution : (q : Query) → PMF (Response q))
    (impl : (q : Query) → StateT State PMF (Response q)) (rep : State → Cache Response)
    (step : ∀ q s, (impl q s).map (fun z => (z.1, rep z.2)) = answer distribution q (rep s))
    (program : OracleComp Response α) (s : State) :
    ((OracleComp.interpret impl program).run s).bind
        (fun z => (complete distribution (rep z.2)).map (z.1, ·)) =
      (complete distribution (rep s)).bind fun table =>
        (OracleComp.interpret (fun q => PMF.pure (table q)) program).map (·, table) := by
  have hcomplete := run_interpret_answer_complete distribution program (rep s)
  rw [← OracleComp.run_interpret_map_state impl _ rep step] at hcomplete
  simpa only [PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.bind_map,
    Function.comp_def] using hcomplete

/-- A stateful handler that, read through `rep`, answers every call as the lazy random oracle
`answer distribution` has the result law of completing the represented initial cache and answering
every call from the completed table. -/
theorem run_interpret_eq_complete_bind (distribution : (q : Query) → PMF (Response q))
    (impl : (q : Query) → StateT State PMF (Response q)) (rep : State → Cache Response)
    (step : ∀ q s, (impl q s).map (fun z => (z.1, rep z.2)) = answer distribution q (rep s))
    (program : OracleComp Response α) (s : State) :
    ((OracleComp.interpret impl program).run s).map Prod.fst =
      (complete distribution (rep s)).bind fun table =>
        OracleComp.interpret (fun q => PMF.pure (table q)) program := by
  have h := congrArg (PMF.map Prod.fst)
    (run_interpret_bind_complete distribution impl rep step program s)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at h
  change ((OracleComp.interpret impl program).run s).bind
      (fun z => (complete distribution (rep z.2)).map (Function.const _ z.1)) =
    (complete distribution (rep s)).bind (fun table =>
      (OracleComp.interpret (fun q => PMF.pure (table q)) program).map id) at h
  simp only [PMF.map_const, PMF.map_id] at h
  exact h

/-- `run_interpret_bind_complete` for a closed stateful handler. -/
theorem eval_run_interpret_bind_complete (distribution : (q : Query) → PMF (Response q))
    (impl : (q : Query) → StateT State ProbComp (Response q)) (rep : State → Cache Response)
    (step : ∀ q s,
      (ProbComp.eval (impl q s)).map (fun z => (z.1, rep z.2)) = answer distribution q (rep s))
    (program : OracleComp Response α) (s : State) :
    (ProbComp.eval ((OracleComp.interpret impl program).run s)).bind
        (fun z => (complete distribution (rep z.2)).map (z.1, ·)) =
      (complete distribution (rep s)).bind fun table =>
        (OracleComp.interpret (fun q => PMF.pure (table q)) program).map (·, table) := by
  rw [OracleComp.map_run_interpret ProbComp.isMonadHom_eval]
  exact run_interpret_bind_complete distribution _ rep step program s

/-- A closed stateful handler that, read through `rep`, answers every call as the lazy random
oracle `answer distribution` has the result law of completing the represented initial cache and
answering every call from the completed table. -/
theorem eval_run_interpret_eq_complete_bind (distribution : (q : Query) → PMF (Response q))
    (impl : (q : Query) → StateT State ProbComp (Response q)) (rep : State → Cache Response)
    (step : ∀ q s,
      (ProbComp.eval (impl q s)).map (fun z => (z.1, rep z.2)) = answer distribution q (rep s))
    (program : OracleComp Response α) (s : State) :
    (ProbComp.eval ((OracleComp.interpret impl program).run s)).map Prod.fst =
      (complete distribution (rep s)).bind fun table =>
        OracleComp.interpret (fun q => PMF.pure (table q)) program := by
  rw [OracleComp.map_run_interpret ProbComp.isMonadHom_eval]
  exact run_interpret_eq_complete_bind distribution _ rep step program s

end Represented

section Sum

universe u

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, u} ι₁} {spec₂ : OracleSpec.{u, u} ι₂}

/-- Completing a joined cache completes its two sides independently. -/
theorem bind_complete_sum [Fintype ι₁] [Fintype ι₂] [∀ q, Finite (spec₁ q)]
    [∀ q, Finite (spec₂ q)] {γ : Type u} (d₁ : (q : ι₁) → PMF (spec₁ q))
    (d₂ : (q : ι₂) → PMF (spec₂ q)) (c₁ : Cache spec₁) (c₂ : Cache spec₂)
    (F : ((q : ι₁) → spec₁ q) → ((q : ι₂) → spec₂ q) → PMF γ) :
    (complete (OracleComp.sumHandler d₁ d₂) (Cache.sum c₁ c₂)).bind
        (fun table => F (fun q => table (.inl q)) fun q => table (.inr q)) =
      (complete d₁ c₁).bind fun t₁ => (complete d₂ c₂).bind fun t₂ => F t₁ t₂ :=
  PMF.bind_pi_sum (β := spec₁ ⊕ₒ spec₂)
    (fun q => (Cache.sum c₁ c₂ q).elim (OracleComp.sumHandler d₁ d₂ q) PMF.pure) F

end Sum

end Cslib.RandomOracle
