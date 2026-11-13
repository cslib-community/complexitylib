/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomOracle
public import CslibFrontier.Languages.Probabilistic.Sum
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

Several oracles are one oracle on the sum of their interfaces. `Cache.sum` joins their caches, so
that one represented state serves them all, and `bind_complete_sum` splits the completed table back
into one table per oracle.

## Main definitions

* `Cslib.RandomOracle.Cache.sum`: the cache of `spec₁ ⊕ₒ spec₂` built from one cache for each side.

## Main results

* `Cslib.RandomOracle.run_interpret_eq_complete_bind`,
  `Cslib.RandomOracle.eval_run_interpret_eq_complete_bind`: a handler that is a lazy random oracle
  on a represented cache has the law of the completed table.
* `Cslib.RandomOracle.answer_sum_inl`, `Cslib.RandomOracle.answer_sum_inr`: a lazy call on one side
  of a joined cache is a lazy call on that side's cache.
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
`answer distribution` has the result law of completing the represented initial cache and answering
every call from the completed table. -/
theorem run_interpret_eq_complete_bind (distribution : (q : Query) → PMF (Response q))
    (impl : (q : Query) → StateT State PMF (Response q)) (rep : State → Cache Response)
    (step : ∀ q s, (impl q s).map (fun z => (z.1, rep z.2)) = answer distribution q (rep s))
    (program : OracleComp Response α) (s : State) :
    ((OracleComp.interpret impl program).run s).map Prod.fst =
      (complete distribution (rep s)).bind fun table =>
        OracleComp.interpret (fun q => PMF.pure (table q)) program := by
  have hrep := congrArg (PMF.map Prod.fst)
    (OracleComp.run_interpret_map_state impl (answer distribution) rep step program s)
  have hcomplete := congrArg (PMF.map Prod.fst)
    (run_interpret_answer_complete distribution program (rep s))
  simp only [PMF.monad_bind_eq_bind, PMF.map_bind, PMF.map_comp, Function.comp_def] at hcomplete
  change ((OracleComp.interpret (answer distribution) program).run (rep s)).bind
      (fun a => (complete distribution a.2).map (Function.const _ a.1)) =
    (complete distribution (rep s)).bind (fun table =>
      (OracleComp.interpret (fun q => PMF.pure (table q)) program).map id) at hcomplete
  simp only [PMF.map_const, PMF.map_id] at hcomplete
  simp only [PMF.map_comp, Function.comp_def] at hrep
  rw [hrep, ← hcomplete]
  rfl

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

/-- The cache of the joined interface `spec₁ ⊕ₒ spec₂`: left queries read `c₁`, right queries read
`c₂`. -/
@[expose] def Cache.sum (c₁ : Cache spec₁) (c₂ : Cache spec₂) : Cache (spec₁ ⊕ₒ spec₂)
  | .inl q => c₁ q
  | .inr q => c₂ q

@[simp] theorem Cache.sum_inl (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₁) :
    Cache.sum c₁ c₂ (.inl q) = c₁ q := rfl

@[simp] theorem Cache.sum_inr (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₂) :
    Cache.sum c₁ c₂ (.inr q) = c₂ q := rfl

/-- The responses of a joined interface are finite when both sides' responses are. -/
instance [∀ q, Finite (spec₁ q)] [∀ q, Finite (spec₂ q)] : ∀ q, Finite ((spec₁ ⊕ₒ spec₂) q)
  | .inl q => inferInstanceAs (Finite (spec₁ q))
  | .inr q => inferInstanceAs (Finite (spec₂ q))

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

variable [DecidableEq ι₁] [DecidableEq ι₂]

/-- Recording a left answer in a joined cache records it in the left cache. -/
theorem Cache.update_sum_inl (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₁) (v : spec₁ q) :
    Function.update (Cache.sum c₁ c₂) (.inl q) (some v) =
      Cache.sum (Function.update c₁ q (some v)) c₂ := by
  funext q'
  rcases q' with q' | q'
  · by_cases h : q' = q
    · subst h; simp
    · simp [Function.update_of_ne h, Function.update_of_ne (Sum.inl_injective.ne h)]
  · simp

/-- Recording a right answer in a joined cache records it in the right cache. -/
theorem Cache.update_sum_inr (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₂) (v : spec₂ q) :
    Function.update (Cache.sum c₁ c₂) (.inr q) (some v) =
      Cache.sum c₁ (Function.update c₂ q (some v)) := by
  funext q'
  rcases q' with q' | q'
  · simp
  · by_cases h : q' = q
    · subst h; simp
    · simp [Function.update_of_ne h, Function.update_of_ne (Sum.inr_injective.ne h)]

/-- A lazy call on the left side of a joined cache is a lazy call on the left cache. -/
theorem answer_sum_inl (d₁ : (q : ι₁) → PMF (spec₁ q)) (d₂ : (q : ι₂) → PMF (spec₂ q))
    (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₁) :
    answer (OracleComp.sumHandler d₁ d₂) (.inl q) (Cache.sum c₁ c₂) =
      (answer d₁ q c₁).map fun z => (z.1, Cache.sum z.2 c₂) := by
  cases h : c₁ q with
  | none =>
    rw [answer_of_none d₁ c₁ q h,
      answer_of_none (OracleComp.sumHandler d₁ d₂) (Cache.sum c₁ c₂) (.inl q) h, PMF.map_comp]
    exact congrArg (PMF.map · (d₁ q))
      (funext fun v => Prod.ext rfl (Cache.update_sum_inl c₁ c₂ q v))
  | some v =>
    rw [answer_of_some d₁ c₁ q v h,
      answer_of_some (OracleComp.sumHandler d₁ d₂) (Cache.sum c₁ c₂) (.inl q) v h, PMF.pure_map]

/-- A lazy call on the right side of a joined cache is a lazy call on the right cache. -/
theorem answer_sum_inr (d₁ : (q : ι₁) → PMF (spec₁ q)) (d₂ : (q : ι₂) → PMF (spec₂ q))
    (c₁ : Cache spec₁) (c₂ : Cache spec₂) (q : ι₂) :
    answer (OracleComp.sumHandler d₁ d₂) (.inr q) (Cache.sum c₁ c₂) =
      (answer d₂ q c₂).map fun z => (z.1, Cache.sum c₁ z.2) := by
  cases h : c₂ q with
  | none =>
    rw [answer_of_none d₂ c₂ q h,
      answer_of_none (OracleComp.sumHandler d₁ d₂) (Cache.sum c₁ c₂) (.inr q) h, PMF.map_comp]
    exact congrArg (PMF.map · (d₂ q))
      (funext fun v => Prod.ext rfl (Cache.update_sum_inr c₁ c₂ q v))
  | some v =>
    rw [answer_of_some d₂ c₂ q v h,
      answer_of_some (OracleComp.sumHandler d₁ d₂) (Cache.sum c₁ c₂) (.inr q) v h, PMF.pure_map]

end Sum

end Cslib.RandomOracle
