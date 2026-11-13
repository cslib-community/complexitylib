/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# Running an oracle program against a stateful or logging oracle

`A.runState O` runs `A : ProbOracleComp spec α` against a stateful oracle `O`: each private sample
is a fresh uniform draw, and each external query `q` runs `O q`, a program that reads and updates
the oracle's state. The result is a `StateT` program, so `(A.runState O).run s` is the closed
sampler that starts the oracle in state `s` and returns the result with the final state.

`A.runLog O` runs `A` against the oracle `O` and records every query with its reply, oldest first.
This is the challenger of a forgery experiment, which later checks a forgery against the log of
signing or tagging queries. `A.runLogWith O` lets the oracle read the log so far and refuse a
query: `O log q = none` answers `default` and records nothing, as a one-time signing oracle does
after its first query. A memoryless oracle `O` gives `runLogWith fun _ q => some (O q)`, which is
`runLog O`.

On every supported run, a program with at most `n` queries leaves a log of length at most `n`.
This is the instance, for the log length, of a general bound: if each query raises a measure of
the oracle state by at most its cost, a run raises it by at most the program's cost budget.

## Main definitions

* `Cslib.ProbOracleComp.runState`: run against a stateful oracle.
* `Cslib.ProbOracleComp.runLogWith`, `Cslib.ProbOracleComp.runLog`: run against an oracle, logging
  every answered query with its reply.

## Main results

* `Cslib.ProbOracleComp.runState_pure`, `runState_bind`, `runState_map`, `runState_query`,
  `runState_sample`: `runState` is the monad morphism answering queries with `O` and sampling with
  fresh coins.
* `Cslib.ProbOracleComp.eval_runState`: the law of a stateful run is `runWith` against the
  evaluated oracle.
* `Cslib.ProbOracleComp.runState_lift`: against a memoryless oracle, the stateful run is `run`
  with the state unchanged.
* `Cslib.ProbOracleComp.measure_runState_le`: a run raises a measure of the oracle state by at most
  the cost budget, when each query raises it by at most its cost
  (`OracleComp.IsCostBounded.measure_le` for this handler).
* `Cslib.ProbOracleComp.logOracle_run`: one call of the logging oracle.
* `Cslib.ProbOracleComp.runLogWith_map`: mapping the program's result keeps the log.
* `Cslib.ProbOracleComp.IsQueryBounded.length_runLogWith_le`,
  `Cslib.ProbOracleComp.IsQueryBounded.length_runLog_le`: a program with at most `n` queries
  leaves a log of length at most `n`.
* `Cslib.ProbOracleComp.forall_mem_runLogWith`: every logged pair is a reply that the oracle's
  answering program can produce.
-/

public section

namespace Cslib.ProbOracleComp

open OracleComp (sumHandler)

variable {Query α β σ : Type} {spec : Query → Type}

/-! ### Stateful oracles -/

/-- Run `A` with fresh uniform private coins, answering each external query `q` with the stateful
program `O q`. -/
@[expose] def runState (A : ProbOracleComp spec α) (O : (q : Query) → StateT σ ProbComp (spec q)) :
    StateT σ ProbComp α :=
  OracleComp.interpret (sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) O) A

/-- Returning a value makes no call, draws no coins and keeps the state. -/
@[simp] theorem runState_pure (a : α) (O : (q : Query) → StateT σ ProbComp (spec q)) :
    (pure a : ProbOracleComp spec α).runState O = pure a := rfl

/-- A sequenced program runs its first part, then the continuation from the state it reached. -/
@[simp] theorem runState_bind (A : ProbOracleComp spec α) (next : α → ProbOracleComp spec β)
    (O : (q : Query) → StateT σ ProbComp (spec q)) :
    (A >>= next).runState O = A.runState O >>= fun a => (next a).runState O :=
  OracleComp.interpret_bind _ _ _

/-- Deterministic postprocessing commutes with running. -/
@[simp] theorem runState_map (f : α → β) (A : ProbOracleComp spec α)
    (O : (q : Query) → StateT σ ProbComp (spec q)) :
    (f <$> A).runState O = f <$> A.runState O :=
  OracleComp.interpret_map _ _ _

/-- A single external query is answered by the oracle from the current state. -/
@[simp] theorem runState_query (q : Query) (O : (q : Query) → StateT σ ProbComp (spec q)) :
    (query q : ProbOracleComp spec (spec q)).runState O = O q :=
  interpret_query _ _ _

/-- A private sample is the sampled program, and it keeps the state. -/
@[simp] theorem runState_sample (program : ProbComp α)
    (O : (q : Query) → StateT σ ProbComp (spec q)) :
    (sample program : ProbOracleComp spec α).runState O = StateT.lift program := by
  funext s
  simp only [runState, interpret_sample]
  change (OracleComp.interpret (m := StateT σ ProbComp) _ program).run s = _
  rw [OracleComp.run_interpret_lift]
  change (fun a => (a, s)) <$> OracleComp.interpret OracleComp.query program = _
  rw [OracleComp.interpret_query_eq_self]
  simp [StateT.lift, bind_pure_comp]

/-- The law of a stateful run is `runWith` against the evaluated oracle. -/
theorem eval_runState (A : ProbOracleComp spec α) (O : (q : Query) → StateT σ ProbComp (spec q))
    (s : σ) :
    ProbComp.eval ((A.runState O).run s) =
      runWith (fun q state => ProbComp.eval (O q state)) A s :=
  eval_run_interpret_eq_runWith O A s

/-- Against a memoryless oracle, the stateful run is `run`, and the state is unchanged. -/
theorem runState_lift (A : ProbOracleComp spec α) (O : (q : Query) → ProbComp (spec q)) (s : σ) :
    (A.runState fun q => StateT.lift (O q)).run s = (·, s) <$> A.run O := by
  have hlift : sumHandler (fun n => StateT.lift (σ := σ) (ProbComp.unifFin n))
      (fun q => StateT.lift (O q)) = fun q => StateT.lift (sumHandler ProbComp.unifFin O q) := by
    funext q
    cases q <;> rfl
  rw [runState, hlift, OracleComp.run_interpret_lift]
  rfl

/-- If each query `q` raises the measure `μ` of the oracle state by at most `cost q`, a run of a
program whose queries cost at most `n` raises it by at most `n`. Private samples keep the state.
This is `OracleComp.IsCostBounded.measure_le` for the handler of `runState`. -/
theorem measure_runState_le {cost : Query → ℕ} {A : ProbOracleComp spec α} {n : ℕ}
    (h : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) cost) A n)
    (O : (q : Query) → StateT σ ProbComp (spec q)) (μ : σ → ℕ)
    (hstep : ∀ q s, ∀ z ∈ (ProbComp.eval ((O q).run s)).support, μ z.2 ≤ μ s + cost q) (s : σ) :
    ∀ z ∈ (ProbComp.eval ((A.runState O).run s)).support, μ z.2 ≤ μ s + n := by
  rintro ⟨result, s'⟩ hz
  rw [eval_runState] at hz
  change (result, s') ∈ ((OracleComp.interpret (sumHandler
    (fun n => StateT.lift (ProbComp.unifOracle n)) fun q t => ProbComp.eval (O q t)) A).run
      s).support at hz
  refine OracleComp.IsCostBounded.measure_le h _ μ (fun q t a t' ht => ?_) hz
  cases q with
  | inl k =>
    change (a, t') ∈ (StateT.lift (ProbComp.unifOracle k) t).support at ht
    simp only [StateT.lift, Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at ht
    obtain ⟨_, _, -, rfl⟩ := ht
    simp
  | inr q => exact hstep q t (a, t') ht

/-! ### Logging oracles -/

variable {Q R : Type}

/-- The logging oracle of `runLogWith`: answer `q` with `O log q` and append `(q, reply)` to the
log, or answer `default` and keep the log when `O log q = none`. -/
@[expose] def logOracle [Inhabited R] (O : List (Q × R) → Q → Option (ProbComp R)) (q : Q) :
    StateT (List (Q × R)) ProbComp R := fun log =>
  match O log q with
  | some reply => (fun r => (r, log ++ [(q, r)])) <$> reply
  | none => pure (default, log)

/-- One call of the logging oracle runs `O log q` and appends the answered pair, or answers
`default` and keeps the log when `O log q = none`. -/
@[simp] theorem logOracle_run [Inhabited R] (O : List (Q × R) → Q → Option (ProbComp R)) (q : Q)
    (log : List (Q × R)) :
    (logOracle O q).run log = match O log q with
      | some reply => (fun r => (r, log ++ [(q, r)])) <$> reply
      | none => pure (default, log) := rfl

/-- Run `A` against an oracle that reads the log so far, returning the result and the log of
answered queries with their replies, oldest first. A refused query (`O log q = none`) is answered
with `default` and not logged. -/
@[expose] def runLogWith [Inhabited R] (A : ProbOracleComp (fun _ : Q => R) α)
    (O : List (Q × R) → Q → Option (ProbComp R)) : ProbComp (α × List (Q × R)) :=
  (A.runState (logOracle O)).run []

/-- Run `A` against the oracle `O`, returning the result and the log of its queries with their
replies, oldest first. -/
@[expose] def runLog (A : ProbOracleComp (fun _ : Q => R) α) (O : Q → ProbComp R) :
    ProbComp (α × List (Q × R)) :=
  (A.runState fun q log => (fun r => (r, log ++ [(q, r)])) <$> O q).run []

/-- An oracle that never refuses and ignores the log is `runLog`. -/
theorem runLogWith_some [Inhabited R] (A : ProbOracleComp (fun _ : Q => R) α)
    (O : Q → ProbComp R) : A.runLogWith (fun _ q => some (O q)) = A.runLog O := rfl

/-- Mapping the program's result maps the result of the logged run and keeps the log. -/
theorem runLogWith_map [Inhabited R] (f : α → β) (A : ProbOracleComp (fun _ : Q => R) α)
    (O : List (Q × R) → Q → Option (ProbComp R)) :
    (f <$> A).runLogWith O = Prod.map f id <$> A.runLogWith O := by
  simp only [runLogWith, runState_map, StateT.run_map]
  rfl

/-- On every supported run, a program with at most `n` queries leaves a log of length at most
`n`. -/
theorem IsQueryBounded.length_runLogWith_le [Inhabited R] {A : ProbOracleComp (fun _ : Q => R) α}
    {n : ℕ} (h : A.IsQueryBounded n) (O : List (Q × R) → Q → Option (ProbComp R)) :
    ∀ z ∈ (ProbComp.eval (A.runLogWith O)).support, z.2.length ≤ n := by
  intro z hz
  have hbound := measure_runState_le (cost := fun _ => 1) h (logOracle O) List.length
    (fun q log z hz => ?_) [] z hz
  · simpa using hbound
  · rw [logOracle_run] at hz
    split at hz
    · simp only [ProbComp.eval_map, PMF.support_map, Set.mem_image] at hz
      obtain ⟨r, -, rfl⟩ := hz
      simp
    · simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp

/-- On every supported run, a program with at most `n` queries leaves a log of length at most
`n`. -/
theorem IsQueryBounded.length_runLog_le {A : ProbOracleComp (fun _ : Q => R) α} {n : ℕ}
    (h : A.IsQueryBounded n) (O : Q → ProbComp R) :
    ∀ z ∈ (ProbComp.eval (A.runLog O)).support, z.2.length ≤ n := by
  intro z hz
  have hbound := measure_runState_le (cost := fun _ => 1) h
    (fun q log => (fun r => (r, log ++ [(q, r)])) <$> O q) List.length
    (fun q log z hz => ?_) [] z hz
  · simpa using hbound
  · simp only [StateT.run, ProbComp.eval_map, PMF.support_map, Set.mem_image] at hz
    obtain ⟨r, -, rfl⟩ := hz
    simp

/-- **Every logged pair is a possible reply**: a property of query-reply pairs that holds for
every reply of every program the oracle runs holds for every pair in the log of `runLogWith`. -/
theorem forall_mem_runLogWith [Inhabited R] {O : List (Q × R) → Q → Option (ProbComp R)}
    {P : Q × R → Prop}
    (hO : ∀ log q program, O log q = some program →
      ∀ r ∈ (ProbComp.eval program).support, P (q, r))
    (A : ProbOracleComp (fun _ : Q => R) α) {z : α × List (Q × R)}
    (hz : z ∈ (ProbComp.eval (A.runLogWith O)).support) : ∀ p ∈ z.2, P p := by
  rw [runLogWith, runState, eval_run_interpret] at hz
  refine run_interpret_invariant _ (fun log => ∀ p ∈ log, P p) ?_ A [] (by simp) z.1 z.2 hz
  intro q log hlog r log' hstep
  simp only [logOracle] at hstep
  cases hprog : O log q with
  | none =>
    simp only [hprog, ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
    exact hstep.2 ▸ hlog
  | some program =>
    simp only [hprog, ProbComp.eval_map, PMF.mem_support_map_iff, Prod.mk.injEq] at hstep
    obtain ⟨r', hr', rfl, rfl⟩ := hstep
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hlog p hp
    · exact List.mem_singleton.mp hp ▸ hO log q program hprog r' hr'

end Cslib.ProbOracleComp
