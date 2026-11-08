/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.Semantics

/-!
# Running a program against a stateful oracle

A program with private samples and typed external calls (`Cslib.ProbOracleComp`) interacts with a
stateful probabilistic oracle answering each call `q` with an element of `spec q`, possibly at
random and updating a private state. `Cslib.ProbOracleComp.runWith` is the joint law of the result
and the final oracle state, with fresh fair samples for the private coins, and
`Cslib.ProbOracleComp.acceptProbWith` the probability that a Boolean program returns `true`.
A prover of an interactive proof is such an oracle; `Cslib.Complexity.Prover.run` is the case of
word queries and replies (`Cslib.Complexity.Prover.run_eq_runWith`).

`runWith` is the instance of the generic `OracleComp.runWith` whose handler is the sum
`OracleComp.sumHandler` of fresh uniform draws for private samples, which keep the state, and
`oracle` for external calls. Against a memoryless oracle it is `OracleComp.evalWith` of the sum of
the uniform handler and the oracle, with the state unchanged (`runWith_lift`). Its structural
rules are those of `OracleComp.runWith`; `Languages.Probabilistic.Oracle.Simulation` gives its
simulation and state-representation rules.

## Main definitions

* `Cslib.ProbOracleComp.runWith`: the joint law of the result and the final oracle state.
* `Cslib.ProbOracleComp.acceptProbWith`: the acceptance probability.

## Main results

* `Cslib.ProbOracleComp.runWith_lift`, `Cslib.ProbOracleComp.acceptProbWith_lift`: against a
  memoryless oracle, the instances of `OracleComp.evalWith`.
* `Cslib.ProbOracleComp.induction`: structural induction over returned values, private uniform
  draws and external calls; `Cslib.ProbOracleComp.sample_unifFin` identifies a draw with its
  sampling request.
* `Cslib.ProbOracleComp.runWith_pure`, `Cslib.ProbOracleComp.runWith_bind`,
  `Cslib.ProbOracleComp.runWith_map`, `Cslib.ProbOracleComp.runWith_query`,
  `Cslib.ProbOracleComp.runWith_sample`: structural rules for `runWith`.
* `Cslib.ProbOracleComp.eval_run_interpret_eq_runWith`: evaluating a closed run is `runWith`
  against the evaluated handler.
* `Cslib.ProbOracleComp.runWith_sample_bind`: a private sample averages the continuation's run.
* `Cslib.ProbOracleComp.runWith_interpret`, `Cslib.ProbOracleComp.runWith_interpret_sumHandler`:
  running an interpreted program runs the original program against the handler programs' runs.
* `Cslib.ProbOracleComp.acceptProbWith_bind`: sequencing for acceptance probability.
* `Cslib.ProbOracleComp.acceptProbWith_query_bind`,
  `Cslib.ProbOracleComp.acceptProbWith_sample_bind`: averages over replies and samples.
* `Cslib.ProbOracleComp.acceptProbWith_bind_ite_le`: a check run only after another one accepted
  accepts at most as often.
-/

@[expose] public section

namespace Cslib.ProbOracleComp

open scoped ENNReal

variable {Query : Type} {spec : Query → Type} {State α β : Type}
  (oracle : (q : Query) → StateT State PMF (spec q))

/-- A private uniform draw is the sampling request that it embeds. -/
theorem sample_unifFin (n : ℕ) :
    sample (spec := spec) (ProbComp.unifFin n) = OracleComp.query (Sum.inl n) := by
  simp [sample, ProbComp.unifFin]

/-- Structural induction on a program with private samples and external calls: a returned value,
a private uniform draw followed by a continuation, or an external call followed by a
continuation. -/
@[elab_as_elim] theorem induction {motive : ProbOracleComp spec α → Prop}
    (pure : ∀ a, motive (pure a))
    (sample_bind : ∀ n (cont : Fin (n + 1) → ProbOracleComp spec α), (∀ i, motive (cont i)) →
      motive (sample (ProbComp.unifFin n) >>= cont))
    (query_bind : ∀ q (cont : spec q → ProbOracleComp spec α), (∀ a, motive (cont a)) →
      motive (query q >>= cont))
    (program : ProbOracleComp spec α) : motive program := by
  induction program using OracleComp.induction with
  | pure a => exact pure a
  | query_bind q cont ih =>
    cases q with
    | inl n => rw [← sample_unifFin]; exact sample_bind n cont ih
    | inr q => exact query_bind q cont ih

/-- The joint law of the result of `program` and the final state of the oracle answering its
external calls, starting from the state `s`. Private samples are fresh. This is the generic
stateful run `OracleComp.runWith` of the sum handler. -/
noncomputable def runWith (program : ProbOracleComp spec α) (s : State) : PMF (α × State) :=
  OracleComp.runWith
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program s

/-- The probability that `program` returns `true` against the oracle from the state `s`. -/
noncomputable def acceptProbWith (program : ProbOracleComp spec Bool) (s : State) : ℝ≥0∞ :=
  (runWith oracle program s).map Prod.fst true

/-- Against a memoryless oracle, the run is `OracleComp.evalWith` of the uniform handler on the
sampling side and the oracle on the other, with the state unchanged. -/
theorem runWith_lift (h : (q : Query) → PMF (spec q)) (program : ProbOracleComp spec α)
    (s : State) :
    runWith (fun q => StateT.lift (h q)) program s =
      (OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle h) program).map (·, s) := by
  have hlift : OracleComp.sumHandler (fun n => StateT.lift (σ := State) (ProbComp.unifOracle n))
      (fun q => StateT.lift (h q)) =
      fun q => StateT.lift (OracleComp.sumHandler ProbComp.unifOracle h q) := by
    funext q
    cases q <;> rfl
  rw [runWith, hlift, OracleComp.runWith_lift]

/-- Against a memoryless oracle, the acceptance probability is the probability of `true` under
`OracleComp.evalWith` of the uniform handler and the oracle. -/
theorem acceptProbWith_lift (h : (q : Query) → PMF (spec q)) (program : ProbOracleComp spec Bool)
    (s : State) :
    acceptProbWith (fun q => StateT.lift (h q)) program s =
      OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle h) program true := by
  rw [acceptProbWith, runWith_lift, PMF.map_comp,
    show (Prod.fst ∘ fun a : Bool => (a, s)) = id from rfl, PMF.map_id]

/-- A pure program returns its value and leaves the oracle state unchanged. -/
@[simp] theorem runWith_pure (a : α) (s : State) : runWith oracle (pure a) s = PMF.pure (a, s) :=
  OracleComp.runWith_pure _ _ _

/-- Running `program >>= next` runs `program`, then runs `next` at its result from the oracle
state it reached. -/
@[simp] theorem runWith_bind (program : ProbOracleComp spec α) (next : α → ProbOracleComp spec β)
    (s : State) :
    runWith oracle (program >>= next) s =
      (runWith oracle program s).bind fun x => runWith oracle (next x.1) x.2 :=
  OracleComp.runWith_bind _ _ _ _

/-- Mapping `f` over a program maps it over the result and keeps the final oracle state. -/
@[simp] theorem runWith_map (f : α → β) (program : ProbOracleComp spec α) (s : State) :
    runWith oracle (f <$> program) s = (runWith oracle program s).map (Prod.map f id) :=
  OracleComp.runWith_map _ _ _ _

/-- A single external call is answered by the oracle from the current state. -/
@[simp] theorem runWith_query (q : Query) (s : State) :
    runWith oracle (query (spec := spec) q) s = oracle q s :=
  OracleComp.runWith_query _ (Sum.inr q) _

/-- A private sample has the law of the sampled program and leaves the oracle state unchanged. -/
@[simp] theorem runWith_sample (program : ProbComp α) (s : State) :
    runWith oracle (sample (spec := spec) program) s = (ProbComp.eval program).map (·, s) :=
  run_interpret_sample _ _ _

/-- A private sample followed by a continuation averages the continuation's run over the sample,
from the same oracle state. -/
theorem runWith_sample_bind (program : ProbComp α) (next : α → ProbOracleComp spec β)
    (s : State) :
    runWith oracle (sample program >>= next) s =
      (ProbComp.eval program).bind fun a => runWith oracle (next a) s := by
  rw [runWith_bind, runWith_sample, PMF.bind_map]
  rfl

/-- Running a program whose calls a handler answers with `ProbOracleComp spec` programs is a
stateful run of the original program, each call answered by running its handler program. -/
theorem runWith_interpret {ι : Type} {spec' : OracleSpec ι}
    (handler : (q : ι) → ProbOracleComp spec (spec' q)) (program : OracleComp spec' α)
    (s : State) :
    runWith oracle (OracleComp.interpret handler program) s =
      OracleComp.runWith (fun q => runWith oracle (handler q)) program s := by
  rw [runWith, OracleComp.runWith, OracleComp.runWith, OracleComp.interpret_interpret]
  rfl

/-- A program whose private draws are forwarded and whose external calls a handler answers with
`ProbOracleComp spec` programs runs against the oracle that runs each handler program. -/
theorem runWith_interpret_sumHandler {Query' : Type} {spec' : Query' → Type}
    (handler : (q : Query') → ProbOracleComp spec (spec' q)) (program : ProbOracleComp spec' α)
    (s : State) :
    runWith oracle (OracleComp.interpret
        (OracleComp.sumHandler (fun n => sample (ProbComp.unifFin n)) handler) program) s =
      runWith (fun q => runWith oracle (handler q)) program s := by
  rw [runWith_interpret, runWith]
  congr 1
  funext q t
  cases q with
  | inl n =>
    simp [OracleComp.sumHandler, StateT.lift, ProbComp.unifOracle, PMF.map, Function.comp_def]
  | inr q => rfl

/-- Evaluating a closed run, in which a handler program answers the external calls, is `runWith`
against the evaluated handler. -/
theorem eval_run_interpret_eq_runWith (oracle : (q : Query) → StateT State ProbComp (spec q))
    (program : ProbOracleComp spec α) (s : State) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) oracle) program).run s) =
      runWith (fun q state => ProbComp.eval (oracle q state)) program s :=
  eval_run_interpret oracle program s

/-- A pure program accepts with probability `1` if it returns `true` and `0` otherwise. -/
theorem acceptProbWith_pure (b : Bool) (s : State) :
    acceptProbWith oracle (pure b) s = if b then 1 else 0 := by
  rw [acceptProbWith, runWith_pure, PMF.pure_map, PMF.pure_apply]
  cases b <;> simp

/-- An acceptance probability is at most `1`. -/
theorem acceptProbWith_le_one (program : ProbOracleComp spec Bool) (s : State) :
    acceptProbWith oracle program s ≤ 1 :=
  PMF.coe_le_one _ _

/-- The acceptance probability of `program >>= next` averages the acceptance probability of `next`
over the joint law of the result and oracle state of `program`. -/
theorem acceptProbWith_bind (program : ProbOracleComp spec α)
    (next : α → ProbOracleComp spec Bool) (s : State) :
    acceptProbWith oracle (program >>= next) s =
      ∑' x, runWith oracle program s x * acceptProbWith oracle (next x.1) x.2 := by
  rw [acceptProbWith, runWith_bind, PMF.map_bind, PMF.bind_apply]
  rfl

/-- The acceptance probability after an external call `q` averages over the oracle's replies and
next states. -/
theorem acceptProbWith_query_bind (q : Query) (next : spec q → ProbOracleComp spec Bool)
    (s : State) :
    acceptProbWith oracle (query (spec := spec) q >>= next) s =
      ∑' x, oracle q s x * acceptProbWith oracle (next x.1) x.2 := by
  rw [acceptProbWith_bind, runWith_query]

/-- The acceptance probability after a private sample averages over the law of the sample, with
the oracle state unchanged. -/
theorem acceptProbWith_sample_bind (program : ProbComp α) (next : α → ProbOracleComp spec Bool)
    (s : State) :
    acceptProbWith oracle (sample program >>= next) s =
      ∑' a, ProbComp.eval program a * acceptProbWith oracle (next a) s := by
  rw [acceptProbWith, runWith_bind, runWith_sample, PMF.bind_map, PMF.map_bind, PMF.bind_apply]
  rfl

/-- Running a second check only after a first one accepted accepts at most as often as the first
check. -/
theorem acceptProbWith_bind_ite_le (program : ProbOracleComp spec Bool)
    (next : ProbOracleComp spec Bool) (s : State) :
    acceptProbWith oracle (program >>= fun b => if b then next else pure false) s ≤
      acceptProbWith oracle program s := by
  conv_rhs => rw [← bind_pure program, acceptProbWith_bind]
  rw [acceptProbWith_bind]
  refine tsum_le_tsum fun x => mul_le_mul_right ?_ _
  cases x.1
  · simp only [Bool.false_eq_true, ↓reduceIte, le_refl]
  · simp only [↓reduceIte, acceptProbWith_pure]
    exact acceptProbWith_le_one _ _ _

end Cslib.ProbOracleComp
