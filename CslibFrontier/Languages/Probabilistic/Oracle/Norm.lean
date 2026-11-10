/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Norm
public import CslibFrontier.Languages.Probabilistic.Oracle.Norm.Init
public import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# Priority-ordered normalization of stateful and stateless oracle runs

Tags the lemmas of the simp set `runWith_norm`. Combined with `pmf_norm`,
`simp only [runWith_norm, pmf_norm]` reduces concrete `ProbOracleComp` and `OracleComp` `do`-blocks
to `PMF.bind`, `PMF.pure`, and `PMF.map` in one pass, while stopping cleanly at
`ProbOracleComp.runWith oracle (adversary n pk) s` when `adversary` is a black-box parameter:

* folding spelled-out runs into `ProbOracleComp.runWith`:
  `ProbOracleComp.eval_run_interpret_eq_runWith`, `ProbOracleComp.run_interpret_eq_runWith`;
* composing handlers inside `ProbOracleComp.runWith`:
  `ProbOracleComp.runWith_interpret_sumHandler_eta`, `ProbOracleComp.runWith_run_interpret`;
* stepping `ProbOracleComp.runWith` over program syntax, lifted sub-interfaces, and lifted
  memoryless oracles:
  `ProbOracleComp.runWith_lift`, `ProbOracleComp.runWith_sample_bind`,
  `ProbOracleComp.runWith_pure`, `ProbOracleComp.runWith_bind`, `ProbOracleComp.runWith_map`,
  `ProbOracleComp.runWith_query`, `ProbOracleComp.runWith_sample`,
  `ProbOracleComp.runWith_liftLeft`, `ProbOracleComp.runWith_liftRight`;
* stepping generic `OracleComp.runWith` and stateless `OracleComp.evalWith`:
  `OracleComp.runWith_lift`, `OracleComp.runWith_pure`, `OracleComp.runWith_bind`,
  `OracleComp.runWith_map`, `OracleComp.runWith_query`, `OracleComp.runWith_sumHandler_liftLeft`,
  `OracleComp.runWith_sumHandler_liftRight`, `OracleComp.evalWith_pure`,
  `OracleComp.evalWith_bind`, `OracleComp.evalWith_map`, `OracleComp.evalWith_query`,
  `OracleComp.evalWith_interpret`, `OracleComp.evalWith_sumHandler_liftLeft`,
  `OracleComp.evalWith_sumHandler_liftRight`,
  `ProbOracleComp.evalWith_sumHandler_unifOracle_sample`,
  `ProbOracleComp.evalWith_sumHandler_sample`, `ProbOracleComp.evalWith_sumHandler_query`;
* normalizing embedded private sampling and tuple maps produced by `runWith_map`:
  `ProbOracleComp.sample_pure`, `ProbOracleComp.sample_bind`, `ProbOracleComp.sample_map`,
  `Prod.map_apply`, `Prod.map_fst`, `Prod.map_snd`, `id_eq`.

`OracleComp.interpret_bind` and `StateT.run_bind` are deliberately excluded: bottom-up `simp` would
otherwise rewrite inside `((OracleComp.interpret …).run s)` before
`ProbOracleComp.eval_run_interpret_eq_runWith` or `ProbOracleComp.runWith_run_interpret` matches the
enclosing run.

The set is priority-ordered and is not claimed to be confluent: when several rules match the same
term, the run-folding and handler-composition rules (priority 1200) and the lifted-oracle and
embedded-sampling rules (priority 1100) take precedence over the default-priority syntax-stepping
rules.

## Main results

* `Cslib.ProbOracleComp.run_interpret_eq_runWith`: folds the spelled-out `ProbComp.unifOracle` sum
  handler run into `ProbOracleComp.runWith`.
* `Cslib.ProbOracleComp.runWith_interpret_sumHandler_eta`: eta-expanded form of
  `ProbOracleComp.runWith_interpret_sumHandler` so `runWith_norm` also steps concrete handler bodies
  when the client program is a black-box parameter.
* `Cslib.ProbOracleComp.runWith_liftLeft`, `Cslib.ProbOracleComp.runWith_liftRight`: step
  `ProbOracleComp.runWith` across `OracleComp.liftLeft` and `OracleComp.liftRight`.
* `Cslib.ProbOracleComp.evalWith_sumHandler_unifOracle_sample`,
  `Cslib.ProbOracleComp.evalWith_sumHandler_sample`,
  `Cslib.ProbOracleComp.evalWith_sumHandler_query`: step `OracleComp.evalWith` across
  `ProbOracleComp.sample` and `ProbOracleComp.query`.
-/

public section

namespace Cslib

/-- Running a `ProbOracleComp` against the lifted uniform sampler and a stateful `PMF` oracle is
`ProbOracleComp.runWith`. -/
theorem ProbOracleComp.run_interpret_eq_runWith {Query : Type} {spec : Query → Type}
    {State α : Type} (oracle : (q : Query) → StateT State PMF (spec q))
    (program : ProbOracleComp spec α) (s : State) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      program).run s =
      ProbOracleComp.runWith oracle program s :=
  rfl

/-- Eta-expanded form of `ProbOracleComp.runWith_interpret_sumHandler` supplying the state argument
to the inner `ProbOracleComp.runWith`, so `runWith_norm` normalizes concrete handler programs even
when `program` is an opaque adversary. -/
theorem ProbOracleComp.runWith_interpret_sumHandler_eta {Query Query' State α : Type}
    {spec : Query → Type} {spec' : Query' → Type}
    (oracle : (q : Query) → StateT State PMF (spec q))
    (handler : (q : Query') → ProbOracleComp spec (spec' q)) (program : ProbOracleComp spec' α)
    (s : State) :
    ProbOracleComp.runWith oracle
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n)) handler)
        program) s =
      ProbOracleComp.runWith (fun q state => ProbOracleComp.runWith oracle (handler q) state)
        program s :=
  ProbOracleComp.runWith_interpret_sumHandler oracle handler program s

/-- Evaluating an embedded private sample under a sum handler uses only the sampling handler. -/
theorem ProbOracleComp.evalWith_sumHandler_sample {Query α : Type} {spec : Query → Type}
    (random : (n : ℕ) → PMF (Fin (n + 1))) (oracle : (q : Query) → PMF (spec q))
    (program : ProbComp α) :
    OracleComp.evalWith (OracleComp.sumHandler random oracle)
      (ProbOracleComp.sample (spec := spec) program) =
      OracleComp.evalWith random program :=
  OracleComp.evalWith_sumHandler_liftLeft random oracle program

/-- Evaluating a single external query under a sum handler invokes the external handler. -/
theorem ProbOracleComp.evalWith_sumHandler_query {Query : Type} {spec : Query → Type}
    (random : (n : ℕ) → PMF (Fin (n + 1))) (oracle : (q : Query) → PMF (spec q))
    (q : Query) :
    OracleComp.evalWith (OracleComp.sumHandler random oracle)
      (ProbOracleComp.query (spec := spec) q) =
      oracle q :=
  OracleComp.evalWith_query _ (Sum.inr q)

/-- Evaluating an embedded private sample under `ProbComp.unifOracle` and an external handler gives
`ProbComp.eval`. -/
theorem ProbOracleComp.evalWith_sumHandler_unifOracle_sample {Query α : Type}
    {spec : Query → Type} (oracle : (q : Query) → PMF (spec q)) (program : ProbComp α) :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle oracle)
      (ProbOracleComp.sample (spec := spec) program) =
      ProbComp.eval program :=
  OracleComp.evalWith_sumHandler_liftLeft ProbComp.unifOracle oracle program

/-- Running an embedded left (`ProbComp`) program under `ProbOracleComp.runWith` evaluates the
program and leaves the oracle state unchanged. -/
theorem ProbOracleComp.runWith_liftLeft {Query State α : Type} {spec : Query → Type}
    (oracle : (q : Query) → StateT State PMF (spec q))
    (program : ProbComp α) (s : State) :
    ProbOracleComp.runWith oracle (OracleComp.liftLeft (spec₂ := spec) program) s =
      (ProbComp.eval program).map (·, s) :=
  ProbOracleComp.runWith_sample oracle program s

/-- Running an embedded right (`OracleComp spec`) program under `ProbOracleComp.runWith` runs it
directly against `oracle` via `OracleComp.runWith`. -/
theorem ProbOracleComp.runWith_liftRight {Query State α : Type} {spec : Query → Type}
    (oracle : (q : Query) → StateT State PMF (spec q))
    (program : OracleComp spec α) (s : State) :
    ProbOracleComp.runWith oracle (OracleComp.liftRight program) s =
      OracleComp.runWith oracle program s :=
  OracleComp.runWith_sumHandler_liftRight _ oracle program s

end Cslib

-- Handler composition and memoryless lift rules get higher priority than syntax-stepping rules so
-- `runWith` folds composite handlers and `StateT.lift` oracles before unfolding concrete `do`
-- syntax.
attribute [runWith_norm 1200]
  Cslib.ProbOracleComp.eval_run_interpret_eq_runWith
  Cslib.ProbOracleComp.run_interpret_eq_runWith
  Cslib.ProbOracleComp.runWith_interpret_sumHandler_eta
  Cslib.ProbOracleComp.runWith_run_interpret

attribute [runWith_norm 1100]
  Cslib.ProbOracleComp.runWith_lift
  Cslib.ProbOracleComp.runWith_sample_bind
  Cslib.ProbOracleComp.evalWith_sumHandler_unifOracle_sample
  Cslib.OracleComp.runWith_lift

attribute [runWith_norm]
  Cslib.ProbOracleComp.runWith_pure
  Cslib.ProbOracleComp.runWith_bind
  Cslib.ProbOracleComp.runWith_map
  Cslib.ProbOracleComp.runWith_query
  Cslib.ProbOracleComp.runWith_sample
  Cslib.ProbOracleComp.runWith_liftLeft
  Cslib.ProbOracleComp.runWith_liftRight
  Cslib.OracleComp.runWith_pure
  Cslib.OracleComp.runWith_bind
  Cslib.OracleComp.runWith_map
  Cslib.OracleComp.runWith_query
  Cslib.OracleComp.runWith_sumHandler_liftLeft
  Cslib.OracleComp.runWith_sumHandler_liftRight
  Cslib.OracleComp.evalWith_pure
  Cslib.OracleComp.evalWith_bind
  Cslib.OracleComp.evalWith_map
  Cslib.OracleComp.evalWith_query
  Cslib.OracleComp.evalWith_interpret
  Cslib.OracleComp.evalWith_sumHandler_liftLeft
  Cslib.OracleComp.evalWith_sumHandler_liftRight
  Cslib.ProbOracleComp.evalWith_sumHandler_sample
  Cslib.ProbOracleComp.evalWith_sumHandler_query
  Cslib.ProbOracleComp.sample_pure
  Cslib.ProbOracleComp.sample_bind
  Cslib.ProbOracleComp.sample_map
  Prod.map_apply
  Prod.map_fst
  Prod.map_snd
  id_eq

end
