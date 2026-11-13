/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle

/-!
# Oracle substitution preserving private randomness

`ProbOracleComp.simulate handler program` replaces the external calls of `program` with
`handler`, forwarding private sampling unchanged. Both the handler and the resulting reduction
remain free-monadic programs. The outer `OracleComp.interpret` supplies the random sampler and
any shared oracle state; reductions need only describe their external-oracle simulation.

## Main definitions

* `Cslib.ProbOracleComp.simulate`: substitute external calls while preserving private samples.

## Main results

* `Cslib.ProbOracleComp.interpret_simulate`: compose substitution with an outer interpreter.
* `Cslib.ProbOracleComp.simulate_simulate`: compose two oracle substitutions.

## References

This API follows the separation of untouched effects from simulated oracles in Devon Tuma,
Quang Dao, and collaborators' [VCVio](https://github.com/Verified-zkEVM/VCVio), in particular
`OracleSpec.passthrough` and `simulateQ` (revision `87bc1892fff1982e97cfd8c7303c9d1f2bfdc2f9`),
in the `OracleComp.SimSemantics.Append.Core` and `OracleComp.SimSemantics.SimulateQ` modules.
The implementation uses the existing
`OracleComp.interpret` and its composition law.
-/

public section

namespace Cslib.ProbOracleComp

universe v

variable {Query Query' Query'' α β : Type}
  {spec : Query → Type} {spec' : Query' → Type} {spec'' : Query'' → Type}

/-- Replace external oracle calls by programs over another interface, preserving every private
sample. Randomness is interpreted only when the resulting program is run. -/
@[expose] def simulate (handler : (q : Query) → ProbOracleComp spec' (spec q))
    (program : ProbOracleComp spec α) : ProbOracleComp spec' α :=
  OracleComp.interpret
    (OracleComp.sumHandler (fun n => sample (ProbComp.unifFin n)) handler) program

/-- Substitution leaves a returned value unchanged. -/
@[simp] theorem simulate_pure (handler : (q : Query) → ProbOracleComp spec' (spec q))
    (a : α) : simulate handler (pure a) = pure a := rfl

/-- Substitution preserves sequential composition. -/
@[simp] theorem simulate_bind (handler : (q : Query) → ProbOracleComp spec' (spec q))
    (program : ProbOracleComp spec α) (next : α → ProbOracleComp spec β) :
    simulate handler (program >>= next) =
      (simulate handler program >>= fun a => simulate handler (next a)) :=
  OracleComp.interpret_bind _ _ _

/-- Substitution preserves deterministic postprocessing. -/
@[simp] theorem simulate_map (handler : (q : Query) → ProbOracleComp spec' (spec q))
    (f : α → β) (program : ProbOracleComp spec α) :
    simulate handler (f <$> program) = f <$> simulate handler program :=
  OracleComp.interpret_map _ _ _

/-- An external call is replaced by its handler program. -/
@[simp] theorem simulate_query (handler : (q : Query) → ProbOracleComp spec' (spec q))
    (q : Query) : simulate handler (query q) = handler q :=
  interpret_query _ _ _

/-- Substitution forwards private samples without consulting the external handler. -/
@[simp] theorem simulate_sample (handler : (q : Query) → ProbOracleComp spec' (spec q))
    (program : ProbComp α) : simulate handler (sample program) = sample program := by
  rw [simulate, interpret_sample]
  simp only [sample, ProbComp.unifFin, OracleComp.interpret_query]

/-- Running a substituted program runs each handler under the same outer interpreter. In
particular, a stateful interpreter shares its state across all calls and private samples. -/
theorem interpret_simulate {m : Type → Type v} [Monad m] [LawfulMonad m]
    (random : (n : ℕ) → m (Fin (n + 1))) (oracle : (q : Query') → m (spec' q))
    (handler : (q : Query) → ProbOracleComp spec' (spec q)) (program : ProbOracleComp spec α) :
    OracleComp.interpret (OracleComp.sumHandler random oracle) (simulate handler program) =
      OracleComp.interpret (OracleComp.sumHandler random
        (fun q => OracleComp.interpret (OracleComp.sumHandler random oracle) (handler q)))
        program := by
  simp only [simulate, OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
    interpret_sample, ProbComp.unifFin, OracleComp.interpret_query]

/-- Two successive substitutions compose at the external handler, preserving private samples. -/
theorem simulate_simulate (handler : (q : Query) → ProbOracleComp spec' (spec q))
    (handler' : (q : Query') → ProbOracleComp spec'' (spec' q))
    (program : ProbOracleComp spec α) :
    simulate handler' (simulate handler program) =
      simulate (fun q => simulate handler' (handler q)) program :=
  interpret_simulate _ _ _ _

end Cslib.ProbOracleComp
