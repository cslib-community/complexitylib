/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Semantics

/-!
# Private randomness with typed oracle calls

`ProbOracleComp spec` combines the existing finite-uniform sampling interface with `spec` by a
disjoint sum of query types. It is still an `OracleComp`, interpreted by `OracleComp.interpret`.
`sample` embeds a closed probabilistic program, and `query` calls the external oracle. A handler
can therefore draw fresh private coins while caching only the external queries.

The finite-uniform interface specifies distributions, not their computational efficiency.
Strict fair-coin realizability is certified separately; arbitrary exact finite-uniform sampling
is not automatically a strict PPT operation.

## Main definitions

* `Cslib.probOracleSpec`: the disjoint sum `unifSpec ⊕ₒ spec` of the finite-uniform sampling
  requests and the external queries of `spec`.
* `Cslib.ProbOracleComp`: the sum of the uniform sampling and external oracle interfaces.
* `Cslib.ProbOracleComp.sample`, `.query`: closed sampling and typed external calls.

The sampling and external interfaces form the sum `unifSpec ⊕ₒ spec` of
`Complexity/Languages/Probabilistic/Sum.lean`: `sample` is its left embedding
(`sample_eq_liftLeft`), and a handler is the sum handler `OracleComp.sumHandler random oracle`,
which answers private sampling requests with `random` and external queries with `oracle`. In
particular, memoizing `oracle` does not memoize `random`. The rules of `OracleComp.sumHandler`
apply directly.

## Main results

* `Cslib.ProbOracleComp.isMonadHom_sample`: `sample` is a monad morphism from `ProbComp`.
* `Cslib.ProbOracleComp.interpret_sample`: embedded sampling uses only the sampling handler.
* `Cslib.ProbOracleComp.run_interpret_sample`: private sampling leaves oracle state unchanged.
* `Cslib.ProbOracleComp.run_interpret_lift_sample`: a stateful handler with external calls
  forwards private sampling unchanged.
* `Cslib.ProbOracleComp.sample_run_interpret`: sampling a closed stateful execution is the
  execution of the sampled handler.
* `Cslib.ProbOracleComp.eval_interpret`: closed handlers commute with probability interpretation.
* `Cslib.ProbOracleComp.eval_run_interpret`: closed handler programs preserve the joint state law.

## References

Uses the typed interface of cslib PR #1129, by Samuel Schlesinger and Devon Tuma, based on the
VCVio design credited in `Languages.Probabilistic.Basic`. This replaces the separate sampling
constructor used by the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib

universe v

/-- A disjoint sum keeps fresh sampling requests separate from external oracle requests. -/
abbrev probOracleSpec {Query : Type} (spec : Query → Type) : OracleSpec (ℕ ⊕ Query) :=
  unifSpec ⊕ₒ spec

/-- A program with separate finite-uniform samples and typed external queries. -/
abbrev ProbOracleComp {Query : Type} (spec : Query → Type) (α : Type) :=
  OracleComp (probOracleSpec spec) α

namespace ProbOracleComp

variable {Query α β State : Type} {spec : Query → Type}

/-- Embed a closed probabilistic program; its calls remain separate from the external oracle. -/
def sample (program : ProbComp α) : ProbOracleComp spec α :=
  OracleComp.interpret (spec := unifSpec)
    (fun n => OracleComp.query (spec := probOracleSpec spec) (Sum.inl n)) program

/-- Sampling is the left embedding into the sum `unifSpec ⊕ₒ spec`. -/
theorem sample_eq_liftLeft (program : ProbComp α) :
    sample (spec := spec) program = OracleComp.liftLeft program := rfl

/-- Lifting a closed sampler into `ProbOracleComp spec` is a monad morphism. -/
theorem isMonadHom_sample : IsMonadHom ProbComp (ProbOracleComp spec) (sample (spec := spec)) :=
  PFunctor.FreeM.isMonadHom_liftM (P := ⟨ℕ, unifSpec⟩)
    (fun n => OracleComp.query (spec := probOracleSpec spec) (Sum.inl n))

/-- Make one external call, whose reply may determine later sampling or queries. -/
def query (q : Query) : ProbOracleComp spec (spec q) := OracleComp.query (Sum.inr q)

open OracleComp (sumHandler)

variable {m : Type → Type v} [Monad m] [LawfulMonad m]

/-- The combined handler answers a single external query through its external component. -/
@[simp] theorem interpret_query (random : (n : ℕ) → m (Fin (n + 1)))
    (oracle : (q : Query) → m (spec q)) (q : Query) :
    OracleComp.interpret (sumHandler random oracle) (query q) = oracle q :=
  OracleComp.interpret_query _ _

/-- Embedded closed programs use only the sampling component of the combined handler. -/
@[simp] theorem interpret_sample (random : (n : ℕ) → m (Fin (n + 1)))
    (oracle : (q : Query) → m (spec q)) (program : ProbComp α) :
    OracleComp.interpret (sumHandler random oracle) (sample program) =
      OracleComp.interpret random program := by
  rw [sample_eq_liftLeft, OracleComp.interpret_sumHandler_liftLeft]

/-- Sampling preserves ordinary functional sequencing before any interpretation. -/
@[simp] theorem sample_bind (program : ProbComp α) (next : α → ProbComp β) :
    sample (spec := spec) (program >>= next) = (sample program >>= fun a => sample (next a)) :=
  OracleComp.interpret_bind _ _ _

/-- Sampling a returned value makes no call. -/
@[simp] theorem sample_pure (a : α) : sample (spec := spec) (pure a) = pure a := rfl

/-- Deterministic postprocessing stays inside the embedded closed program. -/
@[simp] theorem sample_map (f : α → β) (program : ProbComp α) :
    sample (spec := spec) (f <$> program) = f <$> sample program :=
  OracleComp.interpret_map _ _ _

/-- Private sampling is fresh and leaves the complete external oracle state unchanged. -/
theorem run_interpret_sample (oracle : (q : Query) → StateT State PMF (spec q))
    (program : ProbComp α) (s : State) :
    (OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) (sample program)).run s =
        (ProbComp.eval program).map (·, s) := by
  rw [interpret_sample]
  exact OracleComp.run_interpret_lift ProbComp.unifOracle program s

/-- A stateful handler that itself has private coins and external calls forwards every private
draw as a fresh sample, leaving its own state unchanged. -/
theorem run_interpret_lift_sample {Query' : Type} {spec' : Query' → Type}
    (oracle : (q : Query) → StateT State (ProbOracleComp spec') (spec q))
    (program : ProbComp α) (s : State) :
    (OracleComp.interpret (sumHandler (fun n => StateT.lift (sample (ProbComp.unifFin n))) oracle)
      (sample program)).run s = (·, s) <$> sample program := by
  rw [interpret_sample, OracleComp.run_interpret_lift]
  rfl

/-- Sampling a closed stateful execution is the execution of the sampled handler: both make the
same private draws and retain the same final handler state. -/
theorem sample_run_interpret {Query' : Type} {spec' : Query' → Type}
    (oracle : (q : Query) → StateT State ProbComp (spec q)) (program : ProbOracleComp spec α)
    (s : State) :
    sample (spec := spec') ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) oracle) program).run s) =
      (OracleComp.interpret (sumHandler (fun n => StateT.lift (sample (ProbComp.unifFin n)))
        (fun q state => sample (oracle q state))) program).run s := by
  rw [OracleComp.map_run_interpret (isMonadHom_sample (spec := spec'))]
  congr 2
  funext q state
  cases q with
  | inl n => simp [StateT.lift]
  | inr q => rfl

/-- Closed handlers have the same probability law when interpreted before or after evaluation. -/
theorem eval_interpret (oracle : (q : Query) → ProbComp (spec q))
    (program : ProbOracleComp spec α) :
    ProbComp.eval (OracleComp.interpret (sumHandler ProbComp.unifFin oracle) program) =
      OracleComp.interpret (sumHandler ProbComp.unifOracle (fun q => ProbComp.eval (oracle q)))
        program := by
  simp only [ProbComp.eval, OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
    ProbComp.unifFin, OracleComp.interpret_query]

/-- Evaluating closed stateful handlers commutes with interpreting the whole oracle program.
Private sampling stays independent, and the final state is retained beside the result. -/
theorem eval_run_interpret (oracle : (q : Query) → StateT State ProbComp (spec q))
    (program : ProbOracleComp spec α) (s : State) :
    ProbComp.eval ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) oracle) program).run s) =
      (OracleComp.interpret (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (fun q state => ProbComp.eval (oracle q state))) program).run s := by
  rw [OracleComp.map_run_interpret ProbComp.isMonadHom_eval]
  apply congrArg (fun oracle => (OracleComp.interpret (m := StateT State PMF) oracle program).run s)
  funext q state
  cases q with
  | inl n => simp [StateT.lift, ProbComp.unifOracle, PMF.map, Function.comp_def]
  | inr q => rfl

end ProbOracleComp

end Cslib
