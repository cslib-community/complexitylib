/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.Iteration

import Complexity.Languages.Probabilistic.Oracle.Simulation

/-!
# Possible results of randomized oracle programs

A result of a program with private coins is possible when some private samples and some replies
to its external queries lead to it: it lies in `OracleComp.support program`, the results at the
leaves of the program's tree of calls. That is the generic support of
`Complexity/Languages/Probabilistic/Semantics.lean`, and the rules of `OracleComp.supportWith`
apply to it.
Private samples range over the support of the closed program (`support_sample`). Every stateful
execution returns only possible results (`mem_support_of_mem`). When every reply type is nonempty,
every possible result is returned by some stateful execution (`mem_support_iff_exists`): an oracle
that answers its first call with a chosen reply realizes each path. Invariants of adaptive loops
(`OracleComp.iterate_invariant`) quantify over possible results, so they remain valid for every
shared oracle and every reply length.

## Main results

* `Cslib.ProbOracleComp.supportWith_query`: an external query may return any possible reply.
* `Cslib.ProbOracleComp.support_sample`: private samples range over the closed program's support.
* `Cslib.ProbOracleComp.mem_support_of_mem`: stateful executions return possible results.
* `Cslib.ProbOracleComp.mem_support_iff_exists`: with nonempty reply types, the possible results
  are the results of stateful executions.

## References

Generalizes the supported loop invariants of Computability/Probabilistic/Adaptive.lean on the
cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8` to programs with external
calls, for the loop rules adapted from Christian Reitwiessner's `Combinators/IterateWhile`
(crei:crei/tidy-universal @7f7c0696).
-/

@[expose] public section

namespace Cslib.ProbOracleComp

open OracleComp

variable {Query α β : Type} {spec : Query → Type}

/-- A returned value is the only possible result. -/
theorem eq_of_mem_support_pure {a result : α}
    (h : result ∈ support (pure a : ProbOracleComp spec α)) : result = a :=
  eq_of_mem_supportWith_pure h

/-- A possible mapped result is the image of a possible result. -/
theorem mem_support_map {program : ProbOracleComp spec α} {f : α → β} {result : β}
    (h : result ∈ support (f <$> program)) : ∃ a ∈ support program, f a = result :=
  mem_supportWith_map_iff.mp h

/-- An external query may return any of its possible replies. -/
@[simp] theorem supportWith_query (possible : (q : ℕ ⊕ Query) → Set (probOracleSpec spec q))
    (q : Query) : supportWith possible (query (spec := spec) q) = possible (.inr q) :=
  OracleComp.supportWith_query possible (.inr q)

/-- Private samples range over the support of the closed program. -/
@[simp] theorem support_sample (program : ProbComp α) :
    support (sample (spec := spec) program) = (ProbComp.eval program).support := by
  rw [sample_eq_liftLeft, support_liftLeft, ProbComp.support_eval]

/-- A result supported by one stateful execution is possible. -/
theorem mem_support_of_mem {program : ProbOracleComp spec α} {State : Type}
    (oracle : (q : Query) → StateT State PMF (spec q)) {s s' : State} {result : α}
    (h : (result, s') ∈ ((OracleComp.interpret
      (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s).support) :
    result ∈ support program :=
  mem_supportWith_of_mem_support_runWith _ (fun _ _ _ _ _ => Set.mem_univ _) h

/-- When every reply type is nonempty, the possible results of a program are exactly the results
of its stateful executions. -/
theorem mem_support_iff_exists [hne : ∀ q, Nonempty (spec q)] {program : ProbOracleComp spec α}
    {result : α} :
    result ∈ support program ↔
      ∃ (State : Type) (oracle : (q : Query) → StateT State PMF (spec q)) (s s' : State),
        (result, s') ∈ ((OracleComp.interpret
          (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s).support
    := by
  classical
  refine ⟨fun h => ?_, fun ⟨State, oracle, s, s', h⟩ => mem_support_of_mem oracle h⟩
  induction program with
  | pure a =>
    refine ⟨Unit, fun q _ => PMF.pure (Classical.choice (hne q), ()), (), (), ?_⟩
    rw [eq_of_mem_supportWith_pure h]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | liftBind q cont ih =>
    obtain ⟨a, -, ha⟩ := Set.mem_iUnion₂.mp h
    obtain ⟨State, oracle, s, s', hrun⟩ := ih a ha
    have hrun' {S : Type} (oracle : (q : Query) → StateT S PMF (spec q)) (state : S) :
        (OracleComp.interpret (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (PFunctor.FreeM.liftBind q cont)).run state =
        ((handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle q).run state).bind
          fun first => (OracleComp.interpret
            (handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) (cont first.1)).run
              first.2 := rfl
    cases q with
    | inl n =>
      refine ⟨State, oracle, s, s', ?_⟩
      rw [hrun', PMF.mem_support_bind_iff]
      refine ⟨(a, s), ?_, hrun⟩
      simp [handler, ProbComp.unifOracle]
    | inr q =>
      let first (q' : Query) : spec q' :=
        if hq : q' = q then hq ▸ a else Classical.choice (hne q')
      let oracle' (q' : Query) : StateT (Option State) PMF (spec q') := fun
        | none => PMF.pure (first q', some s)
        | some state => (oracle q' state).map fun (b, state') => (b, some state')
      have hlift := run_interpret_map_state oracle oracle' some (fun q' state => by
        simp [oracle']) (cont a) s
      refine ⟨Option State, oracle', none, some s', ?_⟩
      rw [hrun' oracle', PMF.mem_support_bind_iff]
      refine ⟨(a, some s), ?_, ?_⟩
      · change (a, some s) ∈ (PMF.pure (first q, some s)).support
        simp [first]
      · rw [← hlift, PMF.mem_support_map_iff]
        exact ⟨(result, s'), hrun, rfl⟩

end Cslib.ProbOracleComp
