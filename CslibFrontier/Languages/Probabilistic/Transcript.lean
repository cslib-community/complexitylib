/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Simulation

/-!
# Observing oracle transcripts

`withTranscript` records each query and its answer while preserving the oracle's private state.
Entries are stored newest first. Forgetting the transcript recovers the original execution,
including its final private state.

Query budgets (`Cslib.OracleComp.IsCostBounded`) are properties of the program itself; every
logged run respects them.

This is semantic instrumentation, not a claim that recording arbitrary replies is efficient.
In particular, a machine's clock bounds its requests but need not bound the oracle's replies.

## Main definitions

* `Cslib.OracleComp.Transcript`, `.withTranscript`: typed query logging with private state.

## Main results

* `Cslib.OracleComp.run_interpret_withTranscript`: forgetting the log preserves full execution.
* `Cslib.OracleComp.run_interpret_withTranscript_append`: retain an existing transcript suffix.

## References

Adapted from Languages/Probabilistic/Transcript.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the single `OracleComp.interpret` interface.
-/

@[expose] public section

namespace Cslib.OracleComp

universe u

variable {Query : Type u} {Response : Query → Type u} {State α : Type u}

/-- Queries and their typed replies, stored in reverse chronological order. -/
abbrev Transcript (Response : Query → Type u) := List ((q : Query) × Response q)

/-- Observe calls without changing the underlying oracle's replies or private state. -/
noncomputable def withTranscript (oracle : (q : Query) → StateT State PMF (Response q))
    (q : Query) : StateT (State × Transcript Response) PMF (Response q) :=
  fun (s, transcript) => (oracle q s).map
    (fun (answer, s') => (answer, (s', ⟨q, answer⟩ :: transcript)))

/-- Forgetting the transcript preserves the result and the oracle's complete final state. -/
theorem run_interpret_withTranscript (oracle : (q : Query) → StateT State PMF (Response q))
    (program : OracleComp Response α) (s : State) (transcript : Transcript Response) :
    ((interpret (withTranscript oracle) program).run (s, transcript)).map
        (fun (result, state) => (result, state.1)) = (interpret oracle program).run s := by
  apply run_interpret_map_state (withTranscript oracle) oracle Prod.fst
  intro q state
  simp only [withTranscript, PMF.map_comp, Function.comp_def, Prod.mk.eta]
  exact PMF.map_id _

/-- An existing transcript is an untouched suffix of the newly recorded interaction. -/
theorem run_interpret_withTranscript_append (oracle : (q : Query) → StateT State PMF (Response q))
    (program : OracleComp Response α) (s : State) (transcript : Transcript Response) :
    (interpret (withTranscript oracle) program).run (s, transcript) =
      ((interpret (withTranscript oracle) program).run (s, [])).map
        (fun (result, state, fresh) => (result, state, fresh ++ transcript)) := by
  symm
  apply run_interpret_map_state (withTranscript oracle) (withTranscript oracle)
    (fun state => (state.1, state.2 ++ transcript))
  intro q state
  simp [withTranscript, PMF.map_comp, Function.comp_def]

end Cslib.OracleComp
