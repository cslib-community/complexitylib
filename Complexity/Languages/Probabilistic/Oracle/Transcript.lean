/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.Transcript

import Complexity.Languages.Probabilistic.Oracle.Simulation

/-!
# Transcripts of randomized programs

The typed transcript of a program with private coins records only its external requests: private
samples use the other component of `OracleComp.sumHandler` and do not enter the log. Forgetting
the log recovers the original execution, and an existing log is an untouched suffix of the new one.

## Main results

* `Cslib.ProbOracleComp.run_interpret_withTranscript`: forgetting the log preserves full state.
* `Cslib.ProbOracleComp.run_interpret_withTranscript_append`: retain an existing transcript suffix.

## References

Adapts Languages/Probabilistic/Transcript.lean from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing its typed log and the general simulation API.
-/

@[expose] public section

namespace Cslib.ProbOracleComp

open OracleComp

variable {Query α State : Type} {Response : Query → Type}

/-- Forgetting the external log preserves the joint result and complete oracle state. -/
theorem run_interpret_withTranscript (oracle : (q : Query) → StateT State PMF (Response q))
    (program : ProbOracleComp Response α) (s : State) (transcript : Transcript Response) :
    ((interpret (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
      program).run (s, transcript)).map (fun (result, state) => (result, state.1)) =
        (interpret (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          program).run s := by
  apply ProbOracleComp.run_interpret_map_state (withTranscript oracle) oracle Prod.fst
  intro q state
  simp only [withTranscript, PMF.map_comp, Function.comp_def, Prod.mk.eta]
  exact PMF.map_id _

/-- Fresh external observations are prepended to an existing transcript. Private draws do not
change either part of the log. -/
theorem run_interpret_withTranscript_append
    (oracle : (q : Query) → StateT State PMF (Response q)) (program : ProbOracleComp Response α)
    (s : State) (transcript : Transcript Response) :
    (interpret (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
      program).run (s, transcript) =
        ((interpret
          (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
            program).run (s, [])).map (fun (result, state, fresh) =>
              (result, state, fresh ++ transcript)) := by
  symm
  apply ProbOracleComp.run_interpret_map_state (withTranscript oracle) (withTranscript oracle)
    (fun state => (state.1, state.2 ++ transcript))
  intro q state
  simp [withTranscript, PMF.map_comp, Function.comp_def]

end Cslib.ProbOracleComp
