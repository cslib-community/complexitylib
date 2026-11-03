/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.Oracle.QueryCount
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds

/-!
# Polynomial external query budgets

An oracle PPT certificate implies polynomial bounds on the number and encoded length of external
requests, as structural budgets of the program (`ProbOracleComp.IsQueryBounded`,
`ProbOracleComp.QueriesSatisfy`). The derivation instruments the shared oracle state with a
transcript and uses the certificate's equality of the full final-state distribution; the
budgets then follow because they are exactly the bounds that every logged execution respects. It
does not assume a separate query bound or restrict oracle reply sizes. Private randomness is
independent and is not logged.

## Main results

* `Cslib.Probability.IsOraclePPTOn.query_bounds`: one polynomial bounds calls and request lengths
  uniformly over all inputs and shared stateful oracles.

## References

Adapted from Computability/Probabilistic/QueryBounds.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the current word-oracle realization contract.
-/

@[expose] public section

namespace Cslib.Probability

/-- Instrumenting the private state transfers the machine clock's query bounds to the program.
The same machine polynomial bounds the number of external queries and the length of each request.
The certificate is an equality of executions, so the bounds pass through every logged execution. -/
theorem IsOraclePPTOn.query_bounds {Operation α β : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → WordOracleComp Operation β} (h : IsOraclePPTOn input output program) :
    ∃ c d : ℕ, ∀ a, (program a).IsQueryBounded (c * ((input a).length + 1) ^ d) ∧
      (program a).QueriesSatisfy fun request =>
        request.2.length ≤ c * ((input a).length + 1) ^ d := by
  obtain ⟨_, k, Control, _, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a => ?_⟩
  obtain ⟨hcalls, hsize⟩ :=
    machine.query_bounds_runOracle (c * ((input a).length + 1) ^ d) (input a)
  have hrun (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool))
      (s s' : State) (result : List Bool)
      (transcript : OracleComp.Transcript (fun _ : Operation × List Bool => List Bool))
      (hmem : (result, s', transcript) ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
          (OracleComp.withTranscript oracle)) (output <$> program a)).run (s, [])).support) :
      transcript.length ≤ c * ((input a).length + 1) ^ d ∧
        ∀ entry ∈ transcript, entry.1.2.length ≤ c * ((input a).length + 1) ^ d := by
    rw [h a (State × OracleComp.Transcript (fun _ : Operation × List Bool => List Bool))
      (OracleComp.withTranscript oracle) (s, [])] at hmem
    exact ⟨hcalls.length_transcript_le oracle hmem, hsize.forall_mem_transcript oracle hmem⟩
  have hcalls' : ProbOracleComp.IsQueryBounded (output <$> program a)
      (c * ((input a).length + 1) ^ d) :=
    ProbOracleComp.isQueryBounded_of_length_transcript_le fun State oracle s s' result
      transcript hmem => (hrun State oracle s s' result transcript hmem).1
  have hsize' : ProbOracleComp.QueriesSatisfy
      (fun request => request.2.length ≤ c * ((input a).length + 1) ^ d) (output <$> program a) :=
    ProbOracleComp.queriesSatisfy_of_forall_mem_transcript fun State oracle s s' result
      transcript hmem => (hrun State oracle s s' result transcript hmem).2
  exact ⟨(OracleComp.isCostBounded_map_iff _ _ _).mp hcalls',
    (OracleComp.queriesSatisfy_map_iff _ _).mp hsize'⟩

end Cslib.Probability
