/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import CslibFrontier.Languages.Probabilistic.Oracle.Codec

/-! # Typed views of word oracles -/

namespace CslibFrontierTests.OracleCodec

open Cslib

private def wordAdversary :
    ProbOracleComp (fun _ : Unit × List Bool => List Bool) (List Bool × List Bool) := do
  let rejected ← ProbOracleComp.query ((), [true])
  let reply ← ProbOracleComp.query ((), [true, false])
  return (rejected, reply)

private noncomputable def echo (x : BitString 2) : StateT ℕ PMF (BitString 2) := fun calls =>
  PMF.pure (x, calls + 1)

-- The one-bit request carries no 2-bit query: it is answered `[]` without a call, so only the
-- well-formed request reaches the typed oracle and advances its counter.
example (calls : ℕ) :
    ProbOracleComp.runWith echo ((OracleCodec.bitString 2).adapt wordAdversary) calls =
      PMF.pure (([], [true, false]), calls + 1) := by
  rw [OracleCodec.runWith_adapt]
  simp only [ProbOracleComp.runWith, OracleComp.runWith, wordAdversary, OracleComp.interpret_bind,
    ProbOracleComp.interpret_query, StateT.run_bind, OracleComp.interpret_pure, StateT.run_pure]
  simp only [OracleCodec.wordOracle, OracleCodec.bitString, List.ofFn_succ, Fin.isValue,
    Fin.succ_zero_eq_one, List.ofFn_zero, List.length_cons, List.length_nil, zero_add,
    OfNat.one_ne_ofNat, ↓reduceIte, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
    Nat.reduceAdd, Function.Embedding.coeFn_mk, StateT.run_map, PMF.monad_map_eq_map,
    Probability.PMF.monad_bind_eq_bind, PMF.bind_map, PMF.pure_bind]
  simp [echo, StateT.run, BitString.ofList]

-- Adapting removes the malformed request from the program itself.
example : (OracleCodec.bitString 2).adapt wordAdversary = (do
    let reply ← ProbOracleComp.query (spec := fun _ : BitString 2 => BitString 2)
      (BitString.ofList 2 [true, false])
    return ([], List.ofFn reply)) := by
  simp [wordAdversary, OracleCodec.wordOracle, OracleCodec.bitString]

-- The word program's query budget carries over to the adapted program.
example : ((OracleCodec.bitString 2).adapt wordAdversary).IsQueryBounded 2 :=
  (OracleCodec.bitString 2).isQueryBounded_adapt <| by
    simpa [wordAdversary] using (ProbOracleComp.IsQueryBounded.query ((), [true])).bind fun _ =>
      (ProbOracleComp.IsQueryBounded.query ((), [true, false])).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0

end CslibFrontierTests.OracleCodec
