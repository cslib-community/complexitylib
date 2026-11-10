/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Probabilistic.Fold
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Tactic.PPT

/-! Ordinary list folds preserve order, omit empty-list effects and retain external state. -/

namespace CslibFrontierTests.ProbabilisticFold

open Cslib Cslib.Probability Turing.MultiTapeTM

private def prepend (acc : List Bool) (bit : Bool) : ProbComp (List Bool) :=
  pure (bit :: acc)

-- The list and initial accumulator use plain certificates; no tidy premise reaches the client.
theorem closed_fold_isPPT :
    IsPPTOn (encList encBool) encBits (fun bits => bits.foldlM prepend []) := by
  refine IsPPTOn.foldlM_of_bounded_growth false (by fun_prop) (by fun_prop)
    (by unfold prepend; ppt) (growth := 1) ?_
  intro acc bit next hnext
  simp only [prepend, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
  simp [hnext]

theorem closed_fold_eval :
    ProbComp.eval ([true, false].foldlM prepend []) = PMF.pure [false, true] := by rfl

private def queryStep (acc : List Bool) (bit : Bool) : WordOracleComp Unit (List Bool) := do
  let reply ← List.take 1 <$> ProbOracleComp.query ((), [bit])
  return reply ++ acc

theorem oracle_fold_isPPT : IsOraclePPTOn (Operation := Unit) (encList encBool) encBits
    (fun bits => bits.foldlM queryStep []) := by
  refine IsOraclePPTOn.foldlM_of_bounded_growth false (by fun_prop) (by fun_prop)
    ?_ (growth := 1) ?_
  · have hquery : IsOraclePPTOn (Operation := Unit) (encPair encBits encBool) encBits
        (fun p => List.take 1 <$> ProbOracleComp.query ((), [p.2])) :=
      .query_take' () (by fun_prop) (by fun_prop)
    exact hquery.map_with' (f := fun p reply => reply ++ p.1) (by fun_prop)
  · intro acc bit next hnext
    simp only [queryStep, bind_pure_comp, OracleComp.support,
      OracleComp.mem_supportWith_map_iff] at hnext
    obtain ⟨reply, ⟨raw, _, rfl⟩, rfl⟩ := hnext
    simp only [encBits_apply, List.length_append]
    have := List.length_take_le 1 raw
    omega

private noncomputable def echoCounting (request : Unit × List Bool) :
    StateT ℕ PMF (List Bool) := fun count => pure (request.2, count + 1)

-- A nonempty fold preserves the full oracle state and makes its calls from left to right.
theorem oracle_fold_run :
    ProbOracleComp.runWith echoCounting ([true, false].foldlM queryStep []) 0 =
    PMF.pure ([false, true], 2) := by
  simp [List.foldlM_cons, queryStep, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    echoCounting]

-- The fallback is never queried on the empty list.
theorem empty_oracle_fold_run :
    ProbOracleComp.runWith echoCounting ([].foldlM queryStep [true]) 7 =
    PMF.pure ([true], 7) := by rfl

private def adaptiveQueryStep (acc : List Bool) (bit : Bool) : WordOracleComp Unit (List Bool) :=
  queryStep acc (acc.headD false ^^ bit)

-- The next request uses the previous reply, while the same one-bit growth bound still applies.
theorem adaptive_oracle_fold_isPPT : IsOraclePPTOn (Operation := Unit) (encList encBool) encBits
    (fun bits => bits.foldlM adaptiveQueryStep []) := by
  refine IsOraclePPTOn.foldlM_of_bounded_growth false (by fun_prop) (by fun_prop)
    ?_ (growth := 1) ?_
  · have hquery : IsOraclePPTOn (Operation := Unit) (encPair encBits encBool) encBits
        (fun p => List.take 1 <$> ProbOracleComp.query ((), [p.1.headD false ^^ p.2])) :=
      .query_take' () (by fun_prop) (by fun_prop)
    exact hquery.map_with' (f := fun p reply => reply ++ p.1) (by fun_prop)
  · intro acc bit next hnext
    simp only [adaptiveQueryStep, queryStep, bind_pure_comp, OracleComp.support,
      OracleComp.mem_supportWith_map_iff] at hnext
    obtain ⟨reply, ⟨raw, _, rfl⟩, rfl⟩ := hnext
    simp only [encBits_apply, List.length_append]
    have := List.length_take_le 1 raw
    omega

private noncomputable def historyOracle (request : Unit × List Bool) :
    StateT (Bool × List (List Bool)) PMF (List Bool) := fun (phase, history) =>
  pure ([phase, request.2.headD false, !phase], (!phase, history ++ [request.2]))

-- The handler toggles its reply bit and returns three bits per call, of which only one survives.
-- The first reply changes the second request to [true]; the history records all adaptive calls.
theorem adaptive_oracle_fold_run :
    ProbOracleComp.runWith historyOracle
      ([false, false, true].foldlM adaptiveQueryStep []) (true, []) =
    PMF.pure ([true, false, true], (false, [[false], [true], [true]])) := by
  simp [List.foldlM_cons, adaptiveQueryStep, queryStep, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, historyOracle]

end CslibFrontierTests.ProbabilisticFold
