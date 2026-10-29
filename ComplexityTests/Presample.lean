/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.Presample
import Complexity.Crypto.Computational.Hybrid.Sequence
import Complexity.Tactic.PPT

namespace ComplexityTests.Presample

open Cslib Cslib.Crypto Cslib.ProbComp Cslib.Probability Turing.MultiTapeTM

-- Infinite output types and computed repetition counts charge the entire framed result list.
example : IsPPTOn encUnary (encList encBits)
    (fun n => OracleComp.replicate (n + 1) (BitString.sampleList (2 * n))) := by ppt

example : IsPPTOn encUnary (encList encUnary) (fun n =>
    OracleComp.replicate (2 * n)
      ((fun bit => if bit then n else 0) <$> ProbComp.uniform Bool)) := by ppt

-- The wrapper is an ordinary list traversal in execution order.
example (source : ProbComp ℕ) (count : ℕ) :
    OracleComp.replicate count source = (List.replicate count ()).mapM (fun _ => source) := rfl

-- Every pair has mass one quarter; collecting samples must not reuse a single random bit.
example (first second : Bool) :
    ProbComp.eval (OracleComp.replicate 2 (ProbComp.uniform Bool)) [first, second] = 1 / 4 := by
  cases first <;> cases second <;>
    norm_num [OracleComp.replicate_succ, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_uniform, PMF.bind_apply, PMF.map_apply, tsum_fintype,
      PMF.uniformOfFintype_apply, PMF.pure_apply, ← ENNReal.mul_inv]

-- A perfect one-coordinate test loses exactly a factor of two to the padding coordinate.
example (challenge : Bool) :
    (ProbComp.eval (sequenceTest (pure false) (pure true) 1
      (fun bits => pure (bits.headD false)) challenge) true).toReal =
        if challenge then 1 / 2 else 0 := by
  simp only [sequenceTest, ProbComp.eval_bind, eval_sampleDyadicIndex]
  change ((((PMF.uniformOfFintype (Fin 2)).map Fin.val).bind _) true).toReal = _
  cases challenge <;>
    norm_num [PMF.bind_apply, PMF.map_apply, tsum_fintype, Fin.sum_univ_succ,
      PMF.uniformOfFintype_apply, spliceTest, OracleComp.replicate, ProbComp.eval_pure,
      PMF.pure_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]

-- Zero repetitions reject every selected padding coordinate, regardless of the test.
example {α : Type} (left right : ProbComp α) (test : List α → ProbComp Bool) (challenge : α) :
    ProbComp.eval (sequenceTest left right 0 test challenge) = PMF.pure false := by
  simp only [sequenceTest, Nat.not_lt_zero, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure]
  exact PMF.bind_const _ _

private def respond (value query : Bool) (state : List Bool) : ProbComp (Bool × List Bool) :=
  pure (value ^^ query, value :: state)

-- Exhausting the supplied list uses the fallback and still updates ordinary private state.
example : OracleComp.withSampleList false respond true ([true], []) =
    pure (true, [false, true], []) := rfl

-- Consuming a saved sample preserves the unused suffix exactly, with no fresh draw.
example : OracleComp.withSampleList false respond true ([], [true, false]) =
    pure (false, [true], [false]) := rfl

-- Private draws leave both state components unchanged; the saved values belong only to queries.
example (state values : List Bool) :
    (OracleComp.interpret
      (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
        (OracleComp.withSampleList false respond))
          (ProbOracleComp.sample (ProbComp.uniform Bool))).run (state, values) =
      (fun bit => (bit, state, values)) <$> ProbComp.uniform Bool := by
  rw [ProbOracleComp.interpret_sample, OracleComp.run_interpret_lift]
  change (fun bit => (bit, state, values)) <$>
    OracleComp.interpret OracleComp.query (ProbComp.uniform Bool) = _
  rw [OracleComp.interpret_query_eq_self]

private noncomputable def adaptive : ProbOracleComp (fun _ : Bool => Bool) (Bool × Bool) := do
  let first ← ProbOracleComp.query false
  let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
  if first then
    let second ← ProbOracleComp.query (first ^^ coin)
    return (first, second)
  else return (first, coin)

private theorem adaptive_queryBounds : adaptive.IsQueryBounded 2 := by
  refine (ProbOracleComp.IsQueryBounded.query false).bind (m := 1) fun first =>
    ((ProbOracleComp.IsQueryBounded.sample _).bind (m := 1) fun coin => ?_).mono (by norm_num)
  cases first with
  | false => exact OracleComp.IsCostBounded.pure _ _
  | true =>
    exact ((ProbOracleComp.IsQueryBounded.query (true ^^ coin)).bind fun second =>
      OracleComp.IsCostBounded.pure _ 0).mono (by norm_num)

-- Two saved independent bits reproduce online sampling, including the correlated final state.
example (state : List Bool) :
    ProbComp.eval (do
      let values ← OracleComp.replicate 2 (ProbComp.uniform Bool)
      (fun (result, next, _) => (result, next)) <$> (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
          (OracleComp.withSampleList false respond)) adaptive).run (state, values)) =
      ProbComp.eval ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
          (fun query state => ProbComp.uniform Bool >>= fun value => respond value query state))
            adaptive).run state) :=
  adaptive_queryBounds.eval_presample (ProbComp.uniform Bool) false respond state

end ComplexityTests.Presample
