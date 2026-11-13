/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic

/-! A checked eager/lazy adapter: repeated valid queries retain their answer, malformed queries
leave the cache alone, and an intervening private draw remains fresh. -/

namespace CslibFrontierTests.RandomOracleAdapter

open Cslib Cslib.Probability

private def oneBitQuery (word : List Bool) : ProbOracleComp (fun _ : Bool => Bool) (List Bool) :=
  match word with
  | [bit] => List.singleton <$> ProbOracleComp.query bit
  | _ => pure []

private noncomputable def repeated : ProbOracleComp (fun _ : List Bool => List Bool) Bool := do
  let first ← ProbOracleComp.query [false]
  let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let rejected ← ProbOracleComp.query []
  let second ← ProbOracleComp.query [false]
  return (first == second) && rejected.isEmpty && coin

private noncomputable def adapted : ProbOracleComp (fun _ : Bool => Bool) Bool :=
  ProbOracleComp.simulate oneBitQuery repeated

-- The one eager/lazy law applies to the adapted program, with no reconstruction of its private
-- sampling handler. This is the same route used by the GGM and PRF game hops.
example :
    (do
      let table ← PMF.pi (fun _ : Bool => PMF.uniformOfFintype Bool)
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun bit => PMF.pure (table bit))) adapted) =
      (ProbOracleComp.runWith (memoize (fun _ : Bool => PMF.uniformOfFintype Bool))
        adapted []).map Prod.fst :=
  RandomOracle.interpret_prob_eq_memoize _ adapted

-- The complete cached run retains one entry. The invalid query adds no entry, the repeated query
-- reuses the first answer, and the returned coin is sampled independently of that answer.
example :
    ProbOracleComp.runWith (memoize (fun _ : Bool => PMF.uniformOfFintype Bool)) adapted [] = (do
      let value ← PMF.uniformOfFintype Bool
      let coin ← PMF.uniformOfFintype Bool
      pure (coin, [(false, value)])) := by
  simp [adapted, repeated, oneBitQuery, runWith_norm, pmf_norm,
    memoize, ProbComp.eval_uniform]

end CslibFrontierTests.RandomOracleAdapter
