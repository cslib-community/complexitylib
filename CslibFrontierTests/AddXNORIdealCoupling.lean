/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import CslibFrontier.Cryptanalysis.AddXNORIdealCoupling
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Probability.PMF.Uniform

/-!
# Hidden-cut and stopped-coupling clients

Forcing a target already in use repairs its displaced preimage. A three-layer source path
checks that the cut really changes the original endpoint. A private-coin program queries a
changed entry on one branch and an unchanged entry on the other, giving exact bad probability
one half. These are experiment/coupling tests, not instances of a proved Theorem 8 inequality.
-/

public section

open Cslib Cslib.Probability Cslib.OracleComp Cslib.RandomPermutation
open Cslib.Cryptanalysis.AddXNOR.IdealChain

namespace IdealCouplingClient

/-- Every layer uses a non-self-inverse three-cycle in this deterministic test family. -/
@[expose] def cyclic : Label 3 → Equiv.Perm (Fin 3) :=
  fun _ => Equiv.swap 0 1 * Equiv.swap 1 2

example : chain cyclic (fun _ => false) 0 = 0 := by decide

example : chain ((sourceCut (fun _ => false) (1 : Fin 3)).splice cyclic 0 1)
    (fun _ => false) 0 = 1 := by
  rw [← sourceCut_endpoint (fun _ => false) (1 : Fin 3)]
  exact Cut.endpoint_splice _ _ _ _

example : force (cyclic (0, false)) 1 0 0 = 1 ∧
    force (cyclic (0, false)) 1 0 1 = 0 ∧
    force (cyclic (0, false)) 1 0 2 = 2 ∧
    (force (cyclic (0, false)) 1 0).symm 0 = 1 := by decide

/-- No-query observers have identical public-input laws in the two actual source experiments.
The parameters admit the source's query range, although this observer makes no queries. -/
example : decision (q := 3) (Word := Fin 32) true
    (fun seed target : Fin 32 => pure (decide (seed = target))) =
    decision (q := 3) false (fun seed target : Fin 32 => pure (decide (seed = target))) := by
  rw [← coupledDecision_planted (1 : Fin 3), ← coupledDecision_original (1 : Fin 3)]
  simp [coupledDecision]

/-- With a fair private bit, query a changed point or an unchanged point. -/
@[expose] def coinQuery : ProbOracleComp (Family.Spec Unit (Fin 3)) Bool := do
  let bit ← ProbOracleComp.sample (ProbComp.unifFin 1)
  let reply ← ProbOracleComp.query ((), .forward (if bit.val = 0 then 0 else 2))
  return decide (reply = 1)

example : ProbOracleComp.IsQueryBounded coinQuery 1 := by
  have hs := ProbOracleComp.IsQueryBounded.sample (spec := Family.Spec Unit (Fin 3))
    (ProbComp.unifFin 1)
  simpa only [coinQuery, Nat.zero_add, Nat.add_zero] using hs.bind fun bit =>
    (ProbOracleComp.IsQueryBounded.query
      ((), .forward (if bit.val = 0 then 0 else 2))).bind fun reply =>
        IsCostBounded.pure (decide (reply = (1 : Fin 3))) 0

example : Visible.badGame (fun _ : Unit => Equiv.refl (Fin 3))
    (fun _ : Unit => force (Equiv.refl (Fin 3)) 0 1) coinQuery true = 1 / 2 := by
  rw [Visible.badGame_trace]
  simp [coinQuery, pmf_norm, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
    ProbOracleComp.runWith_query, ProbComp.eval,
    ProbComp.unifFin, interpret_query, ProbComp.unifOracle, PMF.bind_apply,
    tsum_fintype, Fin.sum_univ_succ, Visible.reader, withTranscript,
    Visible.traceBad, Family.eval, evalPerm, force, Equiv.swap_apply_def]

end IdealCouplingClient
