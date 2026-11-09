/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.Defs
public import CslibFrontier.Computability.Complexity.Classes.IP.Repetition

/-!
# Sequential repetition against non-communicating provers

`Cslib.Complexity.sequentialRepeat` runs a verifier several times in sequence. Against a family of
non-communicating provers (`Cslib.Complexity.Prover.independent`), the provers after any history
are again such a family, restarted from their own states
(`Cslib.Complexity.Prover.independent_with_init`). So a bound `ε` on the acceptance of one run
against every independent family bounds `k` runs by `ε ^ k`
(`Cslib.Complexity.acceptProb_sequentialRepeat_independent_le`), as for one prover in
`CslibFrontier/Computability/Complexity/Classes/IP/Repetition.lean`.

## Main results

* `Cslib.Complexity.Prover.independent_with_init`: restarting an independent family.
* `Cslib.Complexity.acceptProb_sequentialRepeat_independent_le`: soundness error `ε ^ k`.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability

/-- An independent prover family restarted from a joint state is the family of the individual
provers restarted from their own states. -/
theorem Prover.independent_with_init {ι : Type} [DecidableEq ι] (P : ι → Prover Unit)
    (s : (Prover.independent P).State) :
    ({ Prover.independent P with init := s } : Prover ι) =
      Prover.independent fun i => { P i with init := s i } :=
  rfl

/-- **Soundness amplification against non-communicating provers.** If every independent prover
family is accepted by one run with probability at most `ε`, every independent family is accepted
by `k` sequential runs with probability at most `ε ^ k`: after any history the provers are again
an independent family. -/
theorem acceptProb_sequentialRepeat_independent_le {ι : Type} [DecidableEq ι]
    {round : WordOracleComp ι Bool} {ε : ENNReal}
    (h : ∀ P : ι → Prover Unit, acceptProb round (Prover.independent P) ≤ ε) (k : ℕ)
    (P : ι → Prover Unit) :
    acceptProb (sequentialRepeat k round) (Prover.independent P) ≤ ε ^ k := by
  induction k generalizing P with
  | zero => exact (PMF.coe_le_one _ _).trans (by simp)
  | succ k ih =>
    rw [sequentialRepeat, acceptProb_bind_ite, pow_succ]
    calc ∑' s, (Prover.independent P).run round (Prover.independent P).init (true, s) *
          acceptProb (sequentialRepeat k round) { Prover.independent P with init := s }
        ≤ ∑' s, (Prover.independent P).run round (Prover.independent P).init (true, s) *
            ε ^ k :=
          tsum_le_tsum fun s => mul_le_mul' le_rfl (by
            rw [Prover.independent_with_init]
            exact ih _)
      _ = (∑' s, (Prover.independent P).run round (Prover.independent P).init (true, s)) *
            ε ^ k := ENNReal.tsum_mul_right
      _ ≤ ε * ε ^ k := by
          gcongr
          exact (acceptProb_eq_tsum round _).symm.trans_le (h P)
      _ = ε ^ k * ε := mul_comm _ _

end Cslib.Complexity
