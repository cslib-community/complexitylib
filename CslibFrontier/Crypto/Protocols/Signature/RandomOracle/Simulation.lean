/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.Signature.RandomOracle
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF

/-!
# Replacing a forger by saved-coin interactions

Equality of joint output and arbitrary external state is sufficient to replace a probabilistic
forger by a mixture of fixed-coin programs in the existing shared-world game. The handler state
includes both the cache and signing log, and verification continues with the resulting cache.

## Main results

* `Cslib.Crypto.Protocols.ROMSignature.eval_worldRealize_eq_bind`: shared-world mixture law.

## References

Original consequence of the existing stateful interpreter composition laws.
-/

public section

namespace Cslib.Crypto.Protocols.ROMSignature

open Probability OracleComp

/-- A saved-coin decomposition valid for every stateful handler preserves any shared-world
acceptance rule, including final-message freshness with repeated signing queries allowed. -/
theorem eval_worldRealize_eq_bind {PK SK M Sig Query Digest Coins : Type}
    [DecidableEq Query] [Fintype Digest] [Nonempty Digest]
    (scheme : Scheme PK SK M Sig Query Digest) (pk : PK) (sk : SK)
    (program : ProbOracleComp (ForgerSpec M Query Sig Digest) (M × Sig))
    (coins : PMF Coins) (replay : Coins → OracleComp (ForgerSpec M Query Sig Digest) (M × Sig))
    (h : ∀ (Store : Type)
      (handler : (q : M ⊕ Query) → StateT Store PMF (ForgerSpec M Query Sig Digest q)) s,
      ProbOracleComp.runWith handler program s =
        coins.bind (fun r => ProbOracleComp.runWith handler (liftOracleForger (replay r)) s))
    (accept : Bool → M × Sig → List (M × Sig) → Bool) :
    (world scheme sk).eval (worldRealize scheme pk program accept) = coins.bind (fun r =>
      (world scheme sk).eval (worldRealize scheme pk (liftOracleForger (replay r)) accept)) := by
  simp only [eval_world_worldRealize, runLoggedForger, ProbOracleComp.runWith_run_interpret, h]
  simp only [PMF.map_bind, PMF.monad_bind_eq_bind, PMF.bind_bind]

end Cslib.Crypto.Protocols.ROMSignature
