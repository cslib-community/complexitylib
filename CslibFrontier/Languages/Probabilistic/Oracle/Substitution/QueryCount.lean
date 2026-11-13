/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution

/-!
# Query budgets of substituted programs

A reduction built with `ProbOracleComp.simulate handler A` keeps `A`'s private samples and replaces
each external query `q` by the program `handler q`. When every handler program costs at most the
cost of the query it replaces, the reduction keeps `A`'s budget. In particular, a reduction whose
handlers each make at most one query makes at most as many queries as `A`.

## Main results

* `Cslib.ProbOracleComp.isCostBounded_simulate`: substitution preserves cost budgets.
* `Cslib.ProbOracleComp.IsQueryBounded.simulate`: one-query handlers preserve query budgets.
-/

public section

namespace Cslib.ProbOracleComp

open OracleComp

variable {Query Query' α : Type} {spec : Query → Type} {spec' : Query' → Type}

/-- A substituted program costs at most `n` when the original program does and each handler
program costs at most the cost of the query it replaces. -/
theorem isCostBounded_simulate {cost : Query → ℕ} {cost' : Query' → ℕ}
    {handler : (q : Query) → ProbOracleComp spec' (spec q)}
    (hhandler : ∀ q, IsCostBounded (Sum.elim (fun _ => 0) cost') (handler q) (cost q))
    {program : ProbOracleComp spec α} {n : ℕ}
    (h : IsCostBounded (Sum.elim (fun _ => 0) cost) program n) :
    IsCostBounded (Sum.elim (fun _ => 0) cost') (ProbOracleComp.simulate handler program) n :=
  h.interpret fun
    | .inl k => isCostBounded_sample cost' (ProbComp.unifFin k)
    | .inr q => hhandler q

/-- A substituted program makes at most `n` queries when the original program does and each
handler program makes at most one. -/
theorem IsQueryBounded.simulate {handler : (q : Query) → ProbOracleComp spec' (spec q)}
    (hhandler : ∀ q, (handler q).IsQueryBounded 1) {program : ProbOracleComp spec α} {n : ℕ}
    (h : program.IsQueryBounded n) : (ProbOracleComp.simulate handler program).IsQueryBounded n :=
  isCostBounded_simulate (cost := fun _ => 1) (cost' := fun _ => 1) hhandler h

end Cslib.ProbOracleComp
