/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Languages.Probabilistic.QueryCount
public import Complexity.Languages.Probabilistic.Semantics

/-!
# Query budgets on possible outputs

Connects query budgets (`Cslib.OracleComp.IsCostBounded`) with the possible outputs
(`Cslib.OracleComp.support`) of an oracle computation, and records the unit query budget of
`Cslib.ProbComp.unifFin`.

## Main results

* `Cslib.OracleComp.IsCostBounded.bind_on_support`: query cost budgets add under sequencing when
  the continuation is bounded on every possible output of the first computation.
* `Cslib.ProbComp.isQueryBounded_unifFin`: `ProbComp.unifFin n` makes one oracle query.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β : Type v}

/-- Query cost budgets add under sequencing when the continuation is bounded on every possible
first-stage output. -/
theorem IsCostBounded.bind_on_support {cost : ι → ℕ} {program : OracleComp spec α}
    {next : α → OracleComp spec β} {n m : ℕ}
    (h : IsCostBounded cost program n)
    (hnext : ∀ a ∈ program.support, IsCostBounded cost (next a) m) :
    IsCostBounded cost (program >>= next) (n + m) := by
  induction h with
  | pure a n => exact (hnext a rfl).mono (by omega)
  | liftBind q cont n _ ih =>
    rw [show n + cost q + m = n + m + cost q by omega]
    exact .liftBind q _ (n + m) fun r =>
      ih r fun a ha => hnext a (mem_supportWith_bind_iff.mpr ⟨r, by simp, ha⟩)

end OracleComp

namespace ProbComp

/-- `unifFin n` makes one oracle query. -/
theorem isQueryBounded_unifFin (n : ℕ) : (unifFin n).IsQueryBounded 1 :=
  OracleComp.IsCostBounded.query (spec := unifSpec) (cost := fun _ => 1) n

end ProbComp

end Cslib
