/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.QueryCount

/-!
# Cost budgets from call budgets

A program that makes at most `n` calls, each costing at most `c`, costs at most `n * c`. The
per-call bound need only hold on the calls satisfying a predicate that every call of the program
satisfies (`OracleComp.QueriesSatisfy`), such as a size bound on the requests.

## Main results

* `Cslib.OracleComp.IsQueryBounded.isCostBounded_mul`: at most `n` calls, each satisfying a
  predicate on which calls cost at most `c`, cost at most `n * c`.
* `Cslib.OracleComp.IsQueryBounded.isCostBounded_mul_of_forall_le`: the case where every call
  costs at most `c`.
* `Cslib.OracleComp.IsCostBounded.mul_of_le`: a budget `n` for one cost gives the budget `n * c`
  for a cost at most `c` times it, for example external requests costing at most `c` each.
-/

public section

namespace Cslib.OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α : Type v} {cost : ι → ℕ} {c n : ℕ}
  {program : OracleComp spec α}

/-- At most `n` calls, each satisfying `p`, cost at most `n * c` when the calls satisfying `p`
cost at most `c`. -/
theorem IsQueryBounded.isCostBounded_mul {p : ι → Prop} (h : program.IsQueryBounded n)
    (hp : QueriesSatisfy p program) (hcost : ∀ q, p q → cost q ≤ c) :
    IsCostBounded cost program (n * c) := by
  induction h with
  | pure a n => exact .pure a (n * c)
  | liftBind q cont n _ ih =>
    obtain ⟨hq, hcont⟩ := QueriesSatisfy.liftBind_iff.mp hp
    rw [Nat.succ_mul]
    exact (IsCostBounded.liftBind q cont (n * c) fun a => ih a (hcont a)).mono
      (Nat.add_le_add_left (hcost q hq) _)

/-- At most `n` calls, each costing at most `c`, cost at most `n * c`. -/
theorem IsQueryBounded.isCostBounded_mul_of_forall_le (h : program.IsQueryBounded n)
    (hcost : ∀ q, cost q ≤ c) : IsCostBounded cost program (n * c) :=
  h.isCostBounded_mul (.of_forall (p := fun _ => True) (fun _ => trivial) _) fun q _ => hcost q

/-- A budget `n` for `cost` gives the budget `n * c` for every cost `cost'` with
`cost' q ≤ cost q * c`. With `cost` counting only some calls, such as the external queries of a
program with private coins, this bounds the total cost of those calls at `c` each. -/
theorem IsCostBounded.mul_of_le {cost' : ι → ℕ} (h : IsCostBounded cost program n)
    (hcost : ∀ q, cost' q ≤ cost q * c) : IsCostBounded cost' program (n * c) := by
  induction h with
  | pure a n => exact .pure a (n * c)
  | liftBind q cont n _ ih =>
    rw [Nat.add_mul]
    exact (IsCostBounded.liftBind q cont (n * c) ih).mono (Nat.add_le_add_left (hcost q) _)

end Cslib.OracleComp
