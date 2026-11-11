/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Algorithms.Lean.Query.Arith.Defs
public import Complexity.Init

/-!
# Arithmetic query counts

Lemmas about cslib's arithmetic query model `FreeM (ArithQuery α)` that are not specific to one
program.

## Main results

* `Cslib.Query.ArithQuery.countQueries_eq_cost_weight_one`: the query count is the arithmetic cost
  with unit weights for additions, subtractions and multiplications.
-/

public section

namespace Cslib.Query

variable {α : Type}

/-- Counting queries is the arithmetic cost with unit weights. -/
theorem ArithQuery.countQueries_eq_cost_weight_one {β : Type}
    (o : {ι : Type} → ArithQuery α ι → ι) (prog : FreeM (ArithQuery α) β) :
    prog.countQueries o = prog.cost o (ArithQuery.weight 1 1) := by
  have h : (fun {ι : Type} (_ : ArithQuery α ι) => (1 : ℕ)) = @ArithQuery.weight α 1 1 := by
    funext ι q
    cases q <;> rfl
  rw [FreeM.countQueries_eq_cost_one, h]

end Cslib.Query
