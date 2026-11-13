/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query
public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.CountingQuery

/-!
# Ordinary count bits from local finishing-adder queries

The finishing query reads the two mathematical carry-save root words and a false incoming carry.
Its selected sum bit is exactly the ordinary binary count bit. The root words are semantic data;
a native evaluator must answer their component queries with the charged counting continuation.
-/

public section

namespace Cslib.Circuits.Boolean.CarryLookahead.Query

open CarrySaveQuery

/-- A finishing query on the two root components returns an ordinary count bit. -/
theorem value_count_sum_eq (n w : ℕ) (predicate : ℕ → Bool) (i : Fin w) :
    value w (Nat.clog 2 (w + 1))
      (Fin.append (Fin.append (component (Counting.rootPair n w predicate) false)
        (component (Counting.rootPair n w predicate) true)) ![false]) (.sum i) =
      Counting.count n w predicate i := by
  rw [value_sum_eq]
  simp only [component, Bool.false_eq_true, ↓reduceIte,
    BitString.append_fstBits_sndBits, Counting.count, carryLookaheadAdd,
    Circuit.eval_comp, Circuit.eval_append, Circuit.eval_wiring, Function.comp_def, id_eq]
  congr 2
  funext j
  fin_cases j
  rfl

end Cslib.Circuits.Boolean.CarryLookahead.Query
