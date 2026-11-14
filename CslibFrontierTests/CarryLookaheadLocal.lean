/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Local

/-! Local carry queries use binary widths and materialize at most two gates. -/

namespace CslibFrontierTests.CarryLookaheadLocal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.CarryLookahead
open Turing.MultiTapeTM ComputableInPolyTime

/-- One uniform native machine handles every binary width. -/
example : ComputableInPolyTime (fun n : ℕ => cellGate n n 0 true 0) encNat encGate :=
  cellGate_polyTime (by fun_prop) (by fun_prop) (.const _) (.const _) (.const _)

/-- The incoming carry's propagate bit is false, including at width zero. -/
example : initialCellCode 0 0 false = ([(.const false, [])], [1]) := rfl

/-- A huge numeric width still gives only the two gates of one cell. -/
example : (cellCode (2 ^ 100) (2 ^ 70) 3 true).1.length ≤ 2 :=
  length_cellCode_le _ _ ⟨3, by norm_num⟩ true

/-- The local semantics also covers a missing neighbour (the cell retains its summary). -/
example (row : BitString 6) :
    (cell 3 4 ⟨2, by omega⟩ true).eval interpretation row 0 = row 2 := by
  simp [cell, generateFormula, neighbour, Formula.eval_toCircuit, Formula.eval_or,
    Formula.eval_and, Formula.eval_input]

end CslibFrontierTests.CarryLookaheadLocal
