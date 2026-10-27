/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.SharpThreeSAT
import Complexity.Logics.Propositional.CNF.ThreeCNF.Exact.PolyTime

/-!
# Tests for the #P-completeness of #3SAT and #3SAT-3
-/

namespace ComplexityTests.SharpThreeSAT

open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM

/-- The reduction keeps the fifteen models of one clause of width four, now as a width-three
instance. -/
example : SharpThreeSAT (toSharpThreeSAT [[(0, true), (1, true), (2, true), (3, true)]]) = 15 := by
  rw [sharpThreeSAT_toSharpThreeSAT]
  decide

/-- A formula with a clause of width four fails the `#3SAT` guard, so its guarded count is zero,
while the reduction recovers its fifteen models. -/
example : SharpThreeSAT [[(0, true)], [(1, true), (2, true), (3, true), (4, true)]] = 0 := by
  decide

example :
    SharpThreeSAT (toSharpThreeSAT [[(0, true)], [(1, true), (2, true), (3, true), (4, true)]]) =
      15 := by
  rw [sharpThreeSAT_toSharpThreeSAT]
  decide

/-- The certificate for the OR-gate split applies to any variable encoding. -/
example : ComputableInPolyTime (CNF.toExact3CNF (V := ℕ))
    (encList (encList (encPair encNat encBool)))
    (encList (encList (encPair (encSum encNat (encPair encUnary encUnary)) encBool))) :=
  CNF.isPolyTime_toExact3CNF encNat

/-- Hardness passes on: anything `#SAT` reduces to parsimoniously, `#3SAT-3` also receives. -/
example {β : Type} {encB : β ↪ List Bool} {g : β → ℕ}
    (h : ParsimoniousReducible encCNF encB SharpThreeSATThree g) : SharpPHard encB g :=
  SharpThreeSATThree_sharpPComplete.2.trans h

/-- Both counting problems belong to `#P`. -/
example : SharpThreeSAT ∈ SharpP encCNF ∧ SharpThreeSATThree ∈ SharpP encCNF :=
  ⟨SharpThreeSAT_sharpPComplete.1, SharpThreeSATThree_sharpPComplete.1⟩

end ComplexityTests.SharpThreeSAT
