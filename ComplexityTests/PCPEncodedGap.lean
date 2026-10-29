/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Encoded.GapTheorem
import Complexity.Tactic.PolyTime

/-! Whole SAT-to-gap reduction clients, including arbitrary clause widths and variable encodings.
The enormous fixed amplification tables are not materialized by these semantic clients.
-/

namespace ComplexityTests.PCPEncodedGap

open Cslib.Logic.PL Cslib.PCP.Encoded Turing.MultiTapeTM
open Cslib.PCP.ConstraintGraph.Amplification.Arithmetic

example : ComputableInPolyTime (gapGraph (V := ℕ))
    (encList (encList (encPair encNat encBool)))
    (Graph.encoding (encPi (encPi encBool))) := by polytime

example : ComputableInPolyTime (gapGraph (V := List Bool))
    (encList (encList (encPair encBits encBool)))
    (Graph.encoding (encPi (encPi encBool))) := by polytime

example : ComputableInPolyTime (gapGraph (V := List Bool))
    (encList (encList (encPair (encList encBool) encBool)))
    (Graph.encoding (encPi (encPi encBool))) := by fun_prop

example (empty : Empty ↪ List Bool) : ComputableInPolyTime (gapGraph (V := Empty))
    (encList (encList (encPair empty encBool)))
    (Graph.encoding (encPi (encPi encBool))) := by polytime

section Captured

variable {V Input : Type} [DecidableEq V] {enc : V ↪ List Bool}
  {input : Input ↪ List Bool} {formula : Input → CNF V}
  (hformula : ComputableInPolyTime formula input
    (encList (encList (encPair enc encBool))))

example : ComputableInPolyTime (fun x => gapGraph (formula x)) input
    (Graph.encoding (encPi (encPi encBool))) := by
  fail_if_success (clear hformula; fun_prop)
  fun_prop

example : ComputableInPolyTime
    (fun x => let φ := formula x; gapGraph (φ ++ φ)) input
    (Graph.encoding (encPi (encPi encBool))) := by
  fail_if_success (clear hformula; polytime)
  polytime

end Captured

example : ((gapGraph ([] : CNF Empty)).toGraph id).Satisfiable :=
  (satisfiable_gapGraph_iff _).mpr ⟨Empty.elim, rfl⟩

example : gap ≤ ((gapGraph ([[]] : CNF Empty)).toGraph id).unsatVal :=
  gap_le_unsatVal_gapGraph _ (by simp [CNF.Satisfiable])

private def wideFormula : CNF ℕ :=
  [[(0, true), (1, true), (2, true), (3, true), (4, true)]]

-- A satisfying assignment may depend on a literal beyond the first three positions.
example : ((gapGraph wideFormula).toGraph id).Satisfiable :=
  (satisfiable_gapGraph_iff _).mpr ⟨fun n => n == 4, rfl⟩

private def wideContradiction : CNF ℕ :=
  [[(2 ^ 100, true), (2 ^ 100, true), (2 ^ 100, true), (2 ^ 100, true)],
    [(2 ^ 100, false)]]

-- Repeated sparse names and a wide clause still produce a genuine positive gap.
example : gap ≤ ((gapGraph wideContradiction).toGraph id).unsatVal := by
  apply gap_le_unsatVal_gapGraph
  rintro ⟨σ, hσ⟩
  cases σ (2 ^ 100) <;>
    simp [wideContradiction] at hσ

example : (gapGraph wideContradiction).WellFormed := wellFormed_gapGraph _

end ComplexityTests.PCPEncodedGap
