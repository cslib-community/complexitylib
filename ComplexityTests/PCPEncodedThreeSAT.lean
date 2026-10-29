/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Encoded.ThreeSAT
import Complexity.Tactic.PolyTime

/-! Compact variable names, exact initial graphs, and complete small constraint tables. -/

namespace ComplexityTests.PCPEncodedThreeSAT

open Cslib.Logic.PL Cslib.PCP.Encoded Turing.MultiTapeTM

private def largeName : ℕ := 2 ^ 100

example : CNF.compact [[(largeName, true)], [(largeName, false)]] =
    [[(0, true)], [(0, false)]] := by decide

example : CNF.compact [[(5, true), (2, false)], [(5, false), (7, true)]] =
    [[(0, true), (1, false)], [(0, false), (3, true)]] := by decide

example : CNF.compact ([] : CNF ℕ) = [] := rfl
example : CNF.compact ([[]] : CNF ℕ) = [[]] := rfl

example : (Graph.ofCompactCNF [[(largeName, true)]]).vertices = 4 := by decide
example : (Graph.ofCompactCNF [[(largeName, true)]]).edges.length = 3 := by decide
example : (Graph.ofCompactCNF [[(largeName, true)]]).isWellFormed = true := by decide

example : (Graph.ofCompactCNF ([] : CNF ℕ)).vertices = 0 := rfl
example : (Graph.ofCompactCNF ([] : CNF ℕ)).edges = [] := rfl
example : (Graph.ofCompactCNF ([[]] : CNF ℕ)).edges.length = 3 := by decide

-- The raw constructor requires bounded names for its finite vertex interpretation.
example : (Graph.ofCNF 1 [[(100, true)]]).isWellFormed = false := by decide

-- Explicit binary numbering executes all 64 entries of every small constraint table.
-- This checks the functional construction; its TM resource certificate is tested separately.
private def labels : List (Fin 3 → Bool) :=
  (List.finRange 8).map fun i j => i.val.testBit j.val

example : ∀ a : Fin 3 → Bool, a ∈ labels := by decide
example : labels.Nodup := by decide

private def tables (φ : CNF ℕ) : List (List Bool) :=
  (Graph.ofCompactCNF φ).edges.map fun e =>
    labels.flatMap fun a => labels.map fun b => e.constraint a b

example : (tables [[(largeName, true)]]).map List.length = [64, 64, 64] := by decide

/-- info: [16, 32, 32] -/
#guard_msgs in
#eval (tables [[(largeName, true)]]).map (fun row => row.count true)

/-- info: [24, 24, 48] -/
#guard_msgs in
#eval (tables [[(largeName, true), (largeName, false)]]).map (fun row => row.count true)

example : (tables ([[]] : CNF ℕ)).map (fun row => row.count true) = [0, 0, 0] := by decide

example : ((Graph.ofCompactCNF ([] : CNF ℕ)).toGraph id).Satisfiable := by
  apply (Graph.satisfiable_ofCompactCNF_iff _ (by simp)).mpr
  exact ⟨fun _ => false, rfl⟩

example : ¬ ((Graph.ofCompactCNF ([[]] : CNF ℕ)).toGraph id).Satisfiable := by
  rw [Graph.satisfiable_ofCompactCNF_iff _ (by simp)]
  simp [CNF.Satisfiable]

example : (3 : ℝ)⁻¹ ≤ ((Graph.ofCompactCNF ([[]] : CNF ℕ)).toGraph id).unsatVal := by
  simpa using Graph.inv_edges_le_unsatVal_ofCompactCNF ([[]] : CNF ℕ)
    (by simp) (by simp [CNF.Satisfiable])

example : ComputableInPolyTime (Graph.ofCompactCNF (V := ℕ))
    (encList (encList (encPair encNat encBool)))
    (Graph.encoding (encPi (encPi encBool))) := by polytime

example : ComputableInPolyTime (Graph.ofCompactCNF (V := List Bool))
    (encList (encList (encPair encBits encBool)))
    (Graph.encoding (encPi (encPi encBool))) := by polytime

example : ComputableInPolyTime (Graph.ofCompactCNF (V := List Bool))
    (encList (encList (encPair (encList encBool) encBool)))
    (Graph.encoding (encPi (encPi encBool))) := by fun_prop

example : ComputableInPolyTime (fun names : List ℕ =>
    let formula := names.map fun n => [(n, true)]
    Graph.ofCompactCNF formula) (encList encNat)
    (Graph.encoding (encPi (encPi encBool))) := by polytime

example (algorithm : List Bool → CNF ℕ)
    (h : ComputableInPolyTime algorithm encBits
      (encList (encList (encPair encNat encBool)))) :
    ComputableInPolyTime (fun word => Graph.ofCompactCNF (algorithm word)) encBits
      (Graph.encoding (encPi (encPi encBool))) := by
  fail_if_success (clear h; polytime)
  polytime

end ComplexityTests.PCPEncodedThreeSAT
