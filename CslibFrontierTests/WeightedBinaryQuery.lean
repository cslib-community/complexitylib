/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import CslibFrontier.Computability.PolyTime.CNF.WeightedQuery

/-! # Actual binary query enumeration, deduplication and output -/

open Cslib Cslib.Logic.PL Cslib.Logic.PL.WeightedRow
open Cslib.Logic.PL.WeightedRow.BinaryQuery Turing.MultiTapeTM

namespace WeightedBinaryQueryTests

example : ([0, 1, 2, 3] : List ℕ).sublistsLen 2 =
    [[2, 3], [1, 3], [1, 2], [0, 3], [0, 2], [0, 1]] := by decide
example : ([[], [1], [1], []] : List (List ℕ)).dedup = [[1], []] := by decide
example : boundedAt 2 (1 : ℤ) ([0, 1] : List ℕ) = [[], [1], [0]] := by decide
example : boundedAt 2 (-1) ([0, 1] : List ℕ) = [[]] := by decide

/-- Duplicate normalized rows with unattainable demand. -/
def normalized : RowData := ([(0, true, 2), (1, true, 2)], 1)

example : base 1 [normalized, normalized] =
    [[(1, false)], [(0, false)], [(0, false), (1, false)]] := by decide
example : query 1 3 [normalized] false = query 1 3 [normalized] true := by decide

example : termClauses 4 2 false 1 [] =
    [[(4, false), (5, true)], [(4, true), (5, false)]] := by decide
example : termClauses 4 0 false 0 [] = [] := by decide
example : termClauses 4 0 true 0 [] = [[]] := by decide

/-- Two independent original equations; the Gram scan chooses original indices [1,0]. -/
def original : List BinaryNormalization.Input :=
  [([(0, true, 1)], 1), ([(1, true, 1)], 1)]

example : selectedQuery 0 3 original false =
    [[(1, true)], [(0, true)], [(3, false)], [(3, false)]] := by decide
example : selectedQuery 0 3 original true =
    [[(1, true)], [(0, true)], [(3, false)], [(3, true)]] := by decide

example : originalQueryStage 0 3 original =
    ((false, [1, 0], true, false),
      ([[(1, true)], [(0, true)], [(3, false)], [(3, false)]],
        [[(1, true)], [(0, true)], [(3, false)], [(3, true)]])) := by decide

/-- Test-only exhaustive oracle over every declared bit, including unused variables. -/
def count (N : ℕ) (q : CNF ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin N → Bool)).filter fun σ =>
    q.eval fun i => if hi : i < N then σ ⟨i, hi⟩ else false).card

example : count 4 (selectedQuery 0 3 original false) = 2 := by decide
example : count 4 (selectedQuery 0 3 original true) = 0 := by decide
example : selectedQuery 0 2 [([(0, true, 2 ^ 80)], 2 ^ 80)] false =
    [[(0, true)]] := by decide
example : selectedQuery 0 2 [([(0, true, 2 ^ 80)], 2 ^ 80)] true =
    [[(0, true)], []] := by decide

/-- Original repeated opposite-polarity occurrences run through the certified query stage. -/
example : selectedQuery 1 3 [([(0, true, 3), (0, false, 1), (1, true, 2)], 2)] false =
    [[(1, false)], [(0, false)], [(0, false), (1, false)]] := by decide

example : ComputableInPolyTime (List.sublistsLen 2 : List ℕ → List (List ℕ))
    (encList encUnary) (encList (encList encUnary)) := sublistsLen_polytime encUnary 0 2

example : ComputableInPolyTime (fun p : (ℕ × List BinaryNormalization.Input) × Bool =>
    let ((n, rows), β) := p
    selectedQuery 1 n rows β)
    (encPair (encPair encUnary (encList BinaryNormalization.encInput)) encBool) encCNF :=
  selectedQuery_polytime 1

/-- The same two equations in the reviewed original occurrence representation. -/
def source (j : Fin 2) : Occurrences 3 1 where
  var := fun _ => ⟨j, by omega⟩
  sign := fun _ => true
  weight := fun _ => 1
  positive := by decide
  target := 1

example : (List.finRange 2).map (fun j => BinaryNormalization.ofOccurrences (source j)) =
    original := by decide

example (β : Bool) :
    let ns := (List.finRange 2).map fun j => (source j).normalize 0 (by decide +revert)
    let hk : 1 + 1 = (cappedBasis ns).length := by decide
    selectedQuery 0 3
      ((List.finRange 2).map fun j => BinaryNormalization.ofOccurrences (source j)) β =
      (executableQuery (fun i : Fin 2 => selectedCappedRow ns (Fin.cast hk i)) β).relabel
        (flattenVar (n := 3)) := by
  exact selectedQuery_ofOccurrences source (by decide) (by decide) β

end WeightedBinaryQueryTests
