/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.FineGrained.CountingEncodings
public import CslibFrontier.Computability.Complexity.Problems.SharpTwoSAT
public import CslibFrontier.Foundations.Data.Polynomial.FiniteDifference

/-!
# Tests for counting CNF encodings, finite-difference interpolation, and `#2SAT` completeness

Kernel-checked strict-`module` examples (using no `native_decide` and no `import all`) exercising:

1. Univariate polynomial finite-difference zero-evaluation identity over `ℤ` (`degree ≤ 2`).
2. All six bounded-width CNF counting encodings:
   * Row 1: `Graph.toIndepSetCNF` on the 3-vertex path `0 — 1 — 2` (`5` independent sets,
     width `2`).
   * Row 2: `Graph.toColoringCNF 3` on `K₂` (`6` proper `3`-colourings, `6` variables, width `3`).
   * Row 3: `Graph.toPerfectMatchingCNF` exact width `3` on `C₄`, exact model counts on empty and
     isolated-vertex graphs, and concrete circuit evaluation on `C₄`'s two perfect matchings.
   * Row 4: `CSP.toOneHotCNF` / `CSP.toOneHotDeclaredCNF` on a concrete ternary inequality CSP
     over `Fin 3` (`6` solutions, `6` variables, width `≤ 3`).
   * Row 5: `SetSplittingInstance` with `k = 3` on `{0, 1, 2}` (`6` ordered splitting bipartitions,
     width `≤ 3`).
   * Row 6: `LocalMap.toDeclaredCNF` + `LocalMap.preimageDeclaredEquiv` on a 2-local map.
3. Valiant's `valiantTwoSAT` width-`2` gadget reduction recovering `#SAT = 7` on a `3`-clause via
   `2 * P(1) - P(2) = 2 * 8 - 9 = 7`, `SharpTwoSAT_countingTuringComplete`,
   `SharpTwoSAT_polyTime_implies_P_eq_NP`, and all six conditional runtime transfer endpoints.
-/

public section

namespace Cslib.Complexity.Tests.CountingReductions

open Cslib.Logic.PL Polynomial

/-! ### 1. Polynomial finite-difference identity at `0` -/

/-- Concrete quadratic `P(X) = 5 - 3 X + 2 X^2 ∈ ℤ[X]` has `P(0) = 5` recovered from
`P(1) = 4`, `P(2) = 7`, `P(3) = 14` via `3 * 4 - 3 * 7 + 1 * 14 = 5`. -/
example :
    let P : ℤ[X] := C 5 - C 3 * X + C 2 * X ^ 2
    P.eval 0 =
      ∑ j ∈ Finset.range 3,
        (-1 : ℤ) ^ j * (Nat.choose 3 (j + 1) : ℤ) * P.eval ((j + 1 : ℕ) : ℤ) := by
  intro P
  refine Polynomial.eval_zero_eq_sum_neg_one_pow_choose_eval_succ (n := 2) ?_
  dsimp only [P]
  compute_degree!

/-! ### 2. Row 1: Independent sets (`n = |V|`, width `2`) -/

/-- Path graph `0 — 1 — 2` has `5` independent sets (`∅, {0}, {1}, {2}, {0, 2}`). -/
def path3 : Graph := ([0, 1, 2], [(0, 1), (1, 2)])

example : path3.toIndepSetCNF.numVars = 3 := by decide

example : path3.toIndepSetCNF.all (fun c => decide (c.length = 2)) = true := by decide

example : path3.toIndepSetCNF.modelCount = 5 := by decide

example :
    Nat.card {S : Finset {v : ℕ // v ∈ path3.1} //
      path3.induced.IsIndepSet (S : Set {v : ℕ // v ∈ path3.1})} = 5 := by
  rw [← Graph.modelCount_toIndepSetCNF]
  decide

/-! ### 3. Row 2: Proper `q`-colourings (`n = q * |V|`, width `≤ max q 2`) -/

/-- Single edge `K₂` has `3 * 2 = 6` proper `3`-colourings on `6` Boolean variables. -/
def edgeGraph : Graph := ([0, 1], [(0, 1)])

example : (edgeGraph.toColoringCNF 3).numVars = 6 := by decide

example : (edgeGraph.toColoringCNF 3).all (fun c => decide (c.length ≤ 3)) = true := by decide

example : (edgeGraph.toColoringCNF 3).modelCount = 6 := by decide

example : Nat.card (edgeGraph.induced.Coloring (Fin 3)) = 6 := by
  rw [← Graph.modelCount_toColoringCNF]
  decide

/-! ### 4. Row 3: Perfect matchings via sequential `O(degree)` circuit (`width = 3`) -/

/-- Four-cycle `C₄` compiles to an exact `3`-CNF formula on linear wires. -/
def cycle4 : Graph := ([0, 1, 2, 3], [(0, 1), (1, 2), (2, 3), (3, 0)])

example : cycle4.toPerfectMatchingCNF.all (fun c => decide (c.length = 3)) = true := by decide

example :
    CNF.validDeclaredInput 3
      (cycle4.edgeList.length + cycle4.perfectMatchingCircuit.1.length)
      cycle4.toPerfectMatchingCNF = true :=
  Graph.validDeclaredInput_toPerfectMatchingCNF cycle4

/-- `C₄`'s sequential exact-one circuit accepts both opposite-edge matchings `[true, false, true,
false]` and `[false, true, false, true]` and rejects adjacent edges `[true, true, false, false]`. -/
example :
    Circuits.Boolean.evalOutput [true, false, true, false]
      cycle4.perfectMatchingCircuit.1 cycle4.perfectMatchingCircuit.2 = true := by
  decide

example :
    Circuits.Boolean.evalOutput [false, true, false, true]
      cycle4.perfectMatchingCircuit.1 cycle4.perfectMatchingCircuit.2 = true := by
  decide

example :
    Circuits.Boolean.evalOutput [true, true, false, false]
      cycle4.perfectMatchingCircuit.1 cycle4.perfectMatchingCircuit.2 = false := by
  decide

/-- Single isolated vertex `[0]` has `0` perfect matchings (`5` Tseitin wires, checked by
`decide`), while the empty graph `[]` has `1` perfect matching (`1` Tseitin wire). -/
def isolated1 : Graph := ([0], [])
def emptyGraph : Graph := ([], [])

example : Nat.card {M : isolated1.induced.Subgraph // M.IsPerfectMatching} = 0 := by
  rw [← Graph.modelCountOn_toPerfectMatchingCNF]
  decide

example : Nat.card {M : emptyGraph.induced.Subgraph // M.IsPerfectMatching} = 1 := by
  rw [← Graph.modelCountOn_toPerfectMatchingCNF]
  decide

/-! ### 5. Row 4: Fixed-arity finite-domain `#CSP` via one-hot encoding -/

/-- Concrete binary disequality relation over `Fin 3` on `2` variables (`3 * 2 = 6` solutions). -/
def neqSem3 (_ : Unit) (ts : List (Fin 3)) : Bool :=
  match ts with
  | [a, b] => decide (a ≠ b)
  | _ => false

def ternaryNeqCSP : CSP Unit ℕ := [((), [0, 1])]

example : (CSP.toOneHotCNF 3 2 ternaryNeqCSP neqSem3).numVars = 6 := by decide

example :
    (CSP.toOneHotCNF 3 2 ternaryNeqCSP neqSem3).all (fun c => decide (c.length ≤ 3)) = true := by
  decide

example : (CSP.toOneHotCNF 3 2 ternaryNeqCSP neqSem3).modelCount = 6 := by decide

example :
    (CSP.toOneHotDeclaredCNF 3 2 neqSem3 (2, ternaryNeqCSP)).2.modelCountOn (Finset.range 6) =
      6 := by
  decide

/-! ### 6. Row 5: Set splitting with subsets of size `≤ k` -/

/-- Ground `{0, 1, 2}` with single hyperedge `[0, 1, 2]` (`k = 3`) has `2^3 - 2 = 6` ordered
splitting bipartitions. -/
def split3 : SetSplittingInstance :=
  { ground := [0, 1, 2], sets := [[0, 1, 2]] }

example : split3.maxSetSizeBool 3 = true := by decide

example : (split3.toDeclaredCNF).1 = 3 := by decide

example : (split3.toDeclaredCNF).2.all (fun c => decide (c.length ≤ 3)) = true := by decide

example : (split3.toDeclaredCNF).2.modelCountOn (Finset.range 3) = 6 := by decide

example : split3.count = 6 := by
  have hv : split3.Valid := (split3.validBool_eq_true_iff).mp (by decide)
  rw [← SetSplittingInstance.modelCountOn_toDeclaredCNF hv]
  decide

/-! ### 7. Row 6: Constant-locality Boolean map preimage bijection -/

/-- `2`-local map `(x₀, x₁) ↦ [x₀ && x₁]` targeting `[false]` (`3` preimages out of `4`). -/
def andLocalMap : LocalMap :=
  (2, [([0, 1], [[true, true]])])

example : andLocalMap.Valid 2 = true := by decide

example :
    (LocalMap.toDeclaredCNF 2 (andLocalMap, [false])).2.modelCountOn (Finset.range 2) = 3 := by
  decide

noncomputable example :
    {σ : Finset.range 2 → Bool //
      (LocalMap.toDeclaredCNF 2 (andLocalMap, [false])).2.eval
        (fun v => if hv : v ∈ Finset.range 2 then σ ⟨v, hv⟩ else false) = true} ≃
      {σ : Finset.range 2 → Bool //
        andLocalMap.eval (fun v => if hv : v ∈ Finset.range 2 then σ ⟨v, hv⟩ else false) =
          [false]} :=
  LocalMap.preimageDeclaredEquiv (k := 2) (q := (andLocalMap, [false])) (by decide)

/-! ### 8. Valiant `#2SAT` `#P`-completeness and runtime transfer endpoints -/

/-- A concrete `3`-clause `(x₀ ∨ x₁ ∨ x₂)` compiles via `valiantTwoSAT` to pure width-`≤ 2`
formulas with `P(1) = SharpTwoSAT (valiantTwoSAT φ 0) = 8` and
`P(2) = SharpTwoSAT (valiantTwoSAT φ 1) = 9`, recovering `P(0) = 2 * 8 - 9 = 7 = φ.modelCount`. -/
def single3Clause : CNF ℕ := [[(0, true), (1, true), (2, true)]]

example : (valiantTwoSAT single3Clause 0).all (fun c => decide (c.length ≤ 2)) = true := by
  decide

example : (valiantTwoSAT single3Clause 1).all (fun c => decide (c.length ≤ 2)) = true := by
  decide

example : SharpTwoSAT (valiantTwoSAT single3Clause 0) = 8 := by decide

example : SharpTwoSAT (valiantTwoSAT single3Clause 1) = 9 := by decide

example :
    2 * SharpTwoSAT (valiantTwoSAT single3Clause 0) -
      SharpTwoSAT (valiantTwoSAT single3Clause 1) = single3Clause.modelCount := by
  decide

-- Strict `module`-boundary type checks of main completeness and runtime-transfer endpoints:
section EndpointChecks

example := @SharpTwoSAT_countingTuringComplete
example := @SharpTwoSAT_polyTime_implies_P_eq_NP
example := @CountingTransfer.declaredCounter_of_modelCounter
example := @CountingTransfer.transfer_declaredCounter
example := @CountingTransfer.exists_indepSetCounter_of_declaredCounter
example := @CountingTransfer.exists_coloringCounter_of_declaredCounter
example := @CountingTransfer.exists_perfectMatchingCounter_of_declaredCounter
example := @CountingTransfer.exists_oneHotCSPCounter_of_declaredCounter
example := @CountingTransfer.exists_setSplittingCounter_of_declaredCounter
example := @CountingTransfer.exists_localMapPreimageCounter_of_declaredCounter

end EndpointChecks

end Cslib.Complexity.Tests.CountingReductions
