/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.BalancedRecovery

/-! # Balanced recovery numerator regression checks -/

namespace CslibFrontierTests.BalancedRecovery

open Cslib.Circuits Cslib.Circuits.Frontier.NativeRecovery

-- Four input factors are multiplied at depth two, in their original node order.
example : (basisProductFormula 1).depth = 2 := by
  norm_num [basisProductFormula, Formula.balanced, List.balancedFold, List.finRange,
    List.ofFn_succ, Formula.depth, Fin.univ_succ, Formula.gate₂, Formula.eval, arithInterpretation,
    arithInterpretationWith]
example : (basisProductFormula 1).eval (arithInterpretation ℕ) ![2, 3, 5, 7] = 210 := by
  norm_num [basisProductFormula, Formula.balanced, List.balancedFold, List.finRange,
    List.ofFn_succ, Formula.depth, Formula.gate₂, Formula.eval, arithInterpretation,
    arithInterpretationWith]
example : (basisProductFormula 1).eval (arithInterpretation ℕ) ![2, 3, 0, 7] = 0 := by
  norm_num [basisProductFormula, Formula.balanced, List.balancedFold, List.finRange,
    List.ofFn_succ, Formula.depth, Formula.gate₂, Formula.eval, arithInterpretation,
    arithInterpretationWith]

-- The two excluded nodes become multiplicative identities, rather than being renumbered.
example (N a u h k : ℕ) (fl : List ℕ) :
    basisFactor N fl a u h k (2 ^ a) = Cslib.GaloisRingArith.one fl := by
  simp [basisFactor]
example (N a u h k : ℕ) (fl : List ℕ) :
    basisFactor N fl a u h k k = Cslib.GaloisRingArith.one fl := by
  simp [basisFactor]

-- The smallest grid has two distinct excluded nodes, so its balanced value is the unit.
example (N u h : ℕ) (fl : List ℕ) :
    Cslib.GaloisRingArith.val N fl (balancedBasisNum N fl 0 u h 0) = 1 := by
  rw [val_balancedBasisNum]
  have he : others 0 0 = [] := by decide
  simp [basisNum, he, Cslib.GaloisRingArith.val_one]

end CslibFrontierTests.BalancedRecovery
