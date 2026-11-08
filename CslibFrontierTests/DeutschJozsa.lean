/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.QueryComplexity.DeutschJozsa

/-! The deterministic query complexity of Deutsch–Jozsa on small instances: `N = 2` (Deutsch's
problem, two queries), `N = 4` (three queries), the tightness of the bound, and the degenerate case
`N = 0`. -/

namespace CslibFrontierTests.DeutschJozsa

open Cslib Cslib.QueryComplexity Cslib.BitString

/-! ### Balanced inputs -/

example : IsBalanced (![false, true] : Fin 2 → Bool) := by decide
example : IsBalanced (![true, false, false, true] : Fin 4 → Bool) := by decide
example : ¬ IsBalanced (![true, false, false, false] : Fin 4 → Bool) := by decide
example : ¬ IsBalanced (fun _ => true : Fin 4 → Bool) := by decide
-- A balanced input needs an even number of positions.
example : ¬ IsBalanced (![true, false, false] : Fin 3 → Bool) := by decide

/-! ### `N = 2`: Deutsch's problem needs both queries -/

-- Every deterministic tree solving Deutsch's problem queries both bits.
example (t : DecisionTree (Fin 2) Bool) (ht : SolvesDeutschJozsa t.eval) : 2 ≤ t.depth :=
  depth_ge_of_solvesDeutschJozsa (m := 1) (by simp) t ht

-- Two queries suffice: comparing the two bits.
example : SolvesDeutschJozsa (deutschJozsaTree [(0 : Fin 2), 1]).eval :=
  deutschJozsaTree_solves (m := 1) (by simp) (by decide) (by simp)

example : IsLeast {d | ∃ F : (Fin 2 → Bool) → Bool, SolvesDeutschJozsa F ∧
    DecisionTree.complexity F = d} 2 :=
  isLeast_complexity_solvesDeutschJozsa (m := 1) (by simp) (by norm_num)

/-! ### `N = 4`: three queries are necessary and sufficient -/

example (F : (Fin 4 → Bool) → Bool) (hF : SolvesDeutschJozsa F) : 3 ≤ DecisionTree.complexity F :=
  complexity_ge_of_solvesDeutschJozsa (m := 2) (by simp) hF

example : SolvesDeutschJozsa (deutschJozsaTree [(0 : Fin 4), 1, 2]).eval :=
  deutschJozsaTree_solves (m := 2) (by simp) (by decide) (by simp)

theorem depth_deutschJozsaTree_three : (deutschJozsaTree [(0 : Fin 4), 1, 2]).depth ≤ 3 :=
  depth_deutschJozsaTree_le _

example : IsLeast {d | ∃ F : (Fin 4 → Bool) → Bool, SolvesDeutschJozsa F ∧
    DecisionTree.complexity F = d} 3 :=
  isLeast_complexity_solvesDeutschJozsa (m := 2) (by simp) (by norm_num)

-- Tightness: two queries are not enough. Comparing positions `0` and `1` answers "constant" on the
-- balanced input `0011`.
example : ¬ SolvesDeutschJozsa (deutschJozsaTree [(0 : Fin 4), 1]).eval := by
  intro h
  have hbal : IsBalanced (![false, false, true, true] : Fin 4 → Bool) := by decide
  have := h.balanced _ hbal
  rw [eval_deutschJozsaTree] at this
  revert this
  decide

/-! ### `N = 0`: the promise is contradictory -/

-- With no positions, the only input is both constant and balanced, so no function solves the
-- problem; this is why `isLeast_complexity_solvesDeutschJozsa` assumes `m ≥ 1`.
example (F : (Fin 0 → Bool) → Bool) : ¬ SolvesDeutschJozsa F := by
  intro h
  have h₁ := h.const false
  have h₂ := h.balanced (fun _ => false) (by decide)
  rw [h₁] at h₂
  exact Bool.true_eq_false.mp h₂ |>.elim

end CslibFrontierTests.DeutschJozsa
