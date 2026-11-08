/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.Randomized.DeutschJozsa

/-! Randomized Deutsch–Jozsa on `N = 4` positions: one random query is useless, two err with
probability `1/2` (de Wolf's remark), three err with probability `1/4 < 1/3`, against three
deterministic queries. -/

namespace ComplexityTests.RandomizedDeutschJozsa

open Cslib Cslib.QueryComplexity Cslib.BitString Finset

/-- The balanced input `0110`. -/
def x0110 : Fin 4 → Bool := ![false, true, true, false]

theorem isBalanced_x0110 : IsBalanced x0110 := by decide

-- One random query always answers "constant", so it is always wrong on a balanced input.
example (F : (Fin 4 → Bool) → Bool) (hF : SolvesDeutschJozsa F) :
    (randomDeutschJozsa 1).errorProb F x0110 = 1 := by
  rw [errorProb_randomDeutschJozsa_of_isBalanced (by norm_num) hF isBalanced_x0110]
  norm_num

-- Two random queries: error `1/2` on a balanced input.
example (F : (Fin 4 → Bool) → Bool) (hF : SolvesDeutschJozsa F) :
    (randomDeutschJozsa 2).errorProb F x0110 = 1 / 2 := by
  rw [errorProb_randomDeutschJozsa_of_isBalanced (by norm_num) hF isBalanced_x0110]
  norm_num

-- Three random queries: error `1/4` on a balanced input, and none on a constant input.
example (F : (Fin 4 → Bool) → Bool) (hF : SolvesDeutschJozsa F) :
    (randomDeutschJozsa 3).errorProb F x0110 = 1 / 4 := by
  rw [errorProb_randomDeutschJozsa_of_isBalanced (by norm_num) hF isBalanced_x0110]
  norm_num

example (F : (Fin 4 → Bool) → Bool) (hF : SolvesDeutschJozsa F) :
    (randomDeutschJozsa 3).errorProb F (fun _ => true) = 0 :=
  errorProb_randomDeutschJozsa_const 3 hF true

-- Three random queries with error at most `1/4` against three deterministic queries.
example : (randomDeutschJozsa (ι := Fin 4) 3).depth ≤ 3 ∧
    (∀ F : (Fin 4 → Bool) → Bool, SolvesDeutschJozsa F → ∀ x, (∃ c, x = fun _ => c) ∨
      IsBalanced x → (randomDeutschJozsa 3).errorProb F x ≤ 1 / 4) ∧
    ∀ F : (Fin 4 → Bool) → Bool, SolvesDeutschJozsa F → 3 ≤ DecisionTree.complexity F :=
  randomDeutschJozsa_separation (m := 2) (by simp)

-- The count behind the error: of the `4^3 = 64` position triples, `2 · 2^3 = 16` read equal bits
-- of `0110`.
example : #{l : Fin 3 → Fin 4 | (deutschJozsaTree (List.ofFn l)).eval x0110 = true} = 16 := by
  rw [card_filter_eval_deutschJozsaTree (by norm_num) isBalanced_x0110]
  decide

end ComplexityTests.RandomizedDeutschJozsa
