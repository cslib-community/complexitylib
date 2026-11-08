/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.Simplex.KleeMinty
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.NormNum

/-!
# Worked examples for the Klee–Minty programs

These kernel-checked examples (using no `native_decide`) run the simplex method over `ℚ` on the
Klee–Minty programs `kleeMintyMatrix n`, `kleeMintyRhs n`, `kleeMintyObj n` of
`Complexity.Algorithms.Lean.Simplex.KleeMinty`:

1. For `n = 3` the program is `max 100x₁ + 10x₂ + x₃` subject to `x₁ ≤ 1`, `20x₁ + x₂ ≤ 100`,
   `200x₁ + 20x₂ + x₃ ≤ 10000`, `x ≥ 0`.
2. Dantzig's rule (`dantzigRun`) visits all `8` vertices for `n = 3`, with strictly increasing
   objective values `0, 100, 900, 1000, 9000, 9100, 9900, 10000`, and stops after `7` pivots; for
   `n = 4` it stops after `15` pivots. These are the cases `n = 3, 4` of the general theorem
   `dantzigRun_kleeMinty`, which is also instantiated at `n = 10`.
3. For contrast, Bland's rule (`run`, `simplex`) reaches the same optimum after `5` pivots for
   `n = 3` and `9` pivots for `n = 4`.
-/

public section

namespace ComplexityTests.Algorithms.Lean.KleeMinty

open Cslib.Algorithms.Lean.Simplex Dictionary Matrix Finset

/-- The slack dictionary of the `n`-dimensional Klee–Minty program over `ℚ`. -/
def km (n : ℕ) : Dictionary (Fin (n + n)) ℚ :=
  slackDictionary (kleeMintyMatrix n) (kleeMintyRhs n) (kleeMintyObj n)

/-- Whether a run stopped at an optimal dictionary, with the basis and objective value of the
dictionary it returned. -/
def endpoint {ι K : Type*} : Outcome ι K → Bool × Finset ι × K
  | .optimal D => (true, D.basis, D.objConst)
  | .unbounded D _ => (false, D.basis, D.objConst)
  | .outOfFuel D => (false, D.basis, D.objConst)

/-! ### 1. The program for `n = 3` -/

/-- The three-dimensional Klee–Minty program. -/
example : kleeMintyMatrix 3 = !![(1 : ℚ), 0, 0; 20, 1, 0; 200, 20, 1] ∧
    kleeMintyRhs 3 = ![(1 : ℚ), 100, 10000] ∧ kleeMintyObj 3 = ![(100 : ℚ), 10, 1] := by
  decide +kernel

/-! ### 2. Dantzig's rule -/

/-- Dantzig's rule on the three-dimensional program: after `f ≤ 7` pivots the run is at the
`f`-th vertex (variables `x₁, x₂, x₃, w₁, w₂, w₃` are `0, …, 5`), it visits all `8` vertices
with strictly increasing objective values, and it stops at the optimum `10000` after exactly `7`
pivots. -/
example : (List.range 8).map (fun f => endpoint ((km 3).dantzigRun f)) =
    [(false, {3, 4, 5}, 0), (false, {0, 4, 5}, 100), (false, {0, 1, 5}, 900),
      (false, {1, 3, 5}, 1000), (false, {1, 2, 3}, 9000), (false, {0, 1, 2}, 9100),
      (false, {0, 2, 4}, 9900), (true, {2, 3, 4}, 10000)] := by
  decide +kernel

/-- Dantzig's rule on the four-dimensional program stops after exactly `15` pivots, at the
optimum `100 ^ 3`. -/
example : endpoint ((km 4).dantzigRun 14) = (false, {0, 3, 5, 6}, 999000) ∧
    endpoint ((km 4).dantzigRun 15) = (true, {3, 4, 5, 6}, 1000000) := by
  decide +kernel

/-- The general theorem for `n = 10`: Dantzig's rule makes `1023` pivots. -/
example (f : ℕ) : (∃ D, (km 10).dantzigRun f = .outOfFuel D) ↔ f < 1023 :=
  exists_dantzigRun_kleeMinty_eq_outOfFuel_iff 10 f

/-- The optimum of the three-dimensional program is `100 ^ 2`. -/
example : IsGreatest ((kleeMintyObj 3 ⬝ᵥ ·) ''
    {x | 0 ≤ x ∧ kleeMintyMatrix 3 *ᵥ x ≤ kleeMintyRhs 3}) (10000 : ℚ) := by
  have := isGreatest_kleeMinty (K := ℚ) 2
  norm_num at this
  exact this

/-! ### 3. Bland's rule on the same programs -/

/-- Bland's rule on the three-dimensional program skips three of the vertices visited by
Dantzig's rule and stops after `5` pivots. -/
example : (List.range 6).map (fun f => endpoint ((km 3).run f)) =
    [(false, {3, 4, 5}, 0), (false, {0, 4, 5}, 100), (false, {0, 1, 5}, 900),
      (false, {0, 1, 2}, 9100), (false, {0, 2, 4}, 9900), (true, {2, 3, 4}, 10000)] := by
  decide +kernel

/-- Bland's rule on the four-dimensional program stops after `9` pivots. -/
example : endpoint ((km 4).run 8) = (false, {0, 3, 5, 6}, 999000) ∧
    endpoint ((km 4).run 9) = (true, {3, 4, 5, 6}, 1000000) ∧
    endpoint (km 4).simplex = (true, {3, 4, 5, 6}, 1000000) := by
  decide +kernel

end ComplexityTests.Algorithms.Lean.KleeMinty
