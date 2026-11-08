/-
Copyright (c) 2026 Vincent Palma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Algebraic.CNF
public import Mathlib.Data.ZMod.Basic

/-!
# Boolean assignments and clause polynomials

These examples check both literal polarities, a satisfied and a falsified clause over a ring
with zero divisors, the empty clause, and the need for complementary coordinates in a CNF.
-/

public section

namespace Cslib.Logic.PL

open MvPolynomial

/-- Positive literals contribute negative polynomial variables, and conversely. -/
example : Clause.toPoly [((), true)] ℕ = X ((), false) ∧
    Clause.toPoly [((), false)] ℕ = X ((), true) := by
  simp [Std.Sat.Literal.negate]

local instance : Fact (1 < 6) := ⟨by decide⟩

/-- The clause `x ∨ ¬y` evaluates to `0` when satisfied and `1` when falsified, even with
zero divisors in the coefficient ring. -/
example :
    (Clause.toPoly [(true, true), (false, false)] (ZMod 6)).eval
      (Literal.toPolyAssignment (ZMod 6) id) = 0 ∧
    (Clause.toPoly [(true, true), (false, false)] (ZMod 6)).eval
      (Literal.toPolyAssignment (ZMod 6) Bool.not) = 1 := by
  simp only [Clause.eval_toPoly]
  simp [Clause.eval, Literal.eval]

/-- The empty clause is false and its constant polynomial cannot vanish. -/
example : ∀ σ : Unit → Bool,
    (Clause.toPoly [] ℕ).eval (Literal.toPolyAssignment ℕ σ) = 1 := by
  simp

/-- Unconstrained literal coordinates give a spurious solution to contradictory unit clauses;
the coordinates coming from any Boolean assignment cannot solve both equations. -/
example :
    (∀ c ∈ ([[((), true)], [((), false)]] : CNF Unit),
      (c.toPoly (ZMod 6)).eval (fun _ => 0) = 0) ∧
    ¬∃ σ : Unit → Bool, ∀ c ∈ ([[((), true)], [((), false)]] : CNF Unit),
      (c.toPoly (ZMod 6)).eval (Literal.toPolyAssignment (ZMod 6) σ) = 0 := by
  constructor
  · simp [Clause.toPoly, Std.Sat.Literal.negate]
  · rintro ⟨σ, hσ⟩
    have h := (CNF.eval_eq_true_iff_forall_eval_toPoly_eq_zero (R := ZMod 6) _ σ).mpr hσ
    simp [CNF.eval, Clause.eval, Literal.eval] at h

end Cslib.Logic.PL
