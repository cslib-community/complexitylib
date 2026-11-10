/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the negligible tactic)

public import CslibFrontier.Tactic.Negligible
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold

/-!
# Tests for `negligible`
-/

public section

open Cslib Cslib.Crypto Turing.MultiTapeTM
open scoped NNReal ENNReal

variable {ε δ : ℕ → ℝ≥0} {Q R : ℕ → ℕ}

/-! ### Direct `negligible` closure: dyadic, polynomial, birthday, shifts, square roots, sums -/

example : Negligible (fun n => ((2 : ℝ≥0) ^ n)⁻¹) := by
  negligible

example : Negligible (fun n => (1 : ℝ≥0) / 2 ^ n) := by
  negligible

example : Negligible (fun n => (1 : ℝ≥0) / 2 ^ (2 * n + 1)) := by
  negligible

example (hQ : PolynomiallyBounded Q) (hε : Negligible ε) :
    Negligible (fun n => (Q n : ℝ≥0) * ε n + ε n * (Q n + 3 : ℝ≥0)) := by
  negligible

example (hQ : PolynomiallyBounded Q) :
    Negligible (fun n => (Q n : ℝ≥0) ^ 2 / 2 ^ n + (Q n : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0) ^ n)) := by
  negligible

example (hQ : PolynomiallyBounded Q) :
    Negligible (fun n =>
      ((Q n).choose 2 : ℝ≥0) * ((2 : ℝ≥0) ^ n)⁻¹ + ((Q n).choose 2 : ℝ≥0) / 2 ^ n) := by
  negligible

example (hε : Negligible ε) :
    Negligible (fun n =>
      (5 : ℝ≥0) * ε (n + 1) + ε (1 + n) / 3 + ε (2 * n) + ε (n / 2)) := by
  negligible

example (hQ : PolynomiallyBounded Q) (hε : Negligible ε) :
    Negligible (fun n => NNReal.sqrt ((Q n + 1 : ℝ≥0) * ε n) + (3 / 4 : ℝ≥0) ^ n) := by
  negligible

example (hQ : PolynomiallyBounded Q) (hε : Negligible ε) :
    Negligible (fun n => ∑ _i ∈ Finset.range (Q n), ε n) := by
  negligible

/-! ### Local `let` definitions and unary `ComputableInPolyTime` certificates -/

example (c d : ℕ) (hε : Negligible ε) :
    let Q := fun n => c * (n + 2) ^ d
    Negligible (fun n => (Q n : ℝ≥0) ^ 2 / (2 * (2 : ℝ≥0) ^ n) + (Q n : ℝ≥0) * ε n) := by
  intro Q
  negligible

example (hQ : ComputableInPolyTime Q encUnary encUnary) (hε : Negligible ε) :
    Negligible (fun n => (2 * Q n : ℝ≥0) / 2 ^ n + (Q n : ℝ≥0) * ε n) := by
  negligible

/-! ### Pointwise upper bounds (`negligible using hle`) in `ℝ≥0` and `ℝ` -/

example {f : ℕ → ℝ≥0} (hQ : PolynomiallyBounded Q) (hε : Negligible ε)
    (hle : ∀ n, f n ≤ (Q n : ℝ≥0) * ε n + (1 : ℝ≥0) / 2 ^ n) :
    Negligible f := by
  negligible using hle

example {g₁ g₂ : ℕ → Game} (hQ : PolynomiallyBounded Q) (hε : Negligible ε)
    (hle : ∀ n, (Game.advantage (g₁ n) (g₂ n) : ℝ) ≤
      (Q n : ℝ) * (ε n : ℝ) + 1 / (2 : ℝ) ^ n) :
    Negligible (fun n => Game.advantage (g₁ n) (g₂ n)) := by
  negligible using hle

example {g : ℕ → Game} (hQ : PolynomiallyBounded Q) (hR : PolynomiallyBounded R)
    (hε : Negligible ε) (hδ : Negligible δ)
    (hle : ∀ n, (g n true).toReal ≤
      (Q n : ℝ) ^ 2 / (2 * (2 : ℝ) ^ n) + ((2 : ℝ) ^ n)⁻¹ +
        Real.sqrt (((R n + 1 : ℕ) : ℝ) * (ε n : ℝ)) + (δ n : ℝ)) :
    Negligible (fun n => Game.succProbability (g n)) := by
  negligible using hle

/-! ### Eventual upper bounds (`negligible eventually hle`) in `ℝ≥0` and `ℝ` -/

example {f : ℕ → ℝ≥0} (hQ : PolynomiallyBounded Q) (hε : Negligible ε)
    (hle : ∀ᶠ n in Filter.atTop, f n ≤ ((Q n).choose 2 : ℝ≥0) / 2 ^ n + ε n) :
    Negligible f := by
  negligible eventually hle

example {g₁ g₂ : ℕ → Game} (hQ : PolynomiallyBounded Q) (hε : Negligible ε)
    (hle : ∀ᶠ n in Filter.atTop, (Game.advantage (g₁ n) (g₂ n) : ℝ) ≤
      ((Q n : ℝ) ^ 2) / (2 * (2 : ℝ) ^ n) + ((2 : ℝ) ^ n)⁻¹ + (ε n : ℝ)) :
    Negligible (fun n => Game.advantage (g₁ n) (g₂ n)) := by
  negligible eventually (by
    filter_upwards [hle] with n hn
    exact hn)

/-! ### Sibling goals stay untouched -/

set_option linter.style.multiGoal false in
example : Negligible (fun n => ((2 : ℝ≥0) ^ n)⁻¹) ∧ Nonempty ℕ := by
  constructor
  negligible
  exact ⟨0⟩

/-! ### Negative controls and diagnostics -/

example : True := by
  fail_if_success have : Negligible (fun _ => (1 : ℝ≥0)) := by negligible
  fail_if_success have : Negligible (fun n => 1 / (n + 1 : ℝ≥0)) := by negligible
  trivial

/--
error: negligible: expected a goal `Cslib.Crypto.Negligible f`, got:
  1 ≤ 2
-/
#guard_msgs in
example : 1 ≤ 2 := by
  negligible

end
