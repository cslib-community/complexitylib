/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.UniformSchedules
import Mathlib.Tactic.NormNum

public section

open Cslib.BalancedSchedules
open Finset
open scoped BigOperators

namespace Cslib.BalancedSchedules.Tests

-- Diagonal collision probability is 1, while distinct coordinates collide with probability 1 / |L|.
example :
    (𝔼 a : Bool → Bool, if a false = a false then (1 : ℚ) else 0) = 1 := by
  rw [expect_schedule_collision]
  simp

example :
    (𝔼 a : Bool → Bool, if a false = a true then (1 : ℚ) else 0) = 1 / 2 := by
  rw [expect_schedule_collision]
  norm_num

-- Expected potential of a 4-element source into Bool is 4 * (1 - 1 / 2) = 2.
example :
    (𝔼 a : Fin 4 → Bool, potential a) = 2 := by
  rw [expect_potential]
  norm_num

-- Expected group potential over Q = 2 steps, n = 4 variables, r = 2 groups is 4 ≤ 2 * 4 = 8.
example :
    (𝔼 a : Fin 4 → Bool → Bool, ∑ t : Bool, potential (fun v => a v t)) = 4 ∧
      (𝔼 a : Fin 4 → Bool → Bool, ∑ t : Bool, potential (fun v => a v t)) ≤ 8 := by
  refine ⟨?_, ?_⟩
  · rw [expect_group_potential]
    norm_num
  · exact (expect_group_potential_le (T := Bool) (V := Fin 4) (G := Bool)).trans (by norm_num)

-- Correlated incidences sharing a variable but having distinct factors collide with probability
-- 1 * (1 / |L|) rather than 1 / |L|^2.
example :
    (𝔼 a : Bool → Bool, 𝔼 d : Bool → Bool,
      if (a false, d false) = (a false, d true) then (1 : ℚ) else 0) = 1 / 2 := by
  rw [expect_incidence_collision]
  norm_num

-- Expected incidence potential bound on a 2-incidence system sharing one variable.
example :
    (𝔼 a : Unit → Bool, 𝔼 d : Bool → Bool,
      potential (incidenceLabel (A := Bool) (fun _ => ()) id a d)) ≤ 2 * (2 + 1) := by
  refine expect_incidence_potential_le (fun _ => ()) id (b := 2) (w := 1) ?_ ?_
  · decide
  · decide

-- Conditional expectation step: fixing one coordinate of a schedule does not increase the average.
example (f : (Bool → Bool) → ℚ) :
    ∃ x : Bool,
      (𝔼 a' : ({j : Bool // j ≠ false} → Bool), f ((Equiv.funSplitAt false Bool).symm (x, a'))) ≤
        𝔼 a : Bool → Bool, f a :=
  exists_coord_expect_le false f

-- Normalizing empty-scope factors assigns the default schedule to `none` without changing
-- any incidence label.
example (a : Bool → Unit → Bool) (d : Option Bool → Unit → Bool) :
    normalizeEmptyFactors (A := Bool) some false d none = (fun _ => false) ∧
      incidenceLabel id some a (normalizeEmptyFactors some false d) =
        incidenceLabel id some a d := by
  refine ⟨normalizeEmptyFactors_of_not_exists some false d ?_, ?_⟩
  · rintro ⟨e, ⟨⟩⟩
  · exact incidenceLabel_normalizeEmptyFactors id some false a d

-- Concrete scope family on V = Fin 64 and F = Option (Fin 64) with 64 singleton scopes and
-- one empty scope (`none`), satisfying the Lemma 4.5 size hypotheses (4.13) for T = Unit, G = Bool.
def testScope : Option (Fin 64) → Finset (Fin 64)
  | some v => {v}
  | none => ∅

theorem card_testScope : Fintype.card (ScopeIncidence testScope) = 64 := by
  rw [card_scopeIncidence, Fintype.sum_option]
  simp [testScope]

-- Nonvacuity of `exists_balanced_schedules_of_scopes` (Lemma 4.5):
-- produces schedules `a` and `d` with `d none = fun _ => false`, bounded incidence occupancy,
-- and bounded variable group sizes.
example :
    ∃ (a : Fin 64 → Unit → Bool) (d : Option (Fin 64) → Unit → Bool),
      (∀ f : Option (Fin 64), testScope f = ∅ → d f = fun _ => false) ∧
      (∀ u : (Unit → Bool) × (Unit → Bool),
        occupancy (incidenceLabel (scopeVarOf testScope) (scopeFactorOf testScope) a d) u *
          Fintype.card ((Unit → Bool) × (Unit → Bool)) ≤
            2 * Fintype.card (ScopeIncidence testScope)) ∧
      (∀ t : Unit, ∀ g : Bool,
        occupancy (fun v => a v t) g * Fintype.card Bool ≤ 2 * Fintype.card (Fin 64)) := by
  refine exists_balanced_schedules_of_scopes testScope (b := 1) (w := 1)
    ?_ ?_ (by omega) ?_ ?_ false
  · intro v
    have hsub :
        univ.filter (fun f : Option (Fin 64) => v ∈ testScope f) ⊆ {some v} := by
      rintro (_ | w) hf
      · rw [mem_filter] at hf
        exact False.elim (Finset.notMem_empty v hf.2)
      · rw [mem_filter] at hf
        have hvw : v = w := Finset.mem_singleton.1 hf.2
        subst hvw
        exact Finset.mem_singleton_self _
    exact (Finset.card_le_card hsub).trans (by simp)
  · rintro (_ | v) <;> simp [testScope]
  · rw [card_testScope]
    have hcard : Fintype.card ((Unit → Bool) × (Unit → Bool)) = 4 := by decide
    rw [hcard]
    omega
  · norm_num

end Cslib.BalancedSchedules.Tests
