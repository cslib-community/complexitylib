/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseIncidence

/-!
# Tests for the subset Möbius transform, the incidence expansion and the congruence (D.2)

Kernel-checked values of the subset Möbius transform, the incidence weight and the incidence sum,
and instances of the expansion, the per-factor degree bound preceding (D.1) and the exact recovery
of (D.2) on a two-equation system with one common zero.
-/

@[expose] public section

namespace Cslib.BitString.SparseIncidenceTests

open Finset Polynomial

/-! ### The subset Möbius transform -/

/-- `T ↦ #T ^ 2` has subset Möbius transform `0 - 1 - 1 + 4 = 2` at a two-element set: its
monomial coefficient at `{0, 1}` is `2`, as `(x₀ + x₁) ^ 2 = x₀ + x₁ + 2 x₀ x₁` on bits. -/
example : subsetMobius (fun T : Finset (Fin 2) => ((#T : ℤ)) ^ 2) univ = 2 := by
  decide

/-- At a singleton it is `1 - 0 = 1`. -/
example : subsetMobius (fun T : Finset (Fin 2) => ((#T : ℤ)) ^ 2) {0} = 1 := by
  decide

/-- Möbius inversion, instantiated. -/
example (f : Finset (Fin 3) → ℤ) (T : Finset (Fin 3)) :
    ∑ S ∈ T.powerset, subsetMobius f S = f T :=
  sum_powerset_subsetMobius f T

/-! ### The incidence weight and the incidence sum -/

/-- One chosen set `{0}` among three coordinates: coordinates `1` and `2` are free. -/
example : incidenceWeight (R := ℤ) (fun _ : Fin 1 => ({0} : Finset (Fin 3))) = 4 := by
  decide

/-- A local function `g x = 1 + 2 x₀ + 3 x₀ x₁` on two coordinates sums to `1 + 3 + 1 + 6 = 11`
over the cube, and so does its incidence expansion, by the kernel. -/
def g (x : Fin 2 → Bool) : ℤ :=
  1 + 2 * (if x 0 then 1 else 0) + 3 * (if x 0 && x 1 then 1 else 0)

example : ∑ x : Fin 2 → Bool, g x = 11 := by
  decide

example :
    incidenceSum (fun _ : Fin 1 => (univ : Finset (Fin 2)))
      (fun _ => subsetMobius fun T => g fun v => decide (v ∈ T)) 2 = 11 := by
  decide

/-- The same identity from the expansion theorem. -/
example :
    ∑ x : Fin 2 → Bool, ∏ _i : Fin 1, g x =
      incidenceSum (fun _ : Fin 1 => (univ : Finset (Fin 2)))
        (fun _ => subsetMobius fun T => g fun v => decide (v ∈ T)) 2 :=
  sum_prod_eq_incidenceSum _ (fun _ => g)
    (fun _ x y h => by simp only [g, h 0 (mem_univ _), h 1 (mem_univ _)]) (by decide)

/-- Truncating at `K = 1` drops the choice `{0, 1}`, whose coefficient is `3`: the weights of the
remaining choices `∅` and `{0}` give `1 · 4 + 2 · 2 = 8`. -/
example :
    incidenceSum (fun _ : Fin 1 => (univ : Finset (Fin 2)))
      (fun _ => subsetMobius fun T => g fun v => decide (v ∈ T)) 1 = 8 := by
  decide

/-! ### The congruence (D.2) on a small system -/

/-- `x₀ x₁ + 1 = 0`. -/
def testEq0 : Finset (Finset (Fin 2)) := {{0, 1}, ∅}

/-- `x₀ + x₁ = 0`. -/
def testEq1 : Finset (Finset (Fin 2)) := {{0}, {1}}

/-- The system `{testEq0, testEq1}`, whose only common zero is `(true, true)`. -/
def testSys : Fin 2 → Finset (Finset (Fin 2))
  | 0 => testEq0
  | 1 => testEq1

example : commonZeroCount (univ : Finset (Fin 2)) testSys = 1 := by
  decide

/-- The per-factor degree bound for `testEq1` (`k = 1`): the constant coefficient of its
incidence coefficient vanishes at the two-element set. -/
example (ℓ : ℕ) : (parityCoeff ℓ testEq1 univ).coeff 0 = 0 :=
  coeff_parityCoeff_eq_zero (k := 1) (by decide) (by decide)

/-- Exact recovery (D.2) for `testSys` at `ℓ = 3` with `k = 2` and `K = k (2 + 2 (ℓ - 1)) = 12`:
the coefficients below `V ^ 3` of the incidence sum add up, modulo `8`, to the single common
zero. -/
example :
    (∑ j ∈ range 3, (incidenceSum (fun i => equationScope (testSys i))
      (fun i => parityCoeff 3 (testSys i)) 12).coeff j) % 2 ^ 3 = 1 := by
  rw [emod_sum_eq_commonZeroCount_of_modEq testSys (fun _ => subset_rfl) (k := 2)
    (by decide) (by decide) (by decide) _ fun _ _ => Int.ModEq.refl _]
  decide

end Cslib.BitString.SparseIncidenceTests
