/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Hamming
import Complexity.Foundations.Data.BitString.Hamming
import Mathlib.Tactic.FinCases

/-! The Hamming geometry of gates on the truth tables of two and three inputs: the sorting
identity, geodesics, Lipschitz and isometry statements, the median of the three projections as
majority, and the sharing example `g_i = f + x_i` with exact distances and costs, together with
the boundary cases of zero inputs and an empty index type. Exact distances are checked both from
the general theorems and by evaluation. -/

namespace ComplexityTests.CircuitHamming.Gates

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean

/-- The first input of two. -/
private abbrev y₀ : BooleanFunction 2 := fun x => x 0

/-- The second input of two. -/
private abbrev y₁ : BooleanFunction 2 := fun x => x 1

/-- Their exclusive or. -/
private abbrev yxor : BooleanFunction 2 := fun x => x 0 ^^ x 1

/-! ### Parities and projections -/

/-- The parities on `{0, 1}` and `{1, 2}` of three inputs differ on four of the eight inputs, by
the general theorem and by evaluation. -/
example : hammingDist (parityOn ({0, 1} : Finset (Fin 3))) (parityOn {1, 2}) = 4 := by
  have h : 2 * hammingDist (parityOn ({0, 1} : Finset (Fin 3))) (parityOn {1, 2}) =
      2 ^ Fintype.card (Fin 3) :=
    two_mul_hammingDist_parityOn (by decide)
  rw [Fintype.card_fin] at h
  omega

example : hammingDist (parityOn ({0, 1} : Finset (Fin 3))) (parityOn {1, 2}) = 4 := by decide

/-- The parity on the empty set is the constant `false`, at distance four from the parity of all
three inputs. -/
example : hammingDist (parityOn (∅ : Finset (Fin 3))) (parityOn Finset.univ) = 4 := by
  have h : 2 * hammingDist (parityOn (∅ : Finset (Fin 3))) (parityOn Finset.univ) =
      2 ^ Fintype.card (Fin 3) :=
    two_mul_hammingDist_parityOn (by decide)
  rw [Fintype.card_fin] at h
  omega

/-- Two projections on two inputs differ on two of the four inputs, by the general theorem and by
evaluation. -/
example : hammingDist y₀ y₁ = 2 := by
  have h : 2 * hammingDist y₀ y₁ = 2 ^ Fintype.card (Fin 2) :=
    two_mul_hammingDist_proj (by decide)
  rw [Fintype.card_fin] at h
  omega

example : hammingDist y₀ y₁ = 2 := by decide

/-- On three inputs, two projections differ on four of the eight inputs. -/
example : hammingDist (fun x : BitString 3 => x 0) (fun x => x 2) = 4 := by
  have h : 2 * hammingDist (fun x : BitString 3 => x 0) (fun x => x 2) =
      2 ^ Fintype.card (Fin 3) :=
    two_mul_hammingDist_proj (by decide)
  rw [Fintype.card_fin] at h
  omega

example : hammingDist (fun x : BitString 3 => x 0) (fun x => x 2) = 4 := by decide

/-- The relative distance between two projections is one half. -/
example : (hammingDist (fun x : BitString 3 => x 1) (fun x => x 2) : ℝ) / 2 ^ 3 = 1 / 2 := by
  simpa using hammingDist_proj_div (𝕜 := ℝ) (ι := Fin 3) (i := 1) (j := 2) (by decide)

/-! ### Conjunction and disjunction -/

/-- The sorting identity against the exclusive or: `3 + 1 = 2 + 2`. -/
example : hammingDist (fun x => y₀ x && y₁ x) yxor = 3 ∧
    hammingDist (fun x => y₀ x || y₁ x) yxor = 1 ∧
    hammingDist y₀ yxor = 2 ∧ hammingDist y₁ yxor = 2 := by
  decide

example : hammingDist (fun x => y₀ x && y₁ x) yxor + hammingDist (fun x => y₀ x || y₁ x) yxor =
    hammingDist y₀ yxor + hammingDist y₁ yxor :=
  hammingDist_and_add_hammingDist_or y₀ y₁ yxor

/-- The conjunction of two projections is halfway between them. -/
example : hammingDist y₀ (fun x => y₀ x && y₁ x) = 1 ∧
    hammingDist (fun x => y₀ x && y₁ x) y₁ = 1 := by
  decide

example : hammingDist y₀ (fun x => y₀ x || y₁ x) + hammingDist (fun x => y₀ x || y₁ x) y₁ = 2 := by
  rw [hammingDist_add_hammingDist_or]
  decide

/-- The Lipschitz bound can be strict: conjunction with `0` erases a distance of four. -/
example : hammingDist (fun x => y₀ x && (0 : BooleanFunction 2) x)
      (fun x => !y₀ x && (0 : BooleanFunction 2) x) = 0 ∧
    hammingDist y₀ (fun x => !y₀ x) = 4 := by
  decide

example (f f' g g' : BooleanFunction 3) :
    hammingDist (fun x => f x || g x) (fun x => f' x || g' x) ≤
      hammingDist f f' + hammingDist g g' :=
  hammingDist_or_le f f' g g'

/-! ### Isometries -/

/-- Adding the exclusive or to both projections keeps their distance. -/
example : hammingDist (y₀ + yxor) (y₁ + yxor) = 2 := by
  rw [hammingDist_add_right]
  decide

example : hammingDist (fun x => !y₀ x) (fun x => !y₁ x) = 2 := by
  rw [hammingDist_not]
  decide

/-! ### The median -/

/-- The median of the three projections on three inputs is majority. -/
theorem median_proj : median (fun x : BitString 3 => x 0) (fun x => x 1) (fun x => x 2) =
    majority 3 := by
  funext x
  rw [median_apply_eq_majority]
  congr 1
  funext i
  fin_cases i <;> rfl

example : median (fun x : BitString 3 => x 0) (fun x => x 1) (fun x => x 2) = majority 3 := by
  decide

/-- Majority is between any two projections: `2 + 2 = 4`. -/
example : hammingDist (fun x : BitString 3 => x 0) (majority 3) = 2 ∧
    hammingDist (majority 3) (fun x : BitString 3 => x 1) = 2 := by
  decide

example : hammingDist (fun x : BitString 3 => x 0) (majority 3) +
    hammingDist (majority 3) (fun x : BitString 3 => x 1) = 4 := by
  rw [← median_proj, hammingDist_add_hammingDist_median]
  decide

/-- Majority has total distance six to the three projections, a projection eight. -/
example : hammingDist (majority 3) (fun x : BitString 3 => x 0) +
    hammingDist (majority 3) (fun x : BitString 3 => x 1) +
    hammingDist (majority 3) (fun x : BitString 3 => x 2) = 6 := by
  decide

example : hammingDist (majority 3) (fun x : BitString 3 => x 0) +
    hammingDist (majority 3) (fun x : BitString 3 => x 1) +
    hammingDist (majority 3) (fun x : BitString 3 => x 2) ≤
      hammingDist (fun x : BitString 3 => x 0) (fun x : BitString 3 => x 0) +
      hammingDist (fun x : BitString 3 => x 0) (fun x : BitString 3 => x 1) +
      hammingDist (fun x : BitString 3 => x 0) (fun x : BitString 3 => x 2) := by
  rw [← median_proj]
  exact hammingDist_median_le _ _ _ _

/-- The majority law and symmetry. -/
example : median y₀ y₀ y₁ = y₀ := median_self_left y₀ y₁

example : median y₀ y₁ yxor = median yxor y₁ y₀ := by
  rw [median_swap_left, median_swap_right, median_swap_left]

/-- The associative and distributive laws, checked by evaluation on three inputs. -/
example : median (median (fun x : BitString 3 => x 0) (majority 3) (fun x => x 1)) (majority 3)
      (fun x => x 2) =
    median (fun x => x 0) (majority 3) (median (fun x => x 1) (majority 3) (fun x => x 2)) := by
  decide

example : median (median y₀ y₁ yxor) (fun _ => true) y₀ =
    median (median y₀ (fun _ => true) y₀) (median y₁ (fun _ => true) y₀)
      (median yxor (fun _ => true) y₀) :=
  median_median_distrib _ _ _ _ _

/-! ### Sharing -/

/-- The shifts of two projections by any `f` differ on half of the inputs. -/
example {n : ℕ} (f : BooleanFunction n) {i j : Fin n} (hij : i ≠ j) :
    2 * hammingDist (f + fun x => x i) (f + fun x => x j) = 2 ^ n := by
  simpa using two_mul_hammingDist_add_proj f hij

/-- Shifting majority on three inputs by each of its inputs: the three shifts are pairwise half
the cube apart, cost together at most twelve gates more than majority, and are at computational
distance at most eight. -/
example : hammingDist (majority 3 + fun x => x 0) (majority 3 + fun x => x 1) = 4 := by
  have h : 2 * hammingDist (majority 3 + fun x => x 0) (majority 3 + fun x => x 1) =
      2 ^ Fintype.card (Fin 3) :=
    two_mul_hammingDist_add_proj (majority 3) (by decide)
  rw [Fintype.card_fin] at h
  omega

example : hammingDist (majority 3 + fun x => x 0) (majority 3 + fun x => x 1) = 4 := by decide

example : complexity interpretation (fun x o => majority 3 x + x o) ≤
    complexity interpretation (single (majority 3)) + 12 :=
  complexity_add_projs_le (majority 3) id

example : circuitDist (majority 3 + fun x => x 0) (majority 3 + fun x => x 1) ≤ 8 := by
  rw [circuitDist_add_proj]
  exact circuitDist_proj_le 0 1

example : 5 ≤ circuitDist (majority 3 + fun x => x 0) (majority 3 + fun x => x 1) := by
  rw [circuitDist_add_proj]
  exact five_le_circuitDist_proj (by decide)

example (f : BooleanFunction 2) :
    complexity interpretation (single (f + y₁)) ≤ complexity interpretation (single f) + 4 :=
  complexity_add_proj_le f 1

/-! ### Boundary cases -/

/-- No shifts cost nothing beyond `f`. -/
example {n : ℕ} (f : BooleanFunction n) (i : Fin 0 → Fin n) :
    complexity interpretation (fun x o => f x + x (i o)) ≤ complexity interpretation (single f) :=
  complexity_add_projs_le f i

/-- A projection is at computational distance zero from itself, within the bound for equal
indices. -/
example : circuitDist (fun x : BitString 1 => x 0) (fun x => x 0) = 0 := circuitDist_self _

example : circuitDist (fun x : BitString 1 => x 0) (fun x => x 0) ≤ 8 := circuitDist_proj_le 0 0

/-- With zero inputs the cube of truth tables has two points, at distance one. -/
example : hammingDist (fun _ : BitString 0 => true) (fun _ => false) = 1 := by decide

/-- Over an empty index type all points coincide. -/
example (f g h : Empty → Bool) : hammingDist (fun i => f i && g i) h = 0 ∧ median f g h = f :=
  ⟨hammingDist_eq_zero.2 (funext fun i => i.elim), funext fun i => i.elim⟩

example (f g h : Fin 0 → Bool) :
    hammingDist (fun i => f i && g i) h + hammingDist (fun i => f i || g i) h =
      hammingDist f h + hammingDist g h :=
  hammingDist_and_add_hammingDist_or f g h

/-- Flipping a disagreeing coordinate (`i = 0`) decreases the Hamming distance by one; flipping an
agreeing coordinate (`i = 1`) increases it by one. -/
example :
    hammingDist (flipOn {0} ![true, false, false]) ![false, false, false] = 0 ∧
      hammingDist (flipOn {1} ![true, false, false]) ![false, false, false] = 2 := by
  rw [hammingDist_flip, hammingDist_flip]
  decide

/-! ### Axioms -/

/--
info: 'Cslib.BitString.median_assoc' depends on axioms:
[Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms median_assoc

/--
info: 'Cslib.BitString.median_median_distrib' depends on axioms:
[Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms median_median_distrib

end ComplexityTests.CircuitHamming.Gates
