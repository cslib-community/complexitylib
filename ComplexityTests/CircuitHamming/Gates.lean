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

/-- The parities on `{0, 1}` and `{1, 2}` of three inputs differ on four of the eight inputs. -/
example : hammingDist (parityOn ({0, 1} : Finset (Fin 3))) (parityOn {1, 2}) = 4 := by
  have h : 2 * hammingDist (parityOn ({0, 1} : Finset (Fin 3))) (parityOn {1, 2}) =
      2 ^ Fintype.card (Fin 3) :=
    two_mul_hammingDist_parityOn (by decide)
  rw [Fintype.card_fin] at h
  omega

/-- The parity on the empty set is the constant `false`, at distance four from the parity of all
three inputs. -/
example : hammingDist (parityOn (∅ : Finset (Fin 3))) (parityOn Finset.univ) = 4 := by
  have h : 2 * hammingDist (parityOn (∅ : Finset (Fin 3))) (parityOn Finset.univ) =
      2 ^ Fintype.card (Fin 3) :=
    two_mul_hammingDist_parityOn (by decide)
  rw [Fintype.card_fin] at h
  omega

/-- Two projections on two inputs differ on two of the four inputs. -/
example : hammingDist y₀ y₁ = 2 := by
  have h : 2 * hammingDist y₀ y₁ = 2 ^ Fintype.card (Fin 2) :=
    two_mul_hammingDist_proj (by decide)
  rw [Fintype.card_fin] at h
  omega

/-- On three inputs, two projections differ on four of the eight inputs, and their relative
distance is one half. -/
example :
    hammingDist (fun x : BitString 3 => x 0) (fun x => x 2) = 4 ∧
    (hammingDist (fun x : BitString 3 => x 1) (fun x => x 2) : ℝ) / 2 ^ 3 = 1 / 2 := by
  refine ⟨?_, by
    simpa using hammingDist_proj_div (𝕜 := ℝ) (ι := Fin 3) (i := 1) (j := 2) (by decide)⟩
  have h : 2 * hammingDist (fun x : BitString 3 => x 0) (fun x => x 2) =
      2 ^ Fintype.card (Fin 3) :=
    two_mul_hammingDist_proj (by decide)
  rw [Fintype.card_fin] at h
  omega

/-! ### Conjunction and disjunction -/

/-- The sorting identity against the exclusive or (`3 + 1 = 2 + 2`), the conjunction/disjunction
geodesics between two projections, and the Lipschitz bound on disjunction. -/
example :
    hammingDist (fun x => y₀ x && y₁ x) yxor = 3 ∧
    hammingDist (fun x => y₀ x || y₁ x) yxor = 1 ∧
    hammingDist y₀ yxor = 2 ∧
    hammingDist y₁ yxor = 2 ∧
    hammingDist (fun x => y₀ x && y₁ x) yxor + hammingDist (fun x => y₀ x || y₁ x) yxor =
      hammingDist y₀ yxor + hammingDist y₁ yxor ∧
    hammingDist y₀ (fun x => y₀ x && y₁ x) = 1 ∧
    hammingDist (fun x => y₀ x && y₁ x) y₁ = 1 ∧
    hammingDist y₀ (fun x => y₀ x || y₁ x) + hammingDist (fun x => y₀ x || y₁ x) y₁ = 2 ∧
    hammingDist (fun x => y₀ x && (0 : BooleanFunction 2) x)
      (fun x => !y₀ x && (0 : BooleanFunction 2) x) = 0 ∧
    hammingDist y₀ (fun x => !y₀ x) = 4 ∧
    hammingDist (fun x => y₀ x || y₁ x) (fun x => yxor x || (0 : BooleanFunction 2) x) ≤
      hammingDist y₀ yxor + hammingDist y₁ (0 : BooleanFunction 2) :=
  ⟨by decide, by decide, by decide, by decide,
    hammingDist_and_add_hammingDist_or y₀ y₁ yxor,
    by decide, by decide,
    by rw [hammingDist_add_hammingDist_or]; decide,
    by decide, by decide,
    hammingDist_or_le y₀ yxor y₁ 0⟩

/-! ### Isometries -/

/-- Adding the exclusive or or negating both projections keeps their distance. -/
example :
    hammingDist (y₀ + yxor) (y₁ + yxor) = 2 ∧
    hammingDist (fun x => !y₀ x) (fun x => !y₁ x) = 2 :=
  ⟨by rw [hammingDist_add_right]; decide, by rw [hammingDist_not]; decide⟩

/-! ### The median -/

/-- The median of the three projections on three inputs is majority. -/
theorem median_proj : median (fun x : BitString 3 => x 0) (fun x => x 1) (fun x => x 2) =
    majority 3 := by
  funext x
  rw [median_apply_eq_majority]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Majority is between any two projections (`2 + 2 = 4`) and minimizes total distance to the
three projections (`6 ≤ 8`). -/
example :
    hammingDist (fun x : BitString 3 => x 0) (majority 3) = 2 ∧
    hammingDist (majority 3) (fun x : BitString 3 => x 1) = 2 ∧
    hammingDist (fun x : BitString 3 => x 0) (majority 3) +
      hammingDist (majority 3) (fun x : BitString 3 => x 1) = 4 ∧
    hammingDist (majority 3) (fun x : BitString 3 => x 0) +
      hammingDist (majority 3) (fun x : BitString 3 => x 1) +
      hammingDist (majority 3) (fun x : BitString 3 => x 2) = 6 ∧
    hammingDist (majority 3) (fun x : BitString 3 => x 0) +
      hammingDist (majority 3) (fun x : BitString 3 => x 1) +
      hammingDist (majority 3) (fun x : BitString 3 => x 2) ≤
        hammingDist (fun x : BitString 3 => x 0) (fun x : BitString 3 => x 0) +
        hammingDist (fun x : BitString 3 => x 0) (fun x : BitString 3 => x 1) +
        hammingDist (fun x : BitString 3 => x 0) (fun x : BitString 3 => x 2) :=
  ⟨by decide, by decide,
    by rw [← median_proj, hammingDist_add_hammingDist_median]; decide,
    by decide,
    by rw [← median_proj]; exact hammingDist_median_le _ _ _ _⟩

/-- The majority law, symmetry, associativity, and distributivity of `median`. -/
example :
    median y₀ y₀ y₁ = y₀ ∧
    median y₀ y₁ yxor = median yxor y₁ y₀ ∧
    median (median (fun x : BitString 3 => x 0) (majority 3) (fun x => x 1)) (majority 3)
        (fun x => x 2) =
      median (fun x => x 0) (majority 3) (median (fun x => x 1) (majority 3) (fun x => x 2)) ∧
    median (median y₀ y₁ yxor) (fun _ => true) y₀ =
      median (median y₀ (fun _ => true) y₀) (median y₁ (fun _ => true) y₀)
        (median yxor (fun _ => true) y₀) :=
  ⟨median_self_left y₀ y₁,
    by rw [median_swap_left, median_swap_right, median_swap_left],
    by decide,
    median_median_distrib _ _ _ _ _⟩

/-! ### Sharing -/

/-- Shifting majority on three inputs by each of its inputs: the shifts are pairwise half the cube
apart, cost together at most twelve gates more than majority, and lie at computational distance
between five and eight. -/
example :
    hammingDist (majority 3 + fun x => x 0) (majority 3 + fun x => x 1) = 4 ∧
    complexity interpretation (fun x o => majority 3 x + x o) ≤
      complexity interpretation (single (majority 3)) + 12 ∧
    circuitDist (majority 3 + fun x => x 0) (majority 3 + fun x => x 1) ≤ 8 ∧
    5 ≤ circuitDist (majority 3 + fun x => x 0) (majority 3 + fun x => x 1) ∧
    complexity interpretation (single (y₀ + y₁)) ≤
      complexity interpretation (single y₀) + 4 := by
  refine ⟨?_, complexity_add_projs_le (majority 3) id,
    by rw [circuitDist_add_proj]; exact circuitDist_proj_le 0 1,
    by rw [circuitDist_add_proj]; exact five_le_circuitDist_proj (by decide),
    complexity_add_proj_le y₀ 1⟩
  have h : 2 * hammingDist (majority 3 + fun x => x 0) (majority 3 + fun x => x 1) =
      2 ^ Fintype.card (Fin 3) :=
    two_mul_hammingDist_add_proj (majority 3) (by decide)
  rw [Fintype.card_fin] at h
  omega

/-! ### Boundary cases -/

/-- Boundary cases for zero shifts, self-distance of a projection, zero inputs, empty index types,
and coordinate flips. -/
example :
    complexity interpretation (fun (x : BitString 1) (o : Fin 0) =>
      (0 : BooleanFunction 1) x + x (Fin.elim0 o)) ≤
      complexity interpretation (single (0 : BooleanFunction 1)) ∧
    circuitDist (fun x : BitString 1 => x 0) (fun x => x 0) = 0 ∧
    circuitDist (fun x : BitString 1 => x 0) (fun x => x 0) ≤ 8 ∧
    hammingDist (fun _ : BitString 0 => true) (fun _ => false) = 1 ∧
    hammingDist (fun i : Empty => i.elim && i.elim) Empty.elim = 0 ∧
    median Empty.elim Empty.elim Empty.elim = Empty.elim ∧
    hammingDist (fun i : Fin 0 => (0 : Fin 0 → Bool) i && (0 : Fin 0 → Bool) i) 0 +
      hammingDist (fun i : Fin 0 => (0 : Fin 0 → Bool) i || (0 : Fin 0 → Bool) i) 0 =
      hammingDist (0 : Fin 0 → Bool) 0 + hammingDist (0 : Fin 0 → Bool) 0 ∧
    hammingDist (flipOn {0} ![true, false, false]) ![false, false, false] = 0 ∧
    hammingDist (flipOn {1} ![true, false, false]) ![false, false, false] = 2 := by
  refine ⟨complexity_add_projs_le (0 : BooleanFunction 1) Fin.elim0,
    circuitDist_self _, circuitDist_proj_le 0 0, by decide,
    hammingDist_eq_zero.2 (funext fun i => i.elim), funext fun i => i.elim,
    hammingDist_and_add_hammingDist_or 0 0 0, ?_⟩
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
