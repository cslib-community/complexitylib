/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Flip
public import Complexity.Foundations.Data.BitString.Threshold
public import Complexity.Foundations.Data.BitString.Parity
import Complexity.Foundations.Data.Hamming

/-!
# The Hamming geometry of the Boolean cube

Points of the cube `ι → Bool` are compared by Mathlib's Hamming distance, the number of
coordinates where they differ. The Boolean operations act on points coordinatewise, and their
geometry is exact. For `f g h : ι → Bool` on a finite set `ι`:

* conjunction and disjunction sort a pair coordinatewise, so the distances from `f ∧ g` and
  `f ∨ g` to any `h` add up to those from `f` and `g`
  (`Cslib.BitString.hammingDist_and_add_hammingDist_or`);
* `f ∧ g` and `f ∨ g` lie on geodesics from `f` to `g`
  (`Cslib.BitString.hammingDist_add_hammingDist_and`,
  `Cslib.BitString.hammingDist_add_hammingDist_or`), and both are `1`-Lipschitz in each argument;
* adding a fixed point, which is the coordinatewise exclusive or, and negation are isometries
  (`Cslib.BitString.hammingDist_add_right`, `Cslib.BitString.hammingDist_not`);
* the cube is a median algebra for the coordinatewise majority
  `m(f,g,h) = (f ∧ g) ∨ (g ∧ h) ∨ (h ∧ f)` (`Cslib.BitString.median`), the lattice median of the
  distributive lattice `ι → Bool`: it satisfies the majority law, symmetry and the associative law,
  and it distributes over itself. The median lies between any two of its arguments and minimizes
  the total distance to the three of them.

The truth tables of Boolean functions are points of the cube `(ι → Bool) → Bool`. The parities on
two distinct sets `S` and `T` disagree exactly where the parity on the symmetric difference
`S ∆ T` is true, which happens on half of the inputs, so they differ on exactly half of the inputs
(`Cslib.BitString.two_mul_hammingDist_parityOn`). Two distinct coordinate projections `x ↦ x i`
and `x ↦ x j` are the parities on `{i}` and `{j}`, so they differ on exactly half of the inputs
(`Cslib.BitString.two_mul_hammingDist_proj`), and so do their shifts `f + x_i` and `f + x_j` by
any common function `f` (`Cslib.BitString.two_mul_hammingDist_add_proj`), however complicated `f`
is.

## Main definitions

* `Cslib.BitString.median`: the coordinatewise majority of three points.

## Main results

* `Cslib.BitString.hammingDist_and_add_hammingDist_or`: conjunction and disjunction sort.
* `Cslib.BitString.hammingDist_add_hammingDist_and`,
  `Cslib.BitString.hammingDist_add_hammingDist_or`: geodesics.
* `Cslib.BitString.hammingDist_and_le`, `Cslib.BitString.hammingDist_or_le`: Lipschitz gates.
* `Cslib.BitString.hammingDist_add_right`, `Cslib.BitString.hammingDist_add_left`,
  `Cslib.BitString.hammingDist_not`: isometries.
* `Cslib.BitString.median_self_left`, `Cslib.BitString.median_swap_left`,
  `Cslib.BitString.median_swap_right`, `Cslib.BitString.median_assoc`: the median algebra laws.
* `Cslib.BitString.median_median_distrib`: distributivity.
* `Cslib.BitString.hammingDist_add_hammingDist_median`, `Cslib.BitString.hammingDist_median_le`:
  betweenness and minimality of the median.
* `Cslib.BitString.two_mul_hammingDist_parityOn`: distinct parities are half the cube apart.
* `Cslib.BitString.two_mul_hammingDist_proj`, `Cslib.BitString.hammingDist_proj_div`,
  `Cslib.BitString.two_mul_hammingDist_add_proj`: projections and their shifts are half the cube
  apart.
* `Cslib.BitString.hammingDist_flip_self`, `Cslib.BitString.hammingDist_le_flip_add_one`,
  `Cslib.BitString.hammingDist_flip_le_add_one`, `Cslib.BitString.hammingDist_flip_eq_add_one`,
  `Cslib.BitString.hammingDist_flip`: effect of flipping one coordinate on Hamming distance.

## References

* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable {ι : Type*}

/-! ### The median -/

/-- The median of three points: their coordinatewise majority `(f ∧ g) ∨ (g ∧ h) ∨ (h ∧ f)`.
This is the lattice median `(f ⊓ g) ⊔ (g ⊓ h) ⊔ (h ⊓ f)` of the distributive lattice
`ι → Bool`. -/
def median (f g h : ι → Bool) : ι → Bool :=
  fun i => f i && g i || g i && h i || h i && f i

/-- The median is the majority of three bits at each coordinate. -/
theorem median_apply_eq_majority (f g h : ι → Bool) (i : ι) :
    median f g h i = majority 3 ![f i, g i, h i] := by
  simp only [median]
  cases f i <;> cases g i <;> cases h i <;> decide

/-- **The majority law**: a point repeated twice is the median. -/
@[simp] theorem median_self_left (f g : ι → Bool) : median f f g = f := by
  funext i
  simp only [median]
  cases f i <;> cases g i <;> rfl

/-- The median is symmetric in its first two arguments. -/
theorem median_swap_left (f g h : ι → Bool) : median f g h = median g f h := by
  funext i
  simp only [median]
  cases f i <;> cases g i <;> cases h i <;> rfl

/-- The median is symmetric in its last two arguments. -/
theorem median_swap_right (f g h : ι → Bool) : median f g h = median f h g := by
  funext i
  simp only [median]
  cases f i <;> cases g i <;> cases h i <;> rfl

/-- **The associative law** of median algebras. Together with the majority law and symmetry it
makes the cube a median algebra. -/
theorem median_assoc (f g h k : ι → Bool) :
    median (median f k g) k h = median f k (median g k h) := by
  funext i
  simp only [median]
  cases f i <;> cases g i <;> cases h i <;> cases k i <;> rfl

/-- **The median distributes over itself.** -/
theorem median_median_distrib (f g h k l : ι → Bool) :
    median (median f g h) k l = median (median f k l) (median g k l) (median h k l) := by
  funext i
  simp only [median]
  cases f i <;> cases g i <;> cases h i <;> cases k i <;> cases l i <;> rfl

section Fintype

variable [Fintype ι]

/-- The Hamming distance counts the coordinates of disagreement. -/
private theorem hammingDist_eq_sum (u v : ι → Bool) :
    hammingDist u v = ∑ i, if u i ≠ v i then 1 else 0 :=
  card_filter _ _

/-! ### Conjunction and disjunction -/

/-- **Conjunction and disjunction sort a pair**, so their distances to any `h` add up to those of
the pair. -/
theorem hammingDist_and_add_hammingDist_or (f g h : ι → Bool) :
    hammingDist (fun i => f i && g i) h + hammingDist (fun i => f i || g i) h =
      hammingDist f h + hammingDist g h := by
  simp only [hammingDist_eq_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  cases f i <;> cases g i <;> cases h i <;> decide

/-- **The conjunction lies on a geodesic** from `f` to `g`. -/
theorem hammingDist_add_hammingDist_and (f g : ι → Bool) :
    hammingDist f (fun i => f i && g i) + hammingDist (fun i => f i && g i) g =
      hammingDist f g := by
  simp only [hammingDist_eq_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  cases f i <;> cases g i <;> decide

/-- **The disjunction lies on a geodesic** from `f` to `g`. -/
theorem hammingDist_add_hammingDist_or (f g : ι → Bool) :
    hammingDist f (fun i => f i || g i) + hammingDist (fun i => f i || g i) g =
      hammingDist f g := by
  simp only [hammingDist_eq_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  cases f i <;> cases g i <;> decide

/-- Conjunction is `1`-Lipschitz in each argument. -/
theorem hammingDist_and_le (f f' g g' : ι → Bool) :
    hammingDist (fun i => f i && g i) (fun i => f' i && g' i) ≤
      hammingDist f f' + hammingDist g g' :=
  (hammingDist_triangle _ (fun i => f' i && g i) _).trans (Nat.add_le_add
    (hammingDist_comp_le_hammingDist fun i b => b && g i)
    (hammingDist_comp_le_hammingDist fun i b => f' i && b))

/-- Disjunction is `1`-Lipschitz in each argument. -/
theorem hammingDist_or_le (f f' g g' : ι → Bool) :
    hammingDist (fun i => f i || g i) (fun i => f' i || g' i) ≤
      hammingDist f f' + hammingDist g g' :=
  (hammingDist_triangle _ (fun i => f' i || g i) _).trans (Nat.add_le_add
    (hammingDist_comp_le_hammingDist fun i b => b || g i)
    (hammingDist_comp_le_hammingDist fun i b => f' i || b))

/-! ### Isometries -/

/-- Adding a fixed point, coordinatewise the exclusive or, is an isometry. -/
@[simp] theorem hammingDist_add_right (f g a : ι → Bool) :
    hammingDist (f + a) (g + a) = hammingDist f g :=
  hammingDist_comp (fun i b => b + a i) fun i => add_left_injective (a i)

/-- Adding a fixed point on the left is an isometry. -/
@[simp] theorem hammingDist_add_left (a f g : ι → Bool) :
    hammingDist (a + f) (a + g) = hammingDist f g :=
  hammingDist_comp (fun i b => a i + b) fun i => add_right_injective (a i)

/-- Negation is an isometry. -/
@[simp] theorem hammingDist_not (f g : ι → Bool) :
    hammingDist (fun i => !f i) (fun i => !g i) = hammingDist f g :=
  hammingDist_comp (fun _ => not) fun _ => Function.LeftInverse.injective Bool.not_not

/-! ### Distances to the median -/

/-- **The median lies between any two of its arguments.** -/
theorem hammingDist_add_hammingDist_median (f g h : ι → Bool) :
    hammingDist f (median f g h) + hammingDist (median f g h) g = hammingDist f g := by
  simp only [hammingDist_eq_sum, ← sum_add_distrib, median]
  refine sum_congr rfl fun i _ => ?_
  by_cases hf : f i <;> by_cases hg : g i <;> by_cases hh : h i <;> simp_all

/-- **The median minimizes the total distance** to its three arguments. -/
theorem hammingDist_median_le (f g h k : ι → Bool) :
    hammingDist (median f g h) f + hammingDist (median f g h) g + hammingDist (median f g h) h ≤
      hammingDist k f + hammingDist k g + hammingDist k h := by
  simp only [hammingDist_eq_sum, ← sum_add_distrib, median]
  refine sum_le_sum fun i _ => ?_
  by_cases hf : f i <;> by_cases hg : g i <;> by_cases hh : h i <;>
    by_cases hk : k i <;> simp_all

/-! ### Parities and coordinate projections -/

variable [DecidableEq ι]

/-- **Distinct parities differ on exactly half of the inputs**: they disagree where the parity on
the symmetric difference is true. -/
theorem two_mul_hammingDist_parityOn {S T : Finset ι} (h : S ≠ T) :
    2 * hammingDist (parityOn S) (parityOn T) = 2 ^ Fintype.card ι := by
  have hfilter : (univ.filter fun x : ι → Bool => parityOn S x ≠ parityOn T x) =
      univ.filter fun x => parityOn (symmDiff S T) x = true := by
    refine filter_congr fun x _ => ?_
    rw [parityOn_symmDiff]
    cases parityOn S x <;> cases parityOn T x <;> decide
  have hne : (symmDiff S T).Nonempty := symmDiff_nonempty.2 h
  rw [hammingDist, hfilter, card_filter_parityOn_eq hne, mul_comm,
    Nat.two_pow_pred_mul_two (Fintype.card_pos_iff.2 ⟨hne.choose⟩)]

/-- **Two distinct coordinate projections differ on exactly half of the inputs**: they are the
parities on `{i}` and `{j}`. -/
theorem two_mul_hammingDist_proj {i j : ι} (hij : i ≠ j) :
    2 * hammingDist (fun x : ι → Bool => x i) (fun x => x j) = 2 ^ Fintype.card ι := by
  have hproj (k : ι) : (fun x : ι → Bool => x k) = parityOn {k} :=
    funext fun x => by rw [parityOn_eq_sum, sum_singleton]
  rw [hproj i, hproj j]
  exact two_mul_hammingDist_parityOn (singleton_injective.ne hij)

/-- The relative Hamming distance between two distinct coordinate projections is one half. -/
theorem hammingDist_proj_div {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜] {i j : ι} (hij : i ≠ j) :
    (hammingDist (fun x : ι → Bool => x i) (fun x => x j) : 𝕜) / 2 ^ Fintype.card ι = 1 / 2 := by
  have h : (2 * hammingDist (fun x : ι → Bool => x i) (fun x => x j) : 𝕜) =
      2 ^ Fintype.card ι := by
    exact_mod_cast two_mul_hammingDist_proj hij
  have h2 : (2 : 𝕜) ≠ 0 := OfNat.ofNat_ne_zero 2
  rw [div_eq_div_iff (pow_ne_zero _ h2) h2, one_mul, ← h, mul_comm]

/-- **Shifts of distinct projections by a common function differ on half of the inputs**, however
complicated the common function `f` is. -/
theorem two_mul_hammingDist_add_proj (f : (ι → Bool) → Bool) {i j : ι} (hij : i ≠ j) :
    2 * hammingDist (f + fun x => x i) (f + fun x => x j) = 2 ^ Fintype.card ι := by
  rw [hammingDist_add_left]
  exact two_mul_hammingDist_proj hij

/-! ### Coordinate flips -/

/-- Flipping one coordinate yields an input at Hamming distance `1` from the original. -/
theorem hammingDist_flip_self (x : ι → Bool) (i : ι) :
    hammingDist x (flipOn {i} x) = 1 := by
  rw [flipOn_singleton, hammingDist_update_of_ne (by simp)]

/-- A one-bit flip decreases the Hamming distance to any `z` by at most one:
`hammingDist x z ≤ hammingDist (flipOn {i} x) z + 1`. -/
theorem hammingDist_le_flip_add_one (x z : ι → Bool) (i : ι) :
    hammingDist x z ≤ hammingDist (flipOn {i} x) z + 1 := by
  have h := hammingDist_triangle x (flipOn {i} x) z
  rw [hammingDist_flip_self] at h
  omega

/-- A one-bit flip increases the Hamming distance to any `z` by at most one:
`hammingDist (flipOn {i} x) z ≤ hammingDist x z + 1`. -/
theorem hammingDist_flip_le_add_one (x z : ι → Bool) (i : ι) :
    hammingDist (flipOn {i} x) z ≤ hammingDist x z + 1 := by
  have h := hammingDist_triangle (flipOn {i} x) x z
  rw [hammingDist_comm (flipOn {i} x) x, hammingDist_flip_self] at h
  omega

/-- If `x i = z i`, flipping coordinate `i` of `x` increases the Hamming distance to `z`
by exactly one. -/
theorem hammingDist_flip_eq_add_one (x z : ι → Bool) (i : ι)
    (hi : x i = z i) :
    hammingDist (flipOn {i} x) z = hammingDist x z + 1 := by
  have h : (Finset.univ.filter fun j => flipOn {i} x j ≠ z j) =
      insert i (Finset.univ.filter fun j => x j ≠ z j) := by
    ext j
    by_cases hj : j = i
    · subst j
      cases hx : x i <;> simp_all [flipOn_apply]
    · simp [flipOn_apply, hj]
  rw [hammingDist, h, Finset.card_insert_of_notMem]
  · rfl
  · simp [hi]

/-- Flipping one coordinate changes the Hamming distance to `z` by one: it increases by one if
`x i = z i` and decreases by one otherwise. -/
theorem hammingDist_flip (x z : ι → Bool) (i : ι) :
    hammingDist (flipOn {i} x) z =
      if x i = z i then hammingDist x z + 1 else hammingDist x z - 1 := by
  split_ifs with hi
  · exact hammingDist_flip_eq_add_one x z i hi
  · have h := hammingDist_flip_eq_add_one (flipOn {i} x) z i
      (by rw [flipOn_singleton_self]; cases hx : x i <;> cases hz : z i <;> simp_all)
    rw [flipOn_flipOn] at h
    omega

end Fintype

end Cslib.BitString
