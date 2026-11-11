/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveBlocks
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Ring

/-!
# Superquadratic sensitivity separation: tower

Iterates the recursive construction `n` times, starting from a base family indexed by its number of
predicates. Each level consumes one predicate index, adds a factor `Fin k × Fin r` to the
coordinates, and lifts the base sensitive blocks along rows. The file computes the sizes of the
coordinate and block index types, and shows that nestedness, rejection of the all-false input, and
acceptance after flipping a block propagate up the tower.

## Main definitions

* `TowerCoordinates`: coordinate type after `n` recursive levels.
* `TowerBlockIndex`: index type of the lifted sensitive blocks after `n` levels.
* `towerFamily`: the `n`-fold iterate of `recursiveFamily` applied to a base family.
* `towerBlocks`: the base sensitive blocks lifted through `n` levels by `rowLift`.
* `baseExtension`: extension of a family with `D` indices to all index counts.

## Main results

* `tower_coordinates_card`: there are `(k * r) ^ n * Fintype.card I` coordinates at level `n`.
* `towerBlocks_pairwise`: pairwise disjoint base blocks lift to pairwise disjoint blocks.
* `towerFamily_nested`: nestedness of the base family propagates up the tower.
* `towerFamily_zero`: rejection of the all-false input propagates up the tower.
* `towerFamily_blocks`: every tower predicate accepts the all-false input flipped on any lifted
  block.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/Tower.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- Coordinate type after the specified number of recursive construction levels. -/
def TowerCoordinates (k r : ℕ) (I : Type) : ℕ → Type
  | 0 => I
  | n + 1 => (Fin k × Fin r) × TowerCoordinates k r I n

/-- The tower coordinate types are finite whenever the base coordinate type is finite. -/
instance towerCoordinatesFintype (k r : ℕ) (I : Type) [Fintype I] :
    (n : ℕ) → Fintype (TowerCoordinates k r I n)
  | 0 => inferInstanceAs (Fintype I)
  | n + 1 =>
    letI := towerCoordinatesFintype k r I n
    inferInstanceAs (Fintype ((Fin k × Fin r) × TowerCoordinates k r I n))

/-- Index type for the disjoint sensitive blocks after each recursive level. -/
def TowerBlockIndex (k : ℕ) (K : Type) : ℕ → Type
  | 0 => K
  | n + 1 => Fin k × TowerBlockIndex k K n

/-- The tower block index types are finite whenever the base block index type is finite. -/
instance towerBlockIndexFintype (k : ℕ) (K : Type) [Fintype K] :
    (n : ℕ) → Fintype (TowerBlockIndex k K n)
  | 0 => inferInstanceAs (Fintype K)
  | n + 1 =>
    letI := towerBlockIndexFintype k K n
    inferInstanceAs (Fintype (Fin k × TowerBlockIndex k K n))

/-- Iterate the tournament construction, adding a predicate index at each preceding level. -/
def towerFamily {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool) :
    (n h : ℕ) → Fin h → (TowerCoordinates k r I n → Bool) → Bool
  | 0, h => base h
  | n + 1, h => recursiveFamily T label (towerFamily T label base n (h + 1))

/-- Lift the base sensitive blocks through the recursive row products. -/
def towerBlocks {k r : ℕ} {I K : Type} (blocks : K → Finset I) :
    (n : ℕ) → TowerBlockIndex k K n → Finset (TowerCoordinates k r I n)
  | 0, b => blocks b
  | n + 1, b => rowLift b.1 (towerBlocks blocks n b.2)

/-- Extend a prescribed initial family to unused index counts without adding assumptions. -/
def baseExtension {I : Type} (D : ℕ) (F : Fin D → (I → Bool) → Bool)
    (h : ℕ) (q : Fin h) (x : I → Bool) : Bool :=
  if he : h = D then F (Fin.cast he q) x else false

/-- At the prescribed index count `D`, the extension `baseExtension D F` is `F`. -/
@[simp] theorem baseExtension_same {I : Type} (D : ℕ) (F : Fin D → (I → Bool) → Bool) :
    baseExtension D F D = F := by
  funext q x
  simp [baseExtension]

/-- After `n` levels there are `(k * r) ^ n * Fintype.card I` coordinates. -/
theorem tower_coordinates_card {k r : ℕ} {I : Type} [Fintype I] (n : ℕ) :
    Fintype.card (TowerCoordinates k r I n) = (k * r) ^ n * Fintype.card I := by
  induction n with
  | zero =>
    change Fintype.card I = (k * r) ^ 0 * Fintype.card I
    simp
  | succ n ih =>
    change Fintype.card ((Fin k × Fin r) × TowerCoordinates k r I n) = _
    simp only [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
    ring

/-- After `n` levels there are `k ^ n * Fintype.card K` block indices. -/
theorem tower_block_index_card {k : ℕ} {K : Type} [Fintype K] (n : ℕ) :
    Fintype.card (TowerBlockIndex k K n) = k ^ n * Fintype.card K := by
  induction n with
  | zero =>
    change Fintype.card K = k ^ 0 * Fintype.card K
    simp
  | succ n ih =>
    change Fintype.card (Fin k × TowerBlockIndex k K n) = _
    simp only [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
    ring

/-- If `0 < r` and every base block is nonempty, then every lifted block is nonempty. -/
theorem towerBlocks_nonempty {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hr : 0 < r) (hne : ∀ b, (blocks b).Nonempty) (n : ℕ) (b : TowerBlockIndex k K n) :
    (towerBlocks (r := r) blocks n b).Nonempty := by
  induction n with
  | zero => exact hne b
  | succ n ih => exact rowLift_nonempty b.1 _ hr (ih b.2)

/-- Pairwise disjoint base blocks lift to pairwise disjoint blocks at every level. -/
theorem towerBlocks_pairwise {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hd : Pairwise fun a b => Disjoint (blocks a) (blocks b)) (n : ℕ) :
    Pairwise fun a b =>
      Disjoint (towerBlocks (k := k) (r := r) blocks n a) (towerBlocks blocks n b) := by
  induction n with
  | zero => exact hd
  | succ n ih => exact rowLift_family_disjoint (towerBlocks blocks n) ih

/-- If the base family `base (h + n)` is nested, then the `n`-level tower family with `h` indices is
nested. -/
theorem towerFamily_nested {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (n h : ℕ) (hbase : NestedFamily (base (h + n))) :
    NestedFamily (towerFamily T label base n h) := by
  induction n generalizing h with
  | zero =>
    change NestedFamily (base h)
    simpa only [Nat.add_zero] using hbase
  | succ n ih =>
    apply recursiveFamily_nested
    apply ih
    have he : (h + 1) + n = h + (n + 1) := by omega
    rw [he]
    exact hbase

/-- If `0 < r` and every predicate of `base (h + n)` rejects the all-false input, then every
predicate of the `n`-level tower family with `h` indices rejects the all-false input. -/
theorem towerFamily_zero {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (hr : 0 < r) (n h : ℕ) (hbase : ∀ q, base (h + n) q (fun _ => false) = false) :
    ∀ q, towerFamily T label base n h q (fun _ => false) = false := by
  induction n generalizing h with
  | zero =>
    change ∀ q, base h q (fun _ => false) = false
    simpa only [Nat.add_zero] using hbase
  | succ n ih =>
    apply recursiveFamily_zero T label _ hr
    apply ih
    have he : (h + 1) + n = h + (n + 1) := by omega
    rw [he]
    exact hbase

open scoped Classical in
/-- If `0 < r` and every predicate of `base (h + n)` rejects the all-false input and accepts it
after flipping any base block, then every predicate of the `n`-level tower family with `h` indices
accepts the all-false input flipped on any block `towerBlocks blocks n b`. -/
theorem towerFamily_blocks {k r : ℕ} {I K : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (blocks : K → Finset I) (hr : 0 < r) (n h : ℕ)
    (hzero : ∀ q, base (h + n) q (fun _ => false) = false)
    (hblocks : ∀ b q, base (h + n) q (BitString.flipOn (blocks b) (fun _ => false)) = true) :
    ∀ b q, towerFamily T label base n h q
      (BitString.flipOn (towerBlocks blocks n b) (fun _ => false)) = true := by
  induction n generalizing h with
  | zero =>
    change ∀ b q, base h q (BitString.flipOn (blocks b) (fun _ => false)) = true
    simpa only [Nat.add_zero] using hblocks
  | succ n ih =>
    intro b q
    have he : (h + 1) + n = h + (n + 1) := by omega
    have hz : ∀ q, base ((h + 1) + n) q (fun _ => false) = false := by
      rw [he]
      exact hzero
    have hb : ∀ b q,
        base ((h + 1) + n) q (BitString.flipOn (blocks b) (fun _ => false)) = true := by
      rw [he]
      exact hblocks
    exact BitString.flipOn_congr_decidableEq _ _ ▸ recursiveFamily_rowLift T label _
      (towerFamily_zero T label base hr n (h + 1) hz)
      (towerBlocks blocks n b.2) (ih (h + 1) hz hb b.2) b.1 q

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
