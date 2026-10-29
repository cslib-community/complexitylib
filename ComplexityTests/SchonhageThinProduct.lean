/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.MatrixMultiplication.Schonhage.Magnitude
import Complexity.Algorithms.MatrixMultiplication.Schonhage.Full
import Complexity.Algorithms.MatrixMultiplication.Schonhage.Pruned

/-!
Regression clients for finite thin multiplication. Small computable layouts exercise actual signed
products and padding. The positive-depth parameter instance uses symbolic matrices so its large
outer dimension is never enumerated. No example claims a native instruction bound.
-/

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage

namespace SchonhageThinProductTests

/-- One outer level: blocks have three rows, and the inner dimension is one. -/
private def outerLayout : Layout 1 0 where
  hmL := by decide
  rowIdx := (Equiv.funUnique (Fin 1) (Fin 3)).symm
  colIdx := (Equiv.funUnique (Fin 1) (Fin 3)).symm
  innerIdx := by
    change Fin 1 ≃ (Fin 0 → Fin 2 × Fin 2)
    exact Equiv.ofUnique _ _
  table := fun _ => ∅
  table_card := fun _ => rfl
  table_injective := by
    change Function.Injective (fun _ : Fin 1 × Fin 1 => _)
    exact fun _ _ _ => Subsingleton.elim _ _

/-- One inner level: four inner indices and one row per block. -/
private def innerLayout : Layout 1 1 where
  hmL := by decide
  rowIdx := by
    change Fin 1 ≃ (Fin 0 → Fin 3)
    exact Equiv.ofUnique _ _
  colIdx := by
    change Fin 1 ≃ (Fin 0 → Fin 3)
    exact Equiv.ofUnique _ _
  innerIdx := (finProdFinEquiv (m := 2) (n := 2)).symm.trans
    (Equiv.funUnique (Fin 1) (Fin 2 × Fin 2)).symm
  table := fun _ => {0}
  table_card := fun _ => by decide
  table_injective := by
    change Function.Injective (fun _ : Fin 1 × Fin 1 => _)
    exact fun _ _ _ => Subsingleton.elim _ _

private def X : Matrix (Fin 4) (Fin 1) ℤ := !![-3; 2; 0; 5]
private def Y : Matrix (Fin 1) (Fin 4) ℤ := !![2, -1, 4, 0]
private def W : Finset (Fin 4 × Fin 4) := {(0, 1), (3, 2), (2, 3)}

-- N is not a multiple of the band size. The last two padded rows and columns are zero.
example : padN 1 0 4 = 6 := by decide
example : numBands 1 0 4 = 2 := by decide
example : padN 1 0 0 = 0 := by decide +kernel
example : padRows X 4 0 = 0 ∧ padCols Y 0 5 = 0 := by decide +kernel
example : padRows X 3 0 = 5 ∧ padCols Y 0 2 = 4 := by decide

example : outStrOfPos outerLayout 0 1 = ![.z 0 1] := by decide
example : bandArrayL outerLayout X 0 ![.x 0] = -3 := by decide +kernel
-- These compute the finite recursion itself, including encodings and the wanted-output mapping.
example : Pruned.result 1 (encodingL (bandArrayL outerLayout X 0))
    (encodingR (bandArrayR outerLayout Y 0)) (wantedStrings outerLayout W 0 0)
    (outStrOfPos outerLayout 0 1) = 3 := by decide +kernel

example : Pruned.result 1 (encodingL (bandArrayL outerLayout X 1))
    (encodingR (bandArrayR outerLayout Y 0)) (wantedStrings outerLayout W 1 0)
    (outStrOfPos outerLayout 3 2) = 20 := by decide +kernel

example : Pruned.result 1 (encodingL (bandArrayL outerLayout X 0))
    (encodingR (bandArrayR outerLayout Y 1)) (wantedStrings outerLayout W 0 1)
    (outStrOfPos outerLayout 2 3) = 0 := by decide +kernel

example : ∑ T ∈ tiles 1 0 4, (wantedStrings outerLayout W T.1 T.2).card = 3 := by decide +kernel
example : ∑ T ∈ tiles 1 0 4, (leaves (wantedStrings outerLayout W T.1 T.2)).card = 3 := by
  decide
example : wantedStrings outerLayout W 1 1 = ∅ := by decide
example : (leaves (wantedStrings outerLayout W 1 1)).card = 0 := by decide +kernel

-- Four signed summands with a single inner output; there is no outer error coefficient here.
private def A : Matrix (Fin 1) (Fin 4) ℤ := !![-3, 2, 0, 5]
private def B : Matrix (Fin 4) (Fin 1) ℤ := !![2; -1; 4; 0]

example : Full.result 1 (bandArrayL innerLayout A 0) (bandArrayR innerLayout B 0)
    (outStrOfPos innerLayout 0 0) = -8 := by decide +kernel

-- A mixed inner/outer output checks the exact-inner-count zeroing that eliminates error terms.
private def mixedX (_Q : Finset (Fin 2)) : LeftMat 2 1 :=
  fun _ π => A 0 (finProdFinEquiv (π 0))
private def mixedY (_Q : Finset (Fin 2)) : RightMat 2 1 :=
  fun π _ => B (finProdFinEquiv (π 0)) 0
private def mixedOutput : OutStr 2 := ![.z0, .z 0 0]

example : Pruned.result 2 (encodingL (arrayL 1 mixedX)) (encodingR (arrayR 1 mixedY))
    {mixedOutput} mixedOutput = -8 := by decide +kernel

example : Pruned.result 1 (encodingL (bandArrayL innerLayout A 0))
    (encodingR (bandArrayR innerLayout B 0))
    (wantedStrings innerLayout ({(0, 0)} : Finset (Fin 1 × Fin 1)) 0 0)
    (outStrOfPos innerLayout 0 0) = -8 := by decide +kernel

example : (univ.filter fun τ : Leaf 1 =>
    Leaf.Contributes τ (fun _ => OutVar.z0) ∧ order 1 τ = 0).card = 1 := by decide
example : (univ.filter fun τ : Leaf 1 =>
    Leaf.Contributes τ (fun _ => OutVar.z0) ∧ order 1 τ = 1).card = 9 := by decide
example : (leaves ({fun _ => OutVar.z0} : Finset (OutStr 1))).card = 10 := by decide
example : order 0 (fun _ : Fin 1 => Term.P0) = -1 := by decide
example : (leaves (∅ : Finset (OutStr 0))).card = 0 := by decide +kernel

example (β β' : ℕ) : wantedStrings outerLayout (∅ : Finset (Fin 4 × Fin 4)) β β' = ∅ := by
  simp [wantedStrings]

-- Existence at both the degenerate and positive-depth boundary, without assumptions on layouts.
example : Nonempty (Layout 0 0) := nonempty_layout (by decide)
example : Nonempty (Layout 19 1) := nonempty_layout (by decide)

private abbrev admittedN : ℕ := 68719476736
private noncomputable def admittedLayout : Layout 19 1 :=
  Classical.choice (nonempty_layout (by decide))
private def singletonQuery : Finset (Fin admittedN × Fin admittedN) := {(0, 0)}

-- All parameters of the complete composition are simultaneously satisfiable with m > 0.
example : D 1 ^ 18 ≤ admittedN ∧ singletonQuery.card * 2 ^ 1 ≤ admittedN ^ 2 := by
  constructor
  · rfl
  · norm_num [singletonQuery, admittedN]

example :
    ((2 * numBands (19 * 1) 1 admittedN * 10 ^ (19 * 1) : ℕ) : ℝ) ≤
      4 * (D 1 : ℝ) ^ (-(1 / 18 : ℝ)) * (admittedN : ℝ) ^ 2 := by
  have hN : D 1 ^ 18 ≤ admittedN := by norm_num [D, admittedN]
  exact encodings_total_le 1 admittedN hN

example :
    ((∑ T ∈ tiles (19 * 1) 1 admittedN,
      (leaves (wantedStrings admittedLayout singletonQuery T.1 T.2)).card : ℕ) : ℝ) ≤
      33 * (D 1 : ℝ) ^ (-(1 / 18 : ℝ)) * (admittedN : ℝ) ^ 2 := by
  have hN : D 1 ^ 18 ≤ admittedN := by norm_num [D, admittedN]
  have hW : singletonQuery.card * 2 ^ 1 ≤ admittedN ^ 2 := by
    norm_num [singletonQuery, admittedN]
  exact total_leaves_le (m := 1) (N := admittedN) admittedLayout singletonQuery hN hW

example (X' : Matrix (Fin admittedN) (Fin (D 1)) ℤ)
    (Y' : Matrix (Fin (D 1)) (Fin admittedN) ℤ) :
    ((∑ T ∈ tiles (19 * 1) 1 admittedN,
      Pruned.totalSize (encodingL (bandArrayL admittedLayout X' T.1))
        (encodingR (bandArrayR admittedLayout Y' T.2))
        (wantedStrings admittedLayout singletonQuery T.1 T.2) : ℕ) : ℝ) ≤
      ((19 * 1 + 1 : ℕ) : ℝ) * (33 * (D 1 : ℝ) ^ (-(1 / 18 : ℝ)) * (admittedN : ℝ) ^ 2) := by
  have hN : D 1 ^ 18 ≤ admittedN := by norm_num [D, admittedN]
  have hW : singletonQuery.card * 2 ^ 1 ≤ admittedN ^ 2 := by
    norm_num [singletonQuery, admittedN]
  exact total_passed_sets_le (m := 1) (N := admittedN) admittedLayout X' Y' singletonQuery hN hW

end SchonhageThinProductTests
