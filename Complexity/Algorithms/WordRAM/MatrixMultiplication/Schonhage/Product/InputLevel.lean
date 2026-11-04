/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Input

/-!
# Tensor-level independence of original matrix and coordinate words

Changing the original tensor-level header changes only address one. Matrix words,
coordinates, original dimensions and the literal length word are preserved.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Every original word except the level header is independent of that header. -/
theorem input_change_level {m N : ℕ} (bits : Bool) (L L' : ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (a : ℕ) (ha : a ≠ 1) :
    (State.init (input bits L X Y qs) : State 160).data.mem a =
      (State.init (input bits L' X Y qs) : State 160).data.mem a := by
  cases a with
  | zero =>
    change (Data.init _ : Data 160).mem 0 = (Data.init _ : Data 160).mem 0
    rw [Data.init_mem_zero, Data.init_mem_zero]
    have h := input_length bits L X Y qs
    have h' := input_length bits L' X Y qs
    omega
  | succ a =>
    cases a with
    | zero => exact (ha rfl).elim
    | succ a => rfl

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
