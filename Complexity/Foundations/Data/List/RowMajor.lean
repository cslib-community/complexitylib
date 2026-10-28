/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD

/-!
# Row-major finite arrays as lists

## Main results

* `List.flatMap_ofFn_prod`: nested row-major enumeration agrees with the existing product
  equivalence on finite indices.
* `List.getD_flatMap_ofFn`: read a cell at its ordinary flat row-major index.
-/

@[expose] public section

namespace List

/-- Flattening all rows enumerates the standard finite product equivalence. -/
theorem flatMap_ofFn_prod {α : Type*} {n d : ℕ} (f : Fin n → Fin d → α) :
    (finRange n).flatMap (fun i => ofFn (f i)) =
      ofFn (fun p : Fin (n * d) => f (finProdFinEquiv.symm p).1
        (finProdFinEquiv.symm p).2) := by
  rw [ofFn_mul]
  simp only [ofFn_eq_map, ← flatMap_def]
  apply flatMap_congr
  intro i _
  apply map_congr_left
  intro j _
  have heq : (⟨i.val * d + j.val, by
      calc
        i.val * d + j.val < i.val * d + d := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ n * d := Nat.mul_le_mul_right d i.isLt⟩ : Fin (n * d)) = finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [heq, Equiv.symm_apply_apply]

/-- Ordinary flat indexing reads the corresponding original row and column. -/
theorem getD_flatMap_ofFn {α : Type*} {n d : ℕ} (f : Fin n → Fin d → α)
    (default : α) (i : Fin n) (j : Fin d) :
    ((finRange n).flatMap (fun i => ofFn (f i))).getD (i.val * d + j.val) default =
      f i j := by
  rw [flatMap_ofFn_prod]
  have heq : i.val * d + j.val = (finProdFinEquiv (i, j)).val := by
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [heq, getD_eq_getElem _ _ (by
    rw [length_ofFn]
    exact (finProdFinEquiv (i, j)).isLt), List.getElem_ofFn]
  exact congrArg (fun p => f p.1 p.2) (finProdFinEquiv.symm_apply_apply (i, j))

end List
