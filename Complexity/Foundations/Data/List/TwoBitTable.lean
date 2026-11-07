/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.List.RowMajor
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Row-major tables of two-bit counts

Store a square table in row-major order, with the two threshold bits `0 < c` and `1 < c` at
each entry. Counts zero, one and two are exactly `[false, false]`, `[true, false]` and
`[true, true]`; larger counts saturate. The ordinary and clocked compact-configuration writers
share this output specification and its indexing lemmas.

## Main definitions

* `List.twoBitTable`: the row-major two-threshold representation.

## Main results

* `List.length_twoBitTable`, `List.getD_twoBitTable`: exact length and addressing.
* `List.count_twoBitTable`: recover a count that is at most two.
* `List.twoBitTable_eq_flatMap`: agreement with natural-counter enumeration.
-/

public section

namespace List

/-- Two consecutive threshold bits for each entry, enumerated in row-major order. -/
@[expose] def twoBitTable (N : ℕ) (count : ℕ → ℕ → ℕ) : List Bool :=
  (finRange N).flatMap fun u : Fin N => (finRange N).flatMap fun v : Fin N =>
    ofFn fun b : Fin 2 => decide (b.val < count u v)

variable (N : ℕ) (count : ℕ → ℕ → ℕ)

/-- Finite-index enumeration equals the natural-counter loops used by a writer. -/
theorem twoBitTable_eq_flatMap :
    twoBitTable N count = (range N).flatMap fun u => (range N).flatMap fun v =>
      [decide (0 < count u v), decide (1 < count u v)] := by
  have hval (n : ℕ) : (finRange n).map Fin.val = range n := by
    apply List.ext_getElem <;> simp
  dsimp only [twoBitTable]
  conv_rhs => rw [← hval]; simp only [flatMap_map]
  apply flatMap_congr
  intro u _
  apply flatMap_congr
  intro v _
  simp [ofFn_succ]

/-- Exactly two bits are stored for each ordered pair of indices. -/
@[simp] theorem length_twoBitTable : (twoBitTable N count).length = 2 * N ^ 2 := by
  dsimp only [twoBitTable]
  simp_rw [flatMap_ofFn_prod]
  simp only [length_ofFn]
  ring

/-- Reading a bit at its row-major address recovers the corresponding threshold. -/
theorem getD_twoBitTable (u v : Fin N) (b : Fin 2) :
    (twoBitTable N count).getD (2 * (u.val * N + v.val) + b.val) false =
      decide (b.val < count u v) := by
  let p := finProdFinEquiv (u, finProdFinEquiv (v, b))
  have hp : 2 * (u.val * N + v.val) + b.val = p.val := by
    simp only [p, finProdFinEquiv, Equiv.coe_fn_mk]
    ring
  rw [hp]
  dsimp only [twoBitTable]
  simp_rw [flatMap_ofFn_prod]
  rw [getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  simp only [Fin.eta, p, Equiv.symm_apply_apply]

/-- The sum of an entry's two stored bits recovers any count at most two. -/
theorem count_twoBitTable (u v : Fin N) (hcount : count u v ≤ 2) :
    ((twoBitTable N count).getD (2 * (u.val * N + v.val)) false).toNat +
      ((twoBitTable N count).getD (2 * (u.val * N + v.val) + 1) false).toNat = count u v := by
  have h0 := getD_twoBitTable N count u v 0
  have h1 := getD_twoBitTable N count u v 1
  simp only [Fin.val_zero, Fin.val_one, Nat.add_zero] at h0 h1
  rw [h0, h1]
  interval_cases count u v <;> rfl

end List
