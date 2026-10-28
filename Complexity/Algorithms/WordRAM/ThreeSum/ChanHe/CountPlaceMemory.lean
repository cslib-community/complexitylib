/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.CountPlace

/-!
# Memory frames and output readback for complete counting/placement calls

## Main results

* `CountPlace.memory_outside`: only the specified data, descriptor and workspace cells change.
* `CountPlace.memory_heavy`: exact compact heavy data.
* `CountPlace.memory_arrXY`, `CountPlace.memory_arrZ`: exact packed light columns.

## References

These composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.CountPlace

open Cslib.WordRAM.Signed

/-- No write escapes the four explicit blocks and descriptor cell. -/
theorem memory_outside (mem : ℕ → ℕ) (values : ℕ → ℤ)
    (n M out dst col dist t scratch hist descriptor N : ℕ) (neg : Bool)
    (hM : 0 < M) (hN : 2 * M ≤ N) (hc : col < 4) (hd : dist ≤ 4 * M)
    (a : ℕ) (ho : ¬(out ≤ a ∧ a < out + n)) (hp : ¬(dst ≤ a ∧ a < dst + 4 * N))
    (hk : ¬(scratch ≤ a ∧ a < scratch + n)) (hh : ¬(hist ≤ a ∧ a < hist + M))
    (he : a ≠ descriptor) :
    memory mem values n M out dst col dist t scratch hist descriptor neg a = mem a := by
  rw [memory, Function.update_of_ne he,
    Place.memory_outside _ _ _ _ _ _ _ _ _ N neg hM hN hc hd le_rfl ho hp,
    Count.memory, Histogram.memory_outside _ _ _ _ _ _ hh]
  simp only [Residues.memory, hk, ↓reduceIte]

/-- The count store always writes the compact output length. -/
theorem memory_descriptor (mem : ℕ → ℕ) (values : ℕ → ℤ)
    (n M out dst col dist t scratch hist descriptor : ℕ) (neg : Bool) :
    memory mem values n M out dst col dist t scratch hist descriptor neg descriptor =
      (Place.heavyList values n M n).length := by
  exact Function.update_self ..

/-- The compact output contains the original signed encodings in input order. -/
theorem memory_heavy (mem : ℕ → ℕ) (values : ℕ → ℤ)
    (n M out dst col dist t scratch hist descriptor : ℕ) (neg : Bool)
    (hdisj : out + n ≤ dst) (he : descriptor < out)
    {j : ℕ} (hj : j < (Place.heavyList values n M n).length) :
    memory mem values n M out dst col dist t scratch hist descriptor neg (out + j) =
      encode ((Place.heavyList values n M n)[j]) := by
  rw [memory, Function.update_of_ne (by omega)]
  exact Place.memory_heavy _ _ _ _ _ _ _ _ _ _ hdisj le_rfl hj

/-- The counting workspace and descriptor do not affect other packed columns. -/
theorem memory_other_column (mem : ℕ → ℕ) (values : ℕ → ℤ)
    (n M out dst col dist t scratch hist descriptor N : ℕ) (neg : Bool)
    (hdisj : out + n ≤ dst) (hc : col < 4) (hd : dist = 0 ∨ dist = 4 * M)
    (hk : dst + 4 * N ≤ scratch) (hh : scratch + n ≤ hist) (he : descriptor < dst)
    {u : ℕ} (hu : u < 4 * N) (hcol : u % 4 ≠ col) :
    memory mem values n M out dst col dist t scratch hist descriptor neg (dst + u) =
      mem (dst + u) := by
  rw [memory, Function.update_of_ne (by omega),
    Place.memory_other_column _ _ _ _ _ _ _ _ _ _ hdisj hc hd u hcol,
    Count.memory_before _ _ _ _ _ _ _ (by omega) (by omega)]

/-- A complete counting/placement call writes the exact first or second light column. -/
theorem memory_arrXY (mem : ℕ → ℕ) (values : ℕ → ℤ)
    (n M out dst col t U scratch hist descriptor N : ℕ)
    (hM : 0 < M) (hdisj : out + n ≤ dst)
    (hk : dst + 4 * N ≤ scratch) (hh : scratch + n ≤ hist) (he : descriptor < dst)
    (hinj : Set.InjOn values (↑(Finset.range n) : Set ℕ))
    {i : ℕ} (hi : 4 * i + col < 4 * N)
    (hpad : mem (dst + 4 * i + col) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.pad U + (t : ℤ))) :
    memory mem values n M out dst col 0 t scratch hist descriptor false
        (dst + 4 * i + col) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.arrXY
        ((Finset.range n).image values) M U i + (t : ℤ)) := by
  rw [memory, Function.update_of_ne (by omega)]
  apply Place.memory_arrXY _ _ _ _ _ _ _ _ _ hM hdisj hinj i
  rw [Count.memory_before _ _ _ _ _ _ _ (by omega) (by omega)]
  exact hpad

/-- A complete counting/placement call writes the exact duplicated and negated third column. -/
theorem memory_arrZ (mem : ℕ → ℕ) (values : ℕ → ℤ)
    (n M out dst col t U scratch hist descriptor N : ℕ)
    (hM : 0 < M) (hdisj : out + n ≤ dst)
    (hk : dst + 4 * N ≤ scratch) (hh : scratch + n ≤ hist) (he : descriptor < dst)
    (hinj : Set.InjOn values (↑(Finset.range n) : Set ℕ))
    {i : ℕ} (hi : 4 * i + col < 4 * N)
    (hpad : mem (dst + 4 * i + col) =
      encode (-Cslib.Algorithms.ThreeSum.ChanHe.pad U + (t : ℤ))) :
    memory mem values n M out dst col (4 * M) t scratch hist descriptor true
        (dst + 4 * i + col) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.arrZ
        ((Finset.range n).image values) M U i + (t : ℤ)) := by
  rw [memory, Function.update_of_ne (by omega)]
  apply Place.memory_arrZ _ _ _ _ _ _ _ _ _ hM hdisj hinj i
  rw [Count.memory_before _ _ _ _ _ _ _ (by omega) (by omega)]
  exact hpad

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.CountPlace
