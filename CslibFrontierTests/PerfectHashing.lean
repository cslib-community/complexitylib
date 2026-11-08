/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.PerfectHashing.Construction
public import CslibFrontier.Init
public import CslibFrontier.Probability.HashFamily.Collisions
public import CslibFrontier.Probability.HashFamily.Uniform

/-!
# Tests for FKS perfect hashing

* `uniformFamily U`: uniformly random functions `Fin U → Fin (r + 1)` form a range-indexed
  universal family (`uniformFamily_isTwoUniversal`), so every theorem of
  `CslibFrontier.DataStructure.Dictionary.PerfectHashing.Construction` applies to it.
* A concrete table for the keys `[1, 3, 4]` of `Fin 8`, with buckets `{1, 3}`, `∅` and `{4}`:
  every lookup on the whole universe is checked, the table occupies `9 ≤ 5 · 3 + 2` cells, and it
  satisfies `Valid`.
* With a secondary hash that is not injective on its bucket, a lookup misses a key, so
  `SecondaryInjective` cannot be dropped from `runLookup_memory`.
* The top-level test `TopGood` fails for a constant hash on five keys (`25 > 20`) and holds for
  the table above.
* Nonvacuity: with three attempts per level, the construction returns a table with positive
  probability, so `valid_of_mem_support_build` describes actual outputs.
* Collisions: a concrete ordered collision count, and the `1 / 2` bound on non-injectivity of a
  uniformly random function `Fin 8 → Fin 9` on three keys.
-/

public section

namespace CslibFrontierTests.PerfectHashing

open Cslib.DataStructure.Dictionary.PerfectHashing Cslib.OracleComp Cslib.Probability
open scoped ENNReal

/-- Uniformly random functions `Fin U → Fin (r + 1)`. -/
noncomputable def uniformFamily (U : ℕ) : Family (Fin U) where
  Seed r := Fin U → Fin (r + 1)
  seed _ := PMF.uniformOfFintype _
  hash _ s x := s x

/-- Uniformly random functions form a universal family at every range. -/
theorem uniformFamily_isTwoUniversal (U : ℕ) :
    ∀ r, IsTwoUniversal ((uniformFamily U).seed r) ((uniformFamily U).hash r) := fun r =>
  (isDeltaUniversalHash_uniformOfFintype (X := Fin U) (G := Fin (r + 1))).isTwoUniversal

/-! ### A concrete table -/

/-- Three keys of `Fin 8`. -/
def keys : List (Fin 8) := [1, 3, 4]

/-- The top hash into `3` values: buckets `{1, 3}`, `∅` and `{4}`. -/
def topSeed : Fin 8 → Fin 3 := fun x => if x = 4 then 2 else 0

/-- The secondary hashes: bucket `0` has two keys and `4` cells, the others one cell. -/
def secondary : Fin 3 → Member (uniformFamily 8) := fun j =>
  if j = 0 then ⟨3, fun x => if x = 3 then 0 else 2⟩ else ⟨0, fun _ => 0⟩

/-- The table. -/
def table : Description (uniformFamily 8) := ⟨⟨2, topSeed⟩, secondary⟩

/-- Every lookup answers membership, on the whole universe. -/
example : ∀ x : Fin 8, runLookup _ (memory table keys) x = decide (x ∈ keys) := by decide

/-- The table occupies `9` cells: the top cell, three headers, and blocks of `4` and `1` cells. -/
example : size table keys = 9 := by decide

/-- The table satisfies the FKS conditions. -/
theorem table_valid : Valid table keys where
  top_range := rfl
  sum_sq_le := by decide
  secondary_range := by decide
  secondaryInjective := fun j => by
    have h : ∀ j, ∀ x ∈ bucket table keys j, ∀ y ∈ bucket table keys j,
        (table.secondary j).apply x = (table.secondary j).apply y → x = y := by
      decide
    exact fun x hx y hy hxy => h j x hx y hy hxy

/-- The general theorems apply to the table. -/
example : ∀ x, runLookup _ (memory table keys) x = decide (x ∈ keys) :=
  runLookup_memory table_valid.secondaryInjective

example : size table keys ≤ 5 * keys.length + 2 := size_le table_valid

/-! ### Injective secondary hashes are needed -/

/-- A table whose secondary hash of bucket `{1, 3}` is constant. -/
def badTable : Description (uniformFamily 8) := ⟨⟨2, topSeed⟩, fun _ => ⟨3, fun _ => 0⟩⟩

/-- Keys `1` and `3` share a slot, so the lookup of the key `3` fails. -/
example : (3 : Fin 8) ∈ keys ∧ runLookup _ (memory badTable keys) 3 = false := by decide

/-! ### The top-level test -/

/-- Five keys. -/
def fiveKeys : List (Fin 8) := [0, 1, 2, 3, 4]

/-- A constant top hash on five keys has squared bucket sizes summing to `25 > 20`. -/
example : ¬ TopGood fiveKeys
    (⟨fun _ => 0, fiveKeys.map fun _ => 0⟩ : Trial (uniformFamily 8) 4) := by decide

/-- The top hash of the table passes: `2² + 0² + 1² = 5 ≤ 12`. -/
example : TopGood keys (⟨topSeed, keys.map topSeed⟩ : Trial (uniformFamily 8) 2) := by decide

/-! ### The construction succeeds with positive probability -/

/-- With three attempts per level, the construction for three keys fails with probability at most
`4 · 2⁻³ = 1 / 2`, so it returns a table with positive probability. -/
theorem exists_mem_support_build :
    ∃ D, some D ∈
      (evalWith (answer (uniformFamily 8)) (build (uniformFamily 8) 3 keys)).support := by
  by_contra hno
  simp only [not_exists] at hno
  have hone : evalWith (answer (uniformFamily 8)) (build (uniformFamily 8) 3 keys) none = 1 := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_eq_one_iff]
    intro o ho
    cases o with
    | none => rfl
    | some D => exact absurd ho (hno D)
  have hle := evalWith_build_none_le (uniformFamily_isTwoUniversal 8) 3 (by decide : keys.Nodup)
  rw [hone] at hle
  have hhalf : ((keys.length - 1 + 2 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 3 = 2⁻¹ := by
    rw [show keys.length - 1 + 2 = 2 * 2 from rfl, Nat.cast_mul, Nat.cast_two,
      show (2 : ℝ≥0∞) * 2 * 2⁻¹ ^ 3 = (2 * 2⁻¹) * (2 * 2⁻¹) * 2⁻¹ by ring,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul, one_mul]
  rw [hhalf] at hle
  exact absurd hle (not_le.mpr (ENNReal.inv_lt_one.mpr ENNReal.one_lt_two))

/-- Every table the construction returns answers lookups correctly. -/
example {D : Description (uniformFamily 8)}
    (hD : some D ∈ (evalWith (answer (uniformFamily 8)) (build (uniformFamily 8) 3 keys)).support)
    (x : Fin 8) : runLookup _ (memory D keys) x = decide (x ∈ keys) :=
  runLookup_of_mem_support_build (by decide) hD x

/-! ### Collisions -/

/-- Parity collides `1` with `3` (in both orders) and nothing else in `{1, 3, 4}`. -/
example : orderedCollisionCount (fun x : Fin 8 => (x : ℕ) % 2) {1, 3, 4} = 2 := by decide

/-- A uniformly random function `Fin 8 → Fin 9` fails to be injective on three keys with
probability at most `1 / 2`. -/
example : ((uniformFamily 8).seed 8).toOuterMeasure
    {s | ¬ Set.InjOn ((uniformFamily 8).hash 8 s) ({1, 3, 4} : Finset (Fin 8))} ≤ 2⁻¹ :=
  (uniformFamily_isTwoUniversal 8 8).toOuterMeasure_not_injOn_le _ (by simp)

end CslibFrontierTests.PerfectHashing
