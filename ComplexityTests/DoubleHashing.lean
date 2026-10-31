/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.DoubleHashing
public import Complexity.Foundations.Data.Nat.OddMulMod
public import Complexity.Init

/-!
# Tests for Odd-Stride Double Hashing and Power-of-Two Quotient Fiber Bounds

Non-vacuity and concrete evaluation tests for `Complexity.Foundations.Data.Nat.OddMulMod` and
`Complexity.Algorithms.Lean.DoubleHashing`:
* Concrete `decide` checks of the power-of-two odd-stride fiber bound `Nat.card_odd_mul_mod_eq_le`
  when `gcd(Δ, 2 ^ M) > 1` (even step count `Δ = 6` modulo `2 ^ 4 = 16`).
* Concrete instantiation of `oddStridePerm`, `OrderedTableRep.empty`,
  `OrderedTableRep.tableInsert_of_card_lt`, `orderedTableRep_runTable`, and
  `probeCount_le_card_otherOccupied_add_one` on explicit open-addressed insertions.
* Concrete non-vacuity instances of `expect_probeCount_oddStride_doubleTab_of_codeBound_le`,
  `expect_probeCount_oddStride_doubleTab_le` at `n_max = doubleTabThreshold c_exp`, and
  `expect_probeCount_oddStride_unconditional_le` in both small (`n_max = 10`) and large
  (`n_max = doubleTabThreshold c_exp`) capacity regimes.
-/

public section

namespace ComplexityTests.DoubleHashing

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.UniformProbing
open Cslib.Algorithms.Lean.DoubleHashing
open Cslib.Probability
open scoped BigOperators ENNReal

/-- On `M = 4` (`2 ^ M = 16`, `2 ^ (M - 1) = 8`) and even step count `Δ = 6`, the congruence
`(6 * (2 * s + 1)) % 16 = 2` has exactly `2 ≤ 6` solutions (`s = 1` and `s = 5`) in `Fin 8`. -/
example :
    (Finset.univ.filter (fun s : Fin (2 ^ (4 - 1)) =>
      (6 * (2 * s.val + 1)) % 2 ^ 4 = 2)).card = 2 := by
  decide

/-- Concrete check of `Nat.card_odd_mul_mod_eq_le` for `M = 4`, `Δ = 6`, `r = 2`. -/
example :
    (Finset.univ.filter (fun s : Fin (2 ^ (4 - 1)) =>
      (6 * (2 * s.val + 1)) % 2 ^ 4 = 2)).card ≤ 6 :=
  Nat.card_odd_mul_mod_eq_le 4 6 2 (by decide)

/-- Concrete odd-stride permutation family on `U = 8`, `M = 3` (`m = 8`) with `h₁ u = u` and
`h₂ u = ⟨u.val % 4, _⟩`, verifying `OrderedTableRep.empty`,
`OrderedTableRep.tableInsert_of_card_lt`, and the deterministic pigeonhole bound across two
insertions. -/
example (u : Fin 8) :
    let h₁ : Fin 8 → Fin (2 ^ 3) := id
    let h₂ : Fin 8 → Fin (2 ^ (3 - 1)) := fun x => ⟨x.val % 4, Nat.mod_lt _ (by decide)⟩
    let π := oddStridePerm h₁ h₂
    let hm : 0 < 2 ^ 3 := by decide
    let k₁ : Fin 8 := ⟨1, by decide⟩
    let k₂ : Fin 8 := ⟨5, by decide⟩
    let s₀ := Dictionary.empty 8
    let T₀ := emptyTable 8 (2 ^ 3)
    let s₁ := Function.update s₀ k₁ (some 10)
    let T₁ := tableInsert hm π T₀ k₁ 10
    let s₂ := Function.update s₁ k₂ (some 50)
    let T₂ := tableInsert hm π T₁ k₂ 50
    OrderedTableRep π s₂ T₂ ∧ probeCount T₂ u (π u) ≤ 2 + 1 := by
  intro h₁ h₂ π hm k₁ k₂ s₀ T₀ s₁ T₁ s₂ T₂
  have hrep₀ : OrderedTableRep π s₀ T₀ := OrderedTableRep.empty π
  have hrep₁ : OrderedTableRep π s₁ T₁ :=
    hrep₀.tableInsert_of_card_lt (by decide) k₁ 10
  have hrep₂ : OrderedTableRep π s₂ T₂ :=
    hrep₁.tableInsert_of_card_lt (by decide) k₂ 50
  have hdom : (Dictionary.dom s₂).card ≤ 2 := by decide
  exact ⟨hrep₂, probeCount_le_add_one hrep₂.toTableRep hdom u⟩

/-- Concrete check of `probeCount_le_card_otherOccupied_add_one` on an empty table of size `8`. -/
example (u : Fin 8) :
    let h₁ : Fin 8 → Fin (2 ^ 3) := id
    let h₂ : Fin 8 → Fin (2 ^ (3 - 1)) := fun x => ⟨x.val % 4, Nat.mod_lt _ (by decide)⟩
    let π := oddStridePerm h₁ h₂
    probeCount (emptyTable 8 (2 ^ 3)) u (π u) ≤
      (otherOccupiedSlots (emptyTable 8 (2 ^ 3)) u).card + 1 :=
  probeCount_le_card_otherOccupied_add_one (emptyTable 8 (2 ^ 3)) u _

/-- Concrete non-vacuity instance of `expect_probeCount_oddStride_doubleTab_of_codeBound_le` at
`c = 1`, `b = 30`, `U = 256 ≤ 2 ^ 30`, `M = 16` (`2 ^ 16 = 65536 ≥ 2 * 12 ^ 4 = 41472`),
`n_max = 0`, on an empty table. -/
example (u : Fin 256) :
    (∑' θ : DoubleTabOddStrideSeed 1 30 16,
      PMF.uniformOfFintype (DoubleTabOddStrideSeed 1 30 16) θ *
        (probeCount (emptyTable 256 (2 ^ 16)) u
          (doubleTabOddStridePerm 1 30 256 16 θ u) : ℝ≥0∞)) ≤ 3 :=
  expect_probeCount_oddStride_doubleTab_of_codeBound_le
    (c := 1) (b := 30) (U := 256) (M := 16) (n_max := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (T := fun _ => emptyTable 256 (2 ^ 16))
    (fun θ => OrderedTableRep.empty (doubleTabOddStridePerm 1 30 256 16 θ))
    (by simp) u

/-- Concrete non-vacuity instance of `expect_probeCount_oddStride_doubleTab_le` in the large
Double Tabulation regime `n_max = doubleTabThreshold c_exp`,
`U = doubleTabThreshold c_exp ^ c_exp`, `M = 2 * doubleTabMinB c_exp + 5`, evaluated on
`runTable hm (doubleHashOddStridePerm c_exp N (N ^ c_exp) M θ) ops` for any valid history `ops`. -/
example (c_exp V : ℕ)
    (ops : List (Dictionary.Op (doubleTabThreshold c_exp ^ c_exp)))
    (hvh : (Dictionary.spec (doubleTabThreshold c_exp ^ c_exp) V
      (doubleTabThreshold c_exp)).ValidHistory
      (Dictionary.empty (doubleTabThreshold c_exp ^ c_exp)) ops)
    (u : Fin (doubleTabThreshold c_exp ^ c_exp)) :
    let N := doubleTabThreshold c_exp
    let M := 2 * doubleTabMinB c_exp + 5
    let hm_pos : 0 < 2 ^ M := Nat.two_pow_pos M
    (∑' θ : DoubleHashSeed c_exp N M,
      PMF.uniformOfFintype (DoubleHashSeed c_exp N M) θ *
        (probeCount (runTable hm_pos (doubleHashOddStridePerm c_exp N (N ^ c_exp) M θ) ops) u
          (doubleHashOddStridePerm c_exp N (N ^ c_exp) M θ u) : ℝ≥0∞)) ≤ 3 := by
  intro N M hm_pos
  have hmax : max N 4 = N := max_eq_left (four_le_doubleTabThreshold c_exp)
  have hU : N ^ c_exp ≤ max N 4 ^ c_exp := by rw [hmax]
  have hm : 32 * max N 4 ≤ 2 ^ M := by
    rw [hmax]
    dsimp only [N, M]
    rw [doubleTabThreshold_eq, Nat.pow_add, Nat.mul_comm]
  have hcap : N ≤ 2 ^ M := by omega
  have hdom : (Dictionary.dom
      ((Dictionary.spec (N ^ c_exp) V N).run (Dictionary.empty (N ^ c_exp)) ops).1).card ≤ N :=
    Dictionary.card_dom_run_le_of_validHistory (by simp) hvh
  exact expect_probeCount_oddStride_doubleTab_le le_rfl hU hm
    (fun θ => orderedTableRep_runTable hm_pos hcap
      (doubleHashOddStridePerm c_exp N (N ^ c_exp) M θ) hvh)
    hdom u

/-- Concrete non-vacuity instance of `expect_probeCount_oddStride_unconditional_le` in the small
capacity regime `n_max = 10`, `c_exp = 4`, `U = 10000 ≤ 10 ^ 4`, `M = 9` (`2 ^ 9 = 512 ≥ 32 * 10`)
on an empty table. -/
example (u : Fin 10000) :
    (∑' θ : DoubleHashSeed 4 10 9,
      PMF.uniformOfFintype (DoubleHashSeed 4 10 9) θ *
        (probeCount (emptyTable 10000 (2 ^ 9)) u
          (doubleHashOddStridePerm 4 10 10000 9 θ u) : ℝ≥0∞)) ≤
      max (doubleTabThreshold 4 : ℝ≥0∞) 3 :=
  expect_probeCount_oddStride_unconditional_le
    (c_exp := 4) (n_max := 10) (U := 10000) (M := 9)
    (by decide) (by decide)
    (T := fun _ => emptyTable 10000 (2 ^ 9))
    (fun θ => OrderedTableRep.empty (doubleHashOddStridePerm 4 10 10000 9 θ))
    (by simp) u

end ComplexityTests.DoubleHashing
