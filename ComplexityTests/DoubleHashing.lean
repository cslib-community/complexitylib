/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.DoubleHashing
public import Complexity.Foundations.Data.Nat.OddMulMod
public import Complexity.Init

/-!
# Tests for Odd-Stride Double Hashing and Power-of-Two Quotient Fiber Bounds

Non-vacuity and concrete evaluation tests for `Complexity.Foundations.Data.Nat.OddMulMod` and
`Complexity.DataStructure.Dictionary.DoubleHashing`:
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

open Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.UniformProbing
open Cslib.DataStructure.Dictionary.DoubleHashing
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

/-- Concrete collision, lookup, and in-place key-update check on `U = 8`, `M = 3` (`m = 8`) where
`h₁ u = ⟨u.val % 4, _⟩` maps distinct keys `k₁ = 1` and `k₂ = 5` to the same initial slot `1`:
inserting `k₂` after `k₁` takes `probeCount T₁ k₂ (π k₂) = 2 > 1` probes (stepping to slot
`(1 + 3) % 8 = 4`), `tableGet` recovers both stored values and returns `none` on an absent key, and
overwriting `k₁` preserves `OrderedTableRep` and updates `tableGet`. -/
example :
    let h₁ : Fin 8 → Fin (2 ^ 3) :=
      fun x => ⟨x.val % 4, Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)⟩
    let h₂ : Fin 8 → Fin (2 ^ (3 - 1)) := fun x => ⟨x.val % 4, Nat.mod_lt _ (by decide)⟩
    let π := oddStridePerm h₁ h₂
    let hm : 0 < 2 ^ 3 := by decide
    let k₁ : Fin 8 := ⟨1, by decide⟩
    let k₂ : Fin 8 := ⟨5, by decide⟩
    let k₃ : Fin 8 := ⟨3, by decide⟩
    let s₀ := Dictionary.empty 8
    let T₀ := emptyTable 8 (2 ^ 3)
    let s₁ := Function.update s₀ k₁ (some 10)
    let T₁ := tableInsert hm π T₀ k₁ 10
    let s₂ := Function.update s₁ k₂ (some 50)
    let T₂ := tableInsert hm π T₁ k₂ 50
    let s₃ := Function.update s₂ k₁ (some 99)
    let T₃ := tableInsert hm π T₂ k₁ 99
    h₁ k₁ = h₁ k₂ ∧
      probeCount T₁ k₂ (π k₂) = 2 ∧
      tableGet hm π T₂ k₁ = some 10 ∧
      tableGet hm π T₂ k₂ = some 50 ∧
      tableGet hm π T₂ k₃ = none ∧
      tableGet hm π T₃ k₁ = some 99 ∧
      tableGet hm π T₃ k₂ = some 50 ∧
      OrderedTableRep π s₃ T₃ := by
  intro h₁ h₂ π hm k₁ k₂ k₃ s₀ T₀ s₁ T₁ s₂ T₂ s₃ T₃
  have hrep₀ : OrderedTableRep π s₀ T₀ := OrderedTableRep.empty π
  have hrep₁ : OrderedTableRep π s₁ T₁ :=
    hrep₀.tableInsert_of_card_lt (by decide) k₁ 10
  have hrep₂ : OrderedTableRep π s₂ T₂ :=
    hrep₁.tableInsert_of_card_lt (by decide) k₂ 50
  have hrep₃ : OrderedTableRep π s₃ T₃ :=
    hrep₂.tableInsert_of_card_lt (by decide) k₁ 99
  have hmp₀ : missedProbes (otherOccupiedSlots T₀ k₁) (π k₁) = 0 :=
    (missedProbes_eq_iff (⟨0, hm⟩ : Fin (2 ^ 3))).mpr ⟨allOccupied_zero _ _, by simp [T₀]⟩
  have hT₁ : T₁ = Function.update T₀ ⟨1, by decide⟩ (some (k₁, 10)) := by
    dsimp only [T₁, tableInsert]
    simp only [hmp₀, Nat.zero_min, π, oddStridePerm_apply]
    rfl
  have hmp₁ : missedProbes (otherOccupiedSlots T₁ k₂) (π k₂) = 1 := by
    refine (missedProbes_eq_iff (⟨1, by decide⟩ : Fin (2 ^ 3))).mpr ⟨fun i hi => ?_, ?_⟩
    · have hi0 : i = ⟨0, hm⟩ := Fin.ext (Nat.lt_one_iff.mp hi)
      subst hi0
      rw [hT₁]
      simp only [π, oddStridePerm_apply, otherOccupiedSlots, Finset.mem_filter, Finset.mem_univ,
        true_and]
      decide
    · rw [hT₁]
      simp only [π, oddStridePerm_apply, otherOccupiedSlots, Finset.mem_filter, Finset.mem_univ,
        true_and]
      decide
  have hpc : probeCount T₁ k₂ (π k₂) = 2 := congrArg (1 + ·) hmp₁
  have hget₂ (u : Fin 8) : tableGet hm π T₂ u = s₂ u :=
    hrep₂.toTableRep.tableGet_eq hm u
      (lt_of_le_of_lt (hrep₂.toTableRep.card_otherOccupiedSlots_le u) (by decide))
  have hget₃ (u : Fin 8) : tableGet hm π T₃ u = s₃ u :=
    hrep₃.toTableRep.tableGet_eq hm u
      (lt_of_le_of_lt (hrep₃.toTableRep.card_otherOccupiedSlots_le u) (by decide))
  refine ⟨by decide, hpc, ?_, ?_, ?_, ?_, ?_, hrep₃⟩
  · rw [hget₂]; decide
  · rw [hget₂]; decide
  · rw [hget₂]; decide
  · rw [hget₃]; decide
  · rw [hget₃]; decide

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
`n_max = 2`, on `runTable` over an explicit nonempty two-insertion history
`ops = [.insert 1 42, .insert 2 99]`. -/
example (u : Fin 256) :
    let hm_pos : 0 < 2 ^ 16 := by decide
    let ops : List (Dictionary.Op 256) :=
      [.insert ⟨1, by decide⟩ 42, .insert ⟨2, by decide⟩ 99]
    (∑' θ : DoubleTabOddStrideSeed 1 30 16,
      PMF.uniformOfFintype (DoubleTabOddStrideSeed 1 30 16) θ *
        (probeCount (runTable hm_pos (doubleTabOddStridePerm 1 30 256 16 θ) ops) u
          (doubleTabOddStridePerm 1 30 256 16 θ u) : ℝ≥0∞)) ≤ 3 := by
  intro hm_pos ops
  have hvh : (Dictionary.spec 256 100 2).ValidHistory (Dictionary.empty 256) ops :=
    ⟨⟨Or.inl (by simp), by decide⟩,
      ⟨⟨Or.inl (Nat.lt_of_le_of_lt (Dictionary.card_dom_insert_le _ _ _) (by simp)), by decide⟩,
        trivial⟩⟩
  have hdom : (Dictionary.dom
      ((Dictionary.spec 256 100 2).run (Dictionary.empty 256) ops).1).card ≤ 2 :=
    Dictionary.card_dom_run_le_of_validHistory (by simp) hvh
  exact expect_probeCount_oddStride_doubleTab_of_codeBound_le
    (c := 1) (b := 30) (U := 256) (M := 16) (n_max := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (T := fun θ => runTable hm_pos (doubleTabOddStridePerm 1 30 256 16 θ) ops)
    (fun θ => orderedTableRep_runTable hm_pos (by decide)
      (doubleTabOddStridePerm 1 30 256 16 θ) hvh)
    hdom u

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
on `runTable` over an explicit nonempty two-insertion history
`ops = [.insert 1 42, .insert 2 99]`. -/
example (u : Fin 10000) :
    let hm_pos : 0 < 2 ^ 9 := by decide
    let ops : List (Dictionary.Op 10000) :=
      [.insert ⟨1, by decide⟩ 42, .insert ⟨2, by decide⟩ 99]
    (∑' θ : DoubleHashSeed 4 10 9,
      PMF.uniformOfFintype (DoubleHashSeed 4 10 9) θ *
        (probeCount (runTable hm_pos (doubleHashOddStridePerm 4 10 10000 9 θ) ops) u
          (doubleHashOddStridePerm 4 10 10000 9 θ u) : ℝ≥0∞)) ≤
      max (doubleTabThreshold 4 : ℝ≥0∞) 3 := by
  intro hm_pos ops
  have hvh : (Dictionary.spec 10000 100 10).ValidHistory (Dictionary.empty 10000) ops :=
    ⟨⟨Or.inl (by simp), by decide⟩,
      ⟨⟨Or.inl (Nat.lt_of_le_of_lt (Dictionary.card_dom_insert_le _ _ _) (by simp)), by decide⟩,
        trivial⟩⟩
  have hdom : (Dictionary.dom
      ((Dictionary.spec 10000 100 10).run (Dictionary.empty 10000) ops).1).card ≤ 10 :=
    Dictionary.card_dom_run_le_of_validHistory (by simp) hvh
  exact expect_probeCount_oddStride_unconditional_le
    (c_exp := 4) (n_max := 10) (U := 10000) (M := 9)
    (by decide) (by decide)
    (T := fun θ => runTable hm_pos (doubleHashOddStridePerm 4 10 10000 9 θ) ops)
    (fun θ => orderedTableRep_runTable hm_pos (by decide)
      (doubleHashOddStridePerm 4 10 10000 9 θ) hvh)
    hdom u

end ComplexityTests.DoubleHashing
