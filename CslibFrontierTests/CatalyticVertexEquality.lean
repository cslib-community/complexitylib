/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

import CslibFrontier.Computability.Catalytic.VertexEquality

/-!
# Constant-frame two-stage catalytic vertex equality tests

Concrete `decide` runs of chunk extraction and the stage-1 excursion procedure on non-zero borrowed
registers, concrete runs of the 64-excursion `catalyticVertexEq` procedure on multi-chunk
identifiers with non-zero catalytic memory, a modulus-overflow counterexample showing that the
`2 ^ n` range bound is necessary for exactness (while restoration still holds), a nested-excursion
client exercising `catalyticVertexEq_eq` inside an endpoint callback on the same shared catalyst,
and concrete checks of the local-frame and linear catalytic bit-budget bounds.
-/

namespace CslibFrontierTests.CatalyticVertexEquality

open Cslib.Catalytic

local instance {α : Type*} [DecidableEq α] : DecidableEq (Unit → α) :=
  fun f g ↦ decidable_of_iff (f () = g ()) ⟨fun h ↦ funext fun () ↦ h, fun h ↦ congrFun h ()⟩

local instance {n : ℕ} {α : Type*} [DecidableEq α] : DecidableEq (Fin n → α) :=
  fun f g ↦ decidable_of_iff (∀ i : Fin n, f i = g i) ⟨funext, fun h i ↦ congrFun h i⟩

/-- Non-zero stage-1 register file at `B = 4, n = 6` (`q₁ = 2, ℓ₁ = 3, k₁ = 6`). -/
def sampleOuter : OuterRegState 4 6 :=
  ((fun _ ↦ ![19, 42, 7]), 37)

/-- Stage-1 `4`-visit forward and inverse runs by `decide`: `53 = [1, 1, 3]` and `21 = [1, 1, 1]`
in base `4` differ by `2` in chunk `2`, so `+1` adds `2² = 4` to `37` (`37 + 4 = 41`) while
restoring the register file, and `-1` restores `(sampleOuter.1, 37)` exactly. -/
example :
    let fwd := (stageOneSqDistProc 4 6 1).run 53 21 sampleOuter
    fwd = (sampleOuter.1, 41) ∧
      (stageOneSqDistProc 4 6 (-1)).run 53 21 fwd = sampleOuter := by
  decide

/-- Arbitrary non-zero catalytic memory `(T₁, T₂, W)` at `B = 4, n = 6`
(`q₂ = 1, ℓ₂ = 6, k₂ = 5`). -/
def sampleCat : VertexCatState 4 6 :=
  (sampleOuter,
   ((fun _ ↦ ![13, 4, 29, 8, 17, 21]), 11),
   fun k ↦ if k.val % 3 = 0 then 1 else 0)

/-- Equal 6-bit multi-chunk identifiers (`53 = 53 < 64`): returns `true` and restores `sampleCat`
after all `64` excursions. -/
example :
    catalyticVertexEq 4 6 (fun b cat ↦ (bif b then 53 else 53, cat)) sampleCat =
      (true, sampleCat) := by
  rw [catalyticVertexEq_eq (by decide) (by decide) (fun _ _ ↦ rfl)]
  rfl

/-- Distinct 6-bit identifiers differing in the low chunk (`52 ≠ 53`): returns `false` and restores
`sampleCat`. -/
example :
    catalyticVertexEq 4 6 (fun b cat ↦ (bif b then 53 else 52, cat)) sampleCat =
      (false, sampleCat) := by
  rw [catalyticVertexEq_eq (by decide) (by decide) (fun _ _ ↦ rfl)]
  rfl

/-- Distinct 6-bit identifiers differing only in the top chunk (`21 ≠ 53`): returns `false` and
restores `sampleCat`. -/
example :
    catalyticVertexEq 4 6 (fun b cat ↦ (bif b then 53 else 21, cat)) sampleCat =
      (false, sampleCat) := by
  rw [catalyticVertexEq_eq (by decide) (by decide) (fun _ _ ↦ rfl)]
  rfl

/-- **Zero-chunk boundary (`B = 0, n = 0`, `ℓ₁ = 0`).** On `0 < 2 ^ 0`, `catalyticVertexEq 0 0`
returns `true` and restores any catalytic state `cat`. -/
example (cat : VertexCatState 0 0) :
    catalyticVertexEq 0 0 (fun _ c ↦ (0, c)) cat = (true, cat) :=
  catalyticVertexEq_eq (x := 0) (y := 0) (by decide) (by decide) (fun b _ ↦ by cases b <;> rfl) cat

/-- **Range-hypothesis necessity (`x < 2 ^ n`).** At `B = 2, n = 2` (`q₁ = 1, ℓ₁ = 2`), `x = 4`
exceeds `2 ^ 2 - 1` and shares its low two chunks with `y = 0`, so `vertexEqProc` adds `1` while
still restoring any catalytic state `cat`. -/
example (cat : VertexCatState 2 2) :
    (vertexEqProc 2 2).run 4 0 (cat, 0) = (cat, 1) := by
  have hchunks : natChunkVec (outerChunkBits 2) (outerDigits 2 2) 4 =
      natChunkVec (outerChunkBits 2) (outerDigits 2 2) 0 := by decide
  rw [run_vertexEqProc_chunk]
  simp [hchunks]

/-- **Nested restoring excursions on shared catalytic memory** (Lemma 9.9 contract): an endpoint
callback that internally invokes `catalyticVertexEq` on the same `VertexCatState B n` to select
which vertex identifier to return still satisfies the restoring catalyst-independent contract, so
an outer `catalyticVertexEq` call decides equality and restores `cat₀` for every `cat₀`. -/
theorem nested_catalyticVertexEq {B n u v x₀ x₁ y : ℕ}
    (hu : u < 2 ^ n) (hv : v < 2 ^ n) (hx₀ : x₀ < 2 ^ n) (hx₁ : x₁ < 2 ^ n) (hy : y < 2 ^ n)
    (cat₀ : VertexCatState B n) :
    let innerVisit : Bool → VertexCatState B n → ℕ × VertexCatState B n :=
      fun b cat ↦ (bif b then v else u, cat)
    let outerVisit : Bool → VertexCatState B n → ℕ × VertexCatState B n :=
      fun b cat ↦
        if b then (y, cat)
        else
          let r := catalyticVertexEq B n innerVisit cat
          (if r.1 then x₁ else x₀, r.2)
    catalyticVertexEq B n outerVisit cat₀ =
      (decide ((if u = v then x₁ else x₀) = y), cat₀) := by
  intro innerVisit outerVisit
  have hinner : ∀ cat, catalyticVertexEq B n innerVisit cat = (decide (u = v), cat) :=
    catalyticVertexEq_eq hu hv (fun _ _ ↦ rfl)
  have houter : ∀ b cat,
      outerVisit b cat = (bif b then y else (if u = v then x₁ else x₀), cat) := by
    intro b cat
    cases b
    · simp only [outerVisit, Bool.false_eq_true, ↓reduceIte, hinner, decide_eq_true_eq,
        Bool.cond_false]
    · rfl
  have hx : (if u = v then x₁ else x₀) < 2 ^ n := by split_ifs <;> assumption
  exact catalyticVertexEq_eq hx hy houter cat₀

/-- Concrete bit-width and bit-budget checks at `B = 16, n = 10` (`n ≤ 1 * B`). -/
example : outerChunkBits 16 = 4 ∧ outerDigits 16 10 = 3 ∧ outerAccBits 16 10 = 10 ∧
    innerChunkBits 16 = 2 ∧ innerDigits 16 10 = 5 ∧ innerAccBits 16 10 = 7 ∧
    vertexCatBits 16 10 = 210 ∧ vertexCatLinearConst 1 = 160 ∧
    Fintype.card VertexLocalFrame = 128 := by
  rw [card_vertexLocalFrame]
  decide

/-- Symbolic bit-budget specialization at `C_N = 1`: for every `B` and every `n ≤ B`, the shared
catalytic memory uses at most `160 * (B + 1)` bits (`2 ^ (vertexCatBits B n)` states). -/
example {B n : ℕ} (hn : n ≤ B) :
    Fintype.card (VertexCatState B n) = 2 ^ vertexCatBits B n ∧
      vertexCatBits B n ≤ 160 * (B + 1) := by
  refine ⟨card_vertexCatState B n, ?_⟩
  have h := vertexCatBits_le (C_N := 1) (by omega : n ≤ 1 * B)
  have hc : vertexCatLinearConst 1 = 160 := by decide
  rwa [hc] at h

end CslibFrontierTests.CatalyticVertexEquality
