/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.LineCode.Line
import Complexity.Foundations.Combinatorics.LineCode.Menu
import Complexity.Foundations.Combinatorics.LineCode.Menu.Collision
import Complexity.Foundations.Combinatorics.LineCode.Menu.Counting
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Universal recovery menu clients

These clients compute small punctured lines over `ZMod 2` and `ZMod 3`, instantiate the budget of
the collision tail and of the universal-menu theorem with concrete fields and dimensions (`q = 2`
with `ℓ = 11`, and the four-element field `GaloisField 2 2` with `ℓ = 8`), and exercise the
boundary cases of universality: a single request, repeated targets and an occupied target.
-/

namespace ComplexityTests.MassProduction.Menu

open Cslib Cslib.LineCode Finset

/-! ### Punctured lines -/

-- Concrete punctured lines over `ZMod 2` and `ZMod 3`, disjointness for non-proportional
-- directions, direction blocking, and occupied points.
example :
    puncturedLine (![0, 0] : Fin 2 → ZMod 2) ![1, 0] = {![1, 0]} ∧
    puncturedLine (![1, 1] : Fin 2 → ZMod 2) 0 = {![1, 1]} ∧
    puncturedLine (![0, 1] : Fin 2 → ZMod 3) ![1, 1] = {![1, 2], ![2, 0]} ∧
    Disjoint (puncturedLine (0 : Fin 2 → ZMod 3) ![1, 0]) (puncturedLine 0 ![0, 1]) ∧
    ¬Disjoint (puncturedLine (0 : Fin 2 → ZMod 3) ![1, 1]) (puncturedLine 0 ![2, 2]) ∧
    #{v ∈ univ.erase 0 | (![1, 2] : Fin 2 → ZMod 3) ∈ puncturedLine 0 v} = 2 ∧
    occupiedPoints (fun _ : Fin 1 =>
      some ((![1, 0], ![1, 0]) : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))) = {0} := by
  decide

-- The line through zero in a coordinate direction has both nonzero scalar multiples.
example : #(puncturedLine (0 : Fin 2 → ZMod 3) ![1, 0]) = 2 := by
  rw [card_puncturedLine _ (by decide), ZMod.card]

-- Translating the anchor preserves disjointness of these independent directions.
example : Disjoint (puncturedLine (![1, 2] : Fin 2 → ZMod 3) ![1, 0])
    (puncturedLine ![1, 2] ![0, 1]) := by
  rw [disjoint_puncturedLine_iff]
  decide

-- The two nonzero multiples leading to `![2, 0]` are the only blocking directions.
example : #{v ∈ univ.erase 0 | (![2, 0] : Fin 2 → ZMod 3) ∈ puncturedLine 0 v} = 2 := by
  rw [card_filter_mem_puncturedLine (by decide), ZMod.card]

-- The anchor itself lies in no punctured line with a nonzero direction.
example : Disjoint (puncturedLine (![1, 1] : Fin 2 → ZMod 2) ![1, 0]) {![1, 1]} :=
  disjoint_singleton_right.mpr (notMem_puncturedLine_self _ (by decide))

example : #{v ∈ univ.erase 0 |
    ¬Disjoint (puncturedLine (![1, 1] : Fin 2 → ZMod 2) v) {![1, 1]}} = 0 := by
  have h := card_filter_not_disjoint_puncturedLine_le (![1, 1] : Fin 2 → ZMod 2) {![1, 1]}
  rwa [erase_singleton, card_empty, zero_mul, Nat.le_zero] at h

-- Seven repeated requests occupy the same two-point line, within the `7 * (3 - 1)` bound.
private def repeatedLines : Fin 7 → Option ((Fin 2 → ZMod 3) × (Fin 2 → ZMod 3)) :=
  fun _ => some (0, ![1, 0])

example : #(occupiedPoints repeatedLines) = 2 ∧ #(occupiedPoints repeatedLines) ≤ 14 := by
  refine ⟨by decide, ?_⟩
  have h := card_occupiedPoints_le repeatedLines
  rwa [ZMod.card] at h

/-! ### Menu lengths -/

example :
    menuLength 1 1 11 = 35 ∧
    menuLength 8 3 16 = 131 ∧
    8 * (1 + 3 * 16) < 3 * menuLength 8 3 16 ∧
    3 * menuLength 8 3 16 ≤ 8 * (1 + 3 * 16) + 3 :=
  ⟨by decide, by decide, lt_mul_menuLength 8 16 (by decide), mul_menuLength_le 8 3 16⟩

/-! ### Covering menus and collision cuts -/

-- Each candidate fails one of two states, and two entries cover both.
example : ∃ menu : Fin 2 → Bool, ∀ s : Bool, ∃ e, menu e = s :=
  exists_coveringMenu (fun s a => a = s) 1 2 (fun s => by cases s <;> decide) (by decide)

-- On the complete graph of four vertices, two of them have neighbors outside.
example : ∃ S ⊆ (univ : Finset (Fin 4)), 4 ≤ 2 * #S ∧
    ∀ v ∈ S, False ∨ ∃ w ∉ S, (⊤ : SimpleGraph (Fin 4)).Adj v w :=
  exists_collisionCut ⊤ (fun _ => False) univ fun v _ =>
    Or.inr ⟨v + 1, by simp only [SimpleGraph.top_adj, ne_eq]; omega⟩

/-! ### The collision tail with a satisfied budget -/

-- With `q = 2`, `ℓ = 10`, one request and no occupied points the budget is `256 ≤ 1023`, and
-- at most half of the `1023` directions leave the request unclean.
example (targets : Fin 1 → Fin 10 → ZMod 2) :
    #{d : Fin 1 → {v : Fin 10 → ZMod 2 // v ≠ 0} |
        2 * #{i | IsClean ∅ targets (fun j => (d j).1) i} < 1} * 2 ^ 1 ≤ (2 ^ 10 - 1) ^ 1 := by
  have h := card_filter_two_mul_card_isClean_lt_mul_two_pow_le (∅ : Finset (Fin 10 → ZMod 2))
    targets (by rw [ZMod.card, card_empty]; decide)
  rwa [ZMod.card] at h

/-! ### Universal menus -/

-- `q = 2`, one occupied line and one request: the budget is `512 * 1 * 2 ≤ 2 ^ 10`.
theorem exists_menu_zmod_two :
    ∃ menu : Fin (menuLength 1 1 (11 * 1)) → Fin 1 → Fin 11 → ZMod 2, IsUniversalMenu 1 menu :=
  exists_isUniversalMenu (by rw [ZMod.card, pow_one]) (by rw [ZMod.card]; decide) one_pos le_rfl

noncomputable instance : Fintype (GaloisField 2 2) := Fintype.ofFinite _

noncomputable instance : DecidableEq (GaloisField 2 2) := Classical.decEq _

theorem card_galoisField : Fintype.card (GaloisField 2 2) = 2 ^ 2 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card 2 2 two_ne_zero]

-- `q = 4`, eight occupied lines and three requests: the budget is `512 * 8 * 4 ≤ 4 ^ 7`.
example : ∃ menu : Fin (menuLength 8 3 (8 * 2)) → Fin 3 → Fin 8 → GaloisField 2 2,
    IsUniversalMenu 8 menu :=
  exists_isUniversalMenu card_galoisField (by rw [card_galoisField]; decide) (by decide)
    (by decide)

-- A single request is clean in some entry.
theorem exists_isClean_of_isUniversalMenu {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {ℓ g r : ℕ} {menu : Fin r → Fin 1 → Fin ℓ → K} (h : IsUniversalMenu g menu)
    (lines : Fin g → Option ((Fin ℓ → K) × (Fin ℓ → K))) (targets : Fin 1 → Fin ℓ → K) :
    ∃ e, IsClean (occupiedPoints lines) targets (menu e) 0 := by
  obtain ⟨e, clean, hcard, hclean⟩ := h.2 lines targets
  obtain ⟨i, hi⟩ := card_pos.mp (show 0 < #clean by omega)
  exact ⟨e, Subsingleton.elim i 0 ▸ hclean i hi⟩

-- An occupied target: the line through `a` in direction `a` covers the target `0`, and a menu
-- entry still serves the request at `0`.
example :
    (∃ menu : Fin (menuLength 1 1 (11 * 1)) → Fin 1 → Fin 11 → ZMod 2, ∃ e,
      IsClean (occupiedPoints fun _ : Fin 1 => some (Pi.single 0 1, Pi.single 0 1)) (fun _ => 0)
        (menu e) 0) ∧
    (0 : Fin 11 → ZMod 2) ∈
      occupiedPoints fun _ : Fin 1 => some (Pi.single 0 1, Pi.single 0 1) := by
  refine ⟨?_, by decide⟩
  obtain ⟨menu, h⟩ := exists_menu_zmod_two
  exact ⟨menu, exists_isClean_of_isUniversalMenu h _ _⟩

-- Repeated targets: the clean requests at one target have pairwise non-proportional directions.
example {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ g k r : ℕ}
    {menu : Fin r → Fin k → Fin ℓ → K} (h : IsUniversalMenu g menu)
    (lines : Fin g → Option ((Fin ℓ → K) × (Fin ℓ → K))) (u : Fin ℓ → K) :
    ∃ e, ∃ clean : Finset (Fin k), k ≤ 2 * #clean ∧
      ∀ i ∈ clean, ∀ j, j ≠ i → ∀ c : K, c ≠ 0 → menu e i ≠ c • menu e j := by
  obtain ⟨e, clean, hcard, hclean⟩ := h.2 lines fun _ => u
  exact ⟨e, clean, hcard, fun i hi j hji => disjoint_puncturedLine_iff.mp ((hclean i hi).2 j hji)⟩

end ComplexityTests.MassProduction.Menu
