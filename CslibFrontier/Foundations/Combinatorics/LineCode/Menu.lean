/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.LineCode.Basic
import CslibFrontier.Foundations.Combinatorics.LineCode.Line
import CslibFrontier.Foundations.Combinatorics.LineCode.Menu.Collision
import CslibFrontier.Foundations.Combinatorics.LineCode.Menu.Counting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Universal recovery menus

Let `K` be a field with `q = 2 ^ b` elements and let `L = ℓ * b`, so that a point of `K ^ ℓ`
takes `L` bits. A state of the scheduler consists of at most `g` occupied lines, each given by an
anchor and a direction, and a tuple of `k ≤ g` targets; there are at most `2 ^ (g * (1 + 3 * L))`
states. Under the budget `512 * g * q ≤ q ^ (ℓ - 1)`, a uniformly random tuple of nonzero
directions leaves fewer than half of the requests clean with probability at most `2 ^ (-k)` in
every state (`card_filter_two_mul_card_isClean_lt_mul_two_pow_le`). A list of
`menuLength g k L` independent tuples therefore fails some state with probability less than
one (`exists_coveringMenu`), so a universal menu of that length exists.

For `k > 0`, `menuLength g k L = ⌊g * (1 + 3 * L) / k⌋ + 1`; evaluating every entry of such a menu
examines `k * menuLength g k L ≤ g * (1 + 3 * L) + k` candidate lines.

## Main definitions

* `Cslib.LineCode.menuLength`: the length of the universal menus.

## Main results

* `Cslib.LineCode.lt_mul_menuLength`, `Cslib.LineCode.mul_menuLength_le`: bounds on the number
  `k * menuLength g k L` of candidate lines.
* `Cslib.LineCode.exists_isUniversalMenu`: universal menus exist under the budget.

## References

* Adapted, with nonzero vectors in place of projective directions, from
  MassProduction/Nonuniform/PhaseMenu.lean, MassProduction/Nonuniform/BinaryPhaseMenu.lean
  and MassProduction/Nonuniform/Menu.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.LineCode

open Finset

/-- The length of the universal menus for `k` pending requests, `g` occupied lines and points of
`L` bits: `⌊g * (1 + 3 * L) / k⌋ + 1`, the least `r` with `g * (1 + 3 * L) < k * r` when
`0 < k`. -/
def menuLength (g k L : ℕ) : ℕ := (g * (1 + 3 * L) + k) / k

/-- A menu of length `menuLength g k L` has more than `g * (1 + 3 * L)` candidate lines. -/
theorem lt_mul_menuLength (g L : ℕ) {k : ℕ} (hk : 0 < k) :
    g * (1 + 3 * L) < k * menuLength g k L := by
  rw [menuLength, Nat.add_div_right _ hk]
  exact Nat.lt_mul_div_succ _ hk

/-- A menu of length `menuLength g k L` has at most `g * (1 + 3 * L) + k` candidate lines. -/
theorem mul_menuLength_le (g k L : ℕ) : k * menuLength g k L ≤ g * (1 + 3 * L) + k :=
  Nat.mul_div_le _ _

/-- There are at most `2 ^ (g * (1 + 3 * L))` states of `g` optional lines and `k ≤ g` targets
when a point takes `L = ℓ * b` bits. -/
private theorem card_state_le {K : Type*} [Fintype K] {b g k ℓ : ℕ}
    (hK : Fintype.card K = 2 ^ b) (hkg : k ≤ g) :
    Fintype.card ((Fin g → Option ((Fin ℓ → K) × (Fin ℓ → K))) × (Fin k → Fin ℓ → K)) ≤
      2 ^ (g * (1 + 3 * (ℓ * b))) := by
  have hN : Fintype.card (Fin ℓ → K) = 2 ^ (ℓ * b) := by
    rw [Fintype.card_fun, Fintype.card_fin, hK, ← pow_mul, mul_comm]
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_option,
    Fintype.card_prod, hN, Fintype.card_fun, Fintype.card_fin, hN]
  have hslot : 2 ^ (ℓ * b) * 2 ^ (ℓ * b) + 1 ≤ 2 ^ (1 + 2 * (ℓ * b)) := by
    have h1 : 1 ≤ 2 ^ (ℓ * b) * 2 ^ (ℓ * b) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [pow_add, two_mul, pow_add, pow_one]
    linarith
  calc (2 ^ (ℓ * b) * 2 ^ (ℓ * b) + 1) ^ g * (2 ^ (ℓ * b)) ^ k
      ≤ (2 ^ (1 + 2 * (ℓ * b))) ^ g * (2 ^ (ℓ * b)) ^ g :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hslot g)
          (Nat.pow_le_pow_right (by positivity) hkg)
    _ = 2 ^ (g * (1 + 3 * (ℓ * b))) := by
        rw [← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring

/-- **Universal menus.** Let `K` have `q = 2 ^ b` elements, let `0 < k ≤ g`, and suppose
`512 * g * q ≤ q ^ (ℓ - 1)`. Then some menu of `menuLength g k (ℓ * b)` tuples of nonzero
directions for `k` requests is universal for `g` occupied lines: for every list of at most `g`
occupied lines and every tuple of `k` targets, possibly repeated or occupied, some entry leaves at
least half of the requests clean. -/
theorem exists_isUniversalMenu {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ b g k : ℕ}
    (hK : Fintype.card K = 2 ^ b)
    (hbudget : 512 * g * Fintype.card K ≤ Fintype.card K ^ (ℓ - 1)) (hk : 0 < k) (hkg : k ≤ g) :
    ∃ menu : Fin (menuLength g k (ℓ * b)) → Fin k → Fin ℓ → K, IsUniversalMenu g menu := by
  set q := Fintype.card K
  have hq : 1 < q := Fintype.one_lt_card
  have hℓ : ℓ ≠ 0 := by
    rintro rfl
    rw [Nat.zero_sub, pow_zero] at hbudget
    nlinarith
  have hdim : q ^ (ℓ - 1) * (q - 1) ≤ q ^ ℓ - 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.mul_sub_one, pow_succ]
    exact Nat.sub_le_sub_left (Nat.one_le_pow _ _ (by omega)) _
  have : Nonempty {v : Fin ℓ → K // v ≠ 0} := Fintype.card_pos_iff.mp (by
    rw [card_subtype_ne_zero]
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow hℓ hq))
  have hbad : ∀ s : (Fin g → Option ((Fin ℓ → K) × (Fin ℓ → K))) × (Fin k → Fin ℓ → K),
      #{d : Fin k → {v : Fin ℓ → K // v ≠ 0} |
          ¬k ≤ 2 * #{i | IsClean (occupiedPoints s.1) s.2 (fun j => (d j).1) i}} * 2 ^ k ≤
        Fintype.card (Fin k → {v : Fin ℓ → K // v ≠ 0}) := by
    intro s
    have hO := card_occupiedPoints_le s.1
    have hbudget' : 256 * ((#(occupiedPoints s.1) + k * (q - 1)) * (q - 1)) ≤ q ^ ℓ - 1 :=
      calc 256 * ((#(occupiedPoints s.1) + k * (q - 1)) * (q - 1))
          ≤ 256 * ((g * (q - 1) + g * (q - 1)) * (q - 1)) := by gcongr
        _ = 512 * g * (q - 1) * (q - 1) := by ring
        _ ≤ 512 * g * q * (q - 1) := by gcongr; exact Nat.sub_le _ _
        _ ≤ q ^ (ℓ - 1) * (q - 1) := Nat.mul_le_mul_right _ hbudget
        _ ≤ q ^ ℓ - 1 := hdim
    rw [Fintype.card_fun, Fintype.card_fin, card_subtype_ne_zero]
    refine le_trans (Nat.mul_le_mul_right _ (card_le_card fun d hd => ?_))
      (card_filter_two_mul_card_isClean_lt_mul_two_pow_le _ s.2 hbudget')
    exact mem_filter.mpr ⟨mem_univ _, not_le.mp (mem_filter.mp hd).2⟩
  obtain ⟨menu, hmenu⟩ := exists_coveringMenu
    (σ := (Fin g → Option ((Fin ℓ → K) × (Fin ℓ → K))) × (Fin k → Fin ℓ → K))
    (α := Fin k → {v : Fin ℓ → K // v ≠ 0})
    (fun s d => k ≤ 2 * #{i | IsClean (occupiedPoints s.1) s.2 (fun j => (d j).1) i})
    k (menuLength g k (ℓ * b)) hbad
    ((card_state_le hK hkg).trans_lt
      (Nat.pow_lt_pow_right one_lt_two (lt_mul_menuLength g (ℓ * b) hk)))
  refine ⟨fun e i => (menu e i).1, fun e i => (menu e i).2, fun lines targets => ?_⟩
  obtain ⟨e, he⟩ := hmenu (lines, targets)
  exact ⟨e, _, he, fun i hi => (mem_filter.mp hi).2⟩

end Cslib.LineCode
