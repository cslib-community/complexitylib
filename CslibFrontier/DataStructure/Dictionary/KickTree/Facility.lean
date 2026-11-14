/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Basic

/-!
# Multi-Tier Facility Layer for the `k`-Kick Tree Dynamic Dictionary

This module formalizes the multi-tier facility architecture and cubby layout of the STOC 2022
`k`-kick tree dynamic dictionary of Bender, Farach-Colton, J. Kuszmaul, W. Kuszmaul, and Liu
([BenderFarachColtonKuszmaulKuszmaulLiu2022], `arXiv:2111.00602v2`, Section 5.2, pp. 30–32):
1. **Multi-tier full cubbies** (Section 5.2, pp. 30–32): $j$-tiered 100% full cubbies with tier
   capacities $r_j$ and target ratios $t_j \cdot r_j = r_{j+1}$ for $0 \le j < k_{\text{eff}}$,
   with capacity arithmetic behind tier merging `merge_tier_length` (§5.2, p. 31; compare
   Lemma 19, p. 29 for $O(K)$ cubby construction).
2. **Single tail cubby and saturation architecture**: all non-tail cubbies are strictly 100% full
   (zero empty slots, statically enforced via `FullCubby`), while a single partially filled base
   tail cubby of capacity $r_1$ (`TailCubby`) absorbs insertions, with full-tail promotion step
   `promoteFullTail` opening a fresh empty tail.
3. **Non-hash tail replacement on deletion** (Section 5.2, p. 31): deletion from a full cubby is
   refilled by popping an element from the tail cubby (in the full algorithm, drawn with fresh
   per-operation non-hash randomness independent of hash seed $\theta$), maintaining full-cubby
   100% saturation with item count conservation theorem `totalItems_tailReplace`.
   Note: deletion directly from the tail cubby and full tail elimination (when the tail is empty)
   are deferred to subsequent stages.
4. **Tracked extensions**: dynamic resizing, deamortization, physical Word-RAM slab directories
   (`SlabDirectory`), background fallback healing (`FallbackHealer`), and remaining §5.2
   distribution invariants ($t_j / 2 \le \text{count} \le 3 t_j$, $j$-creation/destruction rebuilds)
   are tracked in issue #5186.

## Source attribution

* [BenderFarachColtonKuszmaulKuszmaulLiu2022] (`arXiv:2111.00602v2`):
  - Section 5.1 (printed pp. 27–29 / PDF pp. 28–30): fixed-capacity cubbies, local query routers,
    and Lemma 19 linear-time cubby construction.
  - Section 5.2 (printed pp. 30–32 / PDF pp. 31–33): dynamic resizing, distribution invariant
    with target ratios $t_j = (\log^{(j)} n)^2 / (\log^{(j+1)} n)^2$, saturation invariant,
    non-hash randomness for tail replacement, and Theorem 20 dynamic dictionary.

## Main definitions

* `FacilityConfig`: multi-tier capacity configuration with target ratios $t_j \cdot r_j = r_{j+1}$.
* `FacilityConfig.r1`: base capacity of tier 0 (and tail cubby).
* `FullCubby`: 100% full cubby of exact capacity $r_j$.
* `TailCubby`: partially filled base tail cubby of capacity at most $r_1$.
* `Facility`: multi-tier facility state consisting of full cubbies and a single tail cubby.
* `Facility.totalItems`: total count of items across all full cubbies and the tail cubby.
* `Facility.insertIntoTail`: insert an item into the tail cubby.
* `Facility.promoteFullTail`: promote a full tail cubby to a tier-0 full cubby.
* `Facility.tailReplace`: replace an item in a full cubby with an element popped from the
  tail cubby.

## Main results

* `totalItems_insertIntoTail`: item count conservation under tail insertion.
* `totalItems_promoteFullTail`: item count conservation under full tail promotion.
* `merge_tier_length`: capacity arithmetic for tier merging ($\sum_{i=1}^{t_j} r_j = r_{j+1}$).
* `totalItems_tailReplace`: item count conservation under tail replacement on deletion.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul, M. Liu,
  *Dynamic Dictionaries with Worst-Case Optimal Operations and Space*]
  [BenderFarachColtonKuszmaulKuszmaulLiu2022], arXiv:2111.00602.
-/

public section

namespace Cslib.DataStructure.Dictionary.KickTree

/-! ### 1. Multi-Tier Facility Configuration -/

/-- Multi-tier facility configuration parameters. Tiers are 0-indexed $0 \le j \le k_{\text{eff}}$
(corresponding to paper tiers $1 \le j \le k_{\text{eff}} + 1$, with index $j$ corresponding to
paper tier $j + 1$), where index 0 has base capacity `r1 := r 0` and adjacent tiers satisfy
$t_j \cdot r_j = r_{j+1}$. -/
structure FacilityConfig where
  /-- Largest tier index $k_{\text{eff}} \ge 1$ (providing $k_{\text{eff}} + 1$ total tiers). -/
  kEff : ℕ
  /-- Effective depth positivity. -/
  kEff_pos : 0 < kEff
  /-- Capacity of a tier-$j$ cubby $r_j > 0$ for $0 \le j \le k_{\text{eff}}$. -/
  r : Fin (kEff + 1) → ℕ
  /-- Tier capacity is positive. -/
  r_pos : ∀ j, 0 < r j
  /-- Target ratio $t_j$ of tier-$j$ cubbies forming a tier-$(j+1)$ cubby. -/
  t : Fin kEff → ℕ
  /-- Target ratio equation $t_j \cdot r_j = r_{j+1}$. -/
  t_mul_r : ∀ j : Fin kEff,
    t j * r ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ = r ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩

namespace FacilityConfig

/-- Base tier-1 capacity $r_1$. -/
@[expose] def r1 (cfg : FacilityConfig) : ℕ :=
  cfg.r ⟨0, Nat.zero_lt_succ cfg.kEff⟩

end FacilityConfig

/-! ### 2. Cubby Representation -/

/-- Full cubby storing exactly `cfg.r tier` elements (100% full, zero empty slots). -/
structure FullCubby (cfg : FacilityConfig) (α : Type*) where
  /-- Tier index $0 \le \text{tier} \le k_{\text{eff}}$. -/
  tier : Fin (cfg.kEff + 1)
  /-- Stored items. -/
  items : List α
  /-- Exactly full: length matches tier capacity `cfg.r tier`. -/
  hlen : items.length = cfg.r tier
deriving Repr

/-- Tail cubby of capacity `cfg.r1` with `items.length ≤ cfg.r1`. -/
structure TailCubby (cfg : FacilityConfig) (α : Type*) where
  /-- Stored items. -/
  items : List α
  /-- Tail capacity bound: length at most base capacity `cfg.r1`. -/
  hle : items.length ≤ cfg.r1
deriving Repr

namespace TailCubby

variable {cfg : FacilityConfig} {α : Type*}

/-- Initial empty tail cubby. -/
@[expose] def empty : TailCubby cfg α where
  items := []
  hle := Nat.zero_le _

end TailCubby

/-! ### 3. Facility State and Item Count Conservation Theorems -/

/-- Pure multi-tier facility state.
Statically enforces the saturation invariant: all cubbies in `fullCubbies` are strictly 100%
full (`FullCubby`), and `tail` is a valid bounded tail cubby (`TailCubby`). -/
structure Facility (cfg : FacilityConfig) (α : Type*) where
  /-- Ordered list of 100% full cubbies (across all tiers). -/
  fullCubbies : List (FullCubby cfg α)
  /-- Single designated tail cubby of capacity $r_1$. -/
  tail : TailCubby cfg α
deriving Repr

namespace Facility

variable {cfg : FacilityConfig} {α : Type*}

/-- Total number of items stored across the entire facility. -/
@[expose] def totalItems (F : Facility cfg α) : ℕ :=
  (F.fullCubbies.map (fun c => c.items.length)).sum + F.tail.items.length

/-- Insert an item into the facility tail. -/
@[expose] def insertIntoTail (F : Facility cfg α) (item : α) : Option (Facility cfg α) :=
  if hlt : F.tail.items.length < cfg.r1 then
    have hlen : (F.tail.items ++ [item]).length ≤ cfg.r1 := by
      simp only [List.length_append, List.length_singleton]
      omega
    some { F with tail := ⟨F.tail.items ++ [item], hlen⟩ }
  else none

/-- Inserting into tail increments the total item count by 1. -/
theorem totalItems_insertIntoTail (F : Facility cfg α) (item : α) (F' : Facility cfg α)
    (hins : F.insertIntoTail item = some F') :
    F'.totalItems = F.totalItems + 1 := by
  dsimp [insertIntoTail] at hins
  split_ifs at hins with hlt
  · cases hins
    dsimp [totalItems]
    rw [List.length_append]
    simp only [List.length_singleton]
    omega

/-- Promote a saturated full tail cubby to a tier-0 full cubby and open a fresh empty tail. -/
@[expose] def promoteFullTail (F : Facility cfg α) : Option (Facility cfg α) :=
  if hfull : F.tail.items.length = cfg.r1 then
    let newFull : FullCubby cfg α := ⟨⟨0, Nat.zero_lt_succ cfg.kEff⟩, F.tail.items, hfull⟩
    some { fullCubbies := F.fullCubbies ++ [newFull], tail := .empty }
  else none

/-- Promoting a full tail preserves the total item count. -/
theorem totalItems_promoteFullTail (F : Facility cfg α) (F' : Facility cfg α)
    (hprom : F.promoteFullTail = some F') :
    F'.totalItems = F.totalItems := by
  dsimp [promoteFullTail] at hprom
  split_ifs at hprom with hfull
  · injection hprom with hprom'
    rw [← hprom']
    simp only [totalItems, TailCubby.empty, List.map_append, List.sum_append, List.map_cons,
               List.map_nil, List.sum_cons, List.sum_nil, List.length_nil, Nat.add_zero]

/-- Capacity arithmetic behind tier merging in the $j$-destruction rebuild (`arXiv:2111.00602`
§5.2, p. 31; compare Lemma 19, p. 29 for linear-time cubby construction): merging `t_j` full
cubbies of tier `j` forms a valid full cubby of tier `j + 1`. Full dynamic ratio maintenance
and deamortization across dictionary operations are tracked in issue #5186. -/
theorem merge_tier_length (j : Fin cfg.kEff) (cubbies : List (List α))
    (hcount : cubbies.length = cfg.t j)
    (hall : ∀ l ∈ cubbies, l.length = cfg.r ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) :
    cubbies.flatten.length = cfg.r ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
  rw [List.length_flatten]
  have hmap : cubbies.map List.length =
      List.replicate cubbies.length (cfg.r ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) := by
    rw [List.eq_replicate_iff]
    simp only [List.length_map, true_and]
    intro a ha
    rcases List.mem_map.mp ha with ⟨x, hx, rfl⟩
    exact hall x hx
  rw [hmap, List.sum_replicate_nat, hcount]
  exact cfg.t_mul_r j

/-! ### 4. Non-Hash Tail Replacement on Deletion (`arXiv:2111.00602` §5.2, p. 31) -/

/-- Non-hash tail replacement: when deleting element at `slotIdx` from full cubby `cubbyIdx`,
refill the hole by popping a caller-selected item at `randIdx` from the tail cubby, keeping
the full cubby 100% full.
Returns `none` if `cubbyIdx` is out of bounds, `slotIdx` is out of bounds, or `randIdx` is out
of bounds (e.g. if the tail cubby is empty).
Note: deletion directly from the tail cubby and full tail elimination (underflow handling)
are deferred to subsequent stages. -/
@[expose] def tailReplace (F : Facility cfg α) (cubbyIdx : ℕ) (slotIdx : ℕ) (randIdx : ℕ) :
    Option (Facility cfg α) :=
  match F.fullCubbies[cubbyIdx]? with
  | some fullCubby =>
    if _hslot : slotIdx < fullCubby.items.length then
      if hrand : randIdx < F.tail.items.length then
        let replacement := F.tail.items[randIdx]
        let newFullItems := fullCubby.items.set slotIdx replacement
        have hnewLen : newFullItems.length = cfg.r fullCubby.tier := by
          dsimp [newFullItems]
          rw [List.length_set, fullCubby.hlen]
        let newTailItems := F.tail.items.eraseIdx randIdx
        have htailLen : newTailItems.length ≤ cfg.r1 := by
          dsimp [newTailItems]
          exact Nat.le_trans (List.length_eraseIdx_le F.tail.items randIdx) F.tail.hle
        let newFullCubby : FullCubby cfg α := ⟨fullCubby.tier, newFullItems, hnewLen⟩
        let newCubbies := F.fullCubbies.set cubbyIdx newFullCubby
        let newTail : TailCubby cfg α := ⟨newTailItems, htailLen⟩
        some { fullCubbies := newCubbies, tail := newTail }
      else none
    else none
  | none => none

/-- Tail replacement decrements the total item count by 1 (the deleted element is removed,
and the hole in the full cubby is filled from the tail). -/
theorem totalItems_tailReplace (F : Facility cfg α) (cIdx sIdx rIdx : ℕ) (F' : Facility cfg α)
    (hrep : F.tailReplace cIdx sIdx rIdx = some F') :
    F'.totalItems + 1 = F.totalItems := by
  dsimp [tailReplace] at hrep
  cases hfc : F.fullCubbies[cIdx]? with
  | none => simp [hfc] at hrep
  | some fullCubby =>
    simp only [hfc] at hrep
    split_ifs at hrep with hslot hrand
    · cases hrep
      dsimp [totalItems]
      have hmap : (List.set F.fullCubbies cIdx
            ⟨fullCubby.tier, fullCubby.items.set sIdx (F.tail.items[rIdx]),
             by rw [List.length_set, fullCubby.hlen]⟩).map (fun c => c.items.length) =
          F.fullCubbies.map (fun c => c.items.length) := by
        obtain ⟨hidx_lt, hget⟩ := List.getElem?_eq_some_iff.mp hfc
        rw [List.map_set]
        dsimp
        rw [List.length_set, ← hget]
        have hmap_lt : cIdx < (List.map (fun c => c.items.length) F.fullCubbies).length := by
          simpa using hidx_lt
        rw [← List.getElem_map (f := fun c => c.items.length) (l := F.fullCubbies)
          (i := cIdx) (h := hmap_lt)]
        rw [List.set_getElem_self]
      rw [hmap]
      have htail_len : (F.tail.items.eraseIdx rIdx).length + 1 = F.tail.items.length :=
        List.length_eraseIdx_add_one hrand
      omega

end Facility

end KickTree
end Dictionary
end DataStructure
end Cslib
