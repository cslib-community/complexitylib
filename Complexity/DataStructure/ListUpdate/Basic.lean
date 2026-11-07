/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Online.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.List.Basic

/-!
# The list update problem: arrangements, inversions and the cost model

This file instantiates `Cslib.DataStructure.Online.Problem` for the static list update (list
accessing) problem of [Sleator and Tarjan, *Amortized Efficiency of List Update and Paging
Rules*, Section 2][SleatorTarjan1985]; see also [Borodin and El-Yaniv, *Online Computation and
Competitive Analysis*, Chapter 1][BorodinElYaniv1998].

Over a finite universe `α`, a configuration is an **arrangement**: a duplicate-free list containing
every element of `α` (`IsArrangement`). Serving a request `r` by moving from arrangement `s` to
arrangement `s'` costs
`stepCost s r s' = inversions s s' + (s'.idxOf r + 1)`,
where `inversions s s'` counts the pairs of items in different relative order in `s` and `s'`,
and `s'.idxOf r + 1` is the 1-based position of `r` in `s'`.

## Relation to the Sleator–Tarjan cost model

In [SleatorTarjan1985], accessing the `i`th item costs `i`. Immediately after the access, the
accessed item may be moved forward at no cost ("free exchanges"), and any other exchange of
adjacent items costs `1` ("paid exchanges"). `stepCost s r s'` is the cheapest way to go from `s`
to `s'` while serving `r` in that model. Doing the paid exchanges first and then accessing `r`
costs exactly `stepCost s r s'`. Conversely, any implementation that pays for `X` exchanges,
accesses `r` at position `i` and then moves it forward `F` places satisfies
`X + i ≥ stepCost s r s'`: each adjacent exchange changes the inversion count by one, and moving
`r` forward `F` places creates `F` inversions. Every online strategy and every offline schedule
therefore costs at least as much in the Sleator–Tarjan model as in this one, and move-to-front
costs the same in both (`moveToFront`, in `Complexity.DataStructure.ListUpdate.MoveToFront`).
This justification is informal and is not formalized here.

## Main definitions

* `Cslib.DataStructure.ListUpdate.IsArrangement`: duplicate-free lists containing every element.
* `ListUpdate.inversionSet`, `ListUpdate.inversions`: ordered pairs in different relative order,
  and their number (the Kendall tau distance between the two arrangements).
* `ListUpdate.crossBefore`: items in front of `r` in one list and behind it in another.
* `ListUpdate.stepCost`, `ListUpdate.problem`: the list-update `Online.Problem`.
* `ListUpdate.accessCost`, `ListUpdate.exchangeCost`: the access and rearrangement parts of a
  schedule's cost.

## Main results

* `inversions_self`, `inversions_comm`, `inversions_triangle`, `two_mul_inversions_le`: the
  inversion count is a metric on arrangements bounded by `n (n - 1) / 2`.
* `card_filter_idxOf_lt`: in an arrangement, exactly `l.idxOf r` items precede `r`.
* `idxOf_le_card_crossBefore_add`, `card_filter_ne_add_card_crossBefore_le`,
  `idxOf_le_inversions_add`: counting items that change sides of `r`; in particular
  `l.idxOf r ≤ inversions l l' + l'.idxOf r`.
* `scheduleCost_eq_accessCost_add_exchangeCost`: cost decomposition of schedules.

## References

* [D. D. Sleator and R. E. Tarjan, *Amortized Efficiency of List Update and Paging
  Rules*][SleatorTarjan1985]
* [A. Borodin and R. El-Yaniv, *Online Computation and Competitive Analysis*][BorodinElYaniv1998]
-/

public section

namespace Cslib.DataStructure.ListUpdate

open Cslib.DataStructure.Online

variable {α : Type}

/-- An arrangement of the universe `α` is a duplicate-free list containing every element. -/
@[expose]
def IsArrangement (l : List α) : Prop :=
  l.Nodup ∧ ∀ x, x ∈ l

/-- The enumeration `Finset.univ.toList` of a finite type is an arrangement. -/
theorem isArrangement_univ_toList [Fintype α] : IsArrangement (Finset.univ : Finset α).toList :=
  ⟨Finset.nodup_toList _, fun x => Finset.mem_toList.2 (Finset.mem_univ x)⟩

/-- An arrangement lists each element of `α` exactly once. -/
theorem IsArrangement.length_eq [Fintype α] {l : List α}
    (hl : IsArrangement l) : l.length = Fintype.card α := by
  classical
  rw [← List.toFinset_card_of_nodup hl.1, ← Finset.card_univ,
    Finset.eq_univ_iff_forall.2 fun x => List.mem_toFinset.2 (hl.2 x)]

/-- The reversal of an arrangement is an arrangement. -/
theorem IsArrangement.reverse {l : List α} (hl : IsArrangement l) : IsArrangement l.reverse :=
  ⟨List.nodup_reverse.2 hl.1, fun x => List.mem_reverse.2 (hl.2 x)⟩

variable [DecidableEq α]

/-- Positions in an arrangement are injective. -/
theorem IsArrangement.idxOf_inj {l : List α} (hl : IsArrangement l) {x y : α} :
    l.idxOf x = l.idxOf y ↔ x = y :=
  List.idxOf_inj (hl.2 x)

/-- Positions in a list and its reversal add up to the length minus one. -/
theorem idxOf_reverse_add_idxOf {l : List α} (hl : l.Nodup) {x : α} (hx : x ∈ l) :
    l.reverse.idxOf x + l.idxOf x + 1 = l.length := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons a t ih =>
    obtain ⟨hat, ht⟩ := List.nodup_cons.1 hl
    rw [List.reverse_cons, List.length_cons]
    by_cases hxa : x = a
    · subst hxa
      rw [List.idxOf_append_of_notMem (fun h => hat (List.mem_reverse.1 h)), List.idxOf_cons_self,
        List.idxOf_cons_self, List.length_reverse]
    · have hxt : x ∈ t := (List.mem_cons.1 hx).resolve_left hxa
      rw [List.idxOf_append_of_mem (List.mem_reverse.2 hxt), List.idxOf_cons_ne _ (Ne.symm hxa)]
      have := ih ht hxt
      omega

/-- In an arrangement, exactly `l.idxOf r` items precede `r`. -/
theorem card_filter_idxOf_lt [Fintype α] {l : List α} (hl : IsArrangement l) (r : α) :
    (Finset.univ.filter fun x => l.idxOf x < l.idxOf r).card = l.idxOf r := by
  have h : (Finset.univ.filter fun x => l.idxOf x < l.idxOf r) =
      (l.take (l.idxOf r)).toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    exact (List.mem_take_iff_idxOf_lt (hl.2 x)).symm
  rw [h, List.toFinset_card_of_nodup (hl.1.sublist (List.take_sublist _ _)), List.length_take,
    Nat.min_eq_left List.idxOf_le_length]

/-! ### Inversions -/

/-- Ordered pairs `(x, y)` with `x` before `y` in `l` but `y` before `x` in `l'`. -/
@[expose]
def inversionSet [Fintype α] (l l' : List α) : Finset (α × α) :=
  Finset.univ.filter fun p => l.idxOf p.1 < l.idxOf p.2 ∧ l'.idxOf p.2 < l'.idxOf p.1

/-- The number of pairs of items in different relative order in `l` and `l'` (the Kendall tau
distance between two arrangements). -/
@[expose]
def inversions [Fintype α] (l l' : List α) : Nat :=
  (inversionSet l l').card

theorem mem_inversionSet [Fintype α] {l l' : List α} {x y : α} :
    (x, y) ∈ inversionSet l l' ↔ l.idxOf x < l.idxOf y ∧ l'.idxOf y < l'.idxOf x := by
  simp only [inversionSet, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp]
theorem inversions_self [Fintype α] (l : List α) : inversions l l = 0 := by
  rw [inversions, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  rintro ⟨x, y⟩ h
  rw [mem_inversionSet] at h
  omega

theorem inversions_comm [Fintype α] (l l' : List α) : inversions l l' = inversions l' l := by
  refine Finset.card_equiv (Equiv.prodComm α α) fun ⟨x, y⟩ => ?_
  rw [Equiv.prodComm_apply, Prod.swap_prod_mk, mem_inversionSet, mem_inversionSet]
  exact And.comm

/-- **Triangle inequality** for inversions through an intermediate arrangement. -/
theorem inversions_triangle [Fintype α] (l₁ : List α) {l₂ : List α} (h₂ : IsArrangement l₂)
    (l₃ : List α) : inversions l₁ l₃ ≤ inversions l₁ l₂ + inversions l₂ l₃ := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  rintro ⟨x, y⟩ h
  rw [Finset.mem_union, mem_inversionSet, mem_inversionSet]
  rw [mem_inversionSet] at h
  have hxy : x ≠ y := by
    rintro rfl
    omega
  have hne : l₂.idxOf x ≠ l₂.idxOf y := fun he => hxy (h₂.idxOf_inj.1 he)
  omega

/-- Any two lists have at most `n (n - 1) / 2` inversions, where `n = Fintype.card α`. -/
theorem two_mul_inversions_le [Fintype α] (l l' : List α) :
    2 * inversions l l' ≤ Fintype.card α * (Fintype.card α - 1) := by
  have hdisj : Disjoint (inversionSet l l') (inversionSet l' l) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h₁ h₂
    rw [mem_inversionSet] at h₁ h₂
    omega
  have hsub : inversionSet l l' ∪ inversionSet l' l ⊆ (Finset.univ : Finset α).offDiag := by
    rintro ⟨x, y⟩ h
    rw [Finset.mem_offDiag]
    refine ⟨Finset.mem_univ _, Finset.mem_univ _, fun hxy => ?_⟩
    dsimp only at hxy
    subst hxy
    rw [Finset.mem_union, mem_inversionSet, mem_inversionSet] at h
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.offDiag_card, Finset.card_univ,
    ← Nat.mul_sub_one] at hcard
  have hc := inversions_comm l l'
  unfold inversions at hc ⊢
  omega

/-- Items that precede `r` in `l` but follow it in `l'`. -/
@[expose]
def crossBefore [Fintype α] (l l' : List α) (r : α) : Finset α :=
  Finset.univ.filter fun x => l.idxOf x < l.idxOf r ∧ l'.idxOf r < l'.idxOf x

theorem mem_crossBefore [Fintype α] {l l' : List α} {r x : α} :
    x ∈ crossBefore l l' r ↔ l.idxOf x < l.idxOf r ∧ l'.idxOf r < l'.idxOf x := by
  simp only [crossBefore, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The embedding `x ↦ (x, r)`. -/
private def pairRight (r : α) : α ↪ α × α :=
  ⟨fun x => (x, r), fun _ _ h => congrArg Prod.fst h⟩

/-- The inversions avoiding `r` and the inversions `(x, r)` are disjoint parts of all inversions. -/
theorem card_filter_ne_add_card_crossBefore_le [Fintype α] (l l' : List α) (r : α) :
    ((inversionSet l l').filter fun p => p.1 ≠ r ∧ p.2 ≠ r).card + (crossBefore l l' r).card ≤
      inversions l l' := by
  rw [← Finset.card_map (pairRight r), ← Finset.card_union_of_disjoint]
  · refine Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) ?_)
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hp
    exact mem_inversionSet.2 (mem_crossBefore.1 hx)
  · rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 hp₂
    exact (Finset.mem_filter.1 hp₁).2.2 rfl

/-- Items in front of `r` in `l` are either in front of `r` in `l'` or in `crossBefore l l' r`. -/
theorem idxOf_le_card_crossBefore_add [Fintype α] {l l' : List α}
    (hl : IsArrangement l) (hl' : IsArrangement l') (r : α) :
    l.idxOf r ≤ (crossBefore l l' r).card + l'.idxOf r := by
  rw [← card_filter_idxOf_lt hl r, ← card_filter_idxOf_lt hl' r]
  refine le_trans (Finset.card_le_card ?_) ((Finset.card_union_le _ _).trans_eq (Nat.add_comm _ _))
  intro x hx
  rw [Finset.mem_union, mem_crossBefore]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  have hxr : x ≠ r := by
    rintro rfl
    omega
  have hne : l'.idxOf x ≠ l'.idxOf r := fun he => hxr (hl'.idxOf_inj.1 he)
  omega

/-- If `r` sits at position `l.idxOf r` in `l`, then moving to `l'` either creates inversions or
keeps the items in front of `r`: `l.idxOf r ≤ inversions l l' + l'.idxOf r`. -/
theorem idxOf_le_inversions_add [Fintype α] {l l' : List α} (hl : IsArrangement l)
    (hl' : IsArrangement l') (r : α) : l.idxOf r ≤ inversions l l' + l'.idxOf r := by
  have h₁ := idxOf_le_card_crossBefore_add hl hl' r
  have h₂ := card_filter_ne_add_card_crossBefore_le l l' r
  omega

/-! ### The list-update problem -/

/-- Cost of serving request `r` by moving from arrangement `s` to arrangement `s'`: the inversions
between `s` and `s'` (paid exchanges) plus the 1-based position of `r` in `s'` (access). -/
@[expose]
def stepCost [Fintype α] (s : List α) (r : α) (s' : List α) : Nat :=
  inversions s s' + (s'.idxOf r + 1)

/-- The list-update `Online.Problem` over a finite universe `α`: configurations are arrangements,
every arrangement is reachable in one step, and `stepCost` charges rearrangement plus access. -/
abbrev problem (α : Type) [Fintype α] [DecidableEq α] : Problem where
  State := List α
  Req := α
  ValidInit := IsArrangement
  ValidStep s _ s' := IsArrangement s ∧ IsArrangement s'
  stepCost := stepCost

/-- Total access cost `∑ᵢ pos(rᵢ, sᵢ)` of a schedule. -/
@[expose]
def accessCost : List α → List (List α) → Nat
  | r :: rs, s' :: ss => (s'.idxOf r + 1) + accessCost rs ss
  | _, _ => 0

/-- Total rearrangement cost `∑ᵢ inversions(sᵢ₋₁, sᵢ)` of a schedule starting at `s`. -/
@[expose]
def exchangeCost [Fintype α] (s : List α) : List α → List (List α) → Nat
  | _ :: rs, s' :: ss => inversions s s' + exchangeCost s' rs ss
  | _, _ => 0

/-- The cost of a schedule splits into access cost and rearrangement cost. -/
theorem scheduleCost_eq_accessCost_add_exchangeCost [Fintype α] (s : List α) (reqs : List α)
    (states : List (List α)) :
    (problem α).scheduleCost s reqs states =
      accessCost reqs states + exchangeCost s reqs states := by
  induction reqs generalizing s states with
  | nil => cases states <;> rfl
  | cons r rs ih =>
    cases states with
    | nil => rfl
    | cons s' ss =>
      change stepCost s r s' + (problem α).scheduleCost s' rs ss =
        (s'.idxOf r + 1 + accessCost rs ss) + (inversions s s' + exchangeCost s' rs ss)
      rw [ih, stepCost]
      omega

end Cslib.DataStructure.ListUpdate
