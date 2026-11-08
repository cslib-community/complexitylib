/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.ListUpdate.Basic

/-!
# Move-to-front is 2-competitive for list update

This file formalizes Theorem 1 of [Sleator and Tarjan, *Amortized Efficiency of List Update and
Paging Rules*, Section 2][SleatorTarjan1985] in the list-update model of
`Complexity.DataStructure.ListUpdate.Basic`. It includes the generalization stated after the proof,
where the online and offline lists start from different arrangements.

The **move-to-front** strategy `mtf` serves request `r` by moving `r` to the front of its list,
without changing the relative order of the other items. It pays exactly the position of `r`
(`stepCost_moveToFront`). For every offline schedule serving `m` requests, starting from an
arrangement `s₀` while move-to-front starts from `m₀`,
`cost_MTF + inversions(final MTF list, final offline list) + m ≤`
`2 * accessCost + exchangeCost + inversions m₀ s₀`
(`mtf_cost_add_inversions_add_length_le`). This is the Sleator–Tarjan bound
`C_MF(s) ≤ 2 C_A(s) + X_A(s) - F_A(s) - m + I`, with the offline schedule's paid and free
exchanges accounted for by `exchangeCost`, which counts the inversions between consecutive
offline arrangements. The module docstring of `Complexity.DataStructure.ListUpdate.Basic` gives
the informal translation between the two cost models; it is not formalized.

The proof uses the Sleator–Tarjan potential, the number of inversions between move-to-front's list
and the offline list. Serving `r` costs move-to-front `k = pos(r)`. Moving `r` to the front creates
at most `pos_A(r) - 1` new inversions and destroys at least `k - pos_A(r)` old ones, for an
amortized cost of at most `2 pos_A(r) - 1` (`inversions_moveToFront_le`). A rearrangement by the
offline schedule raises the potential by at most its own cost (`inversions_triangle`).

## Main definitions

* `Cslib.DataStructure.ListUpdate.moveToFront`: move an item to the front of a list.
* `ListUpdate.mtf`: the move-to-front online strategy.

## Main results

* `stepCost_moveToFront`: move-to-front pays exactly the position of the requested item.
* `inversions_moveToFront_le`: the amortized step inequality.
* `mtf_cost_add_inversions_add_length_le`: [SleatorTarjan1985], Theorem 1 with different initial
  lists.
* `mtf_isCompetitive`, `mtf_isCompetitiveAnyInit`: move-to-front is `(2, 0)`-competitive from a
  common initial arrangement and `(2, n (n - 1) / 2)`-competitive from arbitrary arrangements.

## References

* [D. D. Sleator and R. E. Tarjan, *Amortized Efficiency of List Update and Paging
  Rules*][SleatorTarjan1985]
-/

public section

namespace Cslib.DataStructure.ListUpdate

open Cslib.DataStructure.Online

variable {α : Type} [DecidableEq α]

/-- Move `r` to the front of `l`, keeping the relative order of the other items. -/
@[expose]
def moveToFront (r : α) (l : List α) : List α :=
  r :: l.erase r

@[simp]
theorem idxOf_moveToFront_self (r : α) (l : List α) : (moveToFront r l).idxOf r = 0 :=
  List.idxOf_cons_self

theorem idxOf_moveToFront_of_ne {r x : α} (h : x ≠ r) (l : List α) :
    (moveToFront r l).idxOf x = (l.erase r).idxOf x + 1 :=
  List.idxOf_cons_ne _ (Ne.symm h)

/-- Erasing `r` keeps the relative order of the other items. -/
theorem idxOf_erase_lt_iff {r x y : α} (hx : x ≠ r) (hy : y ≠ r) (l : List α) :
    (l.erase r).idxOf x < (l.erase r).idxOf y ↔ l.idxOf x < l.idxOf y := by
  induction l with
  | nil => exact Iff.rfl
  | cons a t ih =>
    by_cases har : a = r
    · subst har
      rw [List.erase_cons_head, List.idxOf_cons_ne _ (Ne.symm hx),
        List.idxOf_cons_ne _ (Ne.symm hy)]
      omega
    · rw [List.erase_cons_tail (by simpa using har)]
      simp only [List.idxOf_cons, beq_iff_eq]
      split_ifs <;> omega

/-- Moving `r` to the front keeps the relative order of the other items. -/
theorem idxOf_moveToFront_lt_iff {r x y : α} (hx : x ≠ r) (hy : y ≠ r) (l : List α) :
    (moveToFront r l).idxOf x < (moveToFront r l).idxOf y ↔ l.idxOf x < l.idxOf y := by
  rw [idxOf_moveToFront_of_ne hx, idxOf_moveToFront_of_ne hy, Nat.add_lt_add_iff_right,
    idxOf_erase_lt_iff hx hy]

/-- Moving an item to the front of an arrangement gives an arrangement. -/
theorem isArrangement_moveToFront {l : List α} (hl : IsArrangement l) (r : α) :
    IsArrangement (moveToFront r l) := by
  refine ⟨List.nodup_cons.2 ⟨fun h => ((hl.1.mem_erase_iff).1 h).1 rfl, hl.1.erase r⟩, fun x => ?_⟩
  by_cases hx : x = r
  · exact hx ▸ List.mem_cons_self
  · exact List.mem_cons_of_mem _ ((hl.1.mem_erase_iff).2 ⟨hx, hl.2 x⟩)

/-- The move-to-front strategy for list update over the finite universe `α`. -/
abbrev mtf (α : Type) [Fintype α] [DecidableEq α] : DetStrategy (problem α) where
  Mem := List α
  ValidMem := IsArrangement
  project := id
  init := id
  step m r := moveToFront r m
  valid_init h := ⟨h, rfl⟩
  valid_step r h := ⟨isArrangement_moveToFront h r, h, isArrangement_moveToFront h r⟩

variable [Fintype α]

/-- Moving `r` to the front creates exactly `l.idxOf r` inversions. -/
theorem inversions_moveToFront {l : List α} (hl : IsArrangement l) (r : α) :
    inversions l (moveToFront r l) = l.idxOf r := by
  refine le_antisymm ?_ ?_
  · rw [← card_filter_idxOf_lt hl r, ← Finset.card_map (Function.Embedding.sectL α r)]
    refine Finset.card_le_card fun ⟨x, y⟩ h => ?_
    rw [mem_inversionSet] at h
    have hyr : y = r := by
      by_contra hyr
      by_cases hxr : x = r
      · subst hxr
        rw [idxOf_moveToFront_self] at h
        omega
      · have := (idxOf_moveToFront_lt_iff hyr hxr l).1 h.2
        omega
    subst hyr
    refine Finset.mem_map.2 ⟨x, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h.1⟩
  · have := idxOf_le_inversions_add hl (isArrangement_moveToFront hl r) r
    rwa [idxOf_moveToFront_self, Nat.add_zero] at this

/-- Move-to-front pays exactly the position of the requested item. -/
theorem stepCost_moveToFront {l : List α} (hl : IsArrangement l) (r : α) :
    stepCost l r (moveToFront r l) = l.idxOf r + 1 := by
  rw [stepCost, inversions_moveToFront hl, idxOf_moveToFront_self]

/-- **Amortized step inequality** ([SleatorTarjan1985], proof of Theorem 1): if `r` is at
position `k = m.idxOf r + 1` in move-to-front's list and at position `i = L.idxOf r + 1` in the
offline list, then moving `r` to the front changes the potential by at most `2i - 1 - k`. -/
theorem inversions_moveToFront_le {m L : List α} (hm : IsArrangement m) (hL : IsArrangement L)
    (r : α) :
    m.idxOf r + 1 + inversions (moveToFront r m) L ≤ 2 * (L.idxOf r + 1) - 1 + inversions m L := by
  have hsub : inversionSet (moveToFront r m) L ⊆
      (Finset.univ.filter fun y => L.idxOf y < L.idxOf r).map (Function.Embedding.sectR r α) ∪
        (inversionSet m L).filter fun p => p.1 ≠ r ∧ p.2 ≠ r := by
    rintro ⟨x, y⟩ h
    rw [mem_inversionSet] at h
    rw [Finset.mem_union, Finset.mem_filter, mem_inversionSet]
    by_cases hxr : x = r
    · subst hxr
      left
      refine Finset.mem_map.2 ⟨y, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h.2⟩
    · by_cases hyr : y = r
      · subst hyr
        rw [idxOf_moveToFront_self] at h
        omega
      · right
        exact ⟨⟨(idxOf_moveToFront_lt_iff hxr hyr m).1 h.1, h.2⟩, hxr, hyr⟩
  have h₁ := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_map, card_filter_idxOf_lt hL r] at h₁
  have h₂ := card_filter_ne_add_card_crossBefore_le m L r
  have h₃ := idxOf_le_card_crossBefore_add hm hL r
  unfold inversions at h₂ ⊢
  omega

/-- **Move-to-front bound** ([SleatorTarjan1985], Theorem 1 and the remark after its proof): for
every valid offline schedule `states` serving `reqs` from `s₀`, move-to-front started from `m₀`
satisfies `cost + inversions(final lists) + |reqs| ≤ 2 * accessCost + exchangeCost +`
`inversions m₀ s₀`. -/
theorem mtf_costFrom_add_inversions_add_length_le {m₀ s₀ : List α} (hm₀ : IsArrangement m₀)
    (hs₀ : IsArrangement s₀) {reqs : List α} {states : List (List α)}
    (hv : (problem α).ValidSchedule s₀ reqs states) :
    (mtf α).costFrom m₀ reqs +
        inversions ((mtf α).runMem m₀ reqs) ((problem α).finalState s₀ states) + reqs.length ≤
      2 * accessCost reqs states + exchangeCost s₀ reqs states + inversions m₀ s₀ := by
  induction reqs generalizing m₀ s₀ states with
  | nil =>
    cases states with
    | nil =>
      change 0 + inversions m₀ s₀ + 0 ≤ 2 * 0 + 0 + inversions m₀ s₀
      omega
    | cons _ _ => exact absurd hv id
  | cons r rs ih =>
    cases states with
    | nil => exact absurd hv id
    | cons s' ss =>
      obtain ⟨⟨-, hs'⟩, hrest⟩ := hv
      have hm' := isArrangement_moveToFront hm₀ r
      have hih := ih hm' hs' hrest
      have hstep := inversions_moveToFront_le hm₀ hs' r
      have htri := inversions_triangle m₀ hs₀ s'
      have hcost := stepCost_moveToFront hm₀ r
      change stepCost m₀ r (moveToFront r m₀) + (mtf α).costFrom (moveToFront r m₀) rs +
          inversions ((mtf α).runMem (moveToFront r m₀) rs) ((problem α).finalState s' ss) +
          (rs.length + 1) ≤
        2 * (s'.idxOf r + 1 + accessCost rs ss) + (inversions s₀ s' + exchangeCost s' rs ss) +
          inversions m₀ s₀
      omega

/-- [SleatorTarjan1985], Theorem 1 with different initial lists, for `DetStrategy.cost`. -/
theorem mtf_cost_add_inversions_add_length_le {m₀ s₀ : List α} (hm₀ : IsArrangement m₀)
    (hs₀ : IsArrangement s₀) {reqs : List α} {states : List (List α)}
    (hv : (problem α).ValidSchedule s₀ reqs states) :
    (mtf α).cost m₀ reqs +
        inversions ((mtf α).runMem m₀ reqs) ((problem α).finalState s₀ states) + reqs.length ≤
      2 * accessCost reqs states + exchangeCost s₀ reqs states + inversions m₀ s₀ := by
  rw [(mtf α).cost_eq_costFrom hm₀]
  exact mtf_costFrom_add_inversions_add_length_le hm₀ hs₀ hv

/-- Move-to-front costs at most twice any offline schedule, plus the initial inversions:
`cost_MTF ≤ 2 * cost_A - |reqs| + inversions m₀ s₀`. -/
theorem mtf_cost_add_length_le {m₀ s₀ : List α} (hm₀ : IsArrangement m₀)
    (hs₀ : IsArrangement s₀) {reqs : List α} {states : List (List α)}
    (hv : (problem α).ValidSchedule s₀ reqs states) :
    (mtf α).cost m₀ reqs + reqs.length ≤
      2 * (problem α).scheduleCost s₀ reqs states + inversions m₀ s₀ := by
  have h := mtf_cost_add_inversions_add_length_le hm₀ hs₀ hv
  rw [scheduleCost_eq_accessCost_add_exchangeCost]
  omega

/-- Move-to-front is `(2, 0)`-competitive from a common initial arrangement. -/
theorem mtf_isCompetitive : (mtf α).IsCompetitive 2 0 := by
  intro s₀ hs₀ reqs states hv
  have h := mtf_cost_add_length_le hs₀ hs₀ hv
  rw [inversions_self] at h
  omega

/-- Move-to-front is `(2, n (n - 1) / 2)`-competitive across arbitrary initial arrangements, where
`n = Fintype.card α`. -/
theorem mtf_isCompetitiveAnyInit :
    (mtf α).IsCompetitiveAnyInit 2 (Fintype.card α * (Fintype.card α - 1) / 2) := by
  intro m₀ s₀ reqs states hm₀ hs₀ hv
  have h := mtf_cost_add_length_le hm₀ hs₀ hv
  have hI := two_mul_inversions_le m₀ s₀
  omega

end Cslib.DataStructure.ListUpdate
