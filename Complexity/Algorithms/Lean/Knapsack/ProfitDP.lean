/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Order.Basic

/-!
# The knapsack dynamic program by profit

Items of a type `ι` have weights `w : ι → ℕ` and profits `p : ι → ℕ`. A selection is a
subsequence of the list of items; it is feasible for a capacity `B` when its total weight is at
most `B`. The dynamic program by profit computes, for every profit `q` up to the total profit, a
minimum-weight subsequence of profit exactly `q` (`Cslib.Algorithms.Lean.Knapsack.profitTable`),
and then returns a most profitable feasible entry (`Cslib.Algorithms.Lean.Knapsack.profitDP`). The
table has `(l.map p).sum + 1` entries, so the program is pseudo-polynomial: polynomial in the
number of items and the total profit [Williamson and Shmoys, Section 3.1][WilliamsonShmoys2011].
Williamson and Shmoys's Algorithm 3.1 keeps the non-dominated `(weight, profit)` pairs instead;
indexing by profit gives the same optimum with a simpler invariant.

Adding an item `a` maps the table `T` to the table whose entry `q` is the lighter of `T[q]` and
`T[q - p a]` extended by `a` (`Cslib.Algorithms.Lean.Knapsack.profitStep`). By induction on the
items, every entry of profit `q` is a subsequence of profit `q`, and for every subsequence `s`
the entry at profit `p(s)` weighs at most `w(s)` (`Cslib.Algorithms.Lean.Knapsack.TableSpec`).

## Main definitions

* `Cslib.Algorithms.Lean.Knapsack.profitTable`: the table of minimum-weight selections by profit.
* `Cslib.Algorithms.Lean.Knapsack.profitDP`: the exact dynamic program.

## Main results

* `Cslib.Algorithms.Lean.Knapsack.tableSpec_profitTable`: soundness and completeness of the table.
* `Cslib.Algorithms.Lean.Knapsack.profitDP_sublist`,
  `Cslib.Algorithms.Lean.Knapsack.sum_map_profitDP_le`: the program returns a feasible selection.
* `Cslib.Algorithms.Lean.Knapsack.sum_map_le_profitDP`: it is optimal among feasible selections.

## References

* [D. P. Williamson, D. B. Shmoys, *The Design of Approximation Algorithms*][WilliamsonShmoys2011]
-/

public section

namespace Cslib.Algorithms.Lean.Knapsack

open scoped List

variable {ι : Type*} (w p : ι → ℕ)

/-! ### The dynamic program -/

/-- The lighter of two optional selections, preferring the first on ties. -/
@[expose] def lighter (x y : Option (List ι)) : Option (List ι) :=
  x.elim y fun s => y.elim (some s) fun t =>
    if (t.map w).sum < (s.map w).sum then some t else some s

/-- One step of the dynamic program by profit: entry `q` of the new table is the lighter of the
old entry `q` and the old entry `q - p a` extended by `a`. -/
@[expose] def profitStep (T : List (Option (List ι))) (a : ι) : List (Option (List ι)) :=
  List.zipWith (lighter w) (T ++ List.replicate (p a) none)
    (List.replicate (p a) none ++ T.map (Option.map (· ++ [a])))

/-- The profit table of `l`: entry `q` is a minimum-weight subsequence of `l` of profit `q`, or
`none` if there is none. -/
@[expose] def profitTable (l : List ι) : List (Option (List ι)) :=
  l.foldl (profitStep w p) [some []]

/-- One step of the selection scan: replace the current choice by an entry within the capacity of
at least its profit. -/
@[expose] def selectStep (B : ℕ) (best : List ι) (x : Option (List ι)) : List ι :=
  x.elim best fun s =>
    if (s.map w).sum ≤ B ∧ (best.map p).sum ≤ (s.map p).sum then s else best

/-- **The dynamic program by profit** with capacity `B`. -/
@[expose] def profitDP (B : ℕ) (l : List ι) : List ι :=
  (profitTable w p l).foldl (selectStep w p B) []

/-! ### Correctness -/

variable {w p}

/-- The lighter of two selections is one of them. -/
theorem lighter_eq_some {x y : Option (List ι)} {s : List ι} (h : lighter w x y = some s) :
    x = some s ∨ y = some s := by
  cases x with
  | none => exact Or.inr h
  | some t =>
    cases y with
    | none => exact Or.inl h
    | some u =>
      simp only [lighter, Option.elim_some] at h
      split_ifs at h
      · exact Or.inr h
      · exact Or.inl h

/-- The lighter of a selection and anything weighs at most the selection. -/
theorem exists_lighter_left (s : List ι) (y : Option (List ι)) :
    ∃ r, lighter w (some s) y = some r ∧ (r.map w).sum ≤ (s.map w).sum := by
  cases y with
  | none => exact ⟨s, rfl, le_rfl⟩
  | some t =>
    simp only [lighter, Option.elim_some]
    split_ifs with h
    · exact ⟨t, rfl, h.le⟩
    · exact ⟨s, rfl, le_rfl⟩

/-- The lighter of anything and a selection weighs at most the selection. -/
theorem exists_lighter_right (x : Option (List ι)) (t : List ι) :
    ∃ r, lighter w x (some t) = some r ∧ (r.map w).sum ≤ (t.map w).sum := by
  cases x with
  | none => exact ⟨t, rfl, le_rfl⟩
  | some s =>
    simp only [lighter, Option.elim_some]
    split_ifs with h
    · exact ⟨t, rfl, le_rfl⟩
    · exact ⟨s, rfl, not_lt.mp h⟩

/-- The entries of one step of the dynamic program. -/
theorem getElem?_profitStep (T : List (Option (List ι))) (a : ι) (q : ℕ) :
    (profitStep w p T a)[q]? =
      if q < T.length + p a then
        some (lighter w (T.getD q none)
          (if p a ≤ q then (T.getD (q - p a) none).map (· ++ [a]) else none))
      else none := by
  unfold profitStep
  rw [List.getElem?_zipWith]
  by_cases hq : q < T.length + p a
  · rw [ite_eq_left hq]
    have hX : (T ++ List.replicate (p a) none)[q]? = some (T.getD q none) := by
      by_cases h1 : q < T.length
      · rw [List.getElem?_append_left h1, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem h1]
        rfl
      · rw [List.getElem?_append_right (by omega), List.getElem?_replicate,
          ite_eq_left (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
    have hY : (List.replicate (p a) none ++ T.map (Option.map (· ++ [a])))[q]? =
        some (if p a ≤ q then (T.getD (q - p a) none).map (· ++ [a]) else none) := by
      by_cases h1 : q < p a
      · rw [List.getElem?_append_left (by simpa using h1), List.getElem?_replicate,
          ite_eq_left h1, ite_eq_right (by omega)]
      · rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega),
          List.getElem?_map, ite_eq_left (by omega), List.length_replicate,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        rfl
    rw [hX, hY]
  · have hlen : (T ++ List.replicate (p a) none).length ≤ q := by
      simp only [List.length_append, List.length_replicate]
      omega
    rw [ite_eq_right hq, List.getElem?_eq_none hlen]

private theorem getD_eq_some {T : List (Option (List ι))} {q : ℕ} {s : List ι}
    (h : T.getD q none = some s) : T[q]? = some (some s) := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hT : T[q]? with
  | none => rw [hT] at h; exact absurd h (by simp)
  | some x => rw [hT] at h; exact congrArg some h

/-- The invariant of the profit table of `l`: its length, and soundness and completeness of its
entries. -/
structure TableSpec (w p : ι → ℕ) (l : List ι) (T : List (Option (List ι))) : Prop where
  /-- The table has an entry for every profit up to the total profit. -/
  length_eq : T.length = (l.map p).sum + 1
  /-- Every entry of profit `q` is a subsequence of profit `q`. -/
  sound : ∀ q s, T[q]? = some (some s) → s <+ l ∧ (s.map p).sum = q
  /-- For every subsequence, the entry at its profit weighs at most as much. -/
  complete : ∀ s, s <+ l →
    ∃ r, T[(s.map p).sum]? = some (some r) ∧ (r.map w).sum ≤ (s.map w).sum

/-- The initial table holds the empty selection at profit `0`. -/
theorem tableSpec_nil : TableSpec w p [] [some []] where
  length_eq := rfl
  sound q s h := by
    cases q with
    | zero =>
      obtain rfl : [] = s := by simpa using h
      simp
    | succ q => simp at h
  complete s hs := by
    rw [List.sublist_nil.mp hs]
    exact ⟨[], rfl, le_rfl⟩

/-- One step of the dynamic program preserves the invariant. -/
theorem TableSpec.step {l : List ι} {T : List (Option (List ι))} (hT : TableSpec w p l T)
    (a : ι) : TableSpec w p (l ++ [a]) (profitStep w p T a) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [profitStep, List.length_zipWith, List.length_append, List.length_replicate,
      List.length_map, hT.length_eq, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · intro q s h
    rw [getElem?_profitStep] at h
    by_cases hq : q < T.length + p a
    · rw [ite_eq_left hq, Option.some.injEq] at h
      rcases lighter_eq_some h with hx | hy
      · obtain ⟨hs, hsum⟩ := hT.sound q s (getD_eq_some hx)
        exact ⟨hs.trans (List.sublist_append_left l [a]), hsum⟩
      · by_cases hpq : p a ≤ q
        · rw [ite_eq_left hpq] at hy
          obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hy
          obtain ⟨hsub, hsum⟩ := hT.sound _ s' (getD_eq_some hs')
          refine ⟨hsub.append (List.Sublist.refl [a]), ?_⟩
          simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, hsum]
          omega
        · rw [ite_eq_right hpq] at hy
          exact absurd hy (by simp)
    · rw [ite_eq_right hq] at h
      exact absurd h (by simp)
  · intro s hs
    obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp hs
    obtain ⟨r, hr, hrw⟩ := hT.complete l₁ h₁
    have hlt : (l₁.map p).sum < T.length := (List.getElem?_eq_some_iff.mp hr).1
    rcases List.sublist_singleton.mp h₂ with rfl | rfl
    · rw [List.append_nil, getElem?_profitStep, ite_eq_left (by omega)]
      have hX : T.getD (l₁.map p).sum none = some r := by
        rw [List.getD_eq_getElem?_getD, hr]; rfl
      rw [hX]
      obtain ⟨r', hr', hr'w⟩ := exists_lighter_left (w := w) r
        (if p a ≤ (l₁.map p).sum then (T.getD ((l₁.map p).sum - p a) none).map (· ++ [a])
          else none)
      exact ⟨r', by rw [hr'], hr'w.trans hrw⟩
    · have hsum : ((l₁ ++ [a]).map p).sum = (l₁.map p).sum + p a := by simp
      rw [hsum, getElem?_profitStep, ite_eq_left (by omega), ite_eq_left (by omega),
        Nat.add_sub_cancel]
      have hY : T.getD (l₁.map p).sum none = some r := by
        rw [List.getD_eq_getElem?_getD, hr]; rfl
      rw [hY]
      obtain ⟨r', hr', hr'w⟩ := exists_lighter_right (w := w)
        (T.getD ((l₁.map p).sum + p a) none) (r ++ [a])
      refine ⟨r', by rw [Option.map_some, hr'], hr'w.trans ?_⟩
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega

/-- Folding the dynamic program over more items preserves the invariant. -/
theorem TableSpec.foldl {l₀ : List ι} {T : List (Option (List ι))} (hT : TableSpec w p l₀ T)
    (l : List ι) : TableSpec w p (l₀ ++ l) (l.foldl (profitStep w p) T) := by
  induction l generalizing l₀ T with
  | nil => simpa using hT
  | cons a l ih =>
    rw [List.foldl_cons, ← List.singleton_append, ← List.append_assoc]
    exact ih (hT.step a)

/-- **Correctness of the profit table.** -/
theorem tableSpec_profitTable (l : List ι) : TableSpec w p l (profitTable w p l) := by
  have h := tableSpec_nil (w := w) (p := p) |>.foldl l
  rwa [List.nil_append] at h

/-- The selection scan returns an entry within the capacity of maximum profit among the entries
within the capacity. -/
private theorem foldl_selectStep_spec {B : ℕ} (L : List (Option (List ι))) (best : List ι)
    (hbest : (best.map w).sum ≤ B) :
    ((L.foldl (selectStep w p B) best).map w).sum ≤ B ∧
      (L.foldl (selectStep w p B) best = best ∨ some (L.foldl (selectStep w p B) best) ∈ L) ∧
      (best.map p).sum ≤ ((L.foldl (selectStep w p B) best).map p).sum ∧
      ∀ s, some s ∈ L → (s.map w).sum ≤ B →
        (s.map p).sum ≤ ((L.foldl (selectStep w p B) best).map p).sum := by
  induction L generalizing best with
  | nil => exact ⟨hbest, Or.inl rfl, le_rfl, by simp⟩
  | cons x L ih =>
    simp only [List.foldl_cons, List.mem_cons]
    have hstep : ((selectStep w p B best x).map w).sum ≤ B ∧
        (selectStep w p B best x = best ∨ some (selectStep w p B best x) = x) ∧
        (best.map p).sum ≤ ((selectStep w p B best x).map p).sum ∧
        ∀ s, some s = x → (s.map w).sum ≤ B →
          (s.map p).sum ≤ ((selectStep w p B best x).map p).sum := by
      cases x with
      | none => exact ⟨hbest, Or.inl rfl, le_rfl, by simp⟩
      | some s =>
        simp only [selectStep, Option.elim_some, Option.some.injEq]
        split_ifs with h
        · exact ⟨h.1, Or.inr rfl, h.2, fun t ht _ => ht ▸ le_rfl⟩
        · refine ⟨hbest, Or.inl rfl, le_rfl, fun t ht htw => ?_⟩
          subst ht
          exact (not_and.mp h htw |> not_le.mp).le
    obtain ⟨h1, h2, h3, h4⟩ := ih _ hstep.1
    refine ⟨h1, ?_, hstep.2.2.1.trans h3, ?_⟩
    · rcases h2 with h2 | h2
      · rcases hstep.2.1 with h | h
        · exact Or.inl (h2.trans h)
        · exact Or.inr (Or.inl (by rw [h2]; exact h))
      · exact Or.inr (Or.inr h2)
    · rintro s (hs | hs) hsw
      · exact (hstep.2.2.2 s hs hsw).trans h3
      · exact h4 s hs hsw

/-- The selection scan over the profit table stays a subsequence of the items. -/
theorem foldl_selectStep_sublist {B : ℕ} {l : List ι} {L : List (Option (List ι))}
    (hL : ∀ s, some s ∈ L → s <+ l) {best : List ι} (hbest : best <+ l) :
    L.foldl (selectStep w p B) best <+ l := by
  induction L generalizing best with
  | nil => exact hbest
  | cons x L ih =>
    refine ih (fun s hs => hL s (List.mem_cons_of_mem _ hs)) ?_
    cases x with
    | none => exact hbest
    | some s =>
      simp only [selectStep, Option.elim_some]
      split_ifs
      · exact hL s List.mem_cons_self
      · exact hbest

/-- Every entry of the profit table is a subsequence of the items. -/
theorem sublist_of_mem_profitTable {l s : List ι} (hs : some s ∈ profitTable w p l) : s <+ l := by
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hs
  exact ((tableSpec_profitTable l).sound q _ hq).1

/-- The dynamic program returns a subsequence of the items. -/
theorem profitDP_sublist (B : ℕ) (l : List ι) : profitDP w p B l <+ l :=
  foldl_selectStep_sublist (fun _ hs => sublist_of_mem_profitTable hs) (List.nil_sublist l)

/-- The dynamic program respects the capacity. -/
theorem sum_map_profitDP_le (B : ℕ) (l : List ι) : ((profitDP w p B l).map w).sum ≤ B :=
  (foldl_selectStep_spec (w := w) (p := p) (B := B) (profitTable w p l) [] (by simp)).1

/-- **The dynamic program is optimal**: its profit is at least that of every subsequence of the
items within the capacity. -/
theorem sum_map_le_profitDP {B : ℕ} {l s : List ι} (hs : s <+ l) (hsw : (s.map w).sum ≤ B) :
    (s.map p).sum ≤ ((profitDP w p B l).map p).sum := by
  obtain ⟨r, hr, hrw⟩ := (tableSpec_profitTable (w := w) (p := p) l).complete s hs
  have hrp := ((tableSpec_profitTable (w := w) (p := p) l).sound _ r hr).2
  rw [← hrp]
  exact (foldl_selectStep_spec (w := w) (p := p) (B := B) (profitTable w p l) [] (by simp)).2.2.2
    r (List.mem_of_getElem? hr) (hrw.trans hsw)

end Cslib.Algorithms.Lean.Knapsack
