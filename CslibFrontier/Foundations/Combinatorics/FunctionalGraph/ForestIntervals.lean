/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.CheckpointForest
public import CslibFrontier.Foundations.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.Iterate
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Interval labels for finite functional forests

Cut the outgoing edge of each periodic state. For any state `x`, `forestPath f x` is the reversed
orbit segment from its first periodic point (`f^[transientDepth f x] x`) down to `x`. A state `y`
is reached from `x` before cycle entry (`∃ t ≤ transientDepth f x, f^[t] x = y`) if and only if
`forestPath f y` is a prefix of `forestPath f x` (`forestPath_prefix`).

Under the lexicographic order on root-to-vertex paths, the extensions of any prefix form an
order-convex interval (`List.IsPrefix.of_le_of_le`). Ranking the `|α|` root paths (`forestRank`) and
taking the maximum descendant rank (`forestUpper`) therefore assigns two labels in
`Fin (Nat.card α)` to every state such that ancestry before cycle entry is equivalent to interval
containment (`forest_interval_spec`, `exists_forest_intervals`).

## Main definitions

* `Cslib.FunctionalGraph.forestTrace`: the first `k` states of the orbit of `x`.
* `Cslib.FunctionalGraph.forestPath`: the root-to-vertex path from `f^[transientDepth f x] x` to
  `x`.
* `Cslib.FunctionalGraph.forestRank`: the lexicographic rank of `forestPath f x` in
  `Fin (Fintype.card α)`.
* `Cslib.FunctionalGraph.forestDescendantRanks`: the set of ranks of states whose root path has
  `forestPath f x` as a prefix.
* `Cslib.FunctionalGraph.forestUpper`: the inclusive upper endpoint of the subtree interval of `x`.

## Main results

* `Cslib.FunctionalGraph.forestPath_prefix`: `forestPath f y <+: forestPath f x` iff `y` is reached
  from `x` within `transientDepth f x` steps.
* `Cslib.FunctionalGraph.forest_interval_spec`: `forestRank` and `forestUpper` characterize
  ancestry before cycle entry.
* `Cslib.FunctionalGraph.exists_forest_intervals`: interval labels in `Fin (Nat.card α)` exist over
  any finite type `[Finite α]`.

## References

* Adapted from lean/Proofs/ForestIntervals.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph

universe u
variable {α : Type u}

/-- The first `k` states of an orbit (`List.iterate f x k`). -/
def forestTrace (f : α → α) (x : α) (k : ℕ) : List α :=
  List.iterate f x k

/-- The trace of length `k` has `k` states. -/
@[simp] theorem length_forestTrace (f : α → α) (x : α) (k : ℕ) :
    (forestTrace f x k).length = k :=
  List.length_iterate f x k

/-- A state lies on the trace of length `k` exactly when it is `f^[i] x` for some `i < k`. -/
@[simp] theorem mem_forestTrace (f : α → α) (x y : α) (k : ℕ) :
    y ∈ forestTrace f x k ↔ ∃ i < k, f^[i] x = y := by
  simpa only [forestTrace, eq_comm] using List.mem_iterate (f := f) (a := x) (n := k) (b := y)

variable (f : α → α)

section

variable [Finite α]

/-- The path from cycle entry to `x`, with the forest edges read backwards. -/
noncomputable def forestPath (x : α) : List α :=
  (forestTrace f x (transientDepth f x + 1)).reverse

/-- The root path of `x` has one more state than the transient depth of `x`. -/
@[simp] theorem length_forestPath (x : α) :
    (forestPath f x).length = transientDepth f x + 1 := by
  simp [forestPath]

/-- The root path of `x` ends at `x`. -/
theorem forestPath_last (x : α) : (forestPath f x).getLast? = some x := by
  simp [forestPath, forestTrace]

/-- Distinct states have distinct root paths. -/
theorem forestPath_injective : Function.Injective (forestPath f) := by
  intro x y he
  have hh := congrArg List.getLast? he
  simpa only [forestPath_last, Option.some.injEq] using hh

/-- A state lies on the root path of `x` exactly when it is `f^[i] x` for some
`i ≤ transientDepth f x`. -/
@[simp] theorem mem_forestPath (x y : α) :
    y ∈ forestPath f x ↔ ∃ i ≤ transientDepth f x, f^[i] x = y := by
  simp only [forestPath, List.mem_reverse, mem_forestTrace, Nat.lt_succ_iff]

/-- Every state lies on its own root path. -/
theorem self_mem_forestPath (x : α) : x ∈ forestPath f x :=
  (mem_forestPath f x x).mpr ⟨0, Nat.zero_le _, rfl⟩

theorem forestPath_step (x : α) (hx : 0 < transientDepth f x) :
    forestPath f x = forestPath f (f x) ++ [x] := by
  have hd : transientDepth f (f x) + 1 = transientDepth f x := by
    have hh := transientDepth_iterate f x 1
    simp only [Function.iterate_one] at hh
    lia
  rw [forestPath, forestTrace, List.iterate, List.reverse_cons]
  change (forestTrace f (f x) (transientDepth f x)).reverse ++ [x] =
    (forestTrace f (f x) (transientDepth f (f x) + 1)).reverse ++ [x]
  rw [hd]

theorem forestPath_iterate_prefix (x : α) {t : ℕ} (ht : t ≤ transientDepth f x) :
    forestPath f (f^[t] x) <+: forestPath f x := by
  induction t generalizing x with
  | zero => exact ⟨[], List.append_nil _⟩
  | succ t ih =>
    have hd := transientDepth_iterate f x 1
    simp only [Function.iterate_one] at hd
    rw [Function.iterate_succ_apply, forestPath_step f x (by lia)]
    exact (ih (f x) (by lia)).trans ⟨[x], rfl⟩

/-- Prefixes of root paths are exactly the ancestors before cycle entry. -/
theorem forestPath_prefix (x y : α) :
    forestPath f y <+: forestPath f x ↔
      ∃ t ≤ transientDepth f x, f^[t] x = y := by
  constructor
  · rintro ⟨tail, he⟩
    apply (mem_forestPath f x y).mp
    rw [← he]
    exact List.mem_append_left _ (self_mem_forestPath f y)
  · rintro ⟨t, ht, rfl⟩
    exact forestPath_iterate_prefix f x ht

end

section Labels

variable [Fintype α] [LinearOrder α]

/-- The rank of the root path in the lexicographic order of all root paths. -/
noncomputable def forestRank (x : α) : Fin (Fintype.card α) :=
  ((Finset.univ.image (forestPath f)).orderIsoOfFin (by
    rw [Finset.card_image_of_injective _ (forestPath_injective f), Finset.card_univ])).symm
      ⟨forestPath f x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩

/-- Ranks compare exactly as the root paths compare lexicographically. -/
theorem forestRank_le (x y : α) :
    forestRank f x ≤ forestRank f y ↔ forestPath f x ≤ forestPath f y :=
  OrderIso.le_iff_le _

open scoped Classical in
/-- All descendant ranks, including the vertex's own rank. -/
noncomputable def forestDescendantRanks (x : α) : Finset (Fin (Fintype.card α)) :=
  (Finset.univ.filter fun y => forestPath f x <+: forestPath f y).image (forestRank f)

/-- A rank is a descendant rank of `x` exactly when it is the rank of a state whose root path
extends that of `x`. -/
@[simp] theorem mem_forestDescendantRanks (x : α) (r : Fin (Fintype.card α)) :
    r ∈ forestDescendantRanks f x ↔
      ∃ y, forestPath f x <+: forestPath f y ∧ forestRank f y = r := by
  classical
  simp only [forestDescendantRanks, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- Every state has a descendant rank, namely its own. -/
theorem forestDescendantRanks_nonempty (x : α) : (forestDescendantRanks f x).Nonempty :=
  ⟨forestRank f x, (mem_forestDescendantRanks f x _).mpr
    ⟨x, ⟨[], List.append_nil _⟩, rfl⟩⟩

/-- The inclusive upper endpoint of a subtree's rank interval. -/
noncomputable def forestUpper (x : α) : Fin (Fintype.card α) :=
  (forestDescendantRanks f x).max' (forestDescendantRanks_nonempty f x)

/-- Two bounded labels suffice to test ancestry in the cut functional forest. -/
theorem forest_interval_spec (x y : α) :
    forestRank f y ≤ forestRank f x ∧ forestRank f x ≤ forestUpper f y ↔
      ∃ t ≤ transientDepth f x, f^[t] x = y := by
  rw [← forestPath_prefix]
  constructor
  · rintro ⟨hlo, hhi⟩
    obtain ⟨z, hz, he⟩ := (mem_forestDescendantRanks f y _).mp
      ((forestDescendantRanks f y).max'_mem (forestDescendantRanks_nonempty f y))
    change forestRank f z = forestUpper f y at he
    rw [← he] at hhi
    exact hz.of_le_of_le ((forestRank_le f y x).mp hlo) ((forestRank_le f x z).mp hhi)
  · intro hp
    refine ⟨(forestRank_le f y x).mpr (List.isPrefix_le hp), ?_⟩
    exact (forestDescendantRanks f y).le_max' _
      ((mem_forestDescendantRanks f y _).mpr ⟨x, hp, rfl⟩)

end Labels

/-- Interval labels exist over every finite universe, without an input order. -/
theorem exists_forest_intervals [Finite α] : ∃ low high : α → Fin (Nat.card α),
    ∀ x y, (low y ≤ low x ∧ low x ≤ high y) ↔
      ∃ t ≤ transientDepth f x, f^[t] x = y := by
  classical
  let := Fintype.ofFinite α
  let : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  have he : Fintype.card α = Nat.card α := Nat.card_eq_fintype_card.symm
  refine ⟨fun x => Fin.cast he (forestRank f x), fun x => Fin.cast he (forestUpper f x), ?_⟩
  intro x y
  exact forest_interval_spec f x y

end Cslib.FunctionalGraph
