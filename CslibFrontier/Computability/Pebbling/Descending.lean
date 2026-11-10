/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Pebbling.Words
public import Mathlib.Data.Set.Card

/-!
# Evaluating a descending computation along a pebbling walk

A descending computation on the indices `0, …, N - 1` has a source at `0` and, at each positive
index `i`, a gate `gates i` reading the values at the `d` strictly smaller indices
`child i 0, …, child i (d - 1)`. Its dependency graph (`Cslib.Pebbling.Descending.graph`) is a DAG
of in-degree at most `d`, and the Boolean test `Cslib.Pebbling.Descending.ready` decides on
indicator words whether all predecessors of an index carry pebbles. So the word moves
`Cslib.Pebbling.wordStep (ready child) s` are the moves of the black pebble game on the dependency
graph, and Savitch's recursion decides whether an index is pebblable with `s` pebbles.

Following a walk of indicator words, an evaluator keeps a table of `(index, value)` pairs
(`Cslib.Pebbling.Descending.tableStep`). When a step clears a bit, it drops that index; when a step
sets a bit, it computes the value of that index from the values of its children in the table. As
long as consecutive words are equal or one legal move apart, the table holds exactly the values of
the pebbled indices (`Cslib.Pebbling.Descending.Holds`), so a walk from the zero word to the word
of the single pebble `v` ends with the value of `v` in the table. The table never holds more than
`s` entries, whatever the walk. This is how the simulation of Hopcroft, Paul and Valiant uses a
pebbling: one stored value per pebble.

## Main definitions

* `Cslib.Pebbling.Descending.graph`: the dependency graph of a descending computation.
* `Cslib.Pebbling.Descending.ready`: the readiness test on words.
* `Cslib.Pebbling.Descending.diffIndex`: the first position where two words differ.
* `Cslib.Pebbling.Descending.lookupD`, `Cslib.Pebbling.Descending.entry`: reading the table, and
  computing the value of an index from it.
* `Cslib.Pebbling.Descending.tableStep`: one update of the table along a word walk.
* `Cslib.Pebbling.Descending.Holds`: the table holds the values of the pebbled indices.

## Main results

* `Cslib.Pebbling.Descending.wellFounded_graph`, `Cslib.Pebbling.Descending.ncard_graph_adj_le`:
  the dependency graph is a DAG of in-degree at most `d`.
* `Cslib.Pebbling.Descending.ready_indicatorList`: `ready` decides readiness on indicator words.
* `Cslib.Pebbling.Descending.reach_wordStep_ready_iff_blackPebblable`: Savitch's recursion decides
  pebblability of the dependency graph.
* `Cslib.Pebbling.Descending.holds_tableStep`,
  `Cslib.Pebbling.Descending.holds_tableStep_of_wordStep`: one move, or one step of a word walk,
  preserves the invariant.
* `Cslib.Pebbling.Descending.lookupD_eq_of_tableStep`: a walk from the zero word to the word of
  `{v}` ends with the value of `v` in the table.
* `Cslib.Pebbling.Descending.length_tableStep_le`: the table never exceeds `s` entries.

## References

* [J. Hopcroft, W. Paul, L. Valiant, *On time versus space*][HopcroftPaulValiant1977]: simulating
  a computation by a pebbling of its graph, one stored value per pebble (journal text not
  inspected).
-/

public section

namespace Cslib.Pebbling.Descending

open Cslib.BitString (supportOfList indicatorList supportOfList_indicatorList
  indicatorList_supportOfList indicatorList_injective getD_indicatorList indicatorList_insert
  indicatorList_erase indicatorList_empty)

variable {N d : ℕ} (child : ℕ → Fin d → ℕ)

/-! ### The dependency graph -/

/-- The dependency graph of a descending computation on `Fin N`: the predecessors of a positive
index are its children; the source `0` has none. -/
def graph : Digraph (Fin N) where
  Adj u v := 0 < (v : ℕ) ∧ ∃ a, child v a = (u : ℕ)

@[simp] theorem graph_adj {u v : Fin N} :
    (graph child).Adj u v ↔ 0 < (v : ℕ) ∧ ∃ a, child v a = (u : ℕ) :=
  Iff.rfl

/-- With children below their parents, the dependency graph is acyclic. -/
theorem wellFounded_graph (hchild : ∀ i, 0 < i → ∀ a, child i a < i) :
    WellFounded (graph (N := N) child).Adj :=
  Subrelation.wf (r := InvImage (· < ·) fun v : Fin N => (v : ℕ)) (fun {u v} h => by
      obtain ⟨hv, a, ha⟩ := h
      change (u : ℕ) < v
      rw [← ha]
      exact hchild _ hv a)
    (InvImage.wf _ wellFounded_lt)

/-- Every index has at most `d` predecessors. -/
theorem ncard_graph_adj_le (v : Fin N) : {u | (graph child).Adj u v}.ncard ≤ d := by
  rw [← Set.ncard_image_of_injective _ Fin.val_injective]
  refine (Set.ncard_le_ncard ?_ (Set.finite_range (child v))).trans ?_
  · rintro _ ⟨u, ⟨-, a, ha⟩, rfl⟩
    exact ⟨a, ha⟩
  · rw [← Set.image_univ]
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ### Readiness on words -/

/-- Index `i` is ready in the word `w`: it is the source, or each of its children carries a
pebble. -/
@[expose] def ready (w : List Bool) (i : ℕ) : Bool :=
  i == 0 || (List.finRange d).all fun a => w.getD (child i a) false

/-- On indicator words, `ready` tests that all predecessors in the dependency graph carry
pebbles. -/
theorem ready_indicatorList (hchild : ∀ i, 0 < i → i < N → ∀ a, child i a < N)
    (C : Finset (Fin N)) (i : Fin N) :
    ready child (indicatorList C) i = true ↔ ∀ u, (graph child).Adj u i → u ∈ C := by
  simp only [ready, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange, true_implies,
    graph_adj]
  constructor
  · rintro (h0 | h) u ⟨hi, a, ha⟩
    · omega
    · have hget := getD_indicatorList C u
      rw [← ha, h a] at hget
      exact of_decide_eq_true hget.symm
  · intro h
    by_cases h0 : (i : ℕ) = 0
    · exact Or.inl h0
    · refine Or.inr fun a => ?_
      have hlt := hchild i (Nat.pos_of_ne_zero h0) i.isLt a
      rw [show child i a = ((⟨child i a, hlt⟩ : Fin N) : ℕ) from rfl, getD_indicatorList,
        decide_eq_true_eq]
      exact h _ ⟨Nat.pos_of_ne_zero h0, a, rfl⟩

/-- **Savitch's recursion decides pebblability of the dependency graph.** -/
theorem reach_wordStep_ready_iff_blackPebblable
    (hchild : ∀ i, 0 < i → i < N → ∀ a, child i a < N) {s : ℕ} {v : Fin N} :
    Reachability.reach (wordStep (ready child) s) N N (List.replicate N false)
        (indicatorList {v}) = true ↔
      BlackPebblable (graph child) s v :=
  reach_wordStep_iff_blackPebblable (ready_indicatorList child hchild)

/-! ### Differences between words -/

/-- The first position where `u` and `v` differ, or `u.length` when there is none. -/
@[expose] def diffIndex (u v : List Bool) : ℕ :=
  ((List.range u.length).find? fun i => u.getD i false != v.getD i false).getD u.length

theorem diffIndex_le (u v : List Bool) : diffIndex u v ≤ u.length := by
  unfold diffIndex
  cases h : (List.range u.length).find? fun i => u.getD i false != v.getD i false with
  | none => exact le_rfl
  | some j => exact (List.mem_range.1 (List.mem_of_find?_eq_some h)).le

/-- Flipping bit `i` makes `i` the first difference. -/
theorem diffIndex_set {u : List Bool} {i : ℕ} (hi : i < u.length) {b : Bool}
    (hb : u.getD i false ≠ b) : diffIndex u (u.set i b) = i := by
  have hfind : (List.range u.length).find?
      (fun j => u.getD j false != (u.set i b).getD j false) = some i := by
    rw [List.find?_range_eq_some]
    refine ⟨?_, List.mem_range.2 hi, fun j hj => ?_⟩
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_set_self hi] using hb
    · have hne : i ≠ j := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]
  unfold diffIndex
  rw [hfind, Option.getD_some]

variable {U : Type*}

/-! ### The invariant -/

/-- The table `t` holds exactly the values `value i` of the pebbled indices `i ∈ C`, each
once. -/
structure Holds (value : ℕ → U) (C : Finset (Fin N)) (t : List (ℕ × U)) : Prop where
  nodup : (t.map Prod.fst).Nodup
  mem_keys : ∀ i, i ∈ t.map Prod.fst ↔ ∃ v ∈ C, (v : ℕ) = i
  value_eq : ∀ p ∈ t, p.2 = value p.1

variable {value : ℕ → U}

/-- The empty table holds the empty configuration. -/
theorem holds_nil : Holds (N := N) value ∅ ([] : List (ℕ × U)) :=
  ⟨List.nodup_nil, fun _ => by simp, fun _ h => nomatch h⟩

namespace Holds

variable {C : Finset (Fin N)} {t : List (ℕ × U)}

/-- The table has one entry per pebble. -/
theorem length_eq (h : Holds value C t) : t.length = C.card := by
  rw [← List.length_map Prod.fst, ← List.toFinset_card_of_nodup h.nodup,
    ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [List.mem_toFinset, h.mem_keys, Finset.mem_map, Fin.valEmbedding_apply]

/-- Placing a pebble on `v` stores its value. -/
theorem insert (h : Holds value C t) {v : Fin N} (hv : v ∉ C) :
    Holds value (insert v C) (((v : ℕ), value v) :: t) where
  nodup := by
    refine List.nodup_cons.2 ⟨fun hmem => hv ?_, h.nodup⟩
    obtain ⟨w, hw, hwv⟩ := (h.mem_keys v).1 hmem
    exact Fin.ext hwv ▸ hw
  mem_keys i := by
    simp only [List.map_cons, List.mem_cons, h.mem_keys, Finset.mem_insert]
    constructor
    · rintro (rfl | ⟨w, hw, rfl⟩)
      · exact ⟨v, Or.inl rfl, rfl⟩
      · exact ⟨w, Or.inr hw, rfl⟩
    · rintro ⟨w, rfl | hw, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨w, hw, rfl⟩
  value_eq p hp := by
    rcases List.mem_cons.1 hp with rfl | hp
    · rfl
    · exact h.value_eq p hp

/-- Removing the pebble on `v` drops its entry. -/
theorem erase (h : Holds value C t) (v : Fin N) :
    Holds value (C.erase v) (t.filter fun p => p.1 != v) where
  nodup := h.nodup.sublist (List.filter_sublist.map _)
  mem_keys i := by
    simp only [List.mem_map, List.mem_filter, bne_iff_ne, ne_eq, Finset.mem_erase]
    constructor
    · rintro ⟨p, ⟨hp, hpv⟩, rfl⟩
      obtain ⟨w, hw, hwp⟩ := (h.mem_keys p.1).1 (List.mem_map_of_mem hp)
      exact ⟨w, ⟨fun hwv => hpv (by rw [← hwp, hwv]), hw⟩, hwp⟩
    · rintro ⟨w, ⟨hwv, hw⟩, rfl⟩
      obtain ⟨p, hp, hpw⟩ := List.mem_map.1 ((h.mem_keys w).2 ⟨w, hw, rfl⟩)
      exact ⟨p, ⟨hp, fun hpv => hwv (Fin.ext (by rw [← hpw, hpv]))⟩, hpw⟩
  value_eq p hp := h.value_eq p (List.mem_of_mem_filter hp)

end Holds

/-! ### The table -/

variable [Inhabited U]

/-- The value stored for index `i`, or `default` when there is none. -/
@[expose] def lookupD (t : List (ℕ × U)) (i : ℕ) : U :=
  ((t.find? fun p => p.1 == i).map Prod.snd).getD default

/-- A pebbled index is stored with its value. -/
theorem Holds.lookupD_eq {C : Finset (Fin N)} {t : List (ℕ × U)} (h : Holds value C t)
    {v : Fin N} (hv : v ∈ C) : lookupD t v = value v := by
  obtain ⟨p, hp, hpv⟩ := List.mem_map.1 ((h.mem_keys v).2 ⟨v, hv, rfl⟩)
  cases hfind : t.find? fun p => p.1 == (v : ℕ) with
  | none => exact (List.find?_eq_none.1 hfind p hp (by simp [hpv])).elim
  | some q =>
    have hq := List.find?_some hfind
    rw [beq_iff_eq] at hq
    simp only [lookupD, hfind, Option.map_some, Option.getD_some]
    rw [h.value_eq q (List.mem_of_find?_eq_some hfind), hq]

variable (gates : ℕ → (Fin d → U) → U) (source : U)

/-- The value of index `i` computed from the table: the source at `0`, otherwise the gate of `i`
on the stored values of its children. -/
@[expose] def entry (t : List (ℕ × U)) (i : ℕ) : U :=
  if i = 0 then source else gates i fun a => lookupD t (child i a)

/-- One update of the table along a walk from `u` to `v`, with room for `s` entries: if `v` clears
the first bit where the words differ, drop that index; if it sets it, store its value computed
from the table. Equal words leave the table unchanged. -/
@[expose] def tableStep (s : ℕ) (u v : List Bool) (t : List (ℕ × U)) : List (ℕ × U) :=
  if u = v then t
  else if u.getD (diffIndex u v) false then t.filter fun p => p.1 != diffIndex u v
  else if t.length < s then (diffIndex u v, entry child gates source t (diffIndex u v)) :: t
  else t

/-- **The table never exceeds `s` entries**, along any walk. -/
theorem length_tableStep_le {s : ℕ} {u v : List Bool} {t : List (ℕ × U)} (ht : t.length ≤ s) :
    (tableStep child gates source s u v t).length ≤ s := by
  unfold tableStep
  split_ifs with h₁ h₂ h₃
  · exact ht
  · exact (List.length_filter_le _ _).trans ht
  · simpa using h₃
  · exact ht

/-- Every entry after a step is an old entry or the entry of the first difference. -/
theorem mem_tableStep {s : ℕ} {u v : List Bool} {t : List (ℕ × U)} {p : ℕ × U}
    (hp : p ∈ tableStep child gates source s u v t) :
    p ∈ t ∨ p = (diffIndex u v, entry child gates source t (diffIndex u v)) := by
  unfold tableStep at hp
  split_ifs at hp with h₁ h₂ h₃
  · exact Or.inl hp
  · exact Or.inl (List.mem_of_mem_filter hp)
  · exact (List.mem_cons.1 hp).symm
  · exact Or.inl hp

/-- **One move preserves the invariant.** If the table holds the values of `C`, and `D` is `C` or
one legal move with at most `s` pebbles away, then after one step from the word of `C` to the word
of `D` the table holds the values of `D`. -/
theorem holds_tableStep (hchild : ∀ i, 0 < i → ∀ a, child i a < i)
    (hzero : value 0 = source)
    (hsucc : ∀ i, 0 < i → i < N → value i = gates i fun a => value (child i a))
    {s : ℕ} {C D : Finset (Fin N)} {t : List (ℕ × U)} (h : Holds value C t)
    (hmove : C = D ∨ (blackPebbleGame (graph child) s).UnlabelledTr C D) :
    Holds value D (tableStep child gates source s (indicatorList C) (indicatorList D) t) := by
  rcases hmove with rfl | ⟨m, hstep, hcard⟩
  · rwa [tableStep, ite_eq_left rfl]
  by_cases hCD : C = D
  · subst hCD
    rwa [tableStep, ite_eq_left rfl]
  have hne : indicatorList C ≠ indicatorList D := fun e => hCD (indicatorList_injective e)
  cases hstep with
  | @place v hv =>
    have hvC : v ∉ C := fun hm => hCD (Finset.insert_eq_of_mem hm).symm
    have hbit : (indicatorList C).getD v false = false := by
      rw [getD_indicatorList, decide_eq_false hvC]
    have hdiff : diffIndex (indicatorList C) (indicatorList (insert v C)) = v := by
      rw [indicatorList_insert]
      exact diffIndex_set (by simp) (by rw [hbit]; decide)
    have hlen : t.length < s := by
      rw [h.length_eq]
      rw [Finset.card_insert_of_notMem hvC] at hcard
      omega
    have hentry : entry child gates source t v = value v := by
      unfold entry
      split_ifs with h0
      · rw [h0, hzero]
      · rw [hsucc v (Nat.pos_of_ne_zero h0) v.isLt]
        congr 1
        funext a
        have hlt : child v a < N := (hchild v (Nat.pos_of_ne_zero h0) a).trans v.isLt
        exact h.lookupD_eq (v := ⟨child v a, hlt⟩) (hv _ ⟨Nat.pos_of_ne_zero h0, a, rfl⟩)
    rw [tableStep, ite_eq_right hne, hdiff, hbit, ite_eq_right Bool.false_ne_true, ite_eq_left hlen,
      hentry]
    exact h.insert hvC
  | @remove v =>
    have hvC : v ∈ C := by
      by_contra hm
      exact hCD (Finset.erase_eq_of_notMem hm).symm
    have hbit : (indicatorList C).getD v false = true := by
      rw [getD_indicatorList, decide_eq_true hvC]
    have hdiff : diffIndex (indicatorList C) (indicatorList (C.erase v)) = v := by
      rw [indicatorList_erase]
      exact diffIndex_set (by simp) (by rw [hbit]; decide)
    rw [tableStep, ite_eq_right hne, hdiff, hbit, ite_eq_left rfl]
    exact h.erase v

/-- **One step of a word walk preserves the invariant.** Between words of length `N` that are
equal or one word move apart, a step of the table carries the invariant from the support of `u` to
the support of `v`. -/
theorem holds_tableStep_of_wordStep (hchild : ∀ i, 0 < i → ∀ a, child i a < i)
    (hzero : value 0 = source)
    (hsucc : ∀ i, 0 < i → i < N → value i = gates i fun a => value (child i a))
    {s : ℕ} {u v : List Bool} (hu : u.length = N) (hv : v.length = N)
    (huv : u = v ∨ wordStep (ready child) s u v = true) {t : List (ℕ × U)}
    (h : Holds value (supportOfList N u) t) :
    Holds value (supportOfList N v) (tableStep child gates source s u v t) := by
  have hlt : ∀ i, 0 < i → i < N → ∀ a, child i a < N := fun i hi hiN a =>
    (hchild i hi a).trans hiN
  obtain ⟨C, rfl⟩ : ∃ C : Finset (Fin N), indicatorList C = u :=
    ⟨_, indicatorList_supportOfList hu⟩
  obtain ⟨D, rfl⟩ : ∃ D : Finset (Fin N), indicatorList D = v :=
    ⟨_, indicatorList_supportOfList hv⟩
  rw [supportOfList_indicatorList] at h ⊢
  refine holds_tableStep child gates source hchild hzero hsucc h ?_
  rcases huv with huv | huv
  · exact Or.inl (indicatorList_injective huv)
  · exact Or.inr ((wordStep_indicatorList_iff (ready_indicatorList child hlt)).1 huv).2

/-- **The evaluator is correct.** Along a walk `ws` of words of length `N` from the zero word in
which consecutive words are equal or one word move apart, tables built by `tableStep` from the
empty table hold the values of the pebbled indices. When the walk reaches the word of `{v}`, the
table returns the value of `v`. -/
theorem lookupD_eq_of_tableStep (hchild : ∀ i, 0 < i → ∀ a, child i a < i)
    (hzero : value 0 = source)
    (hsucc : ∀ i, 0 < i → i < N → value i = gates i fun a => value (child i a))
    {s : ℕ} (ws : ℕ → List Bool) (ts : ℕ → List (ℕ × U)) (n : ℕ)
    (hlen : ∀ j ≤ n, (ws j).length = N) (hws0 : ws 0 = List.replicate N false)
    (hstep : ∀ j < n, ws j = ws (j + 1) ∨ wordStep (ready child) s (ws j) (ws (j + 1)) = true)
    (hts0 : ts 0 = [])
    (hts : ∀ j < n, ts (j + 1) = tableStep child gates source s (ws j) (ws (j + 1)) (ts j))
    {v : Fin N} (hend : ws n = indicatorList {v}) :
    lookupD (ts n) v = value v := by
  have key : ∀ j ≤ n, Holds value (supportOfList N (ws j)) (ts j) := by
    intro j hj
    induction j with
    | zero =>
      rw [hws0, hts0, ← indicatorList_empty, supportOfList_indicatorList]
      exact holds_nil
    | succ j ih =>
      rw [hts j hj]
      exact holds_tableStep_of_wordStep child gates source hchild hzero hsucc (hlen j (by omega))
        (hlen (j + 1) hj) (hstep j hj) (ih (by omega))
  have h := key n le_rfl
  rw [hend, supportOfList_indicatorList] at h
  exact h.lookupD_eq (Finset.mem_singleton_self v)

end Cslib.Pebbling.Descending
