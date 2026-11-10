/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Pebbling.Basic

/-!
# The reversible pebble game

Bennett's reversible pebble game on a directed graph `G` uses the moves of the black pebble game
under one extra rule. Placing a pebble on `v` and removing the pebble from `v` both require every
predecessor of `v` to carry a pebble. Every move is therefore undone by the opposite move, so on a
loopless graph each run can be played backwards with the same budget. Pebbles model the
checkpoints of a reversible simulation of an irreversible computation: a checkpoint can be
computed, and reversibly erased, only from the checkpoint before it.

We take the toggling form of the rule, as in [LiTrompVitanyi1998], Section 6: `place v` requires
`v` to be unpebbled and `remove v` requires `v` to be pebbled. A no-op move would not change any
configuration, so this does not change which configurations are reachable.

A vertex is *reversibly pebblable* with `s` pebbles if some run from the empty configuration that
never holds more than `s` pebbles reaches a configuration containing it. It is *persistently*
pebblable if the run can end holding the vertex alone, as when a reversible computation keeps its
output and erases all its checkpoints. Both prices are the least such `s`, and `0` when no budget
suffices, as for `blackPebblingPrice`.

## Main definitions

* `Cslib.Pebbling.Move.swap`: the opposite move.
* `Cslib.Pebbling.RevStep`: one legal move of the reversible game, with no pebble budget.
* `Cslib.Pebbling.reversiblePebbleGame G s`: the game with `s` pebbles, as a cslib `LTS`.
* `Cslib.Pebbling.ReversiblePebblable G s v`, `Cslib.Pebbling.reversiblePebblingPrice G v`:
  reaching a configuration containing `v`, and the least budget for it.
* `Cslib.Pebbling.PersistentReversiblePebblable G s v`,
  `Cslib.Pebbling.persistentReversiblePebblingPrice G v`: reaching the configuration `{v}`, and
  the least budget for it.

## Main results

* `Cslib.Pebbling.reversiblePebbleGame_mTr_reverse`: on a loopless graph a run played backwards,
  with each move swapped, is a run with the same budget.
* `Cslib.Pebbling.RevStep.filter`: restricting a move to a predecessor-closed set of vertices
  gives a move or no change.
* `Cslib.Pebbling.ReversiblePebblable.blackPebblable`: every reversible run is a black run, so
  `blackPebblingPrice_le_reversiblePebblingPrice`.
* `Cslib.Pebbling.reversiblePebblingPrice_eq`,
  `Cslib.Pebbling.persistentReversiblePebblingPrice_eq`: the prices are determined by matching
  upper and lower bounds.

## References

* [C. H. Bennett, *Time/space trade-offs for reversible computation*][Bennett1989].
* [M. Li, J. Tromp, P. Vitányi, *Reversible simulation of irreversible computation by pebble
  games*][LiTrompVitanyi1998], Section 6.
-/

public section

namespace Cslib.Pebbling

/-- The opposite move: `place v` and `remove v` are exchanged. -/
@[expose] def Move.swap {V : Type*} : Move V → Move V
  | .place v => .remove v
  | .remove v => .place v

@[simp] theorem Move.swap_place {V : Type*} (v : V) : (Move.place v).swap = .remove v := rfl

@[simp] theorem Move.swap_remove {V : Type*} (v : V) : (Move.remove v).swap = .place v := rfl

@[simp] theorem Move.swap_swap {V : Type*} (m : Move V) : m.swap.swap = m := by
  cases m <;> rfl

section Game

variable {V : Type*} [DecidableEq V] (G : Digraph V)

/-- One legal move of the reversible pebble game, without a budget: a pebble may be placed on an
unpebbled vertex, or removed from a pebbled one, only when every predecessor carries a pebble. -/
inductive RevStep : Finset V → Move V → Finset V → Prop where
  | place {C : Finset V} {v : V} (hv : v ∉ C) (h : ∀ u, G.Adj u v → u ∈ C) :
      RevStep C (.place v) (insert v C)
  | remove {C : Finset V} {v : V} (hv : v ∈ C) (h : ∀ u, G.Adj u v → u ∈ C) :
      RevStep C (.remove v) (C.erase v)

/-- The reversible pebble game with `s` pebbles. -/
@[expose] def reversiblePebbleGame (s : ℕ) : LTS (Finset V) (Move V) where
  Tr C m D := RevStep G C m D ∧ D.card ≤ s

/-- `v` can be reversibly pebbled with at most `s` pebbles: some run from the empty configuration
reaches a configuration containing `v`. -/
@[expose] def ReversiblePebblable (s : ℕ) (v : V) : Prop :=
  ∃ (ms : List (Move V)) (C : Finset V), (reversiblePebbleGame G s).MTr ∅ ms C ∧ v ∈ C

/-- `v` can be persistently reversibly pebbled with at most `s` pebbles: some run from the empty
configuration ends with `v` as the only pebble. -/
@[expose] def PersistentReversiblePebblable (s : ℕ) (v : V) : Prop :=
  ∃ ms : List (Move V), (reversiblePebbleGame G s).MTr ∅ ms {v}

/-- The reversible pebbling price of `v`: the least `s` such that `v` is reversibly pebblable with
`s` pebbles, and `0` when no budget suffices. -/
noncomputable def reversiblePebblingPrice (v : V) : ℕ :=
  sInf {s | ReversiblePebblable G s v}

/-- The persistent reversible pebbling price of `v`: the least `s` such that `v` is persistently
reversibly pebblable with `s` pebbles, and `0` when no budget suffices. -/
noncomputable def persistentReversiblePebblingPrice (v : V) : ℕ :=
  sInf {s | PersistentReversiblePebblable G s v}

end Game

section API

variable {V : Type*} [DecidableEq V] {G : Digraph V}

theorem reversiblePebbleGame_tr {s : ℕ} {C D : Finset V} {m : Move V} :
    (reversiblePebbleGame G s).Tr C m D ↔ RevStep G C m D ∧ D.card ≤ s := Iff.rfl

/-- Every reversible move is a black move. -/
theorem RevStep.blackStep {C D : Finset V} {m : Move V} (h : RevStep G C m D) :
    BlackStep G C m D := by
  cases h with
  | place _ h => exact .place h
  | remove _ _ => exact .remove

/-- A vertex that gains or loses its pebble in a move has all its predecessors pebbled. -/
theorem RevStep.forall_adj_of_mem_iff {C D : Finset V} {m : Move V} (h : RevStep G C m D)
    {x : V} (hx : ¬ (x ∈ C ↔ x ∈ D)) : ∀ u, G.Adj u x → u ∈ C := by
  cases h with
  | @place v _ h =>
    by_cases hxv : x = v
    · exact hxv ▸ h
    · simp [hxv] at hx
  | @remove v _ h =>
    by_cases hxv : x = v
    · exact hxv ▸ h
    · simp [hxv] at hx

/-- On a loopless graph the opposite move undoes a move. -/
theorem RevStep.swap (hG : ∀ v, ¬ G.Adj v v) {C D : Finset V} {m : Move V}
    (h : RevStep G C m D) : RevStep G D m.swap C := by
  cases h with
  | @place v hv h =>
    have h' : ∀ u, G.Adj u v → u ∈ insert v C := fun u hu => Finset.mem_insert_of_mem (h u hu)
    have := RevStep.remove (G := G) (Finset.mem_insert_self v C) h'
    rwa [Finset.erase_insert hv] at this
  | @remove v hv h =>
    have h' : ∀ u, G.Adj u v → u ∈ C.erase v := fun u hu =>
      Finset.mem_erase.2 ⟨fun huv => hG v (huv ▸ hu), h u hu⟩
    have := RevStep.place (G := G) (Finset.notMem_erase v C) h'
    rwa [Finset.insert_erase hv] at this

/-- Restricting a move to a set of vertices closed under predecessors gives either a move or no
change. -/
theorem RevStep.filter {p : V → Prop} [DecidablePred p] (hp : ∀ u v, G.Adj u v → p v → p u)
    {C D : Finset V} {m : Move V} (h : RevStep G C m D) :
    D.filter p = C.filter p ∨ ∃ m', RevStep G (C.filter p) m' (D.filter p) := by
  cases h with
  | @place v hv h =>
    rw [Finset.filter_insert]
    split_ifs with hpv
    · exact .inr ⟨.place v, .place (fun hm => hv (Finset.mem_of_mem_filter v hm))
        fun u hu => Finset.mem_filter.2 ⟨h u hu, hp u v hu hpv⟩⟩
    · exact .inl rfl
  | @remove v hv h =>
    rw [Finset.filter_erase]
    by_cases hpv : p v
    · exact .inr ⟨.remove v, .remove (Finset.mem_filter.2 ⟨hv, hpv⟩)
        fun u hu => Finset.mem_filter.2 ⟨h u hu, hp u v hu hpv⟩⟩
    · exact .inl (Finset.erase_eq_of_notMem fun hm => hpv (Finset.mem_filter.1 hm).2)

theorem reversiblePebbleGame_mTr_mono {s t : ℕ} (hst : s ≤ t) {C D : Finset V}
    {ms : List (Move V)} (h : (reversiblePebbleGame G s).MTr C ms D) :
    (reversiblePebbleGame G t).MTr C ms D := by
  induction h with
  | refl => exact .refl
  | stepL h _ ih => exact .stepL ⟨h.1, h.2.trans hst⟩ ih

theorem card_le_of_reversiblePebbleGame_mTr {s : ℕ} {C D : Finset V} {ms : List (Move V)}
    (h : (reversiblePebbleGame G s).MTr C ms D) (hC : C.card ≤ s) : D.card ≤ s := by
  induction h with
  | refl => exact hC
  | stepL h _ ih => exact ih h.2

/-- Every reversible run is a black run with the same moves and budget. -/
theorem blackPebbleGame_mTr_of_reversiblePebbleGame_mTr {s : ℕ} {C D : Finset V}
    {ms : List (Move V)} (h : (reversiblePebbleGame G s).MTr C ms D) :
    (blackPebbleGame G s).MTr C ms D := by
  induction h with
  | refl => exact .refl
  | stepL h _ ih => exact .stepL ⟨h.1.blackStep, h.2⟩ ih

/-- **Reversibility.** On a loopless graph, a run played backwards with each move swapped is a
run with the same budget, provided the starting configuration fits in the budget. -/
theorem reversiblePebbleGame_mTr_reverse (hG : ∀ v, ¬ G.Adj v v) {s : ℕ} {C D : Finset V}
    {ms : List (Move V)} (h : (reversiblePebbleGame G s).MTr C ms D) (hC : C.card ≤ s) :
    (reversiblePebbleGame G s).MTr D (ms.reverse.map Move.swap) C := by
  induction h with
  | refl => exact .refl
  | stepL h hrest ih =>
    rw [List.reverse_cons, List.map_append]
    exact LTS.MTr.stepR _ (ih h.2) ⟨h.1.swap hG, hC⟩

theorem ReversiblePebblable.mono {s t : ℕ} (hst : s ≤ t) {v : V}
    (h : ReversiblePebblable G s v) : ReversiblePebblable G t v := by
  obtain ⟨ms, C, hC, hv⟩ := h
  exact ⟨ms, C, reversiblePebbleGame_mTr_mono hst hC, hv⟩

theorem PersistentReversiblePebblable.mono {s t : ℕ} (hst : s ≤ t) {v : V}
    (h : PersistentReversiblePebblable G s v) : PersistentReversiblePebblable G t v := by
  obtain ⟨ms, hms⟩ := h
  exact ⟨ms, reversiblePebbleGame_mTr_mono hst hms⟩

theorem PersistentReversiblePebblable.reversiblePebblable {s : ℕ} {v : V}
    (h : PersistentReversiblePebblable G s v) : ReversiblePebblable G s v := by
  obtain ⟨ms, hms⟩ := h
  exact ⟨ms, {v}, hms, Finset.mem_singleton_self v⟩

/-- A reversible pebbling is a black pebbling. -/
theorem ReversiblePebblable.blackPebblable {s : ℕ} {v : V} (h : ReversiblePebblable G s v) :
    BlackPebblable G s v := by
  obtain ⟨ms, C, hC, hv⟩ := h
  exact ⟨ms, C, blackPebbleGame_mTr_of_reversiblePebbleGame_mTr hC, hv⟩

theorem reversiblePebblingPrice_le {s : ℕ} {v : V} (h : ReversiblePebblable G s v) :
    reversiblePebblingPrice G v ≤ s :=
  Nat.sInf_le h

theorem reversiblePebblable_reversiblePebblingPrice {s : ℕ} {v : V}
    (h : ReversiblePebblable G s v) : ReversiblePebblable G (reversiblePebblingPrice G v) v :=
  Nat.sInf_mem (s := {s | ReversiblePebblable G s v}) ⟨s, h⟩

/-- The reversible price is `n` when `n` pebbles suffice and every successful budget is at least
`n`. -/
theorem reversiblePebblingPrice_eq {n : ℕ} {v : V} (h : ReversiblePebblable G n v)
    (hle : ∀ s, ReversiblePebblable G s v → n ≤ s) : reversiblePebblingPrice G v = n :=
  le_antisymm (reversiblePebblingPrice_le h) (hle _ (reversiblePebblable_reversiblePebblingPrice h))

theorem persistentReversiblePebblingPrice_le {s : ℕ} {v : V}
    (h : PersistentReversiblePebblable G s v) : persistentReversiblePebblingPrice G v ≤ s :=
  Nat.sInf_le h

theorem persistentReversiblePebblable_persistentReversiblePebblingPrice {s : ℕ} {v : V}
    (h : PersistentReversiblePebblable G s v) :
    PersistentReversiblePebblable G (persistentReversiblePebblingPrice G v) v :=
  Nat.sInf_mem (s := {s | PersistentReversiblePebblable G s v}) ⟨s, h⟩

/-- The persistent reversible price is `n` when `n` pebbles suffice and every successful budget is
at least `n`. -/
theorem persistentReversiblePebblingPrice_eq {n : ℕ} {v : V}
    (h : PersistentReversiblePebblable G n v)
    (hle : ∀ s, PersistentReversiblePebblable G s v → n ≤ s) :
    persistentReversiblePebblingPrice G v = n :=
  le_antisymm (persistentReversiblePebblingPrice_le h)
    (hle _ (persistentReversiblePebblable_persistentReversiblePebblingPrice h))

/-- Reversible pebbling costs at least as much as black pebbling. -/
theorem blackPebblingPrice_le_reversiblePebblingPrice {s : ℕ} {v : V}
    (h : ReversiblePebblable G s v) : blackPebblingPrice G v ≤ reversiblePebblingPrice G v :=
  blackPebblingPrice_le (reversiblePebblable_reversiblePebblingPrice h).blackPebblable

/-- Ending with the vertex alone costs at least as much as visiting it. -/
theorem reversiblePebblingPrice_le_persistentReversiblePebblingPrice {s : ℕ} {v : V}
    (h : PersistentReversiblePebblable G s v) :
    reversiblePebblingPrice G v ≤ persistentReversiblePebblingPrice G v :=
  reversiblePebblingPrice_le
    (persistentReversiblePebblable_persistentReversiblePebblingPrice h).reversiblePebblable

end API

end Cslib.Pebbling
