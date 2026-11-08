/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Pebbling.Basic

/-!
# Transporting black pebblings along graph isomorphisms

A relation isomorphism `e : G.Adj ≃r H.Adj` carries black pebblings of `G` to black pebblings of
`H` with the same number of pebbles. Pebblability and the black pebbling price are therefore
invariant under graph isomorphism.

## Main definitions

* `Cslib.Pebbling.Move.map`: rename the vertex of a move.

## Main results

* `Cslib.Pebbling.blackPebbleGame_mTr_map_relIso`: runs transport along an isomorphism.
* `Cslib.Pebbling.blackPebblable_relIso_iff`: pebblability is invariant.
* `Cslib.Pebbling.blackPebblingPrice_relIso`: the price is invariant.
-/

public section

namespace Cslib.Pebbling

variable {V W : Type*}

/-- Rename the vertex of a move. -/
def Move.map (f : V → W) : Move V → Move W
  | .place v => .place (f v)
  | .remove v => .remove (f v)

@[simp] theorem Move.map_place (f : V → W) (v : V) : (Move.place v).map f = .place (f v) := by
  rw [Move.map]

@[simp] theorem Move.map_remove (f : V → W) (v : V) : (Move.remove v).map f = .remove (f v) := by
  rw [Move.map]

variable [DecidableEq V] [DecidableEq W] {G : Digraph V} {H : Digraph W}

theorem BlackStep.map_relIso (e : G.Adj ≃r H.Adj) {C D : Finset V} {m : Move V}
    (h : BlackStep G C m D) :
    BlackStep H (C.map e.toEquiv.toEmbedding) (m.map e) (D.map e.toEquiv.toEmbedding) := by
  cases h with
  | @place v hv =>
    rw [Finset.map_insert]
    refine .place fun u hu => ?_
    rw [← e.apply_symm_apply u] at hu ⊢
    exact Finset.mem_map_of_mem _ (hv _ (e.map_rel_iff.1 hu))
  | @remove v =>
    rw [Finset.map_erase]
    exact .remove

theorem blackPebbleGame_mTr_map_relIso (e : G.Adj ≃r H.Adj) {s : ℕ} {C D : Finset V}
    {ms : List (Move V)} (h : (blackPebbleGame G s).MTr C ms D) :
    (blackPebbleGame H s).MTr (C.map e.toEquiv.toEmbedding) (ms.map (Move.map e))
      (D.map e.toEquiv.toEmbedding) := by
  induction h with
  | refl => exact .refl
  | stepL h _ ih =>
    exact .stepL ⟨h.1.map_relIso e, by rw [Finset.card_map]; exact h.2⟩ ih

/-- Black pebblability is invariant under graph isomorphism. -/
theorem blackPebblable_relIso_iff (e : G.Adj ≃r H.Adj) {s : ℕ} {v : V} :
    BlackPebblable H s (e v) ↔ BlackPebblable G s v := by
  constructor
  · rintro ⟨ms, C, hC, hv⟩
    refine ⟨ms.map (Move.map e.symm), C.map e.symm.toEquiv.toEmbedding, ?_, ?_⟩
    · simpa using blackPebbleGame_mTr_map_relIso e.symm hC
    · simpa using Finset.mem_map_of_mem e.symm.toEquiv.toEmbedding hv
  · rintro ⟨ms, C, hC, hv⟩
    exact ⟨ms.map (Move.map e), C.map e.toEquiv.toEmbedding,
      blackPebbleGame_mTr_map_relIso e hC, Finset.mem_map_of_mem _ hv⟩

/-- The black pebbling price is invariant under graph isomorphism. -/
theorem blackPebblingPrice_relIso (e : G.Adj ≃r H.Adj) (v : V) :
    blackPebblingPrice H (e v) = blackPebblingPrice G v := by
  by_cases hv : ∃ s, BlackPebblable G s v
  · obtain ⟨s, hs⟩ := hv
    have hs' := (blackPebblable_relIso_iff e).2 hs
    refine le_antisymm (blackPebblingPrice_le ((blackPebblable_relIso_iff e).2
      (blackPebblable_blackPebblingPrice hs))) (blackPebblingPrice_le ?_)
    exact (blackPebblable_relIso_iff e).1 (blackPebblable_blackPebblingPrice hs')
  · push Not at hv
    rw [blackPebblingPrice_eq_zero_of_forall_not hv, blackPebblingPrice_eq_zero_of_forall_not
      fun s hs => hv s ((blackPebblable_relIso_iff e).1 hs)]

end Cslib.Pebbling
