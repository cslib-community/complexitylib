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

An equivalence `e : V ≃ W` with `H.Adj (e u) (e v) ↔ G.Adj u v` carries black pebblings of `G`
to black pebblings of `H` with the same number of pebbles. Pebblability and the black pebbling
price are therefore invariant under graph isomorphism.

## Main definitions

* `Cslib.Pebbling.Move.map`: rename the vertex of a move.

## Main results

* `Cslib.Pebbling.blackPebbleGame_mTr_map_equiv`: runs transport along an isomorphism.
* `Cslib.Pebbling.blackPebblable_map_equiv_iff`: pebblability is invariant.
* `Cslib.Pebbling.blackPebblingPrice_map_equiv`: the price is invariant.
-/

public section

namespace Cslib.Pebbling

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {G : Digraph V} {H : Digraph W}

/-- Rename the vertex of a move. -/
def Move.map (f : V → W) : Move V → Move W
  | .place v => .place (f v)
  | .remove v => .remove (f v)

theorem BlackStep.map_equiv (e : V ≃ W) (he : ∀ u v, H.Adj (e u) (e v) ↔ G.Adj u v)
    {C D : Finset V} {m : Move V} (h : BlackStep G C m D) :
    BlackStep H (C.map e.toEmbedding) (m.map e) (D.map e.toEmbedding) := by
  cases h with
  | @place v hv =>
    rw [Finset.map_insert]
    refine .place fun u hu => ?_
    rw [← e.apply_symm_apply u] at hu ⊢
    exact Finset.mem_map_of_mem _ (hv _ ((he _ _).1 hu))
  | @remove v =>
    rw [Finset.map_erase]
    exact .remove

theorem blackPebbleGame_mTr_map_equiv (e : V ≃ W) (he : ∀ u v, H.Adj (e u) (e v) ↔ G.Adj u v)
    {s : ℕ} {C D : Finset V} {ms : List (Move V)} (h : (blackPebbleGame G s).MTr C ms D) :
    (blackPebbleGame H s).MTr (C.map e.toEmbedding) (ms.map (Move.map e))
      (D.map e.toEmbedding) := by
  induction h with
  | refl => exact .refl
  | stepL h _ ih =>
    exact .stepL ⟨h.1.map_equiv e he, by rw [Finset.card_map]; exact h.2⟩ ih

/-- Black pebblability is invariant under graph isomorphism. -/
theorem blackPebblable_map_equiv_iff (e : V ≃ W) (he : ∀ u v, H.Adj (e u) (e v) ↔ G.Adj u v)
    {s : ℕ} {v : V} : BlackPebblable H s (e v) ↔ BlackPebblable G s v := by
  have he' : ∀ u v, G.Adj (e.symm u) (e.symm v) ↔ H.Adj u v := fun u v => by
    rw [← he, e.apply_symm_apply, e.apply_symm_apply]
  constructor
  · rintro ⟨ms, C, hC, hv⟩
    refine ⟨ms.map (Move.map e.symm), C.map e.symm.toEmbedding, ?_, ?_⟩
    · simpa using blackPebbleGame_mTr_map_equiv e.symm he' hC
    · simpa using Finset.mem_map_of_mem e.symm.toEmbedding hv
  · rintro ⟨ms, C, hC, hv⟩
    refine ⟨ms.map (Move.map e), C.map e.toEmbedding, ?_, Finset.mem_map_of_mem _ hv⟩
    simpa using blackPebbleGame_mTr_map_equiv e he hC

/-- The black pebbling price is invariant under graph isomorphism. -/
theorem blackPebblingPrice_map_equiv (e : V ≃ W) (he : ∀ u v, H.Adj (e u) (e v) ↔ G.Adj u v)
    (v : V) : blackPebblingPrice H (e v) = blackPebblingPrice G v := by
  by_cases hv : ∃ s, BlackPebblable G s v
  · obtain ⟨s, hs⟩ := hv
    have hs' := (blackPebblable_map_equiv_iff e he).2 hs
    refine le_antisymm (blackPebblingPrice_le ((blackPebblable_map_equiv_iff e he).2
      (blackPebblable_blackPebblingPrice hs))) (blackPebblingPrice_le ?_)
    exact (blackPebblable_map_equiv_iff e he).1 (blackPebblable_blackPebblingPrice hs')
  · push Not at hv
    rw [blackPebblingPrice_eq_zero_of_forall_not hv, blackPebblingPrice_eq_zero_of_forall_not
      fun s hs => hv s ((blackPebblable_map_equiv_iff e he).1 hs)]

end Cslib.Pebbling
