/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.Savitch
public import CslibFrontier.Computability.Pebbling.Basic
public import CslibFrontier.Foundations.Data.BitString.Support
import Cslib.Foundations.Semantics.LTS.Relation
import Mathlib.Data.Fintype.Powerset

/-!
# Black pebble configurations as words

A configuration of the black pebble game on `Fin N` is a word of `N` bits, its indicator word
`Cslib.BitString.indicatorList`, bit `i` recording whether vertex `i` carries a pebble. A legal move
with at most `s` pebbles flips one bit (`Cslib.Pebbling.wordStep`): it clears a bit, or sets the
bit of a vertex
that is ready, meaning that all its predecessors carry pebbles. Readiness is a parameter, a
Boolean test on words, so that a machine can evaluate it directly from its own description of the
graph.

There are `2 ^ N` configurations, so every reachable configuration is reachable within `2 ^ N`
moves, and the midpoint recursion of Savitch's theorem (`Cslib.Reachability.reach`) decides
reachability in the game at depth `N`. In particular it decides whether a vertex is pebblable with
`s` pebbles. A simulation that walks this recursion stores one configuration per level, instead
of a whole pebbling strategy.

## Main definitions

* `Cslib.Pebbling.wordStep`: one legal move with at most `s` pebbles, on words.

## Main results

* `Cslib.Pebbling.wordStep_indicatorList_iff`: on configuration words, a step is a legal move that
  changes the configuration.
* `Cslib.Pebbling.reach_wordStep_iff_canReach`: the recursion at depth `N` decides reachability in
  the game.
* `Cslib.Pebbling.reach_wordStep_iff_blackPebblable`: the recursion at depth `N` decides
  pebblability.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
-/

public section

namespace Cslib.Pebbling

open Cslib.BitString (supportOfList indicatorList length_indicatorList supportOfList_indicatorList
  indicatorList_supportOfList indicatorList_inj count_true_indicatorList getD_indicatorList
  indicatorList_insert indicatorList_erase indicatorList_empty)
open Cslib.Reachability (reach reach_iff)

variable {N : ℕ}

/-! ### Moves on words -/

/-- One legal move with at most `s` pebbles, on words: `v` is `u` with one bit flipped, either
cleared or set at a position that `ready u` declares ready, and `v` has at most `s` bits set. -/
@[expose] def wordStep (ready : List Bool → ℕ → Bool) (s : ℕ) (u v : List Bool) : Bool :=
  (List.range u.length).any fun i =>
    (u.getD i false || ready u i) && decide (v = u.set i (!u.getD i false)) &&
      decide (v.count true ≤ s)

variable {G : Digraph (Fin N)} {ready : List Bool → ℕ → Bool} {s : ℕ}

/-- **On configuration words, a step is a legal move that changes the configuration**, when
`ready` tests on configuration words that all predecessors carry pebbles. -/
theorem wordStep_indicatorList_iff
    (hready : ∀ C (i : Fin N), ready (indicatorList C) i = true ↔ ∀ u, G.Adj u i → u ∈ C)
    {C D : Finset (Fin N)} :
    wordStep ready s (indicatorList C) (indicatorList D) = true ↔
      C ≠ D ∧ (blackPebbleGame G s).UnlabelledTr C D := by
  simp only [wordStep, List.any_eq_true, List.mem_range, length_indicatorList, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, count_true_indicatorList]
  constructor
  · rintro ⟨i, hi, ⟨hlegal, hD⟩, hcard⟩
    have hget := getD_indicatorList C ⟨i, hi⟩
    rw [hget] at hlegal hD
    by_cases hC : (⟨i, hi⟩ : Fin N) ∈ C
    · rw [decide_eq_true hC, Bool.not_true, ← indicatorList_erase C ⟨i, hi⟩,
        indicatorList_inj] at hD
      subst hD
      exact ⟨(Finset.erase_ne_self.2 hC).symm, _, .remove, hcard⟩
    · rw [decide_eq_false hC, Bool.not_false, ← indicatorList_insert C ⟨i, hi⟩,
        indicatorList_inj] at hD
      subst hD
      have hready' := hlegal.resolve_left (by simp [hC])
      exact ⟨(Finset.insert_ne_self.2 hC).symm, _, .place ((hready C _).1 hready'), hcard⟩
  · rintro ⟨hne, m, hstep, hcard⟩
    cases hstep with
    | @place v hv =>
      have hvC : v ∉ C := fun h => hne (Finset.insert_eq_of_mem h).symm
      refine ⟨v, v.isLt, ⟨?_, ?_⟩, hcard⟩
      · exact Or.inr ((hready C v).2 hv)
      · rw [getD_indicatorList, decide_eq_false hvC, Bool.not_false, indicatorList_insert]
    | @remove v =>
      have hvC : v ∈ C := by
        by_contra h
        exact hne (Finset.erase_eq_of_notMem h).symm
      refine ⟨v, v.isLt, ⟨?_, ?_⟩, hcard⟩
      · rw [getD_indicatorList, decide_eq_true hvC]
        exact Or.inl rfl
      · rw [getD_indicatorList, decide_eq_true hvC, Bool.not_true, indicatorList_erase]

/-- Steps that stay put can be dropped from a walk. -/
private theorem reflTransGen_ne {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen (fun x y => x ≠ y ∧ r x y) a b := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    by_cases hne : b = c
    · exact hne ▸ ih
    · exact ih.tail ⟨hne, hbc⟩

/-- **Savitch's recursion decides reachability in the pebble game.** Between configuration words,
the midpoint recursion at depth `N` holds exactly when the game with `s` pebbles can move from one
configuration to the other. -/
theorem reach_wordStep_iff_canReach
    (hready : ∀ C (i : Fin N), ready (indicatorList C) i = true ↔ ∀ u, G.Adj u i → u ∈ C)
    {C D : Finset (Fin N)} :
    reach (wordStep ready s) N N (indicatorList C) (indicatorList D) = true ↔
      (blackPebbleGame G s).CanReach C D := by
  rw [reach_iff (length_indicatorList C) (length_indicatorList D),
    ← LTS.reflTransGen_unlabelledTr_iff]
  constructor
  · intro h
    have h' := Relation.ReflTransGen.lift (supportOfList N)
      (p := (blackPebbleGame G s).UnlabelledTr) (fun a b ⟨ha, hb, hab⟩ => by
        rw [← indicatorList_supportOfList ha, ← indicatorList_supportOfList hb] at hab
        exact ((wordStep_indicatorList_iff hready).1 hab).2) _ _ h.reflTransGen
    simpa only [Function.onFun, supportOfList_indicatorList] using h'
  · intro h
    have hcard : Nat.card (Finset (Fin N)) ≤ 2 ^ N + 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]
      exact Nat.le_succ _
    exact ((Relation.reflTransGen_iff_relatesWithinSteps hcard).1 (reflTransGen_ne h)).map
      indicatorList fun a b hab =>
        ⟨length_indicatorList a, length_indicatorList b, (wordStep_indicatorList_iff hready).2 hab⟩

/-- **Savitch's recursion decides black pebblability.** From the zero word, the midpoint recursion
at depth `N` reaches the word of the single pebble `v` exactly when `v` is pebblable with `s`
pebbles. -/
theorem reach_wordStep_iff_blackPebblable
    (hready : ∀ C (i : Fin N), ready (indicatorList C) i = true ↔ ∀ u, G.Adj u i → u ∈ C)
    {v : Fin N} :
    reach (wordStep ready s) N N (List.replicate N false) (indicatorList {v}) = true ↔
      BlackPebblable G s v := by
  rw [← indicatorList_empty, reach_wordStep_iff_canReach hready,
    blackPebblable_iff_exists_mTr_singleton]
  rfl

end Cslib.Pebbling
