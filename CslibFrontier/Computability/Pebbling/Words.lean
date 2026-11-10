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

A configuration of the black pebble game on `Fin N` is a word of `N` bits, bit `i` recording
whether vertex `i` carries a pebble (`Cslib.Pebbling.configWord`). A legal move with at most `s`
pebbles flips one bit (`Cslib.Pebbling.wordStep`): it clears a bit, or sets the bit of a vertex
that is ready, meaning that all its predecessors carry pebbles. Readiness is a parameter, a
Boolean test on words, so that a machine can evaluate it directly from its own description of the
graph.

There are `2 ^ N` configurations, so every reachable configuration is reachable within `2 ^ N`
moves, and the midpoint recursion of Savitch's theorem (`Cslib.Reachability.reach`) decides
reachability in the game at depth `N`. In particular it decides whether a vertex is pebblable with
`s` pebbles. A simulation that walks this recursion stores one configuration per level, instead
of a whole pebbling strategy.

## Main definitions

* `Cslib.Pebbling.configWord`: the bit word of a configuration.
* `Cslib.Pebbling.wordStep`: one legal move with at most `s` pebbles, on words.

## Main results

* `Cslib.Pebbling.wordStep_configWord_iff`: on configuration words, a step is a legal move that
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

open Cslib.BitString (supportOfList supportOfList_ofFn_decide ofFn_decide_mem_supportOfList
  card_supportOfList_of_length)
open Cslib.Reachability (reach reach_iff)

variable {N : ℕ}

/-! ### Configurations as words -/

/-- The word of a configuration: bit `i` records whether vertex `i` carries a pebble. -/
def configWord (C : Finset (Fin N)) : List Bool :=
  List.ofFn fun i => decide (i ∈ C)

@[simp] theorem length_configWord (C : Finset (Fin N)) : (configWord C).length = N := by
  rw [configWord, List.length_ofFn]

@[simp] theorem supportOfList_configWord (C : Finset (Fin N)) :
    supportOfList N (configWord C) = C := by
  rw [configWord, supportOfList_ofFn_decide]

/-- Every word of length `N` is the word of its support. -/
theorem configWord_supportOfList {w : List Bool} (hw : w.length = N) :
    configWord (supportOfList N w) = w := by
  rw [configWord, ofFn_decide_mem_supportOfList hw]

theorem configWord_injective : Function.Injective (configWord (N := N)) := fun C D h => by
  rw [← supportOfList_configWord C, h, supportOfList_configWord]

@[simp] theorem configWord_inj {C D : Finset (Fin N)} : configWord C = configWord D ↔ C = D :=
  configWord_injective.eq_iff

theorem count_true_configWord (C : Finset (Fin N)) : (configWord C).count true = C.card := by
  rw [← card_supportOfList_of_length (length_configWord C), supportOfList_configWord]

theorem getD_configWord (C : Finset (Fin N)) (i : Fin N) :
    (configWord C).getD i false = decide (i ∈ C) := by
  simp [configWord]

/-- Placing a pebble sets its bit. -/
theorem configWord_insert (C : Finset (Fin N)) (i : Fin N) :
    configWord (insert i C) = (configWord C).set i true := by
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp only [configWord, List.getElem_ofFn, List.getElem_set, Finset.mem_insert]
  by_cases h : (i : ℕ) = j
  · simp [h, Fin.ext_iff]
  · simp [h, Fin.ext_iff, Ne.symm h]

/-- Removing a pebble clears its bit. -/
theorem configWord_erase (C : Finset (Fin N)) (i : Fin N) :
    configWord (C.erase i) = (configWord C).set i false := by
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp only [configWord, List.getElem_ofFn, List.getElem_set, Finset.mem_erase]
  by_cases h : (i : ℕ) = j
  · simp [h, Fin.ext_iff]
  · simp [h, Fin.ext_iff, Ne.symm h]

@[simp] theorem configWord_empty : configWord (∅ : Finset (Fin N)) = List.replicate N false := by
  simp [configWord, List.ofFn_const]

/-- The word of a single pebble on `v`: the zero word with bit `v` set. -/
theorem configWord_singleton (v : Fin N) :
    configWord {v} = (List.replicate N false).set v true := by
  rw [← configWord_empty, ← configWord_insert, insert_empty_eq]

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
theorem wordStep_configWord_iff
    (hready : ∀ C (i : Fin N), ready (configWord C) i = true ↔ ∀ u, G.Adj u i → u ∈ C)
    {C D : Finset (Fin N)} :
    wordStep ready s (configWord C) (configWord D) = true ↔
      C ≠ D ∧ (blackPebbleGame G s).UnlabelledTr C D := by
  simp only [wordStep, List.any_eq_true, List.mem_range, length_configWord, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, count_true_configWord]
  constructor
  · rintro ⟨i, hi, ⟨hlegal, hD⟩, hcard⟩
    have hget := getD_configWord C ⟨i, hi⟩
    rw [hget] at hlegal hD
    by_cases hC : (⟨i, hi⟩ : Fin N) ∈ C
    · rw [decide_eq_true hC, Bool.not_true, ← configWord_erase C ⟨i, hi⟩, configWord_inj] at hD
      subst hD
      exact ⟨(Finset.erase_ne_self.2 hC).symm, _, .remove, hcard⟩
    · rw [decide_eq_false hC, Bool.not_false, ← configWord_insert C ⟨i, hi⟩, configWord_inj] at hD
      subst hD
      have hready' := hlegal.resolve_left (by simp [hC])
      exact ⟨(Finset.insert_ne_self.2 hC).symm, _, .place ((hready C _).1 hready'), hcard⟩
  · rintro ⟨hne, m, hstep, hcard⟩
    cases hstep with
    | @place v hv =>
      have hvC : v ∉ C := fun h => hne (Finset.insert_eq_of_mem h).symm
      refine ⟨v, v.isLt, ⟨?_, ?_⟩, hcard⟩
      · exact Or.inr ((hready C v).2 hv)
      · rw [getD_configWord, decide_eq_false hvC, Bool.not_false, configWord_insert]
    | @remove v =>
      have hvC : v ∈ C := by
        by_contra h
        exact hne (Finset.erase_eq_of_notMem h).symm
      refine ⟨v, v.isLt, ⟨?_, ?_⟩, hcard⟩
      · rw [getD_configWord, decide_eq_true hvC]
        exact Or.inl rfl
      · rw [getD_configWord, decide_eq_true hvC, Bool.not_true, configWord_erase]

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
    (hready : ∀ C (i : Fin N), ready (configWord C) i = true ↔ ∀ u, G.Adj u i → u ∈ C)
    {C D : Finset (Fin N)} :
    reach (wordStep ready s) N N (configWord C) (configWord D) = true ↔
      (blackPebbleGame G s).CanReach C D := by
  rw [reach_iff (length_configWord C) (length_configWord D),
    ← LTS.reflTransGen_unlabelledTr_iff]
  constructor
  · intro h
    have h' := Relation.ReflTransGen.lift (supportOfList N)
      (p := (blackPebbleGame G s).UnlabelledTr) (fun a b ⟨ha, hb, hab⟩ => by
        rw [← configWord_supportOfList ha, ← configWord_supportOfList hb] at hab
        exact ((wordStep_configWord_iff hready).1 hab).2) _ _ h.reflTransGen
    simpa only [Function.onFun, supportOfList_configWord] using h'
  · intro h
    have hcard : Nat.card (Finset (Fin N)) ≤ 2 ^ N + 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]
      exact Nat.le_succ _
    exact ((Relation.reflTransGen_iff_relatesWithinSteps hcard).1 (reflTransGen_ne h)).map
      configWord fun a b hab =>
        ⟨length_configWord a, length_configWord b, (wordStep_configWord_iff hready).2 hab⟩

/-- **Savitch's recursion decides black pebblability.** From the zero word, the midpoint recursion
at depth `N` reaches the word of the single pebble `v` exactly when `v` is pebblable with `s`
pebbles. -/
theorem reach_wordStep_iff_blackPebblable
    (hready : ∀ C (i : Fin N), ready (configWord C) i = true ↔ ∀ u, G.Adj u i → u ∈ C)
    {v : Fin N} :
    reach (wordStep ready s) N N (List.replicate N false) (configWord {v}) = true ↔
      BlackPebblable G s v := by
  rw [← configWord_empty, reach_wordStep_iff_canReach hready,
    blackPebblable_iff_exists_mTr_singleton]
  rfl

end Cslib.Pebbling
