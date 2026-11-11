/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Mathlib.Control.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# Memoizing effectful calls

`memoize compute` stores the first result of each call in an association list. The underlying
computation may be probabilistic or interact with other stateful services. A cache hit does not
repeat its effects. The representation is an ordinary list, so later computational realizations
can charge for lookup and storage without changing the client program.

## Main definitions

* `Cslib.memoize`: cache one effectful computation per key in a list.

## Main results

* `Cslib.memoize_repeat`: repeated queries share their answer and perform the effect once.
* `Cslib.memoize_map`: injective key representations and mapped values preserve execution.

## References

Adapted from Foundations/Control/Monad/Memoize.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib

universe u v

variable {Key Value : Type u} {m : Type u → Type v} [Monad m] [BEq Key]

/-- Cache the result of the first call at each key, sharing the cache through `StateT`. -/
def memoize (compute : Key → m Value) (key : Key) : StateT (List (Key × Value)) m Value :=
  fun cache => match cache.lookup key with
  | some value => pure (value, cache)
  | none => do
    let value ← compute key
    pure (value, (key, value) :: cache)

/-- A previously stored result is returned without repeating the underlying effect. -/
theorem memoize_of_some (compute : Key → m Value) (key : Key) (cache : List (Key × Value))
    (value : Value) (h : cache.lookup key = some value) :
    memoize compute key cache = pure (value, cache) := by
  simp [memoize, h]

/-- A cache miss performs the underlying computation and stores its result. -/
theorem memoize_of_none (compute : Key → m Value) (key : Key) (cache : List (Key × Value))
    (h : cache.lookup key = none) :
    memoize compute key cache = (do
      let value ← compute key
      pure (value, (key, value) :: cache)) := by
  simp [memoize, h]

/-- Two immediate calls at the same key return the same value and perform the effect once. -/
theorem memoize_repeat [LawfulMonad m] [LawfulBEq Key]
    (compute : Key → m Value) (key : Key) (cache : List (Key × Value)) :
    (do
      let (first, cache') ← memoize compute key cache
      let (second, cache'') ← memoize compute key cache'
      pure ((first, second), cache'')) =
    (do
      let (value, cache') ← memoize compute key cache
      pure ((value, value), cache')) := by
  cases h : cache.lookup key <;> simp [memoize, h]

private theorem lookup_map {Key' Value' : Type u} [BEq Key'] [LawfulBEq Key] [LawfulBEq Key']
    (keyMap : Key ↪ Key') (valueMap : Value → Value') (key : Key) (cache : List (Key × Value)) :
    (cache.map (fun entry => (keyMap entry.1, valueMap entry.2))).lookup (keyMap key) =
      (cache.lookup key).map valueMap := by
  induction cache with
  | nil => rfl
  | cons entry cache ih =>
    rcases entry with ⟨other, value⟩
    by_cases h : key = other
    · subst other
      simp
    · have hmap := keyMap.injective.ne h
      simp [List.lookup_cons, beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr hmap, ih]

/-- Injectively re-encode cache keys and map stored values. If the samplers commute with the
value map, memoization preserves the complete result and re-encoded cache, including duplicates. -/
theorem memoize_map [LawfulMonad m] [LawfulBEq Key]
    {Key' Value' : Type u} [BEq Key'] [LawfulBEq Key']
    (keyMap : Key ↪ Key') (valueMap : Value → Value')
    (compute : Key → m Value) (compute' : Key' → m Value')
    (hcompute : ∀ key, compute' (keyMap key) = valueMap <$> compute key)
    (key : Key) (cache : List (Key × Value)) :
    (fun result => (valueMap result.1,
      result.2.map (fun entry => (keyMap entry.1, valueMap entry.2)))) <$>
        memoize compute key cache =
      memoize compute' (keyMap key)
        (cache.map (fun entry => (keyMap entry.1, valueMap entry.2))) := by
  cases h : cache.lookup key <;>
    simp [memoize, lookup_map, h, hcompute]

/-- Interpreting the effects commutes with memoization, including its final list cache. -/
theorem IsMonadHom.map_memoize {n : Type u → Type*} [Monad n]
    {f : ∀ {α}, m α → n α} (hf : IsMonadHom m n f)
    (compute : Key → m Value) (key : Key) (cache : List (Key × Value)) :
    f (memoize compute key cache) = memoize (fun key => f (compute key)) key cache := by
  cases h : cache.lookup key <;> simp [memoize, h, hf.map_pure, hf.map_bind]

end Cslib
