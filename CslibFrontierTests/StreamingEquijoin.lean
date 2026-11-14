/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Streaming.Frequency

/-!
# Unit tests for equijoin cardinalities

An equijoin of two relations pairs each tuple of the first with each tuple of the second that has
the same join key, so the number of pairs is the join size `Cslib.Streaming.joinSize` of the two
key columns. These tests import only `CslibFrontier.Computability.Streaming.Frequency`, without the
probability library, and check by `decide`:
1. `Cslib.Streaming.length_filter_product_eq_joinSize` on relations with repeated keys and on
   empty relations, and its use in a proof that swapping the relations keeps the count;
2. `Cslib.Streaming.length_filter_product_eq_joinSize_filterMap` on relations whose keys may be
   absent: an absent key, such as an SQL `NULL`, matches nothing, whereas comparing the optional
   keys with `=` would also pair two absent keys.
-/

public section

namespace CslibFrontierTests.StreamingEquijoin

open Cslib.Streaming

/-! ## 1. Total keys -/

/-- A relation of `(key, id)` tuples: key `1` three times and key `2` once. -/
def left : List (ℕ × ℕ) := [(1, 0), (1, 1), (1, 2), (2, 3)]

/-- A relation of `(key, id)` tuples: key `1` twice and key `3` once. -/
def right : List (ℕ × ℕ) := [(1, 4), (1, 5), (3, 6)]

example : left.map Prod.fst = [1, 1, 1, 2] ∧ right.map Prod.fst = [1, 1, 3] := by decide

/-- Each of the three left tuples with key `1` matches each of the two right tuples with key `1`;
keys `2` and `3` match nothing. -/
example : ((left ×ˢ right).filter fun (a, b) => a.1 = b.1).length = 6 := by decide

example : joinSize [1, 1, 1, 2] [1, 1, 3] = 6 := by decide

/-- The same count through the join size of the key columns. -/
example : ((left ×ˢ right).filter fun (a, b) => a.1 = b.1).length = 6 := by
  rw [length_filter_product_eq_joinSize Prod.fst Prod.fst]
  decide

/-- An empty relation joins to nothing, on either side. -/
example : ((([] : List (ℕ × ℕ)) ×ˢ right).filter fun (a, b) => a.1 = b.1).length = 0 ∧
    ((left ×ˢ ([] : List (ℕ × ℕ))).filter fun (a, b) => a.1 = b.1).length = 0 := by
  rw [length_filter_product_eq_joinSize Prod.fst Prod.fst,
    length_filter_product_eq_joinSize Prod.fst Prod.fst]
  decide

/-- Relations without a common key have an empty equijoin. -/
example : ((left ×ˢ [(3, 7)]).filter fun (a, b) => a.1 = b.1).length = 0 := by decide

/-- A client proof: swapping the two relations keeps the size of their equijoin. -/
example {β γ κ : Type*} [DecidableEq κ] (k : β → κ) (l : γ → κ) (u : List β) (v : List γ) :
    ((u ×ˢ v).filter fun (a, b) => k a = l b).length =
      ((v ×ˢ u).filter fun (b, a) => l b = k a).length := by
  rw [length_filter_product_eq_joinSize, length_filter_product_eq_joinSize, joinSize_comm]

/-! ## 2. Keys that may be absent -/

/-- A relation of `(key, id)` tuples whose key may be absent: key `1` twice and no key twice. -/
def leftOpt : List (Option ℕ × ℕ) := [(some 1, 0), (none, 1), (some 1, 2), (none, 3)]

/-- A relation of `(key, id)` tuples whose key may be absent: keys `1` and `2` once each and no key
twice. -/
def rightOpt : List (Option ℕ × ℕ) := [(none, 4), (some 1, 5), (some 2, 6), (none, 7)]

example : leftOpt.filterMap Prod.fst = [1, 1] ∧ rightOpt.filterMap Prod.fst = [1, 2] := by decide

/-- Only the two left tuples with key `1` match, each with the one right tuple with key `1`. -/
example :
    ((leftOpt ×ˢ rightOpt).filter fun (a, b) => ∃ c, a.1 = some c ∧ b.1 = some c).length = 2 := by
  decide

example :
    ((leftOpt ×ˢ rightOpt).filter fun (a, b) => ∃ c, a.1 = some c ∧ b.1 = some c).length = 2 := by
  rw [length_filter_product_eq_joinSize_filterMap Prod.fst Prod.fst]
  decide

/-- Comparing the optional keys with `=` also pairs the two left and two right tuples without a key,
so the total form over `Option ℕ` counts `2 + 2 · 2 = 6` pairs. -/
example : ((leftOpt ×ˢ rightOpt).filter fun (a, b) => a.1 = b.1).length = 6 := by
  rw [length_filter_product_eq_joinSize Prod.fst Prod.fst]
  decide

end CslibFrontierTests.StreamingEquijoin
