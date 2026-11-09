/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Algorithms.Lean.LempelZiv.LZ77Count
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

/-!
# Tests for Lempel–Ziv sliding-window parsing (LZ77)

Concrete runs of `CslibFrontier.Algorithms.Lean.LempelZiv.LZ77`:

* the input `ABBABBABBBAABABAA` of the LZ78 tests: its seven phrases (against eight for LZ78),
  its (distance, length, symbol) triples, and decoding;
* an overlapping copy (`a ^ 8` is `a` followed by a copy of length `6` from distance `1`, plus
  `a`), where LZ78 needs four phrases;
* the window: with `W = 0` every phrase is one symbol, and the period-`3` input `abcabcabc` needs
  `W ≥ 3` to copy;
* a history that is not exhaustive, and a factorization that is not a history;
* an input length (`n = 256`, binary alphabet) at which the hypotheses of the
  `n / ((1 - ε_n) log n)` bound hold.

This file is a `module`, so it sees only the public API.
-/

public section

namespace CslibFrontierTests.Algorithms.Lean.LempelZivLZ77

open Cslib.Algorithms.Lean.LempelZiv Cslib.Algorithms.Lean.LempelZiv.LZ77

/-! ### A worked example -/

/-- With a window covering the input, `ABBABBABBBAABABAA` parses as
`A, B, BA, BBABBB, AA, BABA, A`. The fourth phrase copies `BBABB` from distance `3`, so the copy
runs into the phrase itself. -/
example : parse 17 "ABBABBABBBAABABAA".toList =
    ["A", "B", "BA", "BBABBB", "AA", "BABA", "A"].map String.toList := by
  decide +kernel

/-- Its (distance, length, symbol) triples. A literal has distance and length `0`. -/
example : encode 17 "ABBABBABBBAABABAA".toList =
    [(0, 0, 'A'), (0, 0, 'B'), (1, 1, 'A'), (3, 5, 'B'), (4, 1, 'A'), (7, 3, 'A'),
      (0, 0, 'A')] := by
  decide +kernel

/-- Decoding the triples gives the input back. -/
example : decode [(0, 0, 'A'), (0, 0, 'B'), (1, 1, 'A'), (3, 5, 'B'), (4, 1, 'A'), (7, 3, 'A'),
    (0, 0, 'A')] = "ABBABBABBBAABABAA".toList := by
  decide +kernel

/-- The last phrase `A` is reproducible: only the phrases before the last must be new. -/
example : Reproducible 17 "ABBABBABBBAABABA".toList "A".toList := by
  decide +kernel

/-- Its Lempel–Ziv complexity is `7`, while LZ78 uses `8` phrases
(`complexity_le_length_parse`). -/
example : complexity "ABBABBABBBAABABAA".toList = 7 ∧
    (LZ78.parse "ABBABBABBBAABABAA".toList).length = 8 := by
  decide +kernel

/-! ### Overlapping copies -/

/-- `a ^ 8` is `a` followed by six symbols copied from distance `1` and a final `a`. -/
example : parse 8 (List.replicate 8 'a') = [['a'], List.replicate 7 'a'] ∧
    encode 8 (List.replicate 8 'a') = [(0, 0, 'a'), (1, 6, 'a')] := by
  decide +kernel

/-- The decoder copies symbol by symbol, so the overlapping copy decodes correctly. -/
example : decode [(0, 0, 'a'), (1, 6, 'a')] = List.replicate 8 'a' := by
  decide +kernel

/-- LZ78 parses `a ^ 8` as `a, aa, aaa, aa`: four phrases against two. -/
example : LZ78.parse (List.replicate 8 'a') = [['a'], ['a', 'a'], ['a', 'a', 'a'], ['a', 'a']] ∧
    complexity (List.replicate 8 'a') = 2 := by
  decide +kernel

/-! ### The window -/

/-- With window `0` nothing can be copied, so every phrase is a single symbol. -/
example : parse 0 "abab".toList = ["a", "b", "a", "b"].map String.toList := by
  decide +kernel

/-- The period-`3` input `abcabcabc` has no copy within window `2`... -/
example : (parse 2 "abcabcabc".toList).length = 9 := by
  decide +kernel

/-- ... while with window `3` one copy from distance `3` covers the rest. -/
example : parse 3 "abcabcabc".toList = ["a", "b", "c", "abcabc"].map String.toList ∧
    encode 3 "abcabcabc".toList = [(0, 0, 'a'), (0, 0, 'b'), (0, 0, 'c'), (3, 5, 'c')] := by
  decide +kernel

/-! ### Histories -/

/-- `a, a, a` is a history of `aaa` with window `1`, but it is not exhaustive: the second
phrase `a` is reproducible and not last. The greedy parse `a, aa` is shorter
(`length_parse_le_of_isHistory`). -/
example : IsHistory 1 [] [['a'], ['a'], ['a']] ∧ ¬ IsExhaustive 1 [] [['a'], ['a'], ['a']] ∧
    parse 1 "aaa".toList = [['a'], ['a', 'a']] := by
  refine ⟨?_, ?_, by decide +kernel⟩
  · simp only [isHistory_cons, isHistory_nil, and_true]
    decide
  · simp only [isExhaustive_cons, isExhaustive_nil, and_true]
    decide

/-- `ab` is not a history of `ab`: its first symbol `a` cannot be copied from the empty text. -/
example : ¬ IsHistory 5 [] [['a', 'b']] := by
  simp only [isHistory_cons, isHistory_nil, and_true]
  decide

/-! ### The distinct-parsing bound -/

/-- At `n = 256` over `Bool`, `ε_n = (log₂ 8 + 4) / 8 = 7 / 8 < 1`, so `complexity_le_div`
bounds the Lempel–Ziv complexity of every input of length `256` by
`256 / ((1 - ε_256) log₂ 256)`. -/
example (x : List Bool) (hx : x.length = 256) :
    (complexity x : ℝ) ≤ 256 / ((1 - DistinctParsing.epsilon 2 256) * Real.logb 2 256) := by
  have h8 : Real.logb 2 (256 : ℕ) = 8 := by
    rw [show ((256 : ℕ) : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one]
    · norm_num
    · norm_num
  have h3 : Real.logb 2 8 = 3 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one]
    · norm_num
    · norm_num
  have hε : DistinctParsing.epsilon 2 256 < 1 := by
    rw [DistinctParsing.epsilon_def, Nat.cast_ofNat, h8, h3]
    norm_num
  have h := complexity_le_div (by rw [Fintype.card_bool]) x (by omega)
    (by rw [Fintype.card_bool, hx]; exact hε)
  rwa [Fintype.card_bool, hx, Nat.cast_ofNat, Nat.cast_ofNat] at h

end CslibFrontierTests.Algorithms.Lean.LempelZivLZ77
