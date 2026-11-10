/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Algorithms.Lean.LempelZiv.LZ78Bits
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

/-!
# Tests for Lempel–Ziv incremental parsing (LZ78)

Concrete runs of `CslibFrontier.Algorithms.Lean.LempelZiv`:

* the example `ABBABBABBBAABABAA` of [CoverThomas2006], Ch. 13: its phrases, its
  (pointer, symbol) pairs, and its bit code of `17 + 8 = 25` bits;
* edge cases: the empty input, a last phrase that repeats an earlier one, a phrase sequence that
  is not tree structured, and bit strings that do not decode;
* `1 ^ 100` with `14` phrases and `55` bits, against the exact length formula;
* the distinct-parsing inequality on small instances, and an input length (`n = 256`, `k = 2`)
  at which the hypotheses `2 ≤ n` and `ε_n < 1` of the `n / ((1 - ε_n) log n)` bound hold,
  evaluated through the public `epsilon_def` (this file is a `module`, so it sees only the
  public API).
-/

public section

namespace CslibFrontierTests.Algorithms.Lean.LempelZiv

open Cslib.Algorithms.Lean.LempelZiv Cslib.Algorithms.Lean.LempelZiv.LZ78
open Cslib.Algorithms.Lean.LempelZiv.DistinctParsing (epsilon epsilon_def)

/-! ### The Cover–Thomas example -/

/-- `ABBABBABBBAABABAA` parses as `A, B, BA, BB, AB, BBA, ABA, BAA`. -/
example : parse "ABBABBABBBAABABAA".toList =
    ["A", "B", "BA", "BB", "AB", "BBA", "ABA", "BAA"].map String.toList := by
  decide

/-- Its (pointer, symbol) pairs. -/
example : encode "ABBABBABBBAABABAA".toList =
    [(0, 'A'), (0, 'B'), (2, 'A'), (2, 'B'), (1, 'B'), (4, 'A'), (5, 'A'), (3, 'A')] := by
  decide

/-- Decoding the pairs gives the input back. -/
example : decode [(0, 'A'), (0, 'B'), (2, 'A'), (2, 'B'), (1, 'B'), (4, 'A'), (5, 'A'),
    (3, 'A')] = "ABBABBABBBAABABAA".toList := by
  decide

/-- Its last phrase `BAA` is new, so all eight phrases are distinct
(`nodup_parse_of_getLast_notMem`). -/
example : (parse "ABBABBABBBAABABAA".toList).Nodup :=
  nodup_parse_of_getLast_notMem _ (by decide)

/-- The same input over `Fin 2` (`A = 0`, `B = 1`). -/
def ct : List (Fin 2) := [0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0]

/-- Its bit code has `∑_{i=1}^{8} (⌈log₂ i⌉ + 1) = 17 + 8 = 25` bits. -/
example : (encodeBits (Equiv.refl _) ct).length = 25 := by
  rw [length_encodeBits]
  decide

/-- The bit code is lossless (`decodeBits_encodeBits`). -/
example : decodeBits (Equiv.refl _) (encodeBits (Equiv.refl _) ct) = some ct :=
  decodeBits_encodeBits _ le_rfl ct

/-! ### Edge cases -/

/-- The empty input has no phrases and an empty code. -/
example : parse ([] : List (Fin 2)) = [] ∧ encodeBits (Equiv.refl (Fin 2)) [] = [] := by
  decide

/-- The last phrase may repeat an earlier one: `AA` parses as `A, A`, so the parse is not
duplicate free, but the phrases before the last are. -/
example : parse "AA".toList = ["A", "A"].map String.toList ∧ ¬ (parse "AA".toList).Nodup ∧
    (parse "AA".toList).dropLast.Nodup := by
  decide

/-- The repeated last phrase `A` is still encoded as the empty phrase followed by `A`. -/
example : encode "AA".toList = [(0, 'A'), (0, 'A')] ∧
    decode (encode "AA".toList) = "AA".toList := by
  decide

/-- A phrase sequence that is not tree structured: `AB` is not `[]` followed by one symbol. -/
example : ¬ IsTreeStructured [] [['A', 'B']] := by
  simp

/-- Over three symbols every symbol takes `⌈log₂ 3⌉ = 2` bits, so the symbol number `3` is
rejected... -/
example : decodeBits (Equiv.refl (Fin 3)) [true, true] = none := by
  decide

/-- ... and so is a truncated pair. -/
example : decodeBits (Equiv.refl (Fin 3)) [true] = none := by
  decide

/-! ### A long run -/

/-- `1 ^ 100` parses into the phrases `1 ^ 1, …, 1 ^ 13` and the repeated `1 ^ 9`. -/
example : (parse (List.replicate 100 (1 : Fin 2))).map List.length =
    (List.range 13).map (· + 1) ++ [9] := by
  decide

/-- Its code has `∑_{i=1}^{14} (⌈log₂ i⌉ + 1) = 41 + 14 = 55` bits. -/
example : (encodeBits (Equiv.refl _) (List.replicate 100 (1 : Fin 2))).length = 55 := by
  rw [length_encodeBits]
  decide

/-! ### The distinct-parsing bound -/

/-- `m * c ≤ n + 2 * k ^ m` with `m = 2`, `c = 8`, `n = 17`, `k = 2`: `16 ≤ 25`. -/
example : 2 * (parse ct).length ≤ ct.length + 2 * Fintype.card (Fin 2) ^ 2 :=
  mul_length_parse_le (by simp) ct 2

/-- The example has `c = 8` phrases. -/
example : (parse ct).length = 8 := by
  decide

/-- `c log_k c ≤ n + 2 c` for `1 ^ 100`: `14 * 3 ≤ 100 + 28`. -/
example : (parse (List.replicate 100 (1 : Fin 2))).length *
      Nat.log (Fintype.card (Fin 2)) (parse (List.replicate 100 (1 : Fin 2))).length ≤
    100 + 2 * (parse (List.replicate 100 (1 : Fin 2))).length := by
  simpa using length_parse_mul_log_le (List.replicate 100 (1 : Fin 2))

/-- At `n = 256` and `k = 2`, `ε_n = (log₂ 8 + 4) / 8 = 7 / 8 < 1`, so the hypotheses of
`length_parse_le_div` hold for every input of length `256`. -/
example : epsilon 2 256 < 1 := by
  have h8 : Real.logb 2 (256 : ℕ) = 8 := by
    rw [show ((256 : ℕ) : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one]
    · norm_num
    · norm_num
  have h3 : Real.logb 2 8 = 3 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one]
    · norm_num
    · norm_num
  rw [epsilon_def, Nat.cast_ofNat, h8, h3]
  norm_num

end CslibFrontierTests.Algorithms.Lean.LempelZiv
