/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.LempelZiv.LZ77
public import Complexity.Algorithms.Lean.LempelZiv.LZ78Count

/-!
# LZ77 against LZ78

Every LZ78 phrase is an earlier phrase followed by one symbol
(`Cslib.Algorithms.Lean.LempelZiv.LZ78.isTreeStructured_parse`), and an earlier phrase is a copy
from the text already written. So when the window covers the input, the LZ78 parse is an LZ77
history, and the optimality of the exhaustive history
(`Cslib.Algorithms.Lean.LempelZiv.LZ77.length_parse_le_of_isHistory`) gives
`#LZ77 phrases ≤ #LZ78 phrases`. With the distinct-parsing bound for LZ78
(`Cslib.Algorithms.Lean.LempelZiv.LZ78.length_parse_le_div`), the number of LZ77 phrases, and the
Lempel–Ziv complexity, of an input of length `n ≥ 2` over an alphabet of size `k ≥ 2` is at most
`n / ((1 - ε_n) log_k n)`.

## Main results

* `Cslib.Algorithms.Lean.LempelZiv.LZ77.isHistory_of_isTreeStructured`: a tree-structured phrase
  sequence is a history once the window covers the text.
* `Cslib.Algorithms.Lean.LempelZiv.LZ77.length_parse_le_length_parse`: `#LZ77 ≤ #LZ78` for
  `W ≥ n`.
* `Cslib.Algorithms.Lean.LempelZiv.LZ77.length_parse_le_div`,
  `Cslib.Algorithms.Lean.LempelZiv.LZ77.complexity_le_div`: `c ≤ n / ((1 - ε_n) log_k n)`.

## References

* [A. Lempel and J. Ziv, *On the complexity of finite sequences*][LempelZiv1976]
* [J. Ziv and A. Lempel, *Compression of individual sequences via variable-rate
  coding*][ZivLempel1978]
-/

public section

namespace Cslib.Algorithms.Lean.LempelZiv.LZ77

variable {α : Type*}

/-- A tree-structured phrase sequence (every phrase is `[]` or an earlier phrase, followed by one
symbol) whose dictionary entries occur in the text `h` is a history of `h ++ ws.flatten` from `h`,
as long as the window covers the whole text. -/
theorem isHistory_of_isTreeStructured {W : ℕ} :
    ∀ (dict : List (List α)) (h : List α) (ws : List (List α)),
      LZ78.IsTreeStructured dict ws → (∀ q ∈ dict, q <:+: h) →
      (h ++ ws.flatten).length ≤ W → IsHistory W h ws
  | _, h, [], _, _, _ => isHistory_nil W h
  | dict, h, w :: ws, ht, hdict, hW => by
    rw [LZ78.isTreeStructured_cons] at ht
    obtain ⟨⟨q, hq, a, rfl⟩, ht⟩ := ht
    rw [isHistory_cons]
    have hhW : h.length ≤ W := by grind
    refine ⟨by simp, ?_, isHistory_of_isTreeStructured (dict ++ [q ++ [a]]) (h ++ (q ++ [a])) ws
      ht (fun p hp => ?_) (by rwa [List.append_assoc, ← List.flatten_cons])⟩
    · rw [List.dropLast_concat]
      refine reproducible_of_infix hhW ?_
      rcases List.mem_cons.1 hq with rfl | hq
      · exact List.nil_infix
      · exact hdict q hq
    · rcases List.mem_append.1 hp with hp | hp
      · exact (hdict p hp).trans (List.prefix_append h _).isInfix
      · rw [List.mem_singleton.1 hp]
        exact (List.suffix_append _ _).isInfix

variable [DecidableEq α]

/-- When the window covers the input, the LZ78 parse is an LZ77 history. -/
theorem isHistory_lz78Parse {W : ℕ} {x : List α} (hW : x.length ≤ W) :
    IsHistory W [] (LZ78.parse x) :=
  isHistory_of_isTreeStructured [] [] _ (LZ78.isTreeStructured_parse x) (by simp)
    (by simpa using hW)

/-- **LZ77 needs no more phrases than LZ78** when the window covers the input. -/
theorem length_parse_le_length_parse {W : ℕ} {x : List α} (hW : x.length ≤ W) :
    (parse W x).length ≤ (LZ78.parse x).length :=
  length_parse_le_of_isHistory (LZ78.flatten_parse x) (isHistory_lz78Parse hW)

/-- The Lempel–Ziv complexity is at most the number of LZ78 phrases. -/
theorem complexity_le_length_parse (x : List α) : complexity x ≤ (LZ78.parse x).length :=
  length_parse_le_length_parse le_rfl

variable [Fintype α]

/-- The distinct-parsing bound for LZ77: with a window covering the input, the number of phrases
`c` of an input of length `n ≥ 2` over an alphabet of size `k ≥ 2` satisfies
`c ≤ n / ((1 - ε_n) log_k n)` whenever `ε_n < 1`. -/
theorem length_parse_le_div (hα : 2 ≤ Fintype.card α) {W : ℕ} (x : List α) (hW : x.length ≤ W)
    (hn : 2 ≤ x.length) (hε : DistinctParsing.epsilon (Fintype.card α) x.length < 1) :
    ((parse W x).length : ℝ) ≤
      x.length / ((1 - DistinctParsing.epsilon (Fintype.card α) x.length) *
        Real.logb (Fintype.card α) x.length) :=
  (Nat.cast_le.2 (length_parse_le_length_parse hW)).trans (LZ78.length_parse_le_div hα x hn hε)

/-- The Lempel–Ziv complexity of an input of length `n ≥ 2` over an alphabet of size `k ≥ 2` is
at most `n / ((1 - ε_n) log_k n)` whenever `ε_n < 1`. -/
theorem complexity_le_div (hα : 2 ≤ Fintype.card α) (x : List α) (hn : 2 ≤ x.length)
    (hε : DistinctParsing.epsilon (Fintype.card α) x.length < 1) :
    (complexity x : ℝ) ≤
      x.length / ((1 - DistinctParsing.epsilon (Fintype.card α) x.length) *
        Real.logb (Fintype.card α) x.length) :=
  length_parse_le_div hα x le_rfl hn hε

end Cslib.Algorithms.Lean.LempelZiv.LZ77
