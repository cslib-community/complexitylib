/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.LempelZiv.DistinctParsing
public import CslibFrontier.Algorithms.Lean.LempelZiv.LZ78

/-!
# The number of LZ78 phrases

The LZ78 parse (`Cslib.Algorithms.Lean.LempelZiv.LZ78.parse`) is a distinct parsing except
possibly for its last phrase, which may repeat an earlier one. The distinct-parsing bound
(`CslibFrontier.Algorithms.Lean.LempelZiv.DistinctParsing`) still applies: the number `c` of phrases
of an input of length `n` over an alphabet of size `k ≥ 2` satisfies `m * c ≤ n + 2 * k ^ m` for
every `m`, hence `c * ⌊log_k c⌋ ≤ n + 2 c` and `c ≤ n / ((1 - ε_n) log_k n)` with `ε_n → 0`
([CoverThomas2006], §13.5, there for binary inputs).

## Main results

* `Cslib.Algorithms.Lean.LempelZiv.LZ78.mul_length_parse_le`: `m * c ≤ n + 2 * k ^ m`.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.length_parse_mul_log_le`: `c * ⌊log_k c⌋ ≤ n + 2 c`.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.length_parse_mul_logb_sub_le`,
  `Cslib.Algorithms.Lean.LempelZiv.LZ78.length_parse_le_div`: the Cover–Thomas forms
  `c (log_k n - log_k log_k n - 4) ≤ n` and `c ≤ n / ((1 - ε_n) log_k n)`.

## References

* [ZivLempel1978] J. Ziv and A. Lempel, *Compression of individual sequences via variable-rate
  coding*, IEEE Trans. Inf. Theory 24(5), 1978.
* [CoverThomas2006] T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed.,
  2006, Ch. 13 (§13.5 for the distinct-parsing lemma).
-/

public section

namespace Cslib.Algorithms.Lean.LempelZiv.LZ78

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The distinct-parsing inequality for LZ78: `m * c ≤ n + 2 * k ^ m` for every `m`, where `c` is
the number of phrases, `n` the input length and `k ≥ 2` the alphabet size. -/
theorem mul_length_parse_le (hα : 2 ≤ Fintype.card α) (x : List α) (m : ℕ) :
    m * (parse x).length ≤ x.length + 2 * Fintype.card α ^ m := by
  have := DistinctParsing.mul_length_le_of_nodup_dropLast hα
    (fun w hw => ne_nil_of_mem_parse w hw) (nodup_dropLast_parse x) m
  rwa [flatten_parse] at this

/-- The number `c` of LZ78 phrases of an input of length `n` over an alphabet of size `k`
satisfies `c * ⌊log_k c⌋ ≤ n + 2 * c`. -/
theorem length_parse_mul_log_le (x : List α) :
    (parse x).length * Nat.log (Fintype.card α) (parse x).length ≤
      x.length + 2 * (parse x).length :=
  DistinctParsing.mul_log_le_of_forall_mul_le fun hk m => mul_length_parse_le hk x m

/-- The number `c` of LZ78 phrases of an input of length `n` over an alphabet of size `k ≥ 2`
satisfies `c * (log_k n - log_k log_k n - 4) ≤ n` ([CoverThomas2006], §13.5). -/
theorem length_parse_mul_logb_sub_le (hα : 2 ≤ Fintype.card α) (x : List α) :
    ((parse x).length : ℝ) * (Real.logb (Fintype.card α) x.length -
      Real.logb (Fintype.card α) (Real.logb (Fintype.card α) x.length) - 4) ≤ x.length :=
  DistinctParsing.mul_logb_sub_le_of_forall_mul_le hα fun m => mul_length_parse_le hα x m

/-- **The number of LZ78 phrases** ([CoverThomas2006], §13.5, there for binary inputs; here for
an alphabet of size `k ≥ 2`): `c(n) ≤ n / ((1 - ε_n) log_k n)`, where `ε_n → 0`
(`DistinctParsing.tendsto_epsilon`). -/
theorem length_parse_le_div (hα : 2 ≤ Fintype.card α) (x : List α) (hn : 2 ≤ x.length)
    (hε : DistinctParsing.epsilon (Fintype.card α) x.length < 1) :
    ((parse x).length : ℝ) ≤
      x.length / ((1 - DistinctParsing.epsilon (Fintype.card α) x.length) *
        Real.logb (Fintype.card α) x.length) :=
  DistinctParsing.le_div_of_forall_mul_le hα (fun m => mul_length_parse_le hα x m) hε hn

end Cslib.Algorithms.Lean.LempelZiv.LZ78
