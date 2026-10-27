/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingParameters
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Algebra.Ring.GeomSum

/-!
# Binary bit cost of the first-success counting parameter

For each fixed width `k`, the existing `countingThresholdBase k` has an ordinary polynomial-time
native machine from binary inverse budget `B` to binary threshold base. The same machine works
for every `B`, including zero. The width is fixed before the input, and is not a runtime unary
parameter.

The proof refines the selector to a bounded first-match scan through its proven logarithmic
exponent bound. Only the exponent indices and logarithms are unary; the retained budget, powers
of two, coefficient sums and integer-test operands remain binary. Existing plain providers charge
the entire candidate-index list, captured input, arithmetic intermediates and final output. The
scan may materialize the candidate list; no sharper polynomial degree or workspace claim is made.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.computableInPolyTime_countingThresholdBase`:
  a uniform binary-input/output certificate for each fixed width.
* `Cslib.Logic.PL.ClauseSet.Sparsification.exists_length_countingThresholdBase_le`:
  the full binary output length is linear in the binary input length, for width-dependent constants.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*, Appendix A.3, pp. 46–47][OpenAI2026ETH]

This is an implementation of the parameter-search bit-cost claim for `σ = 1/B`; it does not
certify tree construction, a counting algorithm, general rational encodings or runtime width.
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

private abbrev Accepts (k B m : ℕ) : Prop :=
  countingBChoiceCoeff k ≤ 2 ^ m ∧
    B * countingBChoiceCoeff k * Nat.clog 2 (4 * countingDepthCoeff k (2 ^ m) * 2 ^ m) ≤
      2 ^ m

private def firstExponent (k D B : ℕ) : ℕ :=
  ((List.range (D + 2 * Nat.clog 2 B + 1)).filter (fun m => decide (Accepts k B m))).headD 0

private def boundedBase (k D B : ℕ) : ℕ :=
  if B = 0 then 2 else 2 ^ firstExponent k D B

private theorem depthCoeff_polyTime (k : ℕ) :
    ComputableInPolyTime (countingDepthCoeff k) encNat encNat := by
  have hsum (n : ℕ) :
      ComputableInPolyTime (fun M : ℕ => ∑ r ∈ range n, (3 * M) ^ r) encNat encNat := by
    induction n with
    | zero => simpa only [range_zero, sum_empty] using (const (encIn := encNat) 0)
    | succ n ih =>
      simpa only [geom_sum_succ, Function.comp_def] using
        binary_add.comp ((binary_mul' (binary_mul' (const 3) id') ih).prod (const 1))
  exact binary_mul' (const 4) (hsum (k - 1))

private theorem accepts_polyTime (k : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (Accepts k p.1 p.2))
      (encPair encNat encUnary) encBool := by
  have hB := fst encNat encUnary
  have hM := binary_two_pow.comp (snd encNat encUnary)
  have hC := (depthCoeff_polyTime k).comp hM
  have hh := unary_to_binary.comp
    (binary_clog_two.comp (binary_mul' (binary_mul' (const 4) hC) hM))
  have hbudget := binary_le' (binary_mul' (binary_mul' hB (const (countingBChoiceCoeff k))) hh) hM
  have hlarge := binary_le' (const (countingBChoiceCoeff k)) hM
  simpa only [Accepts, Bool.decide_and, Function.comp_def] using
    bool_and.comp (hlarge.prod hbudget)

private theorem firstExponent_polyTime (k D : ℕ) :
    ComputableInPolyTime (firstExponent k D) encNat encUnary := by
  have hcount : ComputableInPolyTime (fun B : ℕ => D + 2 * Nat.clog 2 B + 1)
      encNat encUnary :=
    unary_add' (unary_add' (const D) (unary_mul' (const 2) binary_clog_two)) (const 1)
  exact (headD (encA := encUnary) 0).comp
    (filterWithInput (range.comp hcount) (accepts_polyTime k))

private theorem boundedBase_polyTime (k D : ℕ) :
    ComputableInPolyTime (boundedBase k D) encNat encNat := by
  exact ((id' (encIn := encNat)).decide_eq' (const 0)).ite_decide (const 2)
    (binary_two_pow.comp (firstExponent_polyTime k D))

private theorem boundedBase_eq {k D : ℕ} (hk : 2 ≤ k)
    (hD : ∀ B, 1 ≤ B → Nat.clog 2 (countingThresholdBase k B) ≤ D + 2 * Nat.clog 2 B)
    (B : ℕ) : boundedBase k D B = countingThresholdBase k B := by
  by_cases hB : B = 0
  · simp [boundedBase, hB, countingThresholdBase_zero]
  have hB' : 1 ≤ B := by omega
  obtain ⟨m, hm, hfirst⟩ := countingThresholdBase_first hk hB'
  have hmBound : m ≤ D + 2 * Nat.clog 2 B := by
    have h := hD B hB'
    simpa only [hm, Nat.clog_pow 2 m (by decide)] using h
  have hpass : Accepts k B m := by
    simpa only [Accepts, hm] using countingThresholdBase_spec hk hB'
  have hfound : (List.range (D + 2 * Nat.clog 2 B + 1)).find?
      (fun j => decide (Accepts k B j)) = some m := by
    apply List.find?_range_eq_some.mpr
    refine ⟨by simpa only [decide_eq_true_eq] using hpass, ?_, ?_⟩
    · simpa only [List.mem_range] using Nat.lt_succ_of_le hmBound
    · intro j hj
      simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using hfirst j hj
  have hfirstEq : firstExponent k D B = m := by
    simp only [firstExponent, List.headD_eq_head?_getD, List.head?_filter, hfound, Option.getD_some]
  simp only [boundedBase, hB, ↓reduceIte, hfirstEq, hm]

/-- For each fixed width, one native polynomial-time machine computes the unchanged first-success
threshold from a binary inverse budget, returning the complete binary output. Widths zero and one
and inverse budget zero use the existing total default. -/
theorem computableInPolyTime_countingThresholdBase (k : ℕ) :
    ComputableInPolyTime (countingThresholdBase k) encNat encNat := by
  by_cases hk : 2 ≤ k
  · obtain ⟨D, hD⟩ := exists_clog_countingThresholdBase_le hk
    exact (boundedBase_polyTime k D).of_enc_eq fun B =>
      congrArg encNat (boundedBase_eq hk hD B).symm
  · convert (const (encIn := encNat) (encOut := encNat) 2) using 1
    exact funext fun B => countingThresholdBase_of_lt_two (by omega) B

/-- The complete binary output has a linear bit-length bound in the complete binary input.
The additive constant depends only on the fixed width; all inverse budgets, including zero,
are covered. -/
theorem exists_length_countingThresholdBase_le (k : ℕ) :
    ∃ D : ℕ, ∀ B : ℕ, (encNat (countingThresholdBase k B)).length ≤
      D + 2 * (encNat B).length := by
  by_cases hk : 2 ≤ k
  · obtain ⟨D, hD⟩ := exists_clog_countingThresholdBase_le hk
    refine ⟨D + 2, fun B => ?_⟩
    by_cases hB : B = 0
    · subst B
      rw [countingThresholdBase_zero]
      change 2 ≤ D + 2 + 2 * 0
      omega
    have hB' : 1 ≤ B := by omega
    obtain ⟨m, hm, _⟩ := countingThresholdBase_first hk hB'
    have hmBound := hD B hB'
    have hclog : Nat.clog 2 B ≤ B.size := Nat.clog_le_of_le_pow (Nat.lt_size_self B).le
    simp only [hm, Nat.clog_pow 2 m (by decide)] at hmBound
    simp only [hm, encNat_apply, Nat.size_eq_bits_len, Nat.size_pow]
    omega
  · refine ⟨2, fun B => ?_⟩
    rw [countingThresholdBase_of_lt_two (by omega)]
    change 2 ≤ 2 + 2 * (encNat B).length
    omega

end Cslib.Logic.PL.ClauseSet.Sparsification
