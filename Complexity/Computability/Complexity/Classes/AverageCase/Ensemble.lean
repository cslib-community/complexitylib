/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Foundations.Data.BitString.List.Binary
public import Complexity.Probability.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Languages.Probabilistic.BitString
import Complexity.Probability.PMF.Uniform
import Complexity.Tactic.PolyTime
import Mathlib.Data.List.Lex
import Mathlib.Tactic.Ring

/-!
# Distribution ensembles for average-case complexity

An ensemble `D : Cslib.Complexity.Ensemble` is a family of distributions `D.dist n` on binary
words, where `D.dist n` is supported on words of length exactly `n`. This is the ensemble notion of
[Bogdanov and Trevisan, §2.1][BogdanovTrevisan2006] specialized to distributions on `{0,1}^n`, the
setting of their uniform ensemble `U` and of the compression argument in their Claim 20; the
length `n` is then available to algorithms as the length of the input. Ensembles over words of
other polynomially related lengths can be padded to this form.

Two efficiency classes of ensembles are defined.

* `Cslib.Complexity.Ensemble.PComp`, polynomial-time computable ensembles
  [Bogdanov and Trevisan, Definition 2][BogdanovTrevisan2006]: the cumulative distribution
  `Cslib.Complexity.Ensemble.cdf`, the probability of the words of length `|x|` that are at most
  `x`, is a ratio `num x / den x` of naturals computed in polynomial time in binary. On words of a
  fixed length the order used is the numeric order of `Cslib.BitString.binaryValue`, which is the
  lexicographic order of the source (`Cslib.Complexity.Ensemble.binaryValue_le_iff_le`). Values
  are represented exactly as rationals; the source leaves the output representation implicit.
* `Cslib.Complexity.Ensemble.PSamp`, polynomial-time samplable ensembles
  [Bogdanov and Trevisan, Definition 1][BogdanovTrevisan2006]: a native strict-PPT program
  (`Cslib.Probability.IsPPTOn`) given `n` in unary has output distribution exactly `D.dist n`.

The uniform ensemble `Cslib.Complexity.Ensemble.uniform` lies in both classes.

## Main definitions

* `Cslib.Complexity.Ensemble`: distributions on words of each length.
* `Cslib.Complexity.Ensemble.cdf`, `Cslib.Complexity.Ensemble.PComp`,
  `Cslib.Complexity.Ensemble.PSamp`.
* `Cslib.Complexity.Ensemble.uniform`: the uniform ensemble.

## Main results

* `Cslib.Complexity.Ensemble.binaryValue_le_iff_le`: on words of equal length, the numeric order is
  the lexicographic order.
* `Cslib.Complexity.Ensemble.uniform_apply`: a word has uniform probability `2^{-|x|}`.
* `Cslib.Complexity.Ensemble.cdf_uniform`: the uniform cumulative distribution is
  `(binaryValue x + 1) / 2^{|x|}`.
* `Cslib.Complexity.Ensemble.uniform_pComp`, `Cslib.Complexity.Ensemble.uniform_pSamp`.

## References

* [A. Bogdanov, L. Trevisan, *Average-Case Complexity*][BogdanovTrevisan2006]
-/

public section

namespace Cslib.Complexity

open scoped ENNReal
open Turing.MultiTapeTM

/-- An ensemble of distributions on binary words, the `n`-th supported on words of length `n`
[Bogdanov and Trevisan, §2.1][BogdanovTrevisan2006]. -/
structure Ensemble where
  /-- The distribution on words of length `n`. -/
  dist : ℕ → PMF (List Bool)
  /-- Every word in the support of `dist n` has length `n`. -/
  length_eq : ∀ n x, x ∈ (dist n).support → x.length = n

namespace Ensemble

/-- The cumulative distribution `D_{|x|}({y : y ≤ x})` of an ensemble, ordering words of the same
length by their binary value (equivalently, lexicographically:
`Cslib.Complexity.Ensemble.binaryValue_le_iff_le`). -/
@[expose] noncomputable def cdf (D : Ensemble) (x : List Bool) : ℝ≥0∞ :=
  (D.dist x.length).toOuterMeasure
    {y | BitString.binaryValue y ≤ BitString.binaryValue x}

/-- **Polynomial-time computable ensembles**
[Bogdanov and Trevisan, Definition 2][BogdanovTrevisan2006]: the cumulative distribution is a
ratio of two naturals, each computable in polynomial time from `x` and written in binary. -/
@[expose] def PComp (D : Ensemble) : Prop :=
  ∃ num den : List Bool → ℕ, ComputableInPolyTime num encBits encNat ∧
    ComputableInPolyTime den encBits encNat ∧ (∀ x, den x ≠ 0) ∧
    ∀ x, D.cdf x = (num x : ℝ≥0∞) / den x

/-- **Polynomial-time samplable ensembles**
[Bogdanov and Trevisan, Definition 1][BogdanovTrevisan2006]: a native strict-PPT program, given
`n` in unary, samples exactly `D.dist n`. -/
@[expose] def PSamp (D : Ensemble) : Prop :=
  ∃ S : ℕ → ProbComp (List Bool), Probability.IsPPTOn encUnary encBits S ∧
    ∀ n, ProbComp.eval (S n) = D.dist n

/-- The uniform ensemble `U = {U_n}`, with `U_n` uniform on `{0,1}^n`. -/
noncomputable def uniform : Ensemble where
  dist := BitString.uniformList
  length_eq _ _ h := BitString.length_of_mem_support_uniformList h

@[simp] theorem uniform_dist (n : ℕ) : uniform.dist n = BitString.uniformList n := by rfl

private theorem foldl_binaryValue (a : ℕ) (t : List Bool) :
    t.foldl (fun value bit => 2 * value + bit.toNat) a =
      a * 2 ^ t.length + BitString.binaryValue t := by
  induction t generalizing a with
  | nil => simp [BitString.binaryValue]
  | cons b t ih =>
    have h0 : BitString.binaryValue (b :: t) =
        b.toNat * 2 ^ t.length + BitString.binaryValue t := by
      change List.foldl _ 0 (b :: t) = _
      rw [List.foldl_cons, ih]
      ring
    rw [List.foldl_cons, ih, h0, List.length_cons, pow_succ]
    ring

private theorem binaryValue_cons (b : Bool) (t : List Bool) :
    BitString.binaryValue (b :: t) = b.toNat * 2 ^ t.length + BitString.binaryValue t := by
  change List.foldl _ 0 (b :: t) = _
  rw [List.foldl_cons, foldl_binaryValue]
  ring

/-- On words of equal length, numeric order is strict lexicographic order (with
`false < true`). -/
theorem binaryValue_lt_iff_lt {x y : List Bool} (h : x.length = y.length) :
    BitString.binaryValue x < BitString.binaryValue y ↔ x < y := by
  induction x generalizing y with
  | nil =>
    obtain rfl : y = [] := List.length_eq_zero_iff.mp h.symm
    simp
  | cons a s ih =>
    obtain ⟨b, t, rfl⟩ := List.exists_cons_of_length_eq_add_one h.symm
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [binaryValue_cons, binaryValue_cons, List.cons_lt_cons_iff, ← ih h, h]
    have hs := BitString.binaryValue_lt_two_pow s
    have ht := BitString.binaryValue_lt_two_pow t
    rw [h] at hs
    cases a <;> cases b
    all_goals simp only [Bool.toNat_false, Bool.toNat_true, zero_mul, one_mul, zero_add,
      lt_self_iff_false, true_and, false_or, Bool.false_lt_true, Bool.false_eq_true,
      Bool.true_eq_false, false_and, or_false, iff_true, gt_iff_lt, add_lt_add_iff_left]
    all_goals first | omega | exact iff_of_false (by omega) (by decide)

/-- On words of equal length, numeric order is lexicographic order (with `false < true`). -/
theorem binaryValue_le_iff_le {x y : List Bool} (h : x.length = y.length) :
    BitString.binaryValue x ≤ BitString.binaryValue y ↔ x ≤ y := by
  rw [← not_lt, ← not_lt, binaryValue_lt_iff_lt h.symm]

/-- A word has probability `2^{-|x|}` under the uniform ensemble. -/
theorem uniform_apply (x : List Bool) : uniform.dist x.length x = (2 ^ x.length)⁻¹ := by
  have h := BitString.uniformList_map_apply id x.length x
  simp only [PMF.map_id, id_eq] at h
  rw [uniform_dist, h, div_eq_mul_inv]
  have hcard : (Finset.univ.filter fun r : Fin x.length → Bool => List.ofFn r = x).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨x.get, Finset.ext fun r => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hr
      exact List.ofFn_injective (hr.trans (List.ofFn_get x).symm)
    · rintro rfl
      exact List.ofFn_get x
  rw [hcard, Nat.cast_one, one_mul]

private theorem card_le_binaryValue (x : List Bool) :
    (Finset.univ.filter (fun u : Fin x.length → Bool =>
      List.ofFn u ∈ {y | BitString.binaryValue y ≤ BitString.binaryValue x})).card =
      BitString.binaryValue x + 1 := by
  rw [show BitString.binaryValue x + 1 =
    (Finset.range (BitString.binaryValue x + 1)).card from (Finset.card_range _).symm]
  refine Finset.card_bij (fun u _ => BitString.binaryValue (List.ofFn u)) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hu)
  · intro u _ v _ h
    exact List.ofFn_injective
      (BitString.binaryValue_injective_of_length_eq (by simp only [List.length_ofFn]) h)
  · intro k hk
    have hk' : k ≤ BitString.binaryValue x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    obtain ⟨u, hu⟩ := BitString.exists_binaryValue_eq
      (lt_of_le_of_lt hk' (BitString.binaryValue_lt_two_pow x))
    refine ⟨u, ?_, hu⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hu]
    exact hk'

/-- The uniform cumulative distribution of `x` is `(binaryValue x + 1) / 2^{|x|}`. -/
theorem cdf_uniform (x : List Bool) :
    uniform.cdf x = ((BitString.binaryValue x + 1 : ℕ) : ℝ≥0∞) / (2 ^ x.length : ℕ) := by
  classical
  change (BitString.uniformList x.length).toOuterMeasure _ = _
  unfold BitString.uniformList
  rw [PMF.toOuterMeasure_map_apply, Probability.PMF.toOuterMeasure_uniformOfFintype]
  simp only [Set.mem_preimage]
  rw [card_le_binaryValue x, div_eq_mul_inv]
  simp

/-- The uniform ensemble is polynomial-time computable. -/
theorem uniform_pComp : uniform.PComp :=
  ⟨fun x => BitString.binaryValue x + 1, fun x => 2 ^ x.length,
    ComputableInPolyTime.binary_add.comp
      (ComputableInPolyTime.bitsBinaryValue.prod (ComputableInPolyTime.const 1)),
    by polytime, fun _ => by positivity, cdf_uniform⟩

/-- The uniform ensemble is polynomial-time samplable. -/
theorem uniform_pSamp : uniform.PSamp :=
  ⟨BitString.sampleList, Probability.isPPTOn_sampleList, BitString.eval_sampleList⟩

end Ensemble

end Cslib.Complexity
