/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Foundations.Data.BitString.List.BinaryOrder
public import CslibFrontier.Probability.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Union

/-!
# Distribution ensembles for average-case complexity

An ensemble `D : Cslib.Complexity.Ensemble` is a family of distributions `D.dist n` on binary
words, where `D.dist n` is supported on words of length exactly `n`. This is the ensemble notion of
[Bogdanov and Trevisan, §2.1][BogdanovTrevisan2006] specialized to distributions on `{0,1}^n`, the
setting of their uniform ensemble `U` and of the compression argument in their Claim 20; the
length `n` is then available to algorithms as the length of the input. The source also allows
`D_n` to be supported on words of several lengths; such ensembles are not modelled here, and no
reindexing bridge is provided.

Two efficiency classes of ensembles are defined.

* `Cslib.Complexity.Ensemble.PComp`, polynomial-time computable ensembles
  [Bogdanov and Trevisan, Definition 2][BogdanovTrevisan2006]: the cumulative distribution
  `Cslib.Complexity.Ensemble.cdf`, the probability of the words of length `|x|` that are at most
  `x`, is a ratio `num x / den x` of naturals computed in polynomial time in binary. On words of a
  fixed length the order used is the numeric order of `Cslib.BitString.binaryValue`, which is the
  lexicographic order of the source (`Cslib.BitString.binaryValue_le_iff_le`). Values
  are represented exactly as rationals; the source leaves the output representation implicit.
* `Cslib.Complexity.Ensemble.PSamp`, polynomial-time samplable ensembles
  [Bogdanov and Trevisan, Definition 1][BogdanovTrevisan2006]: a native strict-PPT program
  (`Cslib.Probability.IsPPTOn`) given `n` in unary has output distribution exactly `D.dist n`.

The uniform ensemble `Cslib.Complexity.Ensemble.uniform` lies in both classes.

## Main definitions

* `Cslib.Complexity.Ensemble`: distributions on words of each length.
* `Cslib.Complexity.Ensemble.cdf`, `Cslib.Complexity.Ensemble.cdfLo`,
  `Cslib.Complexity.Ensemble.PComp`, `Cslib.Complexity.Ensemble.PSamp`.
* `Cslib.Complexity.Ensemble.uniform`: the uniform ensemble.

## Main results

* `Cslib.Complexity.Ensemble.cdf_eq_cdfLo_add`: the cumulative distribution at `x` is the
  probability below `x` plus that of `x`.
* `Cslib.Complexity.Ensemble.uniform_apply`: a word has uniform probability `2^{-|x|}`.
* `Cslib.Complexity.Ensemble.cdf_uniform`: the uniform cumulative distribution is
  `(binaryValue x + 1) / 2^{|x|}`.
* `Cslib.Complexity.Ensemble.uniform_toOuterMeasure_binaryValue_lt`: the words of length `N` with
  value below `K ≤ 2^N` have uniform probability `K / 2^N`.
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
`Cslib.BitString.binaryValue_le_iff_le`). -/
@[expose] noncomputable def cdf (D : Ensemble) (x : List Bool) : ℝ≥0∞ :=
  (D.dist x.length).toOuterMeasure
    {y | BitString.binaryValue y ≤ BitString.binaryValue x}

/-- The probability `D_{|x|}({y : y < x})` of the words of length `|x|` below `x`. -/
noncomputable def cdfLo (D : Ensemble) (x : List Bool) : ℝ≥0∞ :=
  (D.dist x.length).toOuterMeasure
    {y | BitString.binaryValue y < BitString.binaryValue x}

/-- The cumulative distribution is the probability below `x` plus that of `x`. -/
theorem cdf_eq_cdfLo_add (D : Ensemble) (x : List Bool) :
    D.cdf x = D.cdfLo x + D.dist x.length x := by
  have hset : {y : List Bool | BitString.binaryValue y ≤ BitString.binaryValue x} =
      {y | BitString.binaryValue y < BitString.binaryValue x} ∪
        {y | BitString.binaryValue y = BitString.binaryValue x} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    omega
  have hdisj : Disjoint {y : List Bool | BitString.binaryValue y < BitString.binaryValue x}
      {y | BitString.binaryValue y = BitString.binaryValue x} := by
    rw [Set.disjoint_left]
    intro y h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    omega
  rw [cdf, cdfLo, hset, Probability.PMF.toOuterMeasure_union_of_disjoint _ hdisj]
  congr 1
  rw [PMF.toOuterMeasure_apply, tsum_eq_single x]
  · simp
  · intro y hy
    by_cases hyx : BitString.binaryValue y = BitString.binaryValue x
    · rw [Set.indicator_of_mem (by exact hyx)]
      by_contra hne
      have hsupp : y ∈ (D.dist x.length).support := (PMF.mem_support_iff _ _).mpr hne
      exact hy (BitString.binaryValue_injective_of_length_eq (D.length_eq _ _ hsupp) hyx)
    · rw [Set.indicator_of_notMem (by exact hyx)]

/-- Nothing lies below a word of value `0`. -/
theorem cdfLo_of_binaryValue_eq_zero (D : Ensemble) {x : List Bool}
    (h : BitString.binaryValue x = 0) : D.cdfLo x = 0 := by
  rw [cdfLo, h]
  simp

/-- Below a word of nonzero value lies the cumulative distribution of its predecessor. -/
theorem cdfLo_eq_cdf_predWord (D : Ensemble) {x : List Bool}
    (h : BitString.binaryValue x ≠ 0) : D.cdfLo x = D.cdf (BitString.predWord x) := by
  rw [cdfLo, cdf, BitString.length_predWord, BitString.binaryValue_predWord]
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq]
  omega

/-- The cumulative distribution at `x` is at most the probability below any later word of the same
length. -/
theorem cdf_le_cdfLo (D : Ensemble) {x x' : List Bool} (hlen : x.length = x'.length)
    (h : BitString.binaryValue x < BitString.binaryValue x') : D.cdf x ≤ D.cdfLo x' := by
  rw [cdf, cdfLo, hlen]
  refine PMF.toOuterMeasure_mono _ fun y hy => ?_
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hy ⊢
  omega

theorem cdf_le_one (D : Ensemble) (x : List Bool) : D.cdf x ≤ 1 :=
  Probability.PMF.toOuterMeasure_le_one _ _

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

/-- The words of length `N` with value below `K ≤ 2^N` have uniform probability `K / 2^N`. -/
theorem uniform_toOuterMeasure_binaryValue_lt {N K : ℕ} (hK : K ≤ 2 ^ N) :
    (uniform.dist N).toOuterMeasure {r | BitString.binaryValue r < K} =
      (K : ℝ≥0∞) / (2 ^ N : ℕ) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK0
  · simp
  · obtain ⟨u, hu⟩ := BitString.exists_binaryValue_eq (t := N) (k := K - 1) (by omega)
    have h := cdf_uniform (List.ofFn u)
    rw [cdf, List.length_ofFn, hu, show K - 1 + 1 = K by omega] at h
    rw [← h]
    congr 1
    ext r
    simp only [Set.mem_ofPred_eq]
    omega

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
