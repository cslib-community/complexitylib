/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.AverageCase.Ensemble
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Probability.PMF.Union
import Complexity.Tactic.PolyTime

/-!
# Collapsing the uniform ensemble at a prefix code

A *header parser* recognizes, in polynomial time, words that begin with a *header*: a word from a
prefix-free code that is recognized from any of its extensions. Flipping uniform bits until either
a header has been read or `N` bits have been flipped, and in the former case padding the header
with ones to length `N`, gives the distribution `Cslib.Complexity.HeaderParser.ensemble`. This is
how [Bogdanov and Trevisan, §3.2][BogdanovTrevisan2006] define the "uniform" ensemble `U^BH` of
instances of the bounded halting problem; this module develops the construction for an arbitrary
header parser.

The collapse map is monotone in the numeric order of words of each length, and it maps the block of
words with a given header to the top word of that block. Its cumulative distribution is therefore
an exact dyadic rational with a polynomial-time numerator
(`Cslib.Complexity.HeaderParser.cdf_ensemble`), so the collapsed ensemble is polynomial-time
computable, and a padded header `h` has probability exactly `2^{-|h|}`.

## Main definitions

* `Cslib.Complexity.HeaderParser`: a polynomial-time recognizer of a prefix-free code of headers.
* `Cslib.Complexity.HeaderParser.collapse`: pad the header of a word with ones.
* `Cslib.Complexity.HeaderParser.ensemble`: the image of the uniform ensemble under collapsing.

## Main results

* `Cslib.Complexity.HeaderParser.binaryValue_collapse_le_iff`: the collapse map is monotone, with
  explicit thresholds `Cslib.Complexity.HeaderParser.cdfNum`.
* `Cslib.Complexity.HeaderParser.cdf_ensemble`: the cumulative distribution is
  `cdfNum y / 2^{|y|}`.
* `Cslib.Complexity.HeaderParser.pComp_ensemble`: the collapsed ensemble is polynomial-time
  computable.
* `Cslib.Complexity.HeaderParser.ensemble_dist_collapse`: a padded header `h` has probability
  `2^{-|h|}`.

## References

* [A. Bogdanov, L. Trevisan, *Average-Case Complexity*][BogdanovTrevisan2006]
-/

public section

namespace Cslib.Complexity

open scoped ENNReal
open Turing.MultiTapeTM

/-- A **header parser**: a test `valid` for the words that begin with a header and the header
`header r` of such a word, a prefix of `r` that is recognized, as the same header, from every word
extending it. The headers thus form a prefix-free code. -/
structure HeaderParser where
  /-- Whether the word begins with a header. -/
  valid : List Bool → Bool
  /-- The header at the start of the word, when `valid` holds. -/
  header : List Bool → List Bool
  /-- The header of a valid word is a prefix of it. -/
  header_isPrefix : ∀ r, valid r = true → header r <+: r
  /-- A header is recognized from every word extending it. -/
  valid_of_isPrefix : ∀ r r', valid r = true → header r <+: r' →
    valid r' = true ∧ header r' = header r

namespace HeaderParser

variable (H : HeaderParser)

/-- Replace everything after the header of `r` by ones (`r` itself if it has no header). -/
@[expose] def collapse (r : List Bool) : List Bool :=
  if H.valid r then H.header r ++ List.replicate (r.length - (H.header r).length) true else r

theorem length_header_le {r : List Bool} (hv : H.valid r = true) :
    (H.header r).length ≤ r.length :=
  (H.header_isPrefix r hv).length_le

theorem collapse_of_valid {r : List Bool} (hv : H.valid r = true) :
    H.collapse r = H.header r ++ List.replicate (r.length - (H.header r).length) true := by
  simp only [collapse, hv, ite_true]

theorem collapse_of_not_valid {r : List Bool} (hv : H.valid r = false) : H.collapse r = r := by
  simp only [collapse, hv, Bool.false_eq_true, ite_false]

@[simp]
theorem length_collapse (r : List Bool) : (H.collapse r).length = r.length := by
  by_cases hv : H.valid r = true
  · rw [H.collapse_of_valid hv, List.length_append, List.length_replicate]
    have := H.length_header_le hv
    omega
  · rw [H.collapse_of_not_valid (by simpa using hv)]

theorem valid_collapse {r : List Bool} (hv : H.valid r = true) :
    H.valid (H.collapse r) = true ∧ H.header (H.collapse r) = H.header r :=
  H.valid_of_isPrefix r _ hv (by rw [H.collapse_of_valid hv]; exact List.prefix_append _ _)

/-- The image under `collapse` of the uniform ensemble: flip uniform bits until a header has been
read, then pad the header with ones. -/
@[expose] noncomputable def ensemble : Ensemble where
  dist N := (Ensemble.uniform.dist N).map H.collapse
  length_eq N y hy := by
    rw [PMF.support_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    rw [H.length_collapse]
    exact Ensemble.uniform.length_eq N r hr

theorem ensemble_dist (N : ℕ) : H.ensemble.dist N = (Ensemble.uniform.dist N).map H.collapse :=
  rfl

/-! ### The block of a header -/

/-- The least value of a word of length `|r|` with the header of `r`. -/
def lo (r : List Bool) : ℕ :=
  BitString.binaryValue (H.header r) * 2 ^ (r.length - (H.header r).length)

/-- One more than the greatest value of a word of length `|r|` with the header of `r`. -/
def hi (r : List Bool) : ℕ :=
  (BitString.binaryValue (H.header r) + 1) * 2 ^ (r.length - (H.header r).length)

theorem lo_le_hi (r : List Bool) : H.lo r ≤ H.hi r :=
  Nat.mul_le_mul_right _ (Nat.le_succ _)

theorem hi_le_two_pow {r : List Bool} (hv : H.valid r = true) : H.hi r ≤ 2 ^ r.length := by
  have hlen := H.length_header_le hv
  have hb := BitString.binaryValue_lt_two_pow (H.header r)
  calc H.hi r ≤ 2 ^ (H.header r).length * 2 ^ (r.length - (H.header r).length) :=
        Nat.mul_le_mul_right _ hb
    _ = 2 ^ r.length := by rw [← pow_add, Nat.add_sub_cancel' hlen]

theorem lo_eq_of_header_eq {r r' : List Bool} (hh : H.header r' = H.header r)
    (hlen : r'.length = r.length) : H.lo r' = H.lo r := by
  rw [lo, lo, hh, hlen]

theorem hi_eq_of_header_eq {r r' : List Bool} (hh : H.header r' = H.header r)
    (hlen : r'.length = r.length) : H.hi r' = H.hi r := by
  rw [hi, hi, hh, hlen]

/-- A valid word lies in the block of its header. -/
theorem mem_block {r : List Bool} (hv : H.valid r = true) :
    H.lo r ≤ BitString.binaryValue r ∧ BitString.binaryValue r < H.hi r :=
  (BitString.isPrefix_iff_binaryValue (H.length_header_le hv)).mp (H.header_isPrefix r hv)

/-- A word of the same length in the block of the header of `r` has that header. -/
theorem valid_of_mem_block {r r' : List Bool} (hv : H.valid r = true)
    (hlen : r'.length = r.length) (h1 : H.lo r ≤ BitString.binaryValue r')
    (h2 : BitString.binaryValue r' < H.hi r) :
    H.valid r' = true ∧ H.header r' = H.header r := by
  have hp : H.header r <+: r' := by
    refine (BitString.isPrefix_iff_binaryValue (by rw [hlen]; exact H.length_header_le hv)).mpr ?_
    rw [hlen]
    exact ⟨h1, h2⟩
  exact H.valid_of_isPrefix r r' hv hp

/-- A collapsed valid word is the top word of its block. -/
theorem binaryValue_collapse_add_one {r : List Bool} (hv : H.valid r = true) :
    BitString.binaryValue (H.collapse r) + 1 = H.hi r := by
  rw [H.collapse_of_valid hv, BitString.binaryValue_append_replicate_true, hi]

theorem binaryValue_le_binaryValue_collapse (r : List Bool) :
    BitString.binaryValue r ≤ BitString.binaryValue (H.collapse r) := by
  by_cases hv : H.valid r = true
  · have := H.binaryValue_collapse_add_one hv
    have := (H.mem_block hv).2
    omega
  · rw [H.collapse_of_not_valid (by simpa using hv)]

/-- Two words of the same length collapse to the same word as a valid `r` exactly when they lie in
its block. -/
theorem collapse_eq_collapse_iff {r r' : List Bool} (hv : H.valid r = true)
    (hlen : r'.length = r.length) :
    H.collapse r' = H.collapse r ↔
      H.lo r ≤ BitString.binaryValue r' ∧ BitString.binaryValue r' < H.hi r := by
  constructor
  · intro h
    by_cases hv' : H.valid r' = true
    · have hh : H.header r' = H.header r := by
        rw [← (H.valid_collapse hv').2, h, (H.valid_collapse hv).2]
      rw [← H.lo_eq_of_header_eq hh hlen, ← H.hi_eq_of_header_eq hh hlen]
      exact H.mem_block hv'
    · rw [H.collapse_of_not_valid (by simpa using hv')] at h
      have := (H.valid_collapse hv).1
      rw [← h] at this
      exact absurd this hv'
  · rintro ⟨h1, h2⟩
    obtain ⟨hv', hh⟩ := H.valid_of_mem_block hv hlen h1 h2
    rw [H.collapse_of_valid hv', H.collapse_of_valid hv, hh, hlen]

/-! ### The cumulative distribution -/

/-- The numerator of the cumulative distribution of the collapsed ensemble at `y`: one more than the
value of `y` if `y` is a collapsed word, and otherwise the bottom of the block of `y`. -/
def cdfNum (y : List Bool) : ℕ :=
  if H.collapse y = y then BitString.binaryValue y + 1 else H.lo y

theorem valid_of_collapse_ne {y : List Bool} (hy : H.collapse y ≠ y) : H.valid y = true := by
  by_contra hv
  exact hy (H.collapse_of_not_valid (by simpa using hv))

theorem cdfNum_le_two_pow (y : List Bool) : H.cdfNum y ≤ 2 ^ y.length := by
  have hb := BitString.binaryValue_lt_two_pow y
  unfold cdfNum
  split_ifs with hy
  · omega
  · have := (H.mem_block (H.valid_of_collapse_ne hy)).1
    omega

/-- **Monotonicity of collapsing.** A word `r` of the length of `y` collapses to a word of value at
most that of `y` exactly when the value of `r` is below `cdfNum y`. -/
theorem binaryValue_collapse_le_iff {r y : List Bool} (hlen : r.length = y.length) :
    BitString.binaryValue (H.collapse r) ≤ BitString.binaryValue y ↔
      BitString.binaryValue r < H.cdfNum y := by
  have hrc := H.binaryValue_le_binaryValue_collapse r
  unfold cdfNum
  split_ifs with hy
  · constructor
    · intro h
      omega
    · intro h
      by_cases hvr : H.valid r = true
      · by_contra hc
        have hcr := H.binaryValue_collapse_add_one hvr
        have hlo := (H.mem_block hvr).1
        obtain ⟨hvy, hhy⟩ := H.valid_of_mem_block hvr hlen.symm (by omega) (by omega)
        have hcy := H.binaryValue_collapse_add_one hvy
        rw [hy] at hcy
        have := H.hi_eq_of_header_eq hhy hlen.symm
        omega
      · rw [H.collapse_of_not_valid (by simpa using hvr)]
        omega
  · have hvy := H.valid_of_collapse_ne hy
    have hcy := H.binaryValue_collapse_add_one hvy
    have hyc : BitString.binaryValue y < BitString.binaryValue (H.collapse y) := by
      have hne : BitString.binaryValue (H.collapse y) ≠ BitString.binaryValue y := fun h =>
        hy (BitString.binaryValue_injective_of_length_eq (H.length_collapse y) h)
      have := H.binaryValue_le_binaryValue_collapse y
      omega
    constructor
    · intro h
      by_contra hc
      obtain ⟨hvr, hhr⟩ := H.valid_of_mem_block hvy hlen (by omega) (by omega)
      have hcr := H.binaryValue_collapse_add_one hvr
      have := H.hi_eq_of_header_eq hhr hlen
      omega
    · intro h
      have hloy := (H.mem_block hvy).1
      by_cases hvr : H.valid r = true
      · by_contra hc
        have hcr := H.binaryValue_collapse_add_one hvr
        have hlor := (H.mem_block hvr).1
        obtain ⟨-, hhy⟩ := H.valid_of_mem_block hvr hlen.symm (by omega) (by omega)
        have := H.lo_eq_of_header_eq hhy hlen.symm
        omega
      · rw [H.collapse_of_not_valid (by simpa using hvr)]
        omega

/-- **The cumulative distribution of the collapsed ensemble** is the dyadic rational
`cdfNum y / 2^{|y|}`. -/
theorem cdf_ensemble (y : List Bool) :
    H.ensemble.cdf y = (H.cdfNum y : ℝ≥0∞) / (2 ^ y.length : ℕ) := by
  rw [Ensemble.cdf, ensemble_dist, PMF.toOuterMeasure_map_apply,
    ← Ensemble.uniform_toOuterMeasure_binaryValue_lt (H.cdfNum_le_two_pow y)]
  apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
  ext r
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, hr⟩
    exact ⟨(H.binaryValue_collapse_le_iff (Ensemble.uniform.length_eq _ _ hr)).mp h, hr⟩
  · rintro ⟨h, hr⟩
    exact ⟨(H.binaryValue_collapse_le_iff (Ensemble.uniform.length_eq _ _ hr)).mpr h, hr⟩

theorem collapse_polyTime (hvalid : ComputableInPolyTime H.valid encBits encBool)
    (hheader : ComputableInPolyTime H.header encBits encBits) :
    ComputableInPolyTime H.collapse encBits encBits := by
  unfold collapse
  polytime

/-- **The collapsed ensemble is polynomial-time computable** when the header parser is. -/
theorem pComp_ensemble (hvalid : ComputableInPolyTime H.valid encBits encBool)
    (hheader : ComputableInPolyTime H.header encBits encBits) : H.ensemble.PComp := by
  have hcoll := H.collapse_polyTime hvalid hheader
  refine ⟨H.cdfNum, fun y => 2 ^ y.length, ?_, by polytime, fun _ => by positivity,
    H.cdf_ensemble⟩
  have hc : ComputableInPolyTime (fun y => decide (H.collapse y = y)) encBits encBool :=
    ComputableInPolyTime.decide_eq' hcoll (.id' (encIn := encBits))
  have hsucc : ComputableInPolyTime (fun y => BitString.binaryValue y + 1) encBits encNat :=
    ComputableInPolyTime.binary_add.comp
      (ComputableInPolyTime.bitsBinaryValue.prod (ComputableInPolyTime.const 1))
  have hexp : ComputableInPolyTime (fun y : List Bool => y.length - (H.header y).length)
      encBits encUnary := by polytime
  have hlo : ComputableInPolyTime H.lo encBits encNat :=
    ComputableInPolyTime.binary_mul' (ComputableInPolyTime.bitsBinaryValue.comp hheader)
      (ComputableInPolyTime.binary_two_pow.comp hexp)
  unfold cdfNum
  simpa only [decide_eq_true_eq] using ComputableInPolyTime.ite' hc hsucc hlo

/-! ### Point masses -/

private theorem two_pow_div_two_pow_add (a k : ℕ) :
    ((2 ^ k : ℕ) : ℝ≥0∞) / ((2 ^ (a + k) : ℕ) : ℝ≥0∞) = (2 ^ a : ℝ≥0∞)⁻¹ := by
  push_cast
  rw [pow_add, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero)) (Or.inl (ENNReal.pow_ne_top
      ENNReal.ofNat_ne_top)), mul_assoc, ENNReal.inv_mul_cancel (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), mul_one]

/-- **A padded header has probability `2^{-|h|}`** under the collapsed ensemble. -/
theorem ensemble_dist_collapse {r : List Bool} (hv : H.valid r = true) :
    H.ensemble.dist r.length (H.collapse r) = (2 ^ (H.header r).length : ℝ≥0∞)⁻¹ := by
  have hlohi := H.lo_le_hi r
  have hblock : (Ensemble.uniform.dist r.length).toOuterMeasure
      {r' | BitString.binaryValue r' < H.hi r} =
      (Ensemble.uniform.dist r.length).toOuterMeasure {r' | BitString.binaryValue r' < H.lo r} +
        H.ensemble.dist r.length (H.collapse r) := by
    have hdisj : Disjoint {r' : List Bool | BitString.binaryValue r' < H.lo r}
        {r' | H.lo r ≤ BitString.binaryValue r' ∧ BitString.binaryValue r' < H.hi r} := by
      rw [Set.disjoint_left]
      intro r' h1 h2
      simp only [Set.mem_ofPred_eq] at h1 h2
      omega
    have hunion : {r' : List Bool | BitString.binaryValue r' < H.hi r} =
        {r' | BitString.binaryValue r' < H.lo r} ∪
          {r' | H.lo r ≤ BitString.binaryValue r' ∧ BitString.binaryValue r' < H.hi r} := by
      ext r'
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      omega
    rw [hunion, Probability.PMF.toOuterMeasure_union_of_disjoint _ hdisj, ensemble_dist,
      ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 1
    apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
    ext r'
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h, hr⟩
      exact ⟨(H.collapse_eq_collapse_iff hv (Ensemble.uniform.length_eq _ _ hr)).mpr h, hr⟩
    · rintro ⟨h, hr⟩
      exact ⟨(H.collapse_eq_collapse_iff hv (Ensemble.uniform.length_eq _ _ hr)).mp h, hr⟩
  rw [Ensemble.uniform_toOuterMeasure_binaryValue_lt (H.hi_le_two_pow hv),
    Ensemble.uniform_toOuterMeasure_binaryValue_lt (hlohi.trans (H.hi_le_two_pow hv))] at hblock
  have hhi : H.hi r = H.lo r + 2 ^ (r.length - (H.header r).length) := by
    unfold hi lo
    ring
  rw [hhi, Nat.cast_add, ENNReal.add_div] at hblock
  have hne : ((H.lo r : ℕ) : ℝ≥0∞) / ((2 ^ r.length : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)
  rw [← (ENNReal.add_right_inj hne).mp hblock]
  have hlen := H.length_header_le hv
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hlen
  rw [hk, Nat.add_sub_cancel_left]
  exact two_pow_div_two_pow_add _ _

end HeaderParser

end Cslib.Complexity
