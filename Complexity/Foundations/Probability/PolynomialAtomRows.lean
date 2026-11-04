/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.PolynomialAtomCutoffs
public import Complexity.Foundations.Probability.CorrectionAtom
public import Complexity.Foundations.Analysis.RowCompression.Stationary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Polynomial atom rows under stationary compression

The preparation, auxiliary score, and broad witness are concrete two-variable polynomial
functions from `Complexity.Foundations.Probability.PolynomialAtomCutoffs`. This file proves
their strict retained-support bound, zero default output, preservation along the constructed
stationary reference, and a weighted fourth-root comparison with truth. `PolynomialAtomRow`
is a closed choice of those three functions; no scalar regularity or support law is assumed.

The common sufficient margin is `0 < η ≤ θ / 10000`, where `θ` is the atom's support scale
and `η` is the compression scale. The comparison constant depends only on the chosen function,
`θ`, and `η`; it is independent of the row, finite retained set, rank, schedule, and error
envelope. The rank includes the actual compressed default. Only the true row uses zero padding.
The bridges to `Matrix.atomPrep` and `Matrix.auxScore` use their existing zero-padded ranks.

These results instantiate the scalar laws in the stationary-reference portion of
[OpenAI2026LogSpace, Lemma 8.2] for the three pre-incoming row functions of Section 5.5.
They belong to the fourth-moment adaptation in complexitylib issue #1721; the pinned paper
uses eighth roots. Normalized main atoms, incoming-gate assembly, enumeration, post-overflow
stability, and a machine-space certificate remain separate.

## Main results

* `Cslib.PolynomialAtomRow.card_filter_eval_ne_zero_lt`: actual support has fewer than `K` entries.
* `Cslib.PolynomialAtomRow.stationaryContinuation_eval_eq`: preservation through the remaining
  real compression schedule after a prefix without overflow.
* `Cslib.PolynomialAtomRow.exists_stationaryContinuation_root_bound`: a uniform weighted
  fourth-root discrepancy bound with all scalar hypotheses discharged.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 5.5, support-margin lemma and compression-threshold table; Section 8.3, Lemma 8.2
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib

/-- The three concrete pre-incoming row functions with polynomial fourth-root regularity. -/
inductive PolynomialAtomRow
  | preparation
  | auxiliary
  | witness
  deriving DecidableEq

namespace PolynomialAtomRow

open Finset RowCompression

/-- Evaluate the chosen concrete function, using rational arithmetic for rational arguments. -/
@[expose] def eval {R : Type*} [Field R] [LinearOrder R] (kind : PolynomialAtomRow)
    (θ v r : R) : R :=
  match kind with
  | preparation => polynomialPrepRow4 θ v r
  | auxiliary => polynomialAuxCutoff4 θ v r
  | witness => polynomialWitnessCutoff4 θ v r

/-- The closed entry-zero threshold of the chosen function. -/
@[expose] def entryThreshold {R : Type*} [Field R] (kind : PolynomialAtomRow) (θ : R) : R :=
  match kind with
  | preparation => θ / 2
  | auxiliary => θ / 8
  | witness => 82 * θ / 1000

/-- The closed rank-zero threshold of the chosen function. -/
@[expose] def gateThreshold {R : Type*} [Field R] (kind : PolynomialAtomRow) (θ : R) : R :=
  match kind with
  | preparation => θ / 500
  | auxiliary => θ / 50
  | witness => 27 * θ / 1000

variable (kind : PolynomialAtomRow) {θ η v r r' : ℝ}

theorem eval_nonneg (θ v r : ℝ) : 0 ≤ kind.eval θ v r := by
  cases kind
  · exact polynomialPrepRow4_nonneg _ _ _
  · exact polynomialAuxCutoff4_nonneg _ _ _
  · exact polynomialWitnessCutoff4_nonneg _ _ _

theorem eval_le_one (θ v r : ℝ) : kind.eval θ v r ≤ 1 := by
  cases kind
  · exact polynomialPrepRow4_le_one _ _ _
  · exact polynomialAuxCutoff4_le_one _ _ _
  · exact polynomialWitnessCutoff4_le_one _ _ _

theorem entryThreshold_pos (hθ : 0 < θ) : 0 < kind.entryThreshold θ := by
  cases kind <;> dsimp only [entryThreshold] <;> positivity

theorem gateThreshold_pos (hθ : 0 < θ) : 0 < kind.gateThreshold θ := by
  cases kind <;> dsimp only [gateThreshold] <;> positivity

theorem three_mul_gateThreshold_lt_entryThreshold (hθ : 0 < θ) :
    3 * kind.gateThreshold θ < kind.entryThreshold θ := by
  cases kind <;> dsimp only [gateThreshold, entryThreshold] <;> linarith

theorem gateThreshold_lt_entryThreshold (hθ : 0 < θ) :
    kind.gateThreshold θ < kind.entryThreshold θ := by
  linarith [kind.gateThreshold_pos hθ, kind.three_mul_gateThreshold_lt_entryThreshold hθ]

theorem scale_lt_gateThreshold (hθ : 0 < θ) (hη : η ≤ θ / 10000) :
    η < kind.gateThreshold θ := by
  cases kind <;> dsimp only [gateThreshold] <;> linarith

theorem eval_eq_zero_of_entry_le (hθ : 0 < θ) (hv : v ≤ kind.entryThreshold θ) :
    kind.eval θ v r = 0 := by
  cases kind
  · exact polynomialPrepRow4_eq_zero_of_entry_le hθ hv
  · exact polynomialAuxCutoff4_eq_zero_of_entry_le hθ hv
  · exact polynomialWitnessCutoff4_eq_zero_of_entry_le hθ hv

theorem eval_eq_zero_of_rank_ge (hθ : 0 < θ) (hr : kind.gateThreshold θ ≤ r) :
    kind.eval θ v r = 0 := by
  cases kind
  · exact polynomialPrepRow4_eq_zero_of_rank_ge hθ hr
  · exact polynomialAuxCutoff4_eq_zero_of_rank_ge hθ hr
  · exact polynomialWitnessCutoff4_eq_zero_of_rank_ge hθ hr

/-- All three actual rank factors are constant throughout the common flat region. -/
theorem eval_eq_of_rank_le (hθ : 0 < θ) (hη : η ≤ θ / 10000) (hr : r ≤ η) (hr' : r' ≤ η) :
    kind.eval θ v r = kind.eval θ v r' := by
  cases kind
  · exact (polynomialPrepRow4_of_rank_le hθ (by linarith)).trans
      (polynomialPrepRow4_of_rank_le hθ (by linarith)).symm
  · exact (polynomialAuxCutoff4_of_rank_le hθ (by linarith)).trans
      (polynomialAuxCutoff4_of_rank_le hθ (by linarith)).symm
  · exact (polynomialWitnessCutoff4_of_rank_le hθ (by linarith)).trans
      (polynomialWitnessCutoff4_of_rank_le hθ (by linarith)).symm

theorem exists_abs_eval_root_sub_le (θ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v r v' r',
      |kind.eval θ v r ^ (4⁻¹ : ℝ) - kind.eval θ v' r' ^ (4⁻¹ : ℝ)| ≤
        C * (|v - v'| + |r - r'|) := by
  cases kind
  · exact exists_abs_polynomialPrepRow4_root_sub_le θ
  · exact exists_abs_polynomialAuxCutoff4_root_sub_le θ
  · exact exists_abs_polynomialWitnessCutoff4_root_sub_le θ

variable {ι : Type*} {s : Finset ι} {K : ℕ} {z : ℝ} {w : ι → Fin 2 → ℝ}

/-- Zero padding in the compression rank agrees with the existing atom rank, including when
`K` exceeds the retained cardinality or the raw first coordinates are negative. -/
theorem eval_firstRank_zero (θ v : ℝ) :
    kind.eval θ v (firstRank s K 0 w) = kind.eval θ v (kthLargest K s fun y => w y 0) := by
  rw [firstRank, max_eq_right kthLargest_nonneg]

/-- The actual default entry always has zero output, with no sign restriction on the default. -/
theorem eval_default_eq_zero (hθ : 0 < θ) :
    kind.eval θ z (firstRank s K z w) = 0 := by
  by_cases hz : z ≤ kind.entryThreshold θ
  · exact kind.eval_eq_zero_of_entry_le hθ hz
  exact kind.eval_eq_zero_of_rank_ge hθ
    ((kind.gateThreshold_lt_entryThreshold hθ).le.trans
      ((not_le.mp hz).le.trans default_le_firstRank))

/-- Fewer than `K` retained endpoints have nonzero output for the actual padded rank. -/
theorem card_filter_eval_ne_zero_lt (hθ : 0 < θ) (hK : 0 < K) :
    #{y ∈ s | kind.eval θ (w y 0) (firstRank s K z w) ≠ 0} < K := by
  classical
  by_contra hlt
  have hle : K ≤ #{y ∈ s | kind.eval θ (w y 0) (firstRank s K z w) ≠ 0} := not_lt.mp hlt
  have hsub : ({y ∈ s | kind.eval θ (w y 0) (firstRank s K z w) ≠ 0} : Finset ι) ⊆
      {y ∈ s | kind.entryThreshold θ < w y 0} := by
    intro y hy
    obtain ⟨hys, hy⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨hys, not_le.mp fun h => hy (kind.eval_eq_zero_of_entry_le hθ h)⟩
  have hrank : kind.entryThreshold θ < kthLargest K s (fun y => w y 0) :=
    (lt_kthLargest_iff hK (kind.entryThreshold_pos hθ).le).mpr (hle.trans (card_le_card hsub))
  obtain ⟨y, hy⟩ := card_pos.mp (hK.trans_le hle)
  exact (mem_filter.mp hy).2 (kind.eval_eq_zero_of_rank_ge hθ
    ((kind.gateThreshold_lt_entryThreshold hθ).le.trans (hrank.le.trans kthLargest_le_firstRank)))

variable {n : ℕ → ℕ} {Δ : ℕ → ι → Fin 2 → ℝ} {a : State ι} {truth : ι → Fin 2 → ℝ}

/-- The constructed stationary reference preserves each actual polynomial row output through
the remaining compression schedule. Scalar support, gate, flatness, and margin laws are proved. -/
theorem stationaryContinuation_eval_eq (hθ : 0 < θ) (hη : 0 ≤ η) (hmargin : η ≤ θ / 10000)
    (hK : 0 < K) (m j r : ℕ) (hr : j + r ≤ m)
    (hno : ∀ i < j,
      stepThreshold s n (fun _ => K) (dyadicFloor η m) Δ a i ≤ dyadicFloor η m i)
    (hfirst : ∀ y ∈ s, 0 ≤ truth y 0) (hsecond : ∀ y ∈ s, |truth y 1| ≤ η / 2)
    (hn : ∀ i, j ≤ i → i < m → K ≤ n i) (y : ι) (hy : y ∈ s) :
    let b := stationaryState s n (fun _ => K) (dyadicFloor η m) Δ a truth j
    let c := stationaryContinuation s n K (dyadicFloor η m) Δ a truth j r
    kind.eval θ (c.row y 0) (firstRank s K c.defaultValue c.row) =
      kind.eval θ (b.row y 0) (firstRank s K b.defaultValue b.row) := by
  exact stationaryContinuation_output_eq_dyadic (H := fun x _ q => kind.eval θ x q)
    hη hK m j r hr hno hfirst hsecond hn (kind.scale_lt_gateThreshold hθ hmargin)
    (kind.three_mul_gateThreshold_lt_entryThreshold hθ)
    (fun _ _ _ hx => kind.eval_eq_zero_of_entry_le hθ hx)
    (fun _ _ _ hq => kind.eval_eq_zero_of_rank_ge hθ hq)
    (fun _ _ _ _ hq hq' => kind.eval_eq_of_rank_le hθ hmargin hq.2 hq'.2) y hy

/-- A constant depending only on the concrete row function and its two scales bounds the
continued reference's fourth-root error by actual prefix-error envelopes. No Lipschitz or
support law is assumed; low-target endpoints need no relative-error hypothesis. -/
theorem exists_stationaryContinuation_root_bound (hθ : 0 < θ) (hη : 0 < η)
    (hmargin : η ≤ θ / 10000) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} (s : Finset ι) (n : ℕ → ℕ) (Δ : ℕ → ι → Fin 2 → ℝ)
      (a : State ι) (truth : ι → Fin 2 → ℝ) (K : ℕ),
      0 < K → 0 ≤ a.defaultValue → a.defaultValue ≤ η / 2 →
      ∀ (m j r : ℕ), j + r ≤ m →
      (∀ i < j, stepThreshold s n (fun _ => K) (dyadicFloor η m) Δ a i ≤ dyadicFloor η m i) →
      (∀ y ∈ s, 0 ≤ truth y 0) → (∀ y ∈ s, |truth y 1| ≤ η / 2) →
      (∀ i, j ≤ i → i < m → K ≤ n i) →
      ∀ (ε : ℕ → ℝ), (∀ i < j, 0 ≤ ε i) →
      (∀ i < j, ∀ y ∈ s, η / 2 ≤ truth y 0 →
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ a.row (i + 1) y) ≤ ε i) →
      ∀ y ∈ s,
      let c := stationaryContinuation s n K (dyadicFloor η m) Δ a truth j r
      |kind.eval θ (c.row y 0) (firstRank s K c.defaultValue c.row) ^ (4⁻¹ : ℝ) -
          kind.eval θ (truth y 0) (firstRank s K 0 truth) ^ (4⁻¹ : ℝ)| ≤
        C * ∑ i ∈ range j, dyadicFloor η m i * ε i := by
  obtain ⟨L, hL, hroot⟩ := kind.exists_abs_eval_root_sub_le θ
  refine ⟨3 * L * (12 * (1 + η / 2) / (η / 2)), by positivity, ?_⟩
  intro ι s n Δ a truth K hK ha haη m j r hr hno hfirst hsecond hn ε hε herr y hy
  have hentry : ∀ (x v q : ℝ), x ≤ η → (fun x (_ : ℝ) q => kind.eval θ x q) x v q = 0 := by
    intro x _ q hx
    exact kind.eval_eq_zero_of_entry_le hθ (hx.trans
      ((kind.scale_lt_gateThreshold hθ hmargin).le.trans
        (kind.gateThreshold_lt_entryThreshold hθ).le))
  have hbound := abs_stationaryState_root_sub_le_weighted_dyadic
    (H := fun x _ q => kind.eval θ x q) (p := (4⁻¹ : ℝ)) (C := L)
    hη hK hL ha haη m j ((Nat.le_add_right j r).trans hr) hno hε herr hentry
    (fun _ _ _ _ hq hq' => kind.eval_eq_of_rank_le hθ hmargin hq.2 hq'.2)
    (fun x v q x' v' q' _ _ _ _ => (hroot x q x' q').trans
      (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (v - v')]) hL)) y hy
  dsimp only
  rw [kind.stationaryContinuation_eval_eq hθ hη.le hmargin hK m j r hr hno hfirst hsecond hn y hy]
  simpa only [mul_assoc] using hbound

end PolynomialAtomRow
end Cslib

namespace Matrix

open Finset

variable {V : Type*}

/-- The existing preparatory expression is the concrete polynomial preparation row. -/
theorem atomPrep_polynomial_eq (θ : ℝ) (K : ℕ) (a : ℝ) (G : Matrix V V ℝ)
    (T : Finset V) (x y : V) :
    atomPrep (Cslib.polynomialPrepCutoff4 θ) (Cslib.polynomialRowCutoff4 θ) K a G T x y =
      Cslib.PolynomialAtomRow.preparation.eval θ (G x y / a)
        (kthLargest K T fun z => G x z / a) := rfl

/-- The existing auxiliary-score expression is the concrete polynomial auxiliary row. -/
theorem auxScore_polynomial_eq (θ : ℝ) (K : ℕ) (a : ℝ) (G : Matrix V V ℝ)
    (T : Finset V) (x y : V) :
    auxScore (Cslib.polynomialAuxCutoff4 θ) K a G T x y =
      Cslib.PolynomialAtomRow.auxiliary.eval θ (G x y / a)
        (kthLargest K T fun z => G x z / a) := rfl

end Matrix
