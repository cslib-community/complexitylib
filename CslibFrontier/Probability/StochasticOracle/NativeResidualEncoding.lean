/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualSelector
import Mathlib.Tactic

/-!
# Original-label binary data for the source residual construction

[Wang2027], Theorem 6 setup (1), PDF pp. 12--13. Finite enumerations explicitly
fix original point and candidate indices. `source` serializes the constructed
incidence, rational weights and rational dual prices, and does not serialize any
exact-cover witness. The same generic native selector consumes these bytes.
`incidence` and `common_candidate` connect the runtime rows to the source block
partition, using the proved whole-block-fallback property of `ResidualCover`.

This supplies the original WSC data and incidence connection, not yet the general
residual-history specialization or universal native optimum comparison.

## Main definitions

* `source`: actual binary-rational source input from arbitrary promised X3C blocks.

## Main results

* `incidence`: original point/candidate labels survive the native conversion.
* `common_candidate`, `region`: native shared incidence and the executed scan recover source blocks.
* `weight_cast`, `dual_cast`: the rational input decodes to the source weights and prices.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualEncoding
open Finset NativeRetention ResidualCover
variable {z n m : ℕ} (T : Fin z → Block)
variable (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

/-- Source rational candidate weight; no exact-cover witness is used. -/
@[expose] def rationalWeight : Candidate T → ℚ
  | ⟨_, none⟩ => 2 / z
  | ⟨j, some _⟩ => 1 / ((z : ℚ) * (T j).r)

/-- Source rational element price, constant on each original block. -/
@[expose] def rationalDual (e : Point T) : ℚ := 1 / (3 * (z : ℚ) * (T e.1).r)

/-- Concrete dense binary incidence data, with binary rational source weights
and prices. Only block sizes, original families and finite enumerations are read;
the `Block.witness` fields are not encoded. -/
@[expose] def source : SourceEncoding.Input :=
  ⟨List.ofFn (fun c => List.ofFn (fun e => decide (points e ∈ sets T (candidates c)))),
    List.ofFn (fun c => rationalWeight T (candidates c)),
    List.ofFn (fun e => rationalDual T (points e)), 1⟩

/-- The source universe has exactly its original finite point labels. -/
theorem ground_length : (source T points candidates).dual.length = n := List.length_ofFn

/-- Every original candidate label is preserved, including fallback rows. -/
theorem rows_length : (SourceEncoding.toNative (source T points candidates)).rows.length = m := by
  simp [source, SourceEncoding.toNative]

/-- Exact original incidence after binary serialization and native startup conversion. -/
theorem incidence (c : Fin m) (e : Fin n) :
    e.val ∈ elements (SourceEncoding.toNative (source T points candidates)) c.val ↔
      points e ∈ sets T (candidates c) := by
  rw [SourceEncoding.elements_toNative]
  simp [source, List.getD_eq_getElem?_getD]

/-- Whole-block fallbacks make native shared incidence characterize the original
block partition. No component-identification certificate is supplied. -/
theorem common_candidate (e f : Fin n) :
    (points e).1 = (points f).1 ↔
      ∃ c : Fin m,
        e.val ∈ elements (SourceEncoding.toNative (source T points candidates)) c.val ∧
        f.val ∈ elements (SourceEncoding.toNative (source T points candidates)) c.val := by
  rw [same_block_iff_common_candidate]
  constructor
  · rintro ⟨c, he, hf⟩
    exact ⟨candidates.symm c, (incidence T points candidates _ _).mpr (by simpa using he),
      (incidence T points candidates _ _).mpr (by simpa using hf)⟩
  · rintro ⟨c, he, hf⟩
    exact ⟨candidates c, (incidence T points candidates _ _).mp he,
      (incidence T points candidates _ _).mp hf⟩

/-- Binary rational weights decode to the exact source real weights. -/
theorem weight_cast (c : Fin m) :
    ((source T points candidates).weights.getD c.val 0 : ℝ) = weight T (candidates c) := by
  simp only [source, List.getD_eq_getElem?_getD, List.getElem?_ofFn, c.isLt,
    Fin.eta]
  rcases candidates c with ⟨j, _ | A⟩ <;>
    norm_num [rationalWeight, weight]

/-- Binary rational prices decode to the exact source real dual. -/
theorem dual_cast (e : Fin n) :
    ((source T points candidates).dual.getD e.val 0 : ℝ) = dual T (points e) := by
  simp [source, rationalDual, dual, List.getD_eq_getElem?_getD]

/-- The actual native incidence scan recovers the source block containing a
point. This instantiates the runtime algorithm using the constructed source
rows, without assuming that component recovery is correct. -/
theorem region (seed e : Fin n) :
    e.val ∈ NativeResidualSelector.region
        (SourceEncoding.toNative (source T points candidates)) seed.val ↔
      (points e).1 = (points seed).1 := by
  have hrows : (SourceEncoding.toNative (source T points candidates)).rows =
      List.ofFn (fun c : Fin m => SourceEncoding.row n
        (List.ofFn (fun a : Fin n => decide (points a ∈ sets T (candidates c))))) := by
    simp [source, SourceEncoding.toNative, List.map_ofFn, Function.comp_def]
  unfold NativeResidualSelector.region NativeRetention.ground
  have hn : (SourceEncoding.toNative (source T points candidates)).dual.length = n :=
    ground_length T points candidates
  rw [hn]
  simp only [List.mem_filter, List.mem_range, e.isLt, true_and, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  rw [hrows]
  constructor
  · rintro ⟨row, hr, hseed, he⟩
    obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hr
    have hs : points seed ∈ sets T (candidates c) := by
      simpa [SourceEncoding.row] using hseed
    have ht : points e ∈ sets T (candidates c) := by
      simpa [SourceEncoding.row] using he
    exact (same_block_iff_common_candidate T (points e) (points seed)).mpr
      ⟨candidates c, ht, hs⟩
  · intro h
    obtain ⟨c, he, hs⟩ :=
      (same_block_iff_common_candidate T (points e) (points seed)).mp h
    let i := candidates.symm c
    refine ⟨SourceEncoding.row n
      (List.ofFn (fun a : Fin n => decide (points a ∈ sets T (candidates i)))),
      List.mem_ofFn.mpr ⟨i, rfl⟩, ?_, ?_⟩
    · simpa [SourceEncoding.row, i] using hs
    · simpa [SourceEncoding.row, i] using he

end Cslib.Probability.StochasticOracle.NativeResidualEncoding
