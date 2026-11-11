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

The decoded native WSC has derived validity and primal/dual optimum one. Coverage,
weights, residuals and local certification commute with the original labels.
This is not yet the complete native query/role specialization or the universal
native query-token optimum comparison.

## Main definitions

* `source`: actual binary-rational source input from arbitrary promised X3C blocks.
* `pointLabel`, `candidateLabel`, `nativeInstance`: original labels and decoded native WSC.

## Main results

* `incidence`: original point/candidate labels survive the native conversion.
* `common_candidate`, `region`: native shared incidence and the executed scan recover source blocks.
* `weight_cast`, `dual_cast`: the rational input decodes to the source weights and prices.
* `source_valid`: source X3C promises derive all external/native validity conditions.
* `covered_label`, `cost_label`, `certified_label`: original families preserve local semantics.
* `native_near_residual`, `native_responses_certified`: decoded residual and sequential tests.
* `native_primal_optimum`, `native_dual_optimum`: decoded WSC L=OPT=1, including universal bounds.
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

/-- Changing only a proof of the number of candidate labels preserves the
original WSC bytes. This transports indices, not the mathematical instance. -/
theorem source_reindex {m' : ℕ} (h : m' = m) :
    source T points ((finCongr h).trans candidates) = source T points candidates := by
  subst m'
  rfl

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

/-- Original point label in the external finite enumeration. -/
@[expose] def pointLabel : Point T ↪ ℕ :=
  ⟨fun e => (points.symm e).val, by
    intro e f h
    exact points.symm.injective (Fin.val_injective h)⟩

/-- Original candidate label in the external finite enumeration. -/
@[expose] def candidateLabel : Candidate T ↪ ℕ :=
  ⟨fun c => (candidates.symm c).val, by
    intro c d h
    exact candidates.symm.injective (Fin.val_injective h)⟩

/-- The actual native incidence set is the original source set with its declared
labels. This includes unused, overlapping triples and whole-block fallbacks. -/
theorem elements_label (c : Candidate T) :
    elements (SourceEncoding.toNative (source T points candidates))
        (candidateLabel T candidates c) = (sets T c).map (pointLabel T points) := by
  ext e
  constructor
  · intro he
    have hn : e < n := by
      have h := (SourceEncoding.elements_toNative _ _ _).mp he
      simpa only [ground_length] using h.1
    let i : Fin n := ⟨e, hn⟩
    have hi : points i ∈ sets T c := by
      have h := (incidence T points candidates (candidates.symm c) i).mp he
      simpa only [Equiv.apply_symm_apply] using h
    exact mem_map.mpr ⟨points i, hi, by simp [pointLabel, i]⟩
  · rintro he
    obtain ⟨f, hf, rfl⟩ := mem_map.mp he
    have h := (incidence T points candidates (candidates.symm c) (points.symm f)).mpr
      (by simpa only [Equiv.apply_symm_apply] using hf)
    exact h

/-- Summing decoded prices on any source subuniverse preserves its exact charge. -/
theorem dual_sum (F : Finset (Point T)) :
    (∑ e ∈ F.map (pointLabel T points),
      ((source T points candidates).dual.getD e 0 : ℝ)) = ∑ e ∈ F, dual T e := by
  rw [sum_map]
  apply sum_congr rfl
  intro e _
  simpa only [pointLabel, Function.Embedding.coeFn_mk, Equiv.apply_symm_apply] using
    dual_cast T points candidates (points.symm e)

/-- All external WSC promises are derived from the source X3C input. In
particular, no native validity or dual certificate is a premise. -/
theorem source_valid (hz : 0 < z) : SourceEncoding.Valid (source T points candidates) := by
  constructor
  · simp [source]
  · intro j hj
    have hm : j < m := by simpa only [source, List.length_ofFn] using hj
    have h := (coverInstance T hz).weight_nonneg (candidates ⟨j, hm⟩)
    change 0 ≤ weight T (candidates ⟨j, hm⟩) at h
    rw [← weight_cast T points candidates ⟨j, hm⟩] at h
    exact_mod_cast h
  · intro e he
    have hn : e < n := by simpa only [ground_length] using he
    have h := (coverInstance T hz).dual_nonneg (points ⟨e, hn⟩)
    change 0 ≤ dual T (points ⟨e, hn⟩) at h
    rw [← dual_cast T points candidates ⟨e, hn⟩] at h
    exact_mod_cast h
  · intro j hj
    have hm : j < m := by simpa only [source, List.length_ofFn] using hj
    let c := candidates ⟨j, hm⟩
    have h := (coverInstance T hz).dual_feasible c
    change (∑ e ∈ sets T c, dual T e) ≤ weight T c at h
    rw [← dual_sum T points candidates, ← elements_label T points candidates,
      ← weight_cast T points candidates ⟨j, hm⟩] at h
    simpa only [SourceEncoding.elements_eq, candidateLabel, Function.Embedding.coeFn_mk, c,
      Equiv.symm_apply_apply] using (show
      ∑ e ∈ elements (SourceEncoding.toNative (source T points candidates))
          (candidateLabel T candidates c),
        (source T points candidates).dual.getD e 0 ≤
          (source T points candidates).weights.getD j 0 by exact_mod_cast h)

/-- The real WSC interpretation of the actual decoded native input. Validity is
proved from the X3C promises, rather than supplied to this definition. -/
@[expose] def nativeInstance (hz : 0 < z) : PartialCover.Instance ℕ ℕ :=
  instanceOf (SourceEncoding.toNative (source T points candidates))
    (SourceEncoding.valid_toNative _ (source_valid T points candidates hz))

/-- The decoded universe is exactly the relabeled original source universe. -/
theorem ground_label (hz : 0 < z) :
    (nativeInstance T points candidates hz).ground =
      (univ : Finset (Point T)).map (pointLabel T points) := by
  ext e
  change e ∈ (ground (SourceEncoding.toNative (source T points candidates))).toFinset ↔ _
  simp only [ground, SourceEncoding.toNative, source, List.length_ofFn,
    List.mem_toFinset, List.mem_range, mem_map, mem_univ, true_and]
  constructor
  · intro he
    exact ⟨points ⟨e, he⟩, by simp [pointLabel]⟩
  · rintro ⟨f, rfl⟩
    exact (points.symm f).isLt

/-- Every actual native family, with its original candidate labels, covers
exactly the same source points. -/
theorem covered_label (hz : 0 < z) (C : Finset (Candidate T)) :
    (nativeInstance T points candidates hz).covered (C.map (candidateLabel T candidates)) =
      ((coverInstance T hz).covered C).map (pointLabel T points) := by
  change (C.map (candidateLabel T candidates)).biUnion
      (elements (SourceEncoding.toNative (source T points candidates))) =
    (C.biUnion (sets T)).map (pointLabel T points)
  ext e
  simp only [mem_biUnion, mem_map]
  constructor
  · rintro ⟨j, ⟨c, hc, rfl⟩, he⟩
    rw [elements_label] at he
    obtain ⟨f, hf, rfl⟩ := mem_map.mp he
    exact ⟨f, ⟨c, hc, hf⟩, rfl⟩
  · rintro ⟨f, ⟨c, hc, hf⟩, rfl⟩
    refine ⟨candidateLabel T candidates c, ⟨c, hc, rfl⟩, ?_⟩
    rw [elements_label]
    exact mem_map.mpr ⟨f, hf, rfl⟩

/-- Decoded native family weight is the original source weight, without
multiplicity or reindexing loss. -/
theorem cost_label (hz : 0 < z) (C : Finset (Candidate T)) :
    (nativeInstance T points candidates hz).cost (C.map (candidateLabel T candidates)) =
      (coverInstance T hz).cost C := by
  rw [PartialCover.Instance.cost, sum_map]
  apply sum_congr rfl
  intro c _
  simpa only [nativeInstance, instanceOf, SourceEncoding.toNative, candidateLabel,
    Function.Embedding.coeFn_mk, coverInstance, Equiv.apply_symm_apply] using
    weight_cast T points candidates (candidates.symm c)

/-- After the actual source near-cover family, the decoded uncovered universe
is exactly the corresponding original block. No residual label is supplied. -/
theorem native_near_residual (hz : 0 < z) (j : Fin z) :
    (nativeInstance T points candidates hz).ground \
        (nativeInstance T points candidates hz).covered
          ((payload T (univ.erase j)).map (candidateLabel T candidates)) =
      (groundBlock T j).map (pointLabel T points) := by
  rw [ground_label, covered_label, ← Finset.map_sdiff]
  exact congrArg (Finset.map (pointLabel T points)) (near_residual T hz j)

/-- The local dual test is preserved on every original-label source history,
not just on a supplied exact-cover output. -/
theorem certified_label (hz : 0 < z) (ρ : ℝ) (C P : Finset (Candidate T)) :
    (nativeInstance T points candidates hz).Certified ρ
        (C.map (candidateLabel T candidates)) (P.map (candidateLabel T candidates)) ↔
      (coverInstance T hz).Certified ρ C P := by
  unfold PartialCover.Instance.Certified
  rw [covered_label, covered_label, cost_label, ← Finset.map_sdiff, map_nonempty]
  change _ ∧ (coverInstance T hz).cost P ≤ ρ *
    (∑ e ∈ ((coverInstance T hz).covered P \ (coverInstance T hz).covered C).map
      (pointLabel T points), ((source T points candidates).dual.getD e 0 : ℝ)) ↔ _
  rw [dual_sum]
  rfl

/-- Both chronological source responses pass the actual interpreted native
local certification test. This is derived for arbitrary promised X3C families,
without serializing the hidden exact covers into the original input. -/
theorem native_responses_certified (hz : 3 ≤ z) (j : Fin z) :
    let I := nativeInstance T points candidates (by omega)
    let near := (payload T (univ.erase j)).map (candidateLabel T candidates)
    let specialist := (ResidualCover.specialist T j).map (candidateLabel T candidates)
    I.Certified 1 ∅ near ∧ I.Certified 1 near specialist := by
  dsimp only
  obtain ⟨hnear, hspecialist⟩ := responses_certified T hz j
  constructor
  · simpa only [map_empty] using
      (certified_label T points candidates (by omega) 1 ∅
        (payload T (univ.erase j))).mpr hnear
  · exact (certified_label T points candidates (by omega) 1
      (payload T (univ.erase j)) (specialist T j)).mpr hspecialist

/-- The interpreted native input has dual objective one for every promised
source family and every original-label enumeration. -/
theorem native_dual_objective (hz : 0 < z) :
    ∑ e ∈ (nativeInstance T points candidates hz).ground,
      (nativeInstance T points candidates hz).dual e = 1 := by
  rw [ground_label]
  change (∑ e ∈ univ.map (pointLabel T points),
    ((source T points candidates).dual.getD e 0 : ℝ)) = 1
  rw [dual_sum]
  exact dual_objective T hz

/-- An actual family of original native candidate labels covers the instance
with weight one, and every native integral cover has weight at least one.
The lower bound also allows out-of-range labels, whose rows are empty. -/
theorem native_primal_optimum (hz : 0 < z) :
    let I := nativeInstance T points candidates hz
    let C := (payload T univ).map (candidateLabel T candidates)
    I.covered C = I.ground ∧ I.cost C = 1 ∧
      ∀ F, I.covered F = I.ground → 1 ≤ I.cost F := by
  dsimp only
  obtain ⟨hcover, hcost, _⟩ := primal_optimum T hz
  refine ⟨?_, ?_, ?_⟩
  · rw [covered_label, hcover, ground_label]
    rfl
  · rw [cost_label, hcost]
  · intro F hF
    have h := (nativeInstance T points candidates hz).dual_le_cost F
    rw [hF, native_dual_objective] at h
    exact h

/-- No feasible nonnegative dual on the decoded native universe exceeds one.
Together with the constructed integral cover this proves native L=OPT=1. -/
theorem native_dual_optimum (hz : 0 < z) (d : ℕ → ℝ) (hd : ∀ e, 0 ≤ d e)
    (hf : ∀ c, ∑ e ∈ (nativeInstance T points candidates hz).sets c, d e ≤
      (nativeInstance T points candidates hz).weight c) :
    ∑ e ∈ (nativeInstance T points candidates hz).ground, d e ≤ 1 := by
  let I : PartialCover.Instance ℕ ℕ :=
    { nativeInstance T points candidates hz with
      dual := d
      dual_nonneg := hd
      dual_feasible := hf }
  obtain ⟨hcover, hcost, _⟩ := native_primal_optimum T points candidates hz
  have h := I.dual_le_cost ((payload T univ).map (candidateLabel T candidates))
  change (∑ e ∈ (nativeInstance T points candidates hz).covered
    ((payload T univ).map (candidateLabel T candidates)), d e) ≤
      (nativeInstance T points candidates hz).cost
        ((payload T univ).map (candidateLabel T candidates)) at h
  rw [hcover, hcost] at h
  exact h

end Cslib.Probability.StochasticOracle.NativeResidualEncoding
