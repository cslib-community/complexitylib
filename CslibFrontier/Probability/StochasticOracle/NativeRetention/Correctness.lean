/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention
public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Codec
import Mathlib.Tactic

/-!
# Correctness of the uniform native retention phase

[Wang2027], Lemma 1 (PDF p. 9, Appendix A.3 p. 15) and the local certification
step in Theorem 5(1), PDF p. 12. The runtime rational tests are identified with the
existing real-valued local dual test. The final retained family and certificate
are derived from the input rows and proposals, not supplied as witnesses.

## Main results

* `certified_eq`, `retain_eq`: exact correspondence with the original real-valued local test.
* `completed_output`: coverage and weight certificate derived from the computed decision.
* `compiled_decodes`: actual native halting output uses the source family-mask codec.

Raw concurrent packet decoding and the adaptive native query/stop loop are not
implemented by this local phase.
-/

public section
namespace Cslib.Probability.StochasticOracle.NativeRetention
open Finset PartialCover

/-- The actual finite original set indexed by a runtime row. -/
@[expose] def elements (x : Input) (j : ℕ) : Finset ℕ :=
  ((ground x).filter fun e => decide (e ∈ x.rows.getD j [])).toFinset

/-- Standard WSC/dual input promises. These are not fields of the runtime input,
and the native program computes its local tests without reading any proof. -/
structure Valid (x : Input) : Prop where
  /-- Nonnegative original weights. -/
  weight_nonneg : ∀ j, 0 ≤ x.weights.getD j 0
  /-- Nonnegative element dual prices. -/
  dual_nonneg : ∀ e, 0 ≤ x.dual.getD e 0
  /-- Feasibility for every actual original set, including empty default rows. -/
  feasible : ∀ j, ∑ e ∈ elements x j, x.dual.getD e 0 ≤ x.weights.getD j 0

/-- The standard real-valued set-cover instance represented by the rational input. -/
@[expose] def instanceOf (x : Input) (hx : Valid x) : Instance ℕ ℕ where
  ground := (ground x).toFinset
  sets := elements x
  sets_subset := by
    intro j e he
    simp only [elements, List.mem_toFinset, List.mem_filter] at he
    exact List.mem_toFinset.mpr he.1
  weight j := x.weights.getD j 0
  weight_nonneg j := by exact_mod_cast hx.weight_nonneg j
  dual e := x.dual.getD e 0
  dual_nonneg e := by exact_mod_cast hx.dual_nonneg e
  dual_feasible j := by exact_mod_cast hx.feasible j

/-- Runtime coverage is exactly coverage by the original incidence rows. -/
theorem covered_eq (x : Input) (hx : Valid x) (C : List ℕ) :
    (covered x C).toFinset = (instanceOf x hx).covered C.toFinset := by
  ext e
  simp only [covered, List.mem_toFinset, List.mem_filter, List.any_eq_true,
    decide_eq_true_eq, Instance.covered, Finset.mem_biUnion, instanceOf, elements]
  aesop

/-- New-coverage tests use the actual difference of original covered sets. -/
theorem newly_eq (x : Input) (hx : Valid x) (C P : List ℕ) :
    (newly x C P).toFinset =
      (instanceOf x hx).covered (normalize x P).toFinset \
        (instanceOf x hx).covered C.toFinset := by
  ext e
  simp only [newly, List.mem_toFinset, List.mem_filter, Bool.not_eq_true', Bool.eq_false_iff,
    Finset.mem_sdiff, ← covered_eq x hx]
  exact and_congr Iff.rfl (not_congr (iff_of_eq decide_eq_true_eq))

/-- Native normalization never duplicates candidates. -/
theorem normalize_nodup (x : Input) (P : List ℕ) : (normalize x P).Nodup :=
  List.nodup_range.filter _

/-- Covered elements are scanned only once. -/
theorem covered_nodup (x : Input) (C : List ℕ) : (covered x C).Nodup :=
  List.nodup_range.filter _

/-- Newly covered elements are charged only once. -/
theorem newly_nodup (x : Input) (C P : List ℕ) : (newly x C P).Nodup :=
  (covered_nodup x _).filter _

/-- Native rational proposal cost equals the original real set-family cost. -/
theorem cost_eq (x : Input) (hx : Valid x) (P : List ℕ) :
    (cost x P : ℝ) = (instanceOf x hx).cost (normalize x P).toFinset := by
  unfold cost Instance.cost
  rw [← List.sum_toFinset _ (normalize_nodup x P)]
  simp [instanceOf]

/-- Native dual-price arithmetic equals the real charge on actual newly covered elements. -/
theorem price_eq (x : Input) (hx : Valid x) (C P : List ℕ) :
    (price x C P : ℝ) = ∑ e ∈
      (instanceOf x hx).covered (normalize x P).toFinset \ (instanceOf x hx).covered C.toFinset,
        (instanceOf x hx).dual e := by
  rw [← newly_eq x hx]
  unfold price
  rw [← List.sum_toFinset _ (newly_nodup x C P)]
  simp [instanceOf]

/-- The actual executable rational test is exactly the existing local dual test. -/
theorem certified_eq (x : Input) (hx : Valid x) (C P : List ℕ) :
    certified x C P = true ↔
      (instanceOf x hx).Certified x.rho C.toFinset (normalize x P).toFinset := by
  have hn := newly_eq x hx C P
  have hc := cost_eq x hx P
  have hp := price_eq x hx C P
  simp only [certified, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    decide_eq_true_eq, Instance.Certified]
  constructor
  · rintro ⟨hne, hcost⟩
    constructor
    · rw [← hn]
      simpa using hne
    · rw [← hc, ← hp, ← Rat.cast_mul]
      exact_mod_cast hcost
  · rintro ⟨hne, hcost⟩
    constructor
    · rw [← hn] at hne
      simpa using hne
    · rw [← hc, ← hp, ← Rat.cast_mul] at hcost
      exact_mod_cast hcost

/-- Every retained state stays within the runtime candidate universe. -/
def Bounded (x : Input) (C : List ℕ) : Prop := ∀ j ∈ C, j < x.rows.length

open scoped Classical in
/-- Canonical native union is exactly union of the already retained/proposed families. -/
theorem step_eq (x : Input) (hx : Valid x) (C P : List ℕ) (hC : Bounded x C) :
    (step x C P).toFinset =
      if (instanceOf x hx).Certified x.rho C.toFinset (normalize x P).toFinset
        then C.toFinset ∪ (normalize x P).toFinset else C.toFinset := by
  rw [step]
  by_cases hc : certified x C P = true
  · rw [ite_eq_left hc, ite_eq_left ((certified_eq x hx C P).mp hc)]
    ext j
    simp only [List.mem_toFinset, List.mem_filter, population, List.mem_range,
      Bool.or_eq_true, decide_eq_true_eq, Finset.mem_union, normalize]
    have := hC j
    aesop
  · rw [ite_eq_right hc, ite_eq_right (by simpa only [certified_eq x hx C P] using hc)]

/-- State boundedness is proved from the actual update, not a loop input promise. -/
theorem step_bounded (x : Input) (C P : List ℕ) (hC : Bounded x C) :
    Bounded x (step x C P) := by
  unfold step
  split_ifs
  · intro j hj
    exact List.mem_range.mp (List.mem_filter.mp hj).1
  · exact hC

/-- Whole native retention computes the existing source retention operator. -/
theorem retain_eq (x : Input) (hx : Valid x) :
    (retain x).toFinset = (instanceOf x hx).retain x.rho ∅
      (x.proposals.map fun P => (normalize x P).toFinset) := by
  classical
  have hf (ps : List (List ℕ)) (C : List ℕ) (hC : Bounded x C) :
      (ps.foldl (step x) C).toFinset = (instanceOf x hx).retain x.rho C.toFinset
        (ps.map fun P => (normalize x P).toFinset) := by
    induction ps generalizing C with
    | nil => rfl
    | cons P ps ih =>
      simp only [List.foldl_cons, List.map_cons, Instance.retain]
      rw [ih _ (step_bounded x C P hC), step_eq x hx C P hC]
  exact hf x.proposals [] (by intro j hj; cases hj)

/-- The generated retained family stays inside the runtime candidate universe. -/
theorem retain_bounded (x : Input) : Bounded x (retain x) := by
  have hf (ps : List (List ℕ)) (C : List ℕ) (hc : Bounded x C) :
      Bounded x (ps.foldl (step x) C) := by
    induction ps generalizing C with
    | nil => exact hc
    | cons P ps ih => exact ih _ (step_bounded x C P hc)
  exact hf x.proposals [] (by intro j hj; cases hj)

/-- The final certificate is derived from executable retention and original data. -/
theorem retained_certificate (x : Input) (hx : Valid x) :
    (instanceOf x hx).cost (retain x).toFinset ≤ (x.rho : ℝ) *
      ∑ e ∈ (instanceOf x hx).covered (retain x).toFinset, (instanceOf x hx).dual e := by
  rw [retain_eq x hx]
  exact (instanceOf x hx).retain_bound _ _ (by simp [Instance.cost, Instance.covered])

/-- The executable phase retains only actually supplied proposal candidates.
Connecting that data origin to raw oracle channels remains the query-loop task. -/
theorem retained_provenance (x : Input) (hx : Valid x) :
    (retain x).toFinset ⊆
      (x.proposals.map fun P => (normalize x P).toFinset).foldr (· ∪ ·) ∅ := by
  rw [retain_eq x hx]
  simpa only [Finset.empty_union] using
    (instanceOf x hx).retain_subset x.rho ∅ (x.proposals.map fun P => (normalize x P).toFinset)

/-- Enumerate source candidate indices in a fixed order without a choice-based
finite-set listing. This data conversion is not a native raw-report parser. -/
@[expose] def sourceIndices {m : ℕ} (C : Finset (Fin m)) : List ℕ :=
  (List.finRange m).filterMap fun i => if i ∈ C then some i.val else none

/-- The computed completion flag is exactly coverage of the actual original
finite ground by the retained family. -/
theorem complete_eq (x : Input) (hx : Valid x) : complete x = true ↔
    (instanceOf x hx).covered (retain x).toFinset = (instanceOf x hx).ground := by
  have hc := (instanceOf x hx).covered_subset (retain x).toFinset
  rw [← covered_eq x hx] at hc
  simp only [complete, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    apply Finset.Subset.antisymm
    · rw [← covered_eq x hx]
      exact hc
    · rw [← covered_eq x hx]
      intro e he
      exact List.mem_toFinset.mpr (h e (List.mem_toFinset.mp he))
  · intro h e he
    have hm : e ∈ (instanceOf x hx).covered (retain x).toFinset := by
      rw [h]
      exact List.mem_toFinset.mpr he
    rw [← covered_eq x hx] at hm
    exact List.mem_toFinset.mp hm

/-- Concrete source-index serialization preserves every proposed candidate. -/
theorem sourceIndices_mem {m : ℕ} (C : Finset (Fin m)) (j : ℕ) :
    j ∈ sourceIndices C ↔ ∃ i ∈ C, i.val = j := by
  simp [sourceIndices, List.mem_filterMap]

/-- Native output candidate family, with bounded indices, decoded from the exact
membership mask emitted by the generated machine. -/
@[expose] def outputFamily (x : Input) : Finset (Fin x.rows.length) :=
  Finset.univ.filter fun j => decide (j.val ∈ retain x) = true

/-- Decoded native indices identify exactly the retained original candidate family. -/
theorem outputFamily_image (x : Input) :
    (outputFamily x).image Fin.val = (retain x).toFinset := by
  ext j
  simp only [outputFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq, List.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hj
    exact ⟨⟨j, retain_bounded x j hj⟩, hj, rfl⟩

/-- The source-decoded family has the certificate derived by actual rational
retention, rather than a certificate supplied with the output. -/
theorem output_certificate (x : Input) (hx : Valid x) :
    (instanceOf x hx).cost ((outputFamily x).image Fin.val) ≤ (x.rho : ℝ) *
      ∑ e ∈ (instanceOf x hx).covered ((outputFamily x).image Fin.val),
        (instanceOf x hx).dual e := by
  rw [outputFamily_image]
  exact retained_certificate x hx

/-- A positive computed completion decision certifies the actual native output
as a full cover with its derived dual-weight guarantee. -/
theorem completed_output (x : Input) (hx : Valid x) (hc : complete x = true) :
    (instanceOf x hx).covered ((outputFamily x).image Fin.val) = (instanceOf x hx).ground ∧
      (instanceOf x hx).cost ((outputFamily x).image Fin.val) ≤
        (x.rho : ℝ) * ∑ e ∈ (instanceOf x hx).ground, (instanceOf x hx).dual e := by
  have hg : (instanceOf x hx).covered ((outputFamily x).image Fin.val) =
      (instanceOf x hx).ground := by
    rw [outputFamily_image]
    exact (complete_eq x hx).mp hc
  refine ⟨hg, ?_⟩
  simpa only [hg] using output_certificate x hx

/-- The emitted word is exactly the source's original candidate-family codec. -/
theorem output_encode (x : Input) : output x = ConcurrentBatch.encodeFamily (outputFamily x) := by
  apply List.ext_getElem
  · simp [output, population, ConcurrentBatch.encodeFamily]
  · intro i h₁ h₂
    simp only [output, List.getElem_map, population, List.getElem_range]
    apply Bool.eq_iff_iff.mpr
    simp [ConcurrentBatch.encodeFamily, outputFamily, decide_eq_true_eq]

/-- The original source decoder reads the actual native output without any
assumed output/parser correctness contract. -/
theorem decode_output (x : Input) :
    ConcurrentBatch.decodeFamily x.rows.length (output x) = some (outputFamily x) := by
  rw [output_encode, ConcurrentBatch.decodeFamily_encode]

/-- Actual compiled native execution writes precisely the decodable retained
family mask. Its runtime input carries data only, not a desired family/certificate. -/
theorem compiled_decodes (x : Input) : ∃ t,
    (compiled.machine.runFrom (compiled.machine.initCfg (encInput x)) t).Halted ∧
      ConcurrentBatch.decodeFamily x.rows.length
        (compiled.machine.runFrom (compiled.machine.initCfg (encInput x)) t).output =
          some (outputFamily x) := by
  obtain ⟨t, ht, ho⟩ := compiled_output x
  exact ⟨t, ht, by rw [ho, decode_output]⟩

end Cslib.Probability.StochasticOracle.NativeRetention
