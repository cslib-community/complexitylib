/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Parity
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.EncLen
import Mathlib.Tactic.Linarith

/-!
# Explicit sparse-query size bounds

These bounds include the full framed sparse-system encoding, rather than just matrix dimensions.
They concern the finite compiler only and do not supply a topological recognition criterion.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Turing.MultiTapeTM Cslib.Logic.PL

/-- Every endpoint in an algebraic frame lies below its declared stride. -/
@[expose] def BoundedEndpoints (F : Frame) : Prop :=
  ∀ e ∈ F.segments, e.source < F.vertexCount ∧ e.target < F.vertexCount

/-- A segment emitted by twice subdivision is closed on its dense declared vertex range. -/
theorem boundedEndpoints_frame {I : FixedRotationInput} (hI : Valid I) :
    BoundedEndpoints (frame I) := by
  intro segment hs
  obtain ⟨entry, he, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp he)
  have hem : entry.1 ∈ I.graph.edges := by rw [← hv]; exact List.getElem_mem hi
  obtain ⟨hu, hw⟩ := hI.edge_endpoints_lt hem
  change segment ∈ [((entry.1.1, I.graph.vertices.length + 2 * entry.2), _),
    ((I.graph.vertices.length + 2 * entry.2, I.graph.vertices.length + 2 * entry.2 + 1), false),
    ((I.graph.vertices.length + 2 * entry.2 + 1, entry.1.2), _)] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> change _ < subdivisionSize I ∧ _ < subdivisionSize I <;>
    unfold subdivisionSize <;> constructor <;>
    dsimp only [Segment.source, Segment.target, Segment.endpoints] <;> omega

/-- Every variable in a literal row lies in the finite rectangular move frame. -/
theorem label_lt_row {F : Frame} (hF : BoundedEndpoints F)
    {e f : Segment × ℕ} (he : e ∈ F.segments.zipIdx) (hf : f ∈ F.segments.zipIdx)
    {label : ℕ} (hl : label ∈ (row F e f).vars) :
    label < F.segments.length * F.vertexCount := by
  have entry (x : Segment × ℕ) (hx : x ∈ F.segments.zipIdx) :
      x.2 < F.segments.length ∧ x.1 ∈ F.segments := by
    obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hx)
    exact ⟨hi, hv ▸ List.getElem_mem hi⟩
  have he' := entry e he
  have hf' := entry f hf
  have eb := hF e.1 he'.2
  have fb := hF f.1 hf'.2
  have helper (n i : ℕ) (s : Segment) (p : ℕ × ℕ) (hi : i < F.segments.length)
      (hp : p.1 < F.vertexCount ∧ p.2 < F.vertexCount) (hn : n = F.vertexCount)
      (hl : label ∈ moveLabels n i s p) : label < F.segments.length * F.vertexCount := by
    subst n
    unfold moveLabels at hl
    split at hl
    · simp at hl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact moveLabel_lt hi hp.1
      · exact moveLabel_lt hi hp.2
  rcases List.mem_append.mp hl with hl | hl
  · exact helper _ _ _ _ he'.1 fb rfl hl
  · exact helper _ _ _ _ hf'.1 eb rfl hl

/-- Every compiled row comes from an actual independent pair of segment occurrences. -/
theorem mem_compileFrame {F : Frame} {r : AffineEquation ℕ} :
    r ∈ compileFrame F ↔ ∃ e ∈ F.segments.zipIdx, ∃ f ∈ F.segments.zipIdx,
      f.2 < e.2 ∧ independent e.1.endpoints f.1.endpoints = true ∧ r = row F e f := by
  simp only [compileFrame, List.mem_flatMap, List.mem_map, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨e, he, f, ⟨hf, hlt, hind⟩, hr⟩
    exact ⟨e, he, f, hf, hlt, hind, hr.symm⟩
  · rintro ⟨e, he, f, hf, hlt, hind, rfl⟩
    exact ⟨e, he, f, ⟨hf, hlt, hind⟩, rfl⟩

/-- The finite system uses at most four labels per row. -/
theorem width_compileFrame {F : Frame} {r : AffineEquation ℕ} (hr : r ∈ compileFrame F) :
    r.vars.length ≤ 4 := by
  obtain ⟨e, _, f, _, _, _, rfl⟩ := mem_compileFrame.mp hr
  exact length_row_le F e f

/-- Full binary label width including the zero/empty-frame case. -/
theorem bits_compileFrame {F : Frame} (hF : BoundedEndpoints F)
    {r : AffineEquation ℕ} (hr : r ∈ compileFrame F) {label : ℕ} (hl : label ∈ r.vars) :
    (encNat label).length ≤ Nat.log2 (F.segments.length * F.vertexCount) + 1 := by
  obtain ⟨e, he, f, hf, _, _, rfl⟩ := mem_compileFrame.mp hr
  exact length_encNat_le_log2 (label_lt_row hF he hf hl).le

/-- Each fully framed sparse row costs at most `32 ell + 21` bits in its outer system list. -/
theorem framed_row_length_le {r : AffineEquation ℕ} {ell : ℕ} (hw : r.vars.length ≤ 4)
    (hb : ∀ label ∈ r.vars, (encNat label).length ≤ ell) :
    2 * (encAffineEquation encNat r).length + 1 ≤ 32 * ell + 21 := by
  have hl := length_encList_le encNat r.vars hb
  have hv : (encList encNat r.vars).length ≤ 4 * (2 * ell + 1) :=
    hl.trans (Nat.mul_le_mul_right _ hw)
  enc_len [encAffineEquation_apply, encAffineEquationFields, List.length_singleton]

/-- The entire sparse system encoding, including equation and list framing. -/
theorem length_encoding_compileFrame_le {F : Frame} (hF : BoundedEndpoints F) :
    (XORSAT.encoding (compileFrame F)).length ≤
      F.segments.length ^ 2 *
        (32 * (Nat.log2 (F.segments.length * F.vertexCount) + 1) + 21) := by
  rw [XORSAT.encoding, length_encList]
  calc
    _ ≤ ((compileFrame F).map fun _ =>
        32 * (Nat.log2 (F.segments.length * F.vertexCount) + 1) + 21).sum := by
      apply List.sum_le_sum
      intro r hr
      exact framed_row_length_le (width_compileFrame hr) (fun _ hl => bits_compileFrame hF hr hl)
    _ = (compileFrame F).length *
        (32 * (Nat.log2 (F.segments.length * F.vertexCount) + 1) + 21) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (length_compileFrame_le F)

end Cslib.Complexity.Graph.RotationRecognition
