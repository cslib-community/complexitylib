/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.Witnesses
public import Mathlib.Data.Nat.Count
import Mathlib.Data.List.GetD

/-!
# One false-positive budget for distinct record/query occurrences

Lists within distinct existing instances inject into the existing global `failedScans` set.
Consequently their failed accepted occurrences share one `falsePositiveCount` bound. This
finite bridge does not multiply that bound by the number of records. A native caller must
derive list membership, nonrepetition and answers from its actual execution/readback.

The counting argument adapts `Host.FailedScans.sum_fails_le` from
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, using the existing local
finite instances and failed-scan API rather than a second host-data model.
-/

public section

namespace Cslib.Algorithms.ExactTriangle

/-- Failed accepted occurrences across distinct records inject into the single global
failed-scan set. Lists may be partial chunks, but each occurrence list must be repetition-free. -/
theorem sum_failed_occurrences_le {n D g p : ℕ}
    (wAB wBC wAC : Fin n → Fin n → ℤ) (hp : p ≠ 0)
    (ans : InstanceIndex p → Fin n × Fin n → Bool)
    (hans : AnswersCorrect wAB wBC wAC D g p ans)
    (I : Finset (InstanceIndex p)) (hI : I ⊆ instanceIndices wAB D g p)
    (queries : InstanceIndex p → List (Fin n × Fin n)) (default : Fin n × Fin n)
    (hnodup : ∀ idx ∈ I, (queries idx).Nodup)
    (hquery : ∀ idx ∈ I, ∀ q ∈ queries idx, q ∈ (lopInstance wAB wBC wAC D g p idx).W) :
    (∑ idx ∈ I, Nat.count (fun j => ans idx ((queries idx).getD j default) = true ∧
      scanPiece wAB wBC wAC D g idx.2.2
        ((queries idx).getD j default).1 ((queries idx).getD j default).2 = none)
      (queries idx).length) ≤ falsePositiveCount wAB wBC wAC p := by
  classical
  let P := fun idx j => ans idx ((queries idx).getD j default) = true ∧
    scanPiece wAB wBC wAC D g idx.2.2
      ((queries idx).getD j default).1 ((queries idx).getD j default).2 = none
  let occurrences : Finset (Σ _ : InstanceIndex p, ℕ) :=
    I.sigma fun idx => (Finset.range (queries idx).length).filter (P idx)
  let failures := failedScans wAB wBC wAC D g p ans
  have mem_occurrence (z : Σ _ : InstanceIndex p, ℕ) (hz : z ∈ occurrences) :
      z.1 ∈ I ∧ z.2 < (queries z.1).length ∧ P z.1 z.2 := by
    simpa only [occurrences, Finset.mem_sigma, Finset.mem_filter, Finset.mem_range,
      and_assoc] using hz
  have get_eq (idx : InstanceIndex p) (j : ℕ) (hj : j < (queries idx).length) :
      (queries idx).getD j default = (queries idx).get ⟨j, hj⟩ := by
    rw [List.getD_eq_getElem _ _ hj, List.get_eq_getElem]
  let f : {z // z ∈ occurrences} → {s // s ∈ failures} := fun z =>
    ⟨(z.val.1, (queries z.val.1).getD z.val.2 default), by
      obtain ⟨hidx, hj, hacc, hnone⟩ := mem_occurrence z.val z.prop
      apply Finset.mem_filter.mpr
      refine ⟨mem_acceptedPairs.mpr ⟨hI hidx, ?_, hacc⟩, hnone⟩
      exact hquery _ hidx _ (get_eq _ _ hj ▸ List.get_mem _ _)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨idx, j⟩, hx⟩ ⟨⟨idx', j'⟩, hy⟩ hxy
    have he : idx = idx' := congrArg (fun s => s.val.1) hxy
    subst idx'
    obtain ⟨hidx, hj, -⟩ := mem_occurrence ⟨idx, j⟩ hx
    obtain ⟨-, hj', -⟩ := mem_occurrence ⟨idx, j'⟩ hy
    have hpair := congrArg (fun s => s.val.2) hxy
    change (queries idx).getD j default = (queries idx).getD j' default at hpair
    rw [get_eq idx j hj, get_eq idx j' hj'] at hpair
    have hpos := List.nodup_iff_injective_get.mp (hnodup idx hidx) hpair
    exact Subtype.ext (Sigma.ext rfl (heq_of_eq (congrArg Fin.val hpos)))
  have hcard : (∑ idx ∈ I, Nat.count (P idx) (queries idx).length) = occurrences.card := by
    simp only [occurrences, Finset.card_sigma, Nat.count_eq_card_filter_range]
  change (∑ idx ∈ I, Nat.count (P idx) (queries idx).length) ≤ _
  rw [hcard]
  calc
    _ = Fintype.card {z // z ∈ occurrences} := (Fintype.card_coe _).symm
    _ ≤ Fintype.card {s // s ∈ failures} := Fintype.card_le_of_injective f hf
    _ = failures.card := Fintype.card_coe _
    _ ≤ falsePositiveCount wAB wBC wAC p := card_failedScans_le hp hans

end Cslib.Algorithms.ExactTriangle
