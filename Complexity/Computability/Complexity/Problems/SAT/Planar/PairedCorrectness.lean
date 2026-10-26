/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedSemantics
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths
import Complexity.Computability.Complexity.Problems.SAT.Planar.PathAssignments
import Complexity.Foundations.Data.List.Filter
import Mathlib.Data.List.GetD

/-!
# Unique assignments in the actual paired compiler

Every occupied ordinary cell belongs to a retained occurrence path. Each selected crossing is
occupied by a horizontal and a vertical occurrence path. The constant-wire theorem therefore
determines both crossover inputs and every ordinary ring from the original assignment.

## Main results

* `Cslib.Complexity.SAT.ParsimoniousPlanar.crossing_axes_exist`: actual selected crossings carry
  both independent signals.

## References

These are original composition proofs using the canonical path occupancy certificates.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ParsimoniousPlanar

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- Every actual selected crossing is used by both a horizontal and a vertical occurrence. -/
theorem crossing_axes_exist {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {p : Point} (hp : p ∈ crossingSites φ) :
    ∃ o ∈ Cslib.Logic.PL.occurrences φ, ∃ t ∈ Cslib.Logic.PL.occurrences φ,
      p ∈ occurrencePath φ o ∧ p ∈ occurrencePath φ t ∧
        StraightThrough (occurrencePath φ o) p (1, 0) ∧
          StraightThrough (occurrencePath φ t) p (0, 1) := by
  have hc := ((PlanarCompile.mem_crossingSites φ p).1 hp).2.2
  rw [← PlanarCompile.occurrencePaths_eq_paths] at hc
  obtain ⟨i, j, hi, hj, hij, hpi, hpj⟩ := (List.two_le_filter_contains_iff _ p).1 hc
  have hi' : i < (Cslib.Logic.PL.occurrences φ).length := by
    simpa only [List.length_map] using hi
  have hj' : j < (Cslib.Logic.PL.occurrences φ).length := by
    simpa only [List.length_map] using hj
  simp only [List.getElem_map] at hpi hpj
  have hoi := List.getElem_mem hi'
  have hoj := List.getElem_mem hj'
  have hot : (Cslib.Logic.PL.occurrences φ)[i] ≠ (Cslib.Logic.PL.occurrences φ)[j] := by
    intro he
    exact hij ((Cslib.Logic.PL.occurrences_nodup φ).getElem_inj_iff.1 he)
  rcases PlanarCompile.occurrencePath_crossing_straight hw hv hoi hp hpi with hs | hs <;>
    rcases PlanarCompile.occurrencePath_crossing_straight hw hv hoj hp hpj with ht | ht
  · exact False.elim (hot (PlanarCompile.crossing_axis_occurrence_eq hw hv hoi hoj hp
      hpi hpj (Or.inl rfl) hs ht))
  · exact ⟨_, hoi, _, hoj, hpi, hpj, hs, ht⟩
  · exact ⟨_, hoj, _, hoi, hpj, hpi, ht, hs⟩
  · exact False.elim (hot (PlanarCompile.crossing_axis_occurrence_eq hw hv hoi hoj hp
      hpi hpj (Or.inr rfl) hs ht))

/-- Every retained ordinary cell lies on an actual source occurrence path. -/
theorem ordinary_occurrence_exists {φ : CNF ℕ} {p : Point} (hp : p ∈ ordinaryCells φ) :
    ∃ o ∈ Cslib.Logic.PL.occurrences φ, p ∈ (occurrencePath φ o).dropLast := by
  obtain ⟨⟨r, hr, hpr⟩, _⟩ := (mem_ordinaryCells φ p).1 hp
  change r ∈ PlanarCompile.paths φ at hr
  rw [← PlanarCompile.occurrencePaths_eq_paths] at hr
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
  exact ⟨o, ho, hpr⟩

/-- A satisfying ordinary ring's value is determined by any occurrence retaining its cell. -/
theorem ordinary_value_source {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ : Variable → Bool} (h : (rawFormula φ).eval σ = true)
    {p : Point} (hp : p ∈ ordinaryCells φ) {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) (hpo : p ∈ (occurrencePath φ o).dropLast) :
    σ (p, Sum.inl (0, 0)) = sourceValue φ σ o.2.2.1 := by
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hpo
  have hk' : k < (occurrencePath φ o).length - 1 := by
    simpa only [List.length_dropLast] using hk
  have hwi : k < (wire (crossingSites φ) (occurrencePath φ o)).length := by
    rwa [length_wire]
  have hc := (wire_values_source hw hv h ho _ (List.getElem_mem hwi) 0).1
  rw [getElem_wire _ _ _ hk'] at hc
  rw [← List.getElem_dropLast hk, heq] at hc
  simpa only [signal, ordinary_port_value h hp] using hc

/-- Each crossover input is exactly the source value on its occupying axis. -/
theorem crossing_axis_value {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ : Variable → Bool} (h : (rawFormula φ).eval σ = true)
    {p : Point} (hp : p ∈ crossingSites φ) {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) (hpo : p ∈ occurrencePath φ o)
    (axis : Bool)
    (hs : StraightThrough (occurrencePath φ o) p (if axis then (0, 1) else (1, 0))) :
    σ (p, Sum.inr (PairedCrossover.terminal (if axis then 2 else 0) 0)) =
      sourceValue φ σ o.2.2.1 := by
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hpo
  obtain ⟨_, hnext, hnb⟩ := hs.getD_neighbors (PlanarCompile.occurrencePath_nodup ho) hk heq
  have hk' : k < (occurrencePath φ o).length - 1 := by omega
  have hwi : k < (wire (crossingSites φ) (occurrencePath φ o)).length := by
    rwa [length_wire]
  have hc := (wire_values_source hw hv h ho _ (List.getElem_mem hwi) 0).1
  rw [getElem_wire _ _ _ hk', heq] at hc
  cases axis with
  | false =>
    have hl : side p (p - (1, 0)) = 0 := by
      simpa [PairedPorts.neighbor, sub_eq_add_neg] using side_neighbor p 0
    have hr : side p (p + (1, 0)) = 1 := by
      simpa [PairedPorts.neighbor] using side_neighbor p 1
    rcases hnb with ⟨hprev, _⟩ | ⟨hprev, _⟩
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte] at hprev ⊢
      simp only [signal, hprev, hl, hr] at hc
      rw [crossing_port_value h hp] at hc
      simpa using hc
  | true =>
    have hb : side p (p - (0, 1)) = 2 := by
      simpa [PairedPorts.neighbor, sub_eq_add_neg] using side_neighbor p 2
    have ht : side p (p + (0, 1)) = 3 := by
      simpa [PairedPorts.neighbor] using side_neighbor p 3
    rcases hnb with ⟨hprev, _⟩ | ⟨hprev, _⟩
    all_goals
      simp only [↓reduceIte] at hprev ⊢
      simp only [signal, hprev, hb, ht] at hc
      rw [crossing_port_value h hp] at hc
      simpa using hc

/-- Source agreement forces agreement on every variable of every emitted ordinary ring. -/
theorem ordinary_assignments_agree {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ τ : Variable → Bool} (hσ : (rawFormula φ).eval σ = true)
    (hτ : (rawFormula φ).eval τ = true)
    (he : ∀ v ∈ φ.vars, sourceValue φ σ v = sourceValue φ τ v)
    {p : Point} (hp : p ∈ ordinaryCells φ) (v : OrdinaryRing.Variable) :
    σ (p, Sum.inl v) = τ (p, Sum.inl v) := by
  obtain ⟨o, ho, hpo⟩ := ordinary_occurrence_exists hp
  have hs := (OrdinaryRing.eval_formula_iff _).1
    (((eval_rawFormula_iff φ σ).1 hσ).2.1 p hp) v
  have ht := (OrdinaryRing.eval_formula_iff _).1
    (((eval_rawFormula_iff φ τ).1 hτ).2.1 p hp) v
  exact hs.trans ((ordinary_value_source hw hv hσ hp ho hpo).trans
    ((he _ (variable_mem_of_mem_occurrences ho)).trans
      ((ordinary_value_source hw hv hτ hp ho hpo).symm.trans ht.symm)))

/-- Source agreement forces agreement on every variable of every emitted crossover. -/
theorem crossing_assignments_agree {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ τ : Variable → Bool} (hσ : (rawFormula φ).eval σ = true)
    (hτ : (rawFormula φ).eval τ = true)
    (he : ∀ v ∈ φ.vars, sourceValue φ σ v = sourceValue φ τ v)
    {p : Point} (hp : p ∈ crossingSites φ) (v : PairedCrossover.Variable) :
    σ (p, Sum.inr v) = τ (p, Sum.inr v) := by
  obtain ⟨o, ho, t, ht, hpo, hpt, hhor, hver⟩ := crossing_axes_exist hw hv hp
  have ha : σ (p, Sum.inr (PairedCrossover.terminal 0 0)) =
      τ (p, Sum.inr (PairedCrossover.terminal 0 0)) :=
    (crossing_axis_value hw hv hσ hp ho hpo false hhor).trans
      ((he _ (variable_mem_of_mem_occurrences ho)).trans
        (crossing_axis_value hw hv hτ hp ho hpo false hhor).symm)
  have hb : σ (p, Sum.inr (PairedCrossover.terminal 2 0)) =
      τ (p, Sum.inr (PairedCrossover.terminal 2 0)) :=
    (crossing_axis_value hw hv hσ hp ht hpt true hver).trans
      ((he _ (variable_mem_of_mem_occurrences ht)).trans
        (crossing_axis_value hw hv hτ hp ht hpt true hver).symm)
  have hs := congrFun (PairedCrossover.eq_canonicalExtension_of_holds
    (((eval_rawFormula_iff φ σ).1 hσ).2.2.1 p hp)) v
  have ht := congrFun (PairedCrossover.eq_canonicalExtension_of_holds
    (((eval_rawFormula_iff φ τ).1 hτ).2.2.1 p hp)) v
  exact hs.trans (by rw [ha, hb]; exact ht.symm)


end Cslib.Complexity.SAT.ParsimoniousPlanar
