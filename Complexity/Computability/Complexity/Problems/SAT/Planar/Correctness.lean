/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathAssignments
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Semantics
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Degree
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths
import Mathlib.Data.List.GetD
import Mathlib.Tactic.SplitIfs

/-!
# Logical correctness along the actual incidence paths

The actual compiler's occurrence paths are the canonical graph unit paths. This module uses
those path certificates to discharge endpoint and local signal conditions of the wire semantics.

## Main definitions

All compiler data and CNF operations are reused from their existing modules.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.satisfiable_source_of_formula`: actual compiler soundness
  under source width and literal-occurrence bounds of three.

## References

These are original logical composition proofs for the finite compiler.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- An actual crossover whose path goes straight through a cell equates the two signals read
by the executable neighbor lookups, in either traversal direction. -/
theorem signals_eq_of_straight {φ : CNF ℕ} {σ : Variable → Bool}
    (hraw : (rawFormula φ).eval σ = true) {p : Point} (hp : p ∈ crossingSites φ)
    {r : Route} (hn : r.Nodup) {k : ℕ} (hk : k < r.length) (heq : r[k] = p)
    (hstraight : StraightThrough r p (1, 0) ∨ StraightThrough r p (0, 1)) :
    σ (signal (crossingSites φ) p (r.getD (k - 1) p)) =
      σ (signal (crossingSites φ) p (r.getD (k + 1) p)) := by
  rcases hstraight with hs | hs
  · obtain ⟨_, _, hnb⟩ := hs.getD_neighbors hn hk heq
    rcases hnb with ⟨hprev, hnext⟩ | ⟨hprev, hnext⟩
    · rw [hprev, hnext]
      exact horizontal_signal_eq hraw hp
    · rw [hprev, hnext]
      exact (horizontal_signal_eq hraw hp).symm
  · obtain ⟨_, _, hnb⟩ := hs.getD_neighbors hn hk heq
    rcases hnb with ⟨hprev, hnext⟩ | ⟨hprev, hnext⟩
    · rw [hprev, hnext]
      exact vertical_signal_eq hraw hp
    · rw [hprev, hnext]
      exact (vertical_signal_eq hraw hp).symm

/-- Actual cell entry/exit values agree: ordinary cells share one variable, while selected
crossings use the certified opposite ports of the fixed crossover. -/
theorem wire_cells_agree {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ : Variable → Bool} (hraw : (rawFormula φ).eval σ = true) :
    ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      ∀ c ∈ wire (crossingSites φ) (occurrencePath φ o), σ c.1 = σ c.2 := by
  intro o ho c hc
  unfold wire at hc
  obtain ⟨⟨p, k⟩, hpk, rfl⟩ := List.mem_map.mp hc
  have hget := List.mem_zipIdx_iff_getElem?.mp hpk
  obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp hget
  have hk' : k < (occurrencePath φ o).length := by
    simp only [List.length_dropLast] at hk
    omega
  have heq' : (occurrencePath φ o)[k] = p := by
    rw [← List.getElem_dropLast hk]
    exact heq
  have hpi : p ∈ occurrencePath φ o := by
    rw [← heq']
    exact List.getElem_mem hk'
  by_cases hp : p ∈ crossingSites φ
  · exact signals_eq_of_straight hraw hp (occurrencePath_nodup ho) hk' heq'
      (occurrencePath_crossing_straight hw hv ho hp hpi)
  · simp only [signal, hp, ite_false]

/-- Under the actual source width and literal-incidence bounds, raw output satisfaction
implies source satisfaction. No local wire equality or endpoint assumption remains. -/
theorem eval_source_of_rawFormula {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ : Variable → Bool} (hraw : (rawFormula φ).eval σ = true) :
    φ.eval (fun v => σ (Layout.center (φ.distinctVars.idxOf v), none)) = true := by
  apply eval_rawFormula_sound_of_cells φ _ σ
    (fun _ ho => occurrencePath_length_ge_two ho) (wire_cells_agree hw hv hraw) ?_ hraw
  intro o ho
  rw [wire_first_entry ho]

/-- Compaction preserves the soundness direction for the actual natural-labelled output. -/
theorem satisfiable_source_of_formula {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    (h : (formula φ).Satisfiable) : φ.Satisfiable := by
  obtain ⟨σ, hσ⟩ := (CNF.satisfiable_compact (rawFormula φ)).1 h
  exact ⟨_, eval_source_of_rawFormula hw hv hσ⟩

end Cslib.Complexity.SAT.PlanarCompile
