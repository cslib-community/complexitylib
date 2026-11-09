/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Fixed finite/cofinite neighbor-count rules

The final table entry represents the entire tail, not only one degree. These are the source
rules of [ChenJiangZhu2027], Corollary 7.2 / Theorem 7.3 (PDF pp.24–25,31–32).
-/

public section

namespace SimpleGraph

/-- An explicit fixed small-count table and one constant tail entry. -/
abbrev DegreeRule (D : ℕ) := Fin (D + 1) → Bool

/-- Inspect a truncated count; entry D accepts or rejects every count at least D. -/
@[expose] def DegreeRule.accepts {D : ℕ} (r : DegreeRule D) (c : ℕ) : Bool :=
  r ⟨min D c, by have := Nat.min_le_left D c; omega⟩

/-- Ordinary number of selected open neighbors on a finite declared graph. -/
@[expose] noncomputable def selectedDegree {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Fin n))
    (u : Fin n) : ℕ := Nat.card {v : Fin n // G.Adj u v ∧ v ∈ S}

/-- A selected vertex follows sigma, and an unselected vertex follows rho. -/
@[expose] def IsSigmaRhoSet {n : ℕ} (G : SimpleGraph (Fin n)) (σ ρ : Set ℕ)
    (S : Set (Fin n)) : Prop :=
  ∀ u, (u ∈ S → G.selectedDegree S u ∈ σ) ∧
    (u ∉ S → G.selectedDegree S u ∈ ρ)

/-- The ordinary count set denoted by a fixed finite table with a tail entry. -/
@[expose] def DegreeRule.counts {D : ℕ} (r : DegreeRule D) : Set ℕ :=
  {c | r.accepts c = true}

open Classical in
/-- Every finite or cofinite count set has a positive constant-tail cutoff. -/
theorem exists_degreeCutoff (S : Set ℕ) (h : S.Finite ∨ Sᶜ.Finite) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ c, D ≤ c → (c ∈ S ↔ D ∈ S) := by
  rcases h with h | h
  · obtain ⟨b, hb⟩ := h.bddAbove
    refine ⟨b + 1, by omega, ?_⟩
    intro c hc
    have hn : c ∉ S := fun hs => by have := hb hs; omega
    have hd : b + 1 ∉ S := fun hs => by have := hb hs; omega
    exact iff_of_false hn hd
  · obtain ⟨b, hb⟩ := h.bddAbove
    refine ⟨b + 1, by omega, ?_⟩
    intro c hc
    have hn : c ∈ S := by by_contra hn; have := hb hn; omega
    have hd : b + 1 ∈ S := by by_contra hn; have := hb hn; omega
    exact iff_of_true hn hd

/-- Compile a fixed count set to its finite threshold-state table. -/
@[expose] def DegreeRule.ofSet (D : ℕ) (S : Set ℕ) [DecidablePred (· ∈ S)] : DegreeRule D :=
  fun j => decide (j.val ∈ S)

/-- Source finite/cofinite rules are represented exactly, including their entire tails. -/
theorem DegreeRule.ofSet_accepts (D : ℕ) (S : Set ℕ) [DecidablePred (· ∈ S)]
    (h : ∀ c, D ≤ c → (c ∈ S ↔ D ∈ S)) (c : ℕ) :
    (DegreeRule.ofSet D S).accepts c = true ↔ c ∈ S := by
  simp only [DegreeRule.accepts, DegreeRule.ofSet, decide_eq_true_eq]
  by_cases hc : c ≤ D
  · rw [Nat.min_eq_right hc]
  · rw [Nat.min_eq_left (by omega)]
    exact (h c (by omega)).symm


/-- Every compiled table denotes a finite or cofinite set of ordinary counts. -/
theorem DegreeRule.finite_or_cofinite {D : ℕ} (r : DegreeRule D) :
    r.counts.Finite ∨ r.countsᶜ.Finite := by
  cases hr : r ⟨D, by omega⟩ with
  | false =>
    left
    apply (Finset.range D).finite_toSet.subset
    intro c hc
    apply Finset.mem_range.mpr
    by_contra hn
    change r.accepts c = true at hc
    simp only [DegreeRule.accepts, Nat.min_eq_left (by omega : D ≤ c), hr] at hc
    exact Bool.false_ne_true hc
  | true =>
    right
    apply (Finset.range D).finite_toSet.subset
    intro c hc
    apply Finset.mem_range.mpr
    by_contra hn
    apply hc
    change r.accepts c = true
    simp only [DegreeRule.accepts, Nat.min_eq_left (by omega : D ≤ c), hr]

open Classical in
/-- All source finite/cofinite rule pairs admit a common positive cutoff and explicit fixed tables.
This choice is part of the fixed problem, never advice varying with the graph instance. -/
theorem exists_degreeRules (σ ρ : Set ℕ) (hσ : σ.Finite ∨ σᶜ.Finite)
    (hρ : ρ.Finite ∨ ρᶜ.Finite) :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ s r : DegreeRule D, s.counts = σ ∧ r.counts = ρ := by
  obtain ⟨dσ, hdσ, htσ⟩ := exists_degreeCutoff σ hσ
  obtain ⟨dρ, hdρ, htρ⟩ := exists_degreeCutoff ρ hρ
  let D := max dσ dρ
  have hDs : dσ ≤ D := le_max_left _ _
  have hDr : dρ ≤ D := le_max_right _ _
  have hs (c : ℕ) (hc : D ≤ c) : c ∈ σ ↔ D ∈ σ :=
    (htσ c (hDs.trans hc)).trans (htσ D hDs).symm
  have hr (c : ℕ) (hc : D ≤ c) : c ∈ ρ ↔ D ∈ ρ :=
    (htρ c (hDr.trans hc)).trans (htρ D hDr).symm
  refine ⟨D, hdσ.trans hDs, DegreeRule.ofSet D σ, DegreeRule.ofSet D ρ, ?_, ?_⟩
  · ext c; exact DegreeRule.ofSet_accepts D σ hs c
  · ext c; exact DegreeRule.ofSet_accepts D ρ hr c

end SimpleGraph
