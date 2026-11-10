/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.CoordinateExpectation
public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyTaskData

/-!
# Spectator transport for genuine hierarchy targets

The detector, final pilot, correction iterates and residual are unchanged when each
seed is represented by one coordinate of a larger uniform product. In particular the
source and terminal coordinates can be chosen independently: changing the source role
preserves these deterministic targets, with the channel predicates (and hence their
rates and identifier padding) fixed.

This is a prerequisite for identifying the targets of actual left and negative requests.
It does not identify a canonical raw request family or prove a conditional mean of a
product on the single shared environment. Different padded identifier maps also need a
separate channel transport; the theorem does not silently identify their distributions.
The transport proofs are Christian Reitwiessner's original work; the hierarchy construction
is adapted from Samuel Schlesinger's work.
-/

public section
open Finset
open scoped BigOperators

namespace Matrix

variable {V A B R T : Type*} [Fintype V] [Fintype A] [Nonempty A]
  [Fintype B] [Nonempty B] [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
  (X : A → V → Prop) (Y : B → V → Prop)
  [∀ a v, Decidable (X a v)] [∀ b v, Decidable (Y b v)]

omit [Nonempty A] [Nonempty B] in
/-- Relabelling both finite seeds preserves the actual detector, including its conditioning.
The equalities concern channel predicates, not a desired detector value. -/
theorem columnDetector_equiv {A' B' : Type*} [Fintype A'] [Fintype B']
    (e : A ≃ A') (d : B ≃ B')
    (X' : A' → V → Prop) (Y' : B' → V → Prop)
    [∀ a v, Decidable (X' a v)] [∀ b v, Decidable (Y' b v)]
    (hX : ∀ a v, X a v ↔ X' (e a) v) (hY : ∀ b v, Y b v ↔ Y' (d b) v)
    (ϕ ρ : ℝ → ℝ) (J K : ℕ) (f : ℝ) (G : Matrix V V ℝ) :
    columnDetector X Y ϕ ρ J K f G = columnDetector X' Y' ϕ ρ J K f G := by
  classical
  funext y
  apply Fintype.expect_equiv e
  intro a
  apply expect_equiv d
  · intro b
    simp only [mem_filter, mem_univ, true_and]
    exact hY b y
  · intro b _
    rw [show ({v | X a v} : Finset V) = ({v | X' (e a) v} : Finset V) from
      filter_congr fun v _ => hX a v,
      show ({v | Y b v} : Finset V) = ({v | Y' (d b) v} : Finset V) from
        filter_congr fun v _ => hY b v]

omit [Nonempty B] in
/-- Integrating a source coordinate leaves the original detector. The terminal seed and
its conditioning are unchanged, so it can subsequently be shared with another child. -/
theorem columnDetector_source_pi (s : R) (ϕ ρ : ℝ → ℝ) (J K : ℕ) (f : ℝ)
    (G : Matrix V V ℝ) :
    columnDetector (fun (σ : R → A) v => X (σ s) v) Y ϕ ρ J K f G =
      columnDetector X Y ϕ ρ J K f G := by
  funext y
  simpa only [columnDetector] using expect_pi_eval s
    (fun a => 𝔼 b ∈ ({b | Y b y} : Finset B),
      detectorTrial ϕ ρ J K f G {v | X a v} {v | Y b v} y)

/-- Exact detector transport, including the terminal conditioning event and all spectators.
Source and terminal coordinates belong to the detector's two independent seed arguments;
this is not an assertion that estimated factors on one environment are independent. -/
theorem columnDetector_pi (s : R) (t : T) (ϕ ρ : ℝ → ℝ) (J K : ℕ) (f : ℝ)
    (G : Matrix V V ℝ) :
    columnDetector (fun (σ : R → A) v => X (σ s) v)
      (fun (σ : T → B) v => Y (σ t) v) ϕ ρ J K f G =
        columnDetector X Y ϕ ρ J K f G := by
  funext y
  simp only [columnDetector]
  have ht (a : A) := expect_pi_eval_filter t (fun b => Y b y)
    (fun b => detectorTrial ϕ ρ J K f G {v | X a v} {v | Y b v} y)
  simp_rw [ht]
  simpa only [columnDetector] using expect_pi_eval s
    (fun a => 𝔼 b ∈ ({b | Y b y} : Finset B),
      detectorTrial ϕ ρ J K f G {v | X a v} {v | Y b v} y)

namespace HierarchyParams

variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  (s : R) (t : T) (f : ℝ) (C : Matrix V V ℝ)

omit [Nonempty A] [Nonempty B] in
/-- Genuine pilot transport under exact relabelling of both channel seeds. -/
theorem pilot_equiv {A' B' : Type*} [Fintype A'] [Fintype B']
    (e : A ≃ A') (d : B ≃ B')
    (X' : A' → V → Prop) (Y' : B' → V → Prop)
    [∀ a v, Decidable (X' a v)] [∀ b v, Decidable (Y' b v)]
    (hX : ∀ a v, X a v ↔ X' (e a) v) (hY : ∀ b v, Y b v ↔ Y' (d b) v) :
    P.pilot X Y f C = P.pilot X' Y' f C := by
  simp only [pilot_eq]
  congr 1
  funext G
  exact columnDetector_equiv X Y e d X' Y' hX hY P.ϕ P.ρ P.J P.K f G

omit [Nonempty A] [Nonempty B] in
/-- Genuine correction transport under exact channel relabelling. -/
theorem correctionIter_equiv {A' B' : Type*} [Fintype A'] [Fintype B']
    (e : A ≃ A') (d : B ≃ B')
    (X' : A' → V → Prop) (Y' : B' → V → Prop)
    [∀ a v, Decidable (X' a v)] [∀ b v, Decidable (Y' b v)]
    (hX : ∀ a v, X a v ↔ X' (e a) v) (hY : ∀ b v, Y b v ↔ Y' (d b) v) (i : ℕ) :
    P.correctionIter X Y f C i = P.correctionIter X' Y' f C i := by
  simp only [correctionIter, pilot_equiv X Y P f C e d X' Y' hX hY]

omit [Nonempty B] in
/-- Genuine pilot target after integrating all source spectators. -/
theorem pilot_source_pi :
    P.pilot (fun (σ : R → A) v => X (σ s) v) Y f C = P.pilot X Y f C := by
  simp only [pilot_eq]
  congr 1
  funext G
  exact columnDetector_source_pi X Y s P.ϕ P.ρ P.J P.K f G

omit [Nonempty B] in
/-- Actual correction target after integrating the source spectators. -/
theorem correctionIter_source_pi (i : ℕ) :
    P.correctionIter (fun (σ : R → A) v => X (σ s) v) Y f C i =
      P.correctionIter X Y f C i := by
  simp only [correctionIter, pilot_source_pi]

/-- The true pilot is invariant under coordinate representation of both channels. -/
theorem pilot_pi :
    P.pilot (fun (σ : R → A) v => X (σ s) v)
      (fun (σ : T → B) v => Y (σ t) v) f C = P.pilot X Y f C := by
  simp only [pilot_eq]
  congr 1
  funext G
  exact columnDetector_pi X Y s t P.ϕ P.ρ P.J P.K f G

/-- Every genuine correction iterate has the same target after source-role reset. -/
theorem correctionIter_pi (i : ℕ) :
    P.correctionIter (fun (σ : R → A) v => X (σ s) v)
      (fun (σ : T → B) v => Y (σ t) v) f C i = P.correctionIter X Y f C i := by
  simp only [correctionIter, pilot_pi]

/-- The genuine raw input retains its matrix units under spectator transport. -/
theorem correctionInput_pi (i : ℕ) :
    P.correctionInput (fun (σ : R → A) v => X (σ s) v)
      (fun (σ : T → B) v => Y (σ t) v) f C i = P.correctionInput X Y f C i := by
  simp only [correctionInput, correctionIter_pi]

/-- The actual final correction, rather than an arbitrary reference, is transported. -/
theorem correction_pi :
    P.correction (fun (σ : R → A) v => X (σ s) v)
      (fun (σ : T → B) v => Y (σ t) v) f C = P.correction X Y f C := by
  simp only [← correctionIter_last, correctionIter_pi]

/-- The genuine residual C-E+EC is invariant under adding spectator coordinates. -/
theorem residual_pi :
    P.residual (fun (σ : R → A) v => X (σ s) v)
      (fun (σ : T → B) v => Y (σ t) v) f C = P.residual X Y f C := by
  simp only [residual_eq, correction_pi]

end HierarchyParams
end Matrix
