/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.KWiseIndependent
public import CslibFrontier.Foundations.Combinatorics.UniformSchedules
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Incidence collisions under four-wise independent labels

Label the disjoint union of the row and column vertices with a four-wise independent family.
Every pair of edges then has the same collision average as under fully independent labels,
including parallel edges and edges sharing one endpoint. Tagging the two vertex sets prevents
a row and a column with the same numeric identifier from accidentally sharing a label.

This is a probabilistic identity, not a native algorithm or a bound on seed length.
-/

public section

namespace Cslib.Probability

open Finset
open Cslib.BalancedSchedules
open scoped BigOperators

private theorem expect_four {S X Y : Type*} [Fintype S] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] {h : S → X → Y}
    (hh : IsKWiseIndependentHash 4 h) (x₀ x₁ x₂ x₃ : X) (f : Y → Y → Y → Y → ℚ) :
    (𝔼 s, f (h s x₀) (h s x₁) (h s x₂) (h s x₃)) =
      𝔼 g : X → Y, f (g x₀) (g x₁) (g x₂) (g x₃) := by
  let T : Finset X := {x₀, x₁, x₂, x₃}
  let F : (T → Y) → ℚ := fun g =>
    f (g ⟨x₀, by simp [T]⟩) (g ⟨x₁, by simp [T]⟩)
      (g ⟨x₂, by simp [T]⟩) (g ⟨x₃, by simp [T]⟩)
  exact (hh.expect_restrict (T := T) card_le_four F).trans
    ((isKWiseIndependentHash_id (X := X) (Y := Y) 4).expect_restrict
      (T := T) card_le_four F).symm

/-- Four-wise independent vertex labels preserve the collision probability for two edges.
Shared endpoints are allowed; the two bipartition sides are tagged by `Sum`. -/
theorem IsKWiseIndependentHash.expect_incidence_collision
    {S E R C L : Type*} [Fintype S] [Finite R] [DecidableEq R]
    [Finite C] [DecidableEq C] [Fintype L] [DecidableEq L] [Nonempty L]
    {h : S → R ⊕ C → L} (hh : IsKWiseIndependentHash 4 h)
    (rowOf : E → R) (colOf : E → C) (e e' : E) :
    (𝔼 s, if incidenceLabel rowOf colOf (fun r => h s (.inl r))
        (fun c => h s (.inr c)) e =
      incidenceLabel rowOf colOf (fun r => h s (.inl r))
        (fun c => h s (.inr c)) e' then (1 : ℚ) else 0) =
      (if rowOf e = rowOf e' then 1 else 1 / (Fintype.card L : ℚ)) *
        (if colOf e = colOf e' then 1 else 1 / (Fintype.card L : ℚ)) := by
  let := Fintype.ofFinite R
  let := Fintype.ofFinite C
  have hfour := expect_four hh (.inl (rowOf e)) (.inr (colOf e))
    (.inl (rowOf e')) (.inr (colOf e'))
    (fun a b c d => if (a, b) = (c, d) then 1 else 0)
  change (𝔼 s, if (h s (.inl (rowOf e)), h s (.inr (colOf e))) =
      (h s (.inl (rowOf e')), h s (.inr (colOf e'))) then (1 : ℚ) else 0) = _
  rw [hfour]
  have he := Fintype.expect_equiv (Equiv.sumArrowEquivProdArrow R C L)
    (fun g => if (g (.inl (rowOf e)), g (.inr (colOf e))) =
      (g (.inl (rowOf e')), g (.inr (colOf e'))) then (1 : ℚ) else 0)
    (fun (ρ, κ) => if incidenceLabel rowOf colOf ρ κ e =
      incidenceLabel rowOf colOf ρ κ e' then (1 : ℚ) else 0) (fun _ => rfl)
  rw [he, Fintype.expect_prod_type]
  exact expect_incidenceLabel_collision rowOf colOf e e'

end Cslib.Probability
