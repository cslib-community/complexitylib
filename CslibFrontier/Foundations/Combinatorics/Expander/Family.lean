/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Reindex

/-!
# Families of expanders

A **family of expanders** (`Cslib.RotationMap.ExpanderFamily`) bundles a choice of a `D`-regular
multigraph on every finite type with a common bound `μ` on their spectral expansions; constructions
that need expanders of constant degree on arbitrary vertex sets, such as Dinur's preprocessing
[Dinur, Section 3.1][Dinur2005], take one as a parameter. The notion is defined apart from the
non-constructive family `Cslib.RotationMap.expanderFamily`, so that explicit families do not depend
on it.

## Main definitions

* `Cslib.RotationMap.ExpanderFamily`: a family of `D`-regular multigraphs on all finite types with
  spectral expansion at most `μ`.
* `Cslib.RotationMap.ExpanderFamily.ofFin`: interpret an indexed family on arbitrary finite types.

## References

* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib.RotationMap

universe u

/-- A **family of expanders** of degree `|D|` and spectral bound `μ`: a `D`-regular multigraph on
every finite type `V` in the universe `u`, of spectral expansion at most `μ`. It is a family of
expanders in the usual sense when `D` is finite and nonempty and `μ < 1`. -/
structure ExpanderFamily (D : Type*) [Fintype D] (μ : ℝ) where
  /-- The multigraph on a finite type. -/
  graph (V : Type u) [Fintype V] : RotationMap V D
  /-- The spectral expansion of each multigraph of the family is at most `μ`. -/
  spectralExpansion_graph_le (V : Type u) [Fintype V] : (graph V).spectralExpansion ≤ μ

/-- Interpret an indexed family on arbitrary finite types by choosing a numbering. Only this
mathematical wrapper is noncomputable; executable clients should use the original indexed family
or supply their own vertex equivalence to `RotationMap.reindex`. -/
noncomputable def ExpanderFamily.ofFin {D : Type*} [Fintype D] {μ : ℝ}
    (graph : (n : ℕ) → RotationMap (Fin n) D)
    (bound : ∀ n, (graph n).spectralExpansion ≤ μ) : ExpanderFamily.{u} D μ where
  graph V _ := (graph (Fintype.card V)).reindex (Fintype.equivFin V).symm
  spectralExpansion_graph_le V _ := by
    simpa only [spectralExpansion_reindex] using bound (Fintype.card V)

end Cslib.RotationMap
