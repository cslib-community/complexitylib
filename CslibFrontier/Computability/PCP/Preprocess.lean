/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.DegreeReduction
public import CslibFrontier.Foundations.Combinatorics.Expander.Existence

/-!
# Preprocessing

Dinur's powering step needs a constraint graph that is regular, of constant degree, an expander,
and has a self-loop at every vertex. **Preprocessing** [Dinur, Section 3.1][Dinur2005] produces one
from an arbitrary constraint graph `G`, over the same alphabet, given a family `X` of `D`-regular
expanders of spectral expansion at most `μ` (`Cslib.RotationMap.ExpanderFamily`), in three steps:

1. **degree reduction** (`Cslib.PCP.ConstraintGraph.degreeReduce`), with the expanders of `X` on the
   clouds: a `(1 + |D|)`-regular constraint graph on the `2 |E|` half-edges of `G`;
2. **expanderization**: the edges of the expander of `X` on the half-edges added, with constraints
   that always hold (`Cslib.PCP.RegularConstraintGraph.addTrivial`), for degree `1 + 2 |D|`;
3. a **self-loop** added at every vertex, with a constraint that always holds
   (`Cslib.PCP.RegularConstraintGraph.addLoops`), for degree `2 + 2 |D|`.

The result `G.preprocess X` is `(2 |D| + 2)`-regular on `2 |E|` vertices, so its size is linear in
the number of edges of `G`; its spectral expansion is at most `1 - (1 - μ) |D| / (2 |D| + 2)`
(`spectralExpansion_preprocess_le`); for `μ < 1` it is satisfiable exactly when `G` is
(`satisfiable_preprocess_iff`); and its value is between `min 1 ((1 - μ) |D|) / (4 (1 + |D|))`
times `UNSAT(G)` and `UNSAT(G)` (`le_unsatVal_preprocess`, `unsatVal_preprocess_le`), whatever the
alphabet.

With the non-explicit family `Cslib.RotationMap.expanderFamily` of `120`-regular expanders of
spectral expansion at most `1 - 1 / 360000`, the preprocessed graph is `242`-regular, its spectral
expansion is at most `1 - 1 / 726000` (`spectralExpansion_preprocess_expanderFamily_le`) and its
value at least `UNSAT(G) / 1452000` (`le_unsatVal_preprocess_expanderFamily`).

Executable clients may supply their own cloud numberings through `PreprocessExpanders` and
`preprocessWith`. The family-based operation is a wrapper of this interface; its correctness does
not require the executable numberings to equal a choice made on arbitrary finite types.

## Main definitions

* `Cslib.PCP.ConstraintGraph.PreprocessExpanders`: specified cloud and half-edge rotations with
  a common spectral bound.
* `Cslib.PCP.ConstraintGraph.preprocessWith`: preprocessing with these specified rotations.
* `Cslib.PCP.ConstraintGraph.PreprocessLabel`: the labels of the darts of a preprocessed graph.
* `Cslib.PCP.ConstraintGraph.degreeReduceExpander`: degree reduction with the expanders of a family
  on the clouds.
* `Cslib.PCP.ConstraintGraph.preprocess`: the preprocessed regular constraint graph.

## Main results

* `Cslib.PCP.ConstraintGraph.spectralExpansion_preprocess_le`: it is an expander.
* `Cslib.PCP.ConstraintGraph.neighbor_preprocess_inr`: it has a self-loop at every vertex.
* `Cslib.PCP.ConstraintGraph.card_vertices_preprocess`,
  `Cslib.PCP.ConstraintGraph.card_label_preprocess`: it has `2 |E|` vertices and degree
  `2 |D| + 2`.
* `Cslib.PCP.ConstraintGraph.satisfiable_preprocess_iff`: it is satisfiable exactly when `G` is.
* `Cslib.PCP.ConstraintGraph.le_unsatVal_preprocess`,
  `Cslib.PCP.ConstraintGraph.unsatVal_preprocess_le`: its value is within a constant factor of
  that of `G`.
* `Cslib.PCP.ConstraintGraph.spectralExpansion_preprocess_expanderFamily_le`,
  `Cslib.PCP.ConstraintGraph.le_unsatVal_preprocess_expanderFamily`: the constants for the
  non-explicit family of expanders.
* `Cslib.PCP.ConstraintGraph.unsatVal_preprocessWith`,
  `Cslib.PCP.ConstraintGraph.unsatVal_preprocessWith_le`: for any specified rotations, the value
  is exactly half that of the degree-reduced graph, and at most that of `G`.
* `Cslib.PCP.ConstraintGraph.preprocessWith_ofFamily`: rotations from a family recover
  `preprocess`.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

universe u

namespace Cslib.PCP

namespace ConstraintGraph

open RotationMap

/-- The labels of the darts of a constraint graph preprocessed with a family of `D`-regular
expanders: the edge-link and the cloud-links of degree reduction, the edges of the expander on the
half-edges, and a self-loop. -/
abbrev PreprocessLabel (D : Type*) : Type _ :=
  ((Unit ⊕ D) ⊕ D) ⊕ Unit

/- The instances on `PreprocessLabel D` are declared on it, rather than found on the sums it
unfolds to, so that the instances on the alphabet `WalkLabels (PreprocessLabel D) T → α` of a
powered graph stay below the size limit of instance synthesis. -/

instance PreprocessLabel.instDecidableEq {D : Type*} [DecidableEq D] :
    DecidableEq (PreprocessLabel D) :=
  inferInstanceAs (DecidableEq (((Unit ⊕ D) ⊕ D) ⊕ Unit))

instance PreprocessLabel.instFintype {D : Type*} [Fintype D] : Fintype (PreprocessLabel D) :=
  inferInstanceAs (Fintype (((Unit ⊕ D) ⊕ D) ⊕ Unit))

/-- A constraint graph preprocessed with a family of `D`-regular expanders has degree
`2 |D| + 2`. -/
theorem card_label_preprocess (D : Type*) [Fintype D] :
    Fintype.card (PreprocessLabel D) = 2 * Fintype.card D + 2 := by
  simp only [PreprocessLabel, Fintype.card_sum, Fintype.card_unit]
  ring

section SpecifiedRotations

variable {V : Type*} {E : Type u} {α : Type*} [Fintype E] [DecidableEq V]
  (G : ConstraintGraph V E α)

/-- The actual cloud and half-edge rotations used in preprocessing. The degree is
`Fintype.card D`; a caller can reuse a fixed spectral bound as the input graph varies. -/
structure PreprocessExpanders (D : Type*) [Fintype D] (μ : ℝ) where
  /-- The expander on each cloud. -/
  cloud (v : V) : RotationMap (G.Cloud v) D
  /-- The expander on all half-edges. -/
  whole : RotationMap (E × Bool) D
  /-- Every cloud has the required spectral bound. -/
  spectralExpansion_cloud_le (v : V) : (cloud v).spectralExpansion ≤ μ
  /-- The whole half-edge graph has the same bound. -/
  spectralExpansion_whole_le : whole.spectralExpansion ≤ μ

variable {D : Type*} [Fintype D] {μ : ℝ}

/-- A family on arbitrary finite types supplies a preprocessing contract. Executable clients may
instead use their own numberings when providing the two rotations. -/
def PreprocessExpanders.ofFamily (X : ExpanderFamily.{u} D μ) : G.PreprocessExpanders D μ where
  cloud v := X.graph (G.Cloud v)
  whole := X.graph (E × Bool)
  spectralExpansion_cloud_le v := X.spectralExpansion_graph_le (G.Cloud v)
  spectralExpansion_whole_le := X.spectralExpansion_graph_le (E × Bool)

variable (X : G.PreprocessExpanders D μ)

/-- Preprocess using the supplied rotations, retaining their actual vertex numberings. -/
def preprocessWith : RegularConstraintGraph (E × Bool) (PreprocessLabel D) α :=
  ((G.degreeReduce X.cloud).addTrivial X.whole).addLoops Unit

/-- The final added label gives a self-loop at every half-edge. -/
@[simp]
theorem neighbor_preprocessWith_inr (p : E × Bool) (i : Unit) :
    (G.preprocessWith X).graph.neighbor p (.inr i) = p :=
  rfl

/-- The supplied whole graph provides a uniform spectral bound after preprocessing. -/
theorem spectralExpansion_preprocessWith_le :
    (G.preprocessWith X).graph.spectralExpansion ≤
      1 - (1 - μ) * Fintype.card D / (2 * Fintype.card D + 2) := by
  set R := (G.degreeReduce X.cloud).graph
  have h₁ := R.spectralExpansion_le_one
  have h₂ := X.spectralExpansion_whole_le
  have h₃ := R.spectralExpansion_union_le X.whole
  have h₄ := (R.union X.whole).spectralExpansion_addLoops_le (E := Unit)
  change ((R.union X.whole).addLoops Unit).spectralExpansion ≤ _
  generalize ((R.union X.whole).addLoops Unit).spectralExpansion = x₄ at h₄ ⊢
  generalize (R.union X.whole).spectralExpansion = x₃ at h₃ h₄
  generalize R.spectralExpansion = x₁ at h₁ h₃
  generalize X.whole.spectralExpansion = x₂ at h₂ h₃
  simp only [Fintype.card_sum, Fintype.card_unit] at h₃ h₄
  push_cast at h₃ h₄
  have hd : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
  generalize (Fintype.card D : ℝ) = d at hd h₃ h₄ ⊢
  rw [le_div_iff₀ (by positivity)] at h₃ h₄
  rw [show 1 - (1 - μ) * d / (2 * d + 2) = (2 + d + d * μ) / (2 * d + 2) by field_simp; ring,
    le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h₁ (by positivity : (0 : ℝ) ≤ 1 + d),
    mul_le_mul_of_nonneg_left h₂ hd]

/-- Expanderization and self-loops divide the degree-reduced value by exactly two. -/
theorem unsatVal_preprocessWith :
    (G.preprocessWith X).toConstraintGraph.unsatVal =
      (G.degreeReduce X.cloud).toConstraintGraph.unsatVal / 2 := by
  rw [preprocessWith, RegularConstraintGraph.unsatVal_addLoops,
    RegularConstraintGraph.unsatVal_addTrivial]
  simp only [Fintype.card_sum, Fintype.card_unit]
  have h₁ : (1 + Fintype.card D + Fintype.card D : ℝ) ≠ 0 := by positivity
  have h₂ : (1 + Fintype.card D + Fintype.card D + 1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

variable [Nonempty α]

/-- Cloud expansion preserves satisfiability through preprocessing. -/
theorem satisfiable_preprocessWith_iff [Nonempty D] (hμ : μ < 1) :
    (G.preprocessWith X).toConstraintGraph.Satisfiable ↔ G.Satisfiable := by
  rw [preprocessWith, RegularConstraintGraph.satisfiable_addLoops_iff,
    RegularConstraintGraph.satisfiable_addTrivial_iff]
  exact G.satisfiable_degreeReduce_iff X.cloud hμ X.spectralExpansion_cloud_le

/-- Soundness depends only on the degree and the common spectral bound, not on the numbering. -/
theorem le_unsatVal_preprocessWith :
    min 1 ((1 - μ) * Fintype.card D) / (4 * (1 + Fintype.card D)) * G.unsatVal ≤
      (G.preprocessWith X).toConstraintGraph.unsatVal := by
  have h := G.le_unsatVal_degreeReduce X.cloud X.spectralExpansion_cloud_le
  rw [unsatVal_preprocessWith]
  calc min 1 ((1 - μ) * Fintype.card D) / (4 * (1 + Fintype.card D)) * G.unsatVal
      = min 1 ((1 - μ) * Fintype.card D) / (2 * (1 + Fintype.card D)) * G.unsatVal / 2 := by
        have : (0 : ℝ) < 1 + Fintype.card D := by positivity
        field_simp
        ring
    _ ≤ _ := by gcongr

/-- Preprocessing does not increase the value. -/
theorem unsatVal_preprocessWith_le :
    (G.preprocessWith X).toConstraintGraph.unsatVal ≤ G.unsatVal := by
  have h := G.one_add_card_mul_unsatVal_degreeReduce_le X.cloud
  have h₀ := (G.degreeReduce X.cloud).toConstraintGraph.unsatVal_nonneg
  have hD : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
  rw [unsatVal_preprocessWith]
  nlinarith

end SpecifiedRotations

variable {V : Type*} {E : Type u} {α D : Type*} [Fintype E] [DecidableEq V] [Fintype D]
  (G : ConstraintGraph V E α) {μ : ℝ} (X : ExpanderFamily.{u} D μ)

/-- The degree reduction of `G` with the expanders of the family `X` on the clouds. -/
abbrev degreeReduceExpander : RegularConstraintGraph (E × Bool) (Unit ⊕ D) α :=
  G.degreeReduce fun v ↦ X.graph (G.Cloud v)

/-- **Preprocessing** [Dinur, Section 3.1][Dinur2005] with the family of expanders `X`: degree
reduction on the clouds, then the whole half-edge expander and self-loops. -/
def preprocess : RegularConstraintGraph (E × Bool) (PreprocessLabel D) α :=
  G.preprocessWith (.ofFamily G X)

/-- Supplying a family to the explicit-rotation interface recovers family-based preprocessing. -/
theorem preprocessWith_ofFamily : G.preprocessWith (.ofFamily G X) = G.preprocess X :=
  rfl

/-- The preprocessed constraint graph has `2 |E|` vertices. -/
theorem card_vertices_preprocess : Fintype.card (E × Bool) = 2 * Fintype.card E := by
  rw [Fintype.card_prod, Fintype.card_bool, mul_comm]

/-- **The preprocessed constraint graph has a self-loop at every vertex.** -/
@[simp]
theorem neighbor_preprocess_inr (p : E × Bool) (i : Unit) :
    (G.preprocess X).graph.neighbor p (.inr i) = p :=
  rfl

/-- **The preprocessed constraint graph is an expander**, with a bound depending only on the
family's degree and spectral expansion. -/
theorem spectralExpansion_preprocess_le :
    (G.preprocess X).graph.spectralExpansion ≤
      1 - (1 - μ) * Fintype.card D / (2 * Fintype.card D + 2) :=
  G.spectralExpansion_preprocessWith_le (.ofFamily G X)

/-- Expanderization and self-loops halve the value of the degree-reduced constraint graph. -/
theorem unsatVal_preprocess :
    (G.preprocess X).toConstraintGraph.unsatVal =
      (G.degreeReduceExpander X).toConstraintGraph.unsatVal / 2 :=
  G.unsatVal_preprocessWith (.ofFamily G X)

section Value

variable [Nonempty α]

/-- **Preprocessing preserves satisfiability** for a positive expander degree and a spectral bound
below one. -/
theorem satisfiable_preprocess_iff [Nonempty D] (hμ : μ < 1) :
    (G.preprocess X).toConstraintGraph.Satisfiable ↔ G.Satisfiable :=
  G.satisfiable_preprocessWith_iff (.ofFamily G X) hμ

/-- **Soundness of preprocessing** [Dinur, Section 3.1][Dinur2005]: the retained fraction depends
only on the family's degree and spectral bound, whatever the alphabet. -/
theorem le_unsatVal_preprocess :
    min 1 ((1 - μ) * Fintype.card D) / (4 * (1 + Fintype.card D)) * G.unsatVal ≤
      (G.preprocess X).toConstraintGraph.unsatVal :=
  G.le_unsatVal_preprocessWith (.ofFamily G X)

/-- **Completeness of preprocessing**: preprocessing does not increase the value. -/
theorem unsatVal_preprocess_le :
    (G.preprocess X).toConstraintGraph.unsatVal ≤ G.unsatVal :=
  G.unsatVal_preprocessWith_le (.ofFamily G X)

end Value

/-! ### The non-explicit family of expanders -/

/-- **The preprocessed constraint graph is an expander**: with the non-explicit family
`expanderFamily` of `120`-regular expanders, its spectral expansion is at most `1 - 1 / 726000`. -/
theorem spectralExpansion_preprocess_expanderFamily_le :
    (G.preprocess expanderFamily).graph.spectralExpansion ≤ 1 - 1 / 726000 := by
  refine (G.spectralExpansion_preprocess_le expanderFamily).trans_eq ?_
  rw [Fintype.card_fin]
  norm_num

/-- **Soundness of preprocessing** [Dinur, Section 3.1][Dinur2005]: with the non-explicit family
`expanderFamily` of `120`-regular expanders, preprocessing divides the value by at most `1452000`,
whatever the alphabet. -/
theorem le_unsatVal_preprocess_expanderFamily [Nonempty α] :
    G.unsatVal / 1452000 ≤ (G.preprocess expanderFamily).toConstraintGraph.unsatVal := by
  refine le_of_eq_of_le ?_ (G.le_unsatVal_preprocess expanderFamily)
  rw [Fintype.card_fin, min_eq_right (by norm_num)]
  ring

end ConstraintGraph

end Cslib.PCP
