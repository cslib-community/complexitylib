/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.MeasureTheory.Group.QuotientDensity
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Group.Measure

/-! Folding clients with trivial/nontrivial quotients, infinite densities, and Borel lattices. -/

open MeasureTheory QuotientAddGroup
open scoped ENNReal

noncomputable section

namespace CslibFrontierTests.QuotientDensity

private theorem bottomDomain {G : Type*} [AddGroup G] [MeasurableSpace G] (μ : Measure G) :
    IsAddFundamentalDomain (⊥ : AddSubgroup G).op Set.univ μ := by
  have : Subsingleton (⊥ : AddSubgroup G).op := by
    rw [AddSubgroup.op_bot]
    infer_instance
  apply IsAddFundamentalDomain.mk' MeasurableSet.univ.nullMeasurableSet
  intro x
  exact ⟨0, Set.mem_univ _, fun _ _ => Subsingleton.elim _ _⟩

private theorem topDomain {G : Type*} [AddGroup G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : Measure G) :
    IsAddFundamentalDomain (⊤ : AddSubgroup G).op {0} μ := by
  apply IsAddFundamentalDomain.mk' (measurableSet_singleton 0).nullMeasurableSet
  intro x
  refine ⟨⟨AddOpposite.op (-x), trivial⟩, ?_, ?_⟩
  · change x + -x = 0
    exact add_neg_cancel x
  · intro γ hγ
    apply Subtype.ext
    apply AddOpposite.unop_injective
    change x + AddOpposite.unop γ.val = 0 at hγ
    exact eq_neg_of_add_eq_zero_right hγ

-- The bottom subgroup leaves each density value unchanged.
example {f : ℤ → ℝ≥0∞} (x : ℤ) :
    automorphize (Γ := ⊥) f (mk x) = f x := by
  change (∑' γ : (⊥ : AddSubgroup ℤ).op, f (γ +ᵥ x)) = f x
  have : Subsingleton (⊥ : AddSubgroup ℤ).op := by
    rw [AddSubgroup.op_bot]
    infer_instance
  have : Unique (⊥ : AddSubgroup ℤ).op := uniqueOfSubsingleton 0
  simp [show (default : (⊥ : AddSubgroup ℤ).op) = 0 from Subsingleton.elim _ _]

example (f : ℤ → ℝ≥0∞) :
    (Measure.count.withDensity f).map (mk : ℤ → ℤ ⧸ (⊥ : AddSubgroup ℤ)) =
      (Measure.count.map (mk : ℤ → ℤ ⧸ (⊥ : AddSubgroup ℤ))).withDensity
        (automorphize f) := by
  simpa only [Measure.restrict_univ] using
    map_withDensity_eq_withDensity_automorphize (bottomDomain Measure.count)
      (measurable_of_countable f)

-- A nontrivial finite group folds both points into its single top-subgroup coset.
example (f : ZMod 2 → ℝ≥0∞) :
    (Measure.count.withDensity f).map (mk : ZMod 2 → ZMod 2 ⧸ (⊤ : AddSubgroup (ZMod 2))) =
      ((Measure.count.restrict {0}).map
        (mk : ZMod 2 → ZMod 2 ⧸ (⊤ : AddSubgroup (ZMod 2)))).withDensity
          (automorphize f) :=
  map_withDensity_eq_withDensity_automorphize (topDomain Measure.count) (measurable_of_countable f)

example (f : ZMod 2 → ℝ≥0∞) :
    automorphize (Γ := ⊤) f (mk 0) = ∑ z : ZMod 2, f z := by
  let e : (⊤ : AddSubgroup (ZMod 2)).op ≃ ZMod 2 :=
    (⊤ : AddSubgroup (ZMod 2)).equivOp.symm.trans AddSubgroup.topEquiv.toEquiv
  let : Fintype (⊤ : AddSubgroup (ZMod 2)).op := Fintype.ofEquiv (ZMod 2) e.symm
  change (∑' γ : (⊤ : AddSubgroup (ZMod 2)).op, f (γ +ᵥ (0 : ZMod 2))) = _
  rw [tsum_fintype]
  exact Fintype.sum_equiv e _ _ fun γ => congrArg f (zero_add _)

-- Infinite values are retained by folding; no conversion to real-valued densities is used.
example : automorphize (Γ := ⊤) (fun _ : ZMod 2 => (⊤ : ℝ≥0∞)) (mk 0) = ⊤ := by
  change (∑' γ : (⊤ : AddSubgroup (ZMod 2)).op, (⊤ : ℝ≥0∞)) = ⊤
  exact tsum_eq_top_of_eq_top ⟨0, rfl⟩

example : ((Measure.count : Measure (ZMod 2)).withDensity (fun _ => (⊤ : ℝ≥0∞))).map
    (mk : ZMod 2 → ZMod 2 ⧸ (⊤ : AddSubgroup (ZMod 2))) =
      (((Measure.count : Measure (ZMod 2)).restrict {0}).map
        (mk : ZMod 2 → ZMod 2 ⧸ (⊤ : AddSubgroup (ZMod 2)))).withDensity
          (automorphize (fun _ => (⊤ : ℝ≥0∞))) :=
  map_withDensity_eq_withDensity_automorphize (topDomain Measure.count) measurable_const

-- In particular, infinite density on a null measure folds to the null measure.
example : ((0 : Measure (ZMod 2)).withDensity (fun _ => (⊤ : ℝ≥0∞))).map
    (mk : ZMod 2 → ZMod 2 ⧸ (⊤ : AddSubgroup (ZMod 2))) = 0 := by
  rw [map_withDensity_eq_withDensity_automorphize (topDomain 0) measurable_const]
  simp

-- The canonical quotient measurable space is Borel on an actual closed lattice quotient.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] : BorelSpace (E ⧸ L.toAddSubgroup) := by
  infer_instance

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {f : E → ℝ≥0∞} (hf : Measurable f) :
    Measurable (automorphize (Γ := L.toAddSubgroup) f) := by
  have : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  exact measurable_automorphize hf

end CslibFrontierTests.QuotientDensity
