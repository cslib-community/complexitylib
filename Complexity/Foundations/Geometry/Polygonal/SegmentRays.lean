/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Polygonal.RayParityColors

/-!
# Distinct endpoint rays of an interior-disjoint segment arrangement

Actual nondegenerate segments with disjoint interiors have distinct outgoing rays at
each common endpoint. The proof retains the indexed occurrences and both segment ends.
-/

public section

namespace Cslib.Polygonal

/-- Moving along either outgoing end vector is the actual affine segment parameter,
with the second end reversing the parameter. -/
theorem rayEndpoint_add_smul_endVector {ι : Type*} (a b : ι → ℂ)
    (e : ι × Bool) (t : ℝ) :
    rayEndpoint a b e + t • rayEndVector a b e =
      AffineMap.lineMap (a e.1) (b e.1) (if e.2 then 1 - t else t) := by
  rcases e with ⟨i, tag⟩
  cases tag <;> simp only [rayEndpoint, rayEndVector, Bool.false_eq_true, ↓reduceIte,
    AffineMap.lineMap_apply_module'] <;> module

/-- Nondegenerate segments have nonzero vectors at both indexed ends. -/
theorem rayEndVector_ne_zero {ι : Type*} (a b : ι → ℂ)
    (hab : ∀ i, a i ≠ b i) (e : ι × Bool) : rayEndVector a b e ≠ 0 := by
  rcases e with ⟨i, tag⟩
  cases tag <;> simp only [rayEndVector, Bool.false_eq_true, ↓reduceIte, sub_ne_zero]
  · exact (hab i).symm
  · exact hab i

/-- Interior disjointness forces distinct indexed outgoing rays at a common endpoint.
Equal rays would give an actual common point at positive parameters less than one third. -/
theorem rayEndVector_injective_of_interior_disjoint {ι : Type*}
    (a b : ι → ℂ) (hab : ∀ i, a i ≠ b i)
    (hdisjoint : ∀ i j, j ≠ i → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      AffineMap.lineMap (a i) (b i) t ∉ segment ℝ (a j) (b j))
    (k e : ι × Bool) (hp : rayEndpoint a b e = rayEndpoint a b k)
    (harg : turnArg (rayEndVector a b e) = turnArg (rayEndVector a b k)) : e = k := by
  have harg' : (rayEndVector a b e).arg = (rayEndVector a b k).arg :=
    Complex.arg_coe_angle_eq_iff.mp (by
      simpa only [turnArg_coe_angle] using congrArg (fun t : ℝ => (t : Real.Angle)) harg)
  obtain ⟨s, hs, t, ht, hst⟩ := exists_small_smul_eq_of_arg_eq
    (rayEndVector_ne_zero a b hab e) (rayEndVector_ne_zero a b hab k) harg'
    (by norm_num : (0 : ℝ) < 1 / 3)
  have hparam (tag : Bool) {u : ℝ} (hu : u ∈ Set.Ioo 0 (1 / 3)) :
      (if tag then 1 - u else u) ∈ Set.Ioo (0 : ℝ) 1 := by
    cases tag <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [hu.1, hu.2]
  have hpoint : AffineMap.lineMap (a e.1) (b e.1) (if e.2 then 1 - s else s) =
      AffineMap.lineMap (a k.1) (b k.1) (if k.2 then 1 - t else t) := by
    rw [← rayEndpoint_add_smul_endVector, ← rayEndpoint_add_smul_endVector, hp, hst]
  have hindex : e.1 = k.1 := by
    by_contra hne
    apply hdisjoint e.1 k.1 (Ne.symm hne) _ (hparam e.2 hs)
    rw [hpoint]
    exact lineMap_mem_segment ℝ _ _ ⟨(hparam k.2 ht).1.le, (hparam k.2 ht).2.le⟩
  rcases e with ⟨i, tag⟩
  rcases k with ⟨j, other⟩
  change i = j at hindex
  subst j
  have htime := AffineMap.lineMap_injective ℝ (hab i) hpoint
  cases tag <;> cases other <;> simp only [Bool.false_eq_true, ↓reduceIte] at htime
  · rfl
  · exfalso
    linarith [hs.2, ht.2]
  · exfalso
    linarith [hs.2, ht.2]
  · rfl

end Cslib.Polygonal
