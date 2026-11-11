/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Foundations.Geometry.Polyhedra

/-!
# Tests for compact polyhedra, triangulations, PL maps, and PQ maps

Exercises the core API of `CslibFrontier.Foundations.Geometry.Polyhedra`:
* concrete polytopes, H-polytope equivalence, and faces on `[0, 1]` and `[0, 1]^2`;
* common refinement of two distinct diagonal triangulations of `[0, 1]^2` and triangulation of
  a nonconvex L-shaped polyhedron compatible with its subpolyhedra;
* piecewise-linear (PL) closure rules (`min`, `max`, `abs`, `comp`, `image_isPolyhedron`,
  `preimage_inter_isPolyhedron`) on a concrete tent function, plus a negative test showing a
  discontinuous step function is not PL;
* piecewise-quadratic (PQ) closure rules (`mul_of_isPLOn`, `comp_isPLOn`) and finite degree-`≤ 2`
  `MvPolynomial` cell-list decomposition, plus a negative test showing `x ↦ x^3` is not quadratic;
* `#print axioms` guards on headline theorems.
-/

namespace CslibFrontierTests.Polyhedra

open Set Cslib.Polyhedra

/-! ### Concrete polytopes, H-polytope equivalence, and faces -/

private noncomputable def pairToVec : ℝ × ℝ →ᵃ[ℝ] (Fin 2 → ℝ) where
  toFun p := ![p.1, p.2]
  linear :=
    { toFun := fun p => ![p.1, p.2]
      map_add' := fun p q => by ext i; fin_cases i <;> rfl
      map_smul' := fun c p => by ext i; fin_cases i <;> rfl }
  map_vadd' p v := by ext i; fin_cases i <;> rfl

private noncomputable def scalarToVec1 : ℝ →ᵃ[ℝ] (Fin 1 → ℝ) where
  toFun t := fun _ => t
  linear :=
    { toFun := fun t _ => t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_vadd' _ _ := rfl

private noncomputable def coord0 (d : ℕ) [NeZero d] : (Fin d → ℝ) →ᵃ[ℝ] ℝ :=
  (LinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) 0).toAffineMap

private noncomputable def coord2 (i : Fin 2) : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ :=
  (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).toAffineMap

private theorem isPolytope_Icc (a b : ℝ) (hab : a ≤ b) : IsPolytope (Icc a b) := by
  have hconv : convexHull ℝ ({a, b} : Set ℝ) = Icc a b := by
    rw [convexHull_pair, segment_eq_Icc hab]
  rw [← hconv]
  exact isPolytope_convexHull (Set.Finite.insert a (Set.finite_singleton b))

private def unitInterval1 : Set (Fin 1 → ℝ) :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ 1}

private theorem isPolytope_unitInterval1 : IsPolytope unitInterval1 := by
  have himg : scalarToVec1 '' Icc (0 : ℝ) 1 = unitInterval1 := by
    ext x
    simp only [Set.mem_image, Set.mem_Icc, unitInterval1, Set.mem_ofPred_eq, scalarToVec1,
      AffineMap.coe_mk]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      refine ⟨x 0, hx, ?_⟩
      ext i
      fin_cases i
      rfl
  rw [← himg]
  exact (isPolytope_Icc 0 1 zero_le_one).image scalarToVec1

private def rect2 (a₁ b₁ a₂ b₂ : ℝ) : Set (Fin 2 → ℝ) :=
  {x | (a₁ ≤ x 0 ∧ x 0 ≤ b₁) ∧ (a₂ ≤ x 1 ∧ x 1 ≤ b₂)}

private theorem isPolytope_rect2 {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    IsPolytope (rect2 a₁ b₁ a₂ b₂) := by
  have himg : pairToVec '' (Icc a₁ b₁ ×ˢ Icc a₂ b₂) = rect2 a₁ b₁ a₂ b₂ := by
    ext x
    simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc, rect2, Set.mem_ofPred_eq, pairToVec,
      AffineMap.coe_mk, Prod.exists]
    constructor
    · rintro ⟨u, v, ⟨hu, hv⟩, rfl⟩
      exact ⟨hu, hv⟩
    · intro hx
      refine ⟨x 0, x 1, hx, ?_⟩
      ext i
      fin_cases i <;> rfl
  rw [← himg]
  exact ((isPolytope_Icc a₁ b₁ h₁).prod (isPolytope_Icc a₂ b₂ h₂)).image pairToVec

private def unitSquare2 : Set (Fin 2 → ℝ) := rect2 0 1 0 1

example : IsPolytope unitSquare2 ∧ IsHPolytope unitSquare2 := by
  have hP : IsPolytope unitSquare2 := isPolytope_rect2 zero_le_one zero_le_one
  exact ⟨hP, isPolytope_iff_isHPolytope.1 hP⟩

private def stdSimplex2 : Set (Fin 2 → ℝ) :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

example : IsHPolytope stdSimplex2 ∧ IsPolytope stdSimplex2 := by
  have hsub : stdSimplex2 ⊆ unitSquare2 := fun x ⟨hx0, hx1, hsum⟩ =>
    ⟨⟨hx0, by linarith⟩, ⟨hx1, by linarith⟩⟩
  have hbd : Bornology.IsBounded stdSimplex2 :=
    (isPolytope_rect2 zero_le_one zero_le_one).isBounded.subset hsub
  let ℓ₀ : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ := -coord2 0
  let ℓ₁ : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ := -coord2 1
  let ℓ₂ : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ :=
    coord2 0 + coord2 1 - AffineMap.const ℝ (Fin 2 → ℝ) 1
  have hH : IsHPolytope stdSimplex2 := by
    refine ⟨hbd, {ℓ₀, ℓ₁, ℓ₂},
      Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _)), ?_⟩
    ext x
    simp only [stdSimplex2, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq, ℓ₀, ℓ₁, ℓ₂, coord2, AffineMap.coe_neg,
      AffineMap.coe_sub, AffineMap.coe_add, AffineMap.coe_const, LinearMap.coe_toAffineMap,
      LinearMap.proj_apply, Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Function.const_apply,
      neg_nonpos, sub_nonpos]
  exact ⟨hH, isPolytope_iff_isHPolytope.2 hH⟩

/-! ### Common refinement of diagonal triangulations and nonconvex L-shape -/

private lemma vec2_eq_iff (x y : Fin 2 → ℝ) : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 :=
  funext_iff.trans Fin.forall_fin_two

private lemma vec2_ne {a b c d : ℝ} (h : a ≠ c ∨ b ≠ d) : (![a, b] : Fin 2 → ℝ) ≠ ![c, d] := by
  intro heq
  rcases h with hac | hbd
  · exact hac (congr_fun heq 0)
  · exact hbd (congr_fun heq 1)

private theorem mem_convexHull_triple_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    {a b c x : E} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    x ∈ convexHull ℝ ({a, b, c} : Set E) ↔
      ∃ u v w : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ u + v + w = 1 ∧
        u • a + v • b + w • c = x := by
  classical
  constructor
  · intro hx
    rw [← Finset.coe_singleton c, ← Finset.coe_insert b, ← Finset.coe_insert a] at hx
    rcases Finset.mem_convexHull.1 hx with ⟨w, hw0, hw1, hsum⟩
    have ha_not : a ∉ ({b, c} : Finset E) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, hac⟩
    have hb_not : b ∉ ({c} : Finset E) := Finset.notMem_singleton.2 hbc
    have hwsum : w a + w b + w c = 1 := by
      rw [Finset.sum_insert ha_not, Finset.sum_insert hb_not, Finset.sum_singleton] at hw1
      linarith
    refine ⟨w a, w b, w c, hw0 a (by simp), hw0 b (by simp), hw0 c (by simp), hwsum, ?_⟩
    simp only [Finset.centerMass, hw1, inv_one, one_smul, Finset.sum_insert ha_not,
      Finset.sum_insert hb_not, Finset.sum_singleton, id_eq] at hsum
    simpa only [add_assoc] using hsum
  · rintro ⟨u, v, w, hu, hv, hw, hsum, rfl⟩
    have ha : a ∈ convexHull ℝ ({a, b, c} : Set E) := subset_convexHull ℝ _ (by simp)
    have hb : b ∈ convexHull ℝ ({a, b, c} : Set E) := subset_convexHull ℝ _ (by simp)
    have hc : c ∈ convexHull ℝ ({a, b, c} : Set E) := subset_convexHull ℝ _ (by simp)
    have hconv := convex_convexHull ℝ ({a, b, c} : Set E)
    by_cases huv : u + v = 0
    · have hu0 : u = 0 := by linarith
      have hv0 : v = 0 := by linarith
      have hw1 : w = 1 := by linarith
      simpa [hu0, hv0, hw1] using hc
    · have huvpos : 0 < u + v := lt_of_le_of_ne (add_nonneg hu hv) (Ne.symm huv)
      have habm : ((u / (u + v)) • a + (v / (u + v)) • b) ∈
          convexHull ℝ ({a, b, c} : Set E) :=
        hconv ha hb (div_nonneg hu huvpos.le) (div_nonneg hv huvpos.le) (by field_simp)
      have htot := hconv habm hc huvpos.le hw (by linarith)
      have hEq : (u + v) • ((u / (u + v)) • a + (v / (u + v)) • b) + w • c =
          u • a + v • b + w • c := by
        rw [smul_add, smul_smul, smul_smul]
        have hu' : (u + v) * (u / (u + v)) = u := by field_simp
        have hv' : (u + v) * (v / (u + v)) = v := by field_simp
        rw [hu', hv']
      rwa [hEq] at htot

private def triLower1 : Set (Fin 2 → ℝ) :=
  convexHull ℝ ({![0, 0], ![1, 0], ![1, 1]} : Set (Fin 2 → ℝ))

private def triUpper1 : Set (Fin 2 → ℝ) :=
  convexHull ℝ ({![0, 0], ![0, 1], ![1, 1]} : Set (Fin 2 → ℝ))

private def triLower2 : Set (Fin 2 → ℝ) :=
  convexHull ℝ ({![0, 0], ![1, 0], ![0, 1]} : Set (Fin 2 → ℝ))

private def triUpper2 : Set (Fin 2 → ℝ) :=
  convexHull ℝ ({![1, 0], ![0, 1], ![1, 1]} : Set (Fin 2 → ℝ))

private theorem diag1_union : triLower1 ∪ triUpper1 = unitSquare2 := by
  ext x
  have hL : triLower1 = {y | ∃ u v w : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ u + v + w = 1 ∧
      u • ![0, 0] + v • ![1, 0] + w • ![1, 1] = y} := by
    ext y
    exact mem_convexHull_triple_iff (vec2_ne (Or.inl (by norm_num)))
      (vec2_ne (Or.inl (by norm_num))) (vec2_ne (Or.inr (by norm_num)))
  have hU : triUpper1 = {y | ∃ u v w : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ u + v + w = 1 ∧
      u • ![0, 0] + v • ![0, 1] + w • ![1, 1] = y} := by
    ext y
    exact mem_convexHull_triple_iff (vec2_ne (Or.inr (by norm_num)))
      (vec2_ne (Or.inl (by norm_num))) (vec2_ne (Or.inl (by norm_num)))
  simp only [Set.mem_union, hL, hU, unitSquare2, rect2, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨u, v, w, hu, hv, hw, hsum, rfl⟩ | ⟨u, v, w, hu, hv, hw, hsum, rfl⟩)
    · constructor <;> constructor <;>
        (simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]; nlinarith)
    · constructor <;> constructor <;>
        (simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]; nlinarith)
  · rintro ⟨⟨hx00, hx01⟩, ⟨hx10, hx11⟩⟩
    rcases le_total (x 1) (x 0) with hle | hle
    · refine Or.inl ⟨1 - x 0, x 0 - x 1, x 1, by linarith, by linarith, hx10, by ring, ?_⟩
      rw [vec2_eq_iff]
      constructor <;>
        (simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]; ring)
    · refine Or.inr ⟨1 - x 1, x 1 - x 0, x 0, by linarith, by linarith, hx00, by ring, ?_⟩
      rw [vec2_eq_iff]
      constructor <;>
        (simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]; ring)

private theorem diag2_union : triLower2 ∪ triUpper2 = unitSquare2 := by
  ext x
  have hL : triLower2 = {y | ∃ u v w : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ u + v + w = 1 ∧
      u • ![0, 0] + v • ![1, 0] + w • ![0, 1] = y} := by
    ext y
    exact mem_convexHull_triple_iff (vec2_ne (Or.inl (by norm_num)))
      (vec2_ne (Or.inr (by norm_num))) (vec2_ne (Or.inl (by norm_num)))
  have hU : triUpper2 = {y | ∃ u v w : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ u + v + w = 1 ∧
      u • ![1, 0] + v • ![0, 1] + w • ![1, 1] = y} := by
    ext y
    exact mem_convexHull_triple_iff (vec2_ne (Or.inl (by norm_num)))
      (vec2_ne (Or.inr (by norm_num))) (vec2_ne (Or.inl (by norm_num)))
  simp only [Set.mem_union, hL, hU, unitSquare2, rect2, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨u, v, w, hu, hv, hw, hsum, rfl⟩ | ⟨u, v, w, hu, hv, hw, hsum, rfl⟩)
    · constructor <;> constructor <;>
        (simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]; nlinarith)
    · constructor <;> constructor <;>
        (simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]; nlinarith)
  · rintro ⟨⟨hx00, hx01⟩, ⟨hx10, hx11⟩⟩
    rcases le_total (x 0 + x 1) 1 with hle | hle
    · refine Or.inl ⟨1 - x 0 - x 1, x 0, x 1, by linarith, hx00, hx10, by ring, ?_⟩
      rw [vec2_eq_iff]
      constructor <;>
        (simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]; ring)
    · refine Or.inr ⟨1 - x 1, 1 - x 0, x 0 + x 1 - 1,
        by linarith, by linarith, by linarith, by ring, ?_⟩
      rw [vec2_eq_iff]
      constructor <;>
        (simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]; ring)

example : IsPolytopeFace (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ({0} ×ˢ Icc (0 : ℝ) 1) := by
  have h01 : ({0} : Set ℝ) ⊆ Icc 0 1 := by
    rintro x rfl
    exact ⟨le_rfl, zero_le_one⟩
  have hface0 : IsPolytopeFace (Icc (0 : ℝ) 1) ({0} : Set ℝ) := by
    refine ⟨⟨h01, fun x hx y hy z hz hzseg => ?_⟩, convex_singleton 0⟩
    rcases hz with rfl
    rcases mem_openSegment_iff_div.1 hzseg with ⟨a, b, ha, hb, hsum⟩
    simp only [smul_eq_mul] at hsum
    have ha' : 0 < a / (a + b) := div_pos ha (add_pos ha hb)
    have hb' : 0 < b / (a + b) := div_pos hb (add_pos ha hb)
    have ha0 : 0 ≤ (a / (a + b)) * x := mul_nonneg ha'.le hx.1
    have hb0 : 0 ≤ (b / (a + b)) * y := mul_nonneg hb'.le hy.1
    have hax0 : (a / (a + b)) * x = 0 := by linarith
    exact Set.mem_singleton_iff.2 ((mul_eq_zero.1 hax0).resolve_left ha'.ne')
  exact hface0.prod (IsPolytopeFace.refl (convex_Icc 0 1))

example : ∃ K : Geometry.SimplicialComplex ℝ (Fin 2 → ℝ),
    K.faces.Finite ∧ K.space = unitSquare2 ∧
      ∀ s ∈ K.faces, (∃ R ∈ ({triLower1, triUpper1} : Set _), convexHull ℝ (s : Set _) ⊆ R) ∧
        (∃ R ∈ ({triLower2, triUpper2} : Set _), convexHull ℝ (s : Set _) ⊆ R) := by
  have h1fin : ({triLower1, triUpper1} : Set (Set (Fin 2 → ℝ))).Finite :=
    Set.Finite.insert _ (Set.finite_singleton _)
  have h2fin : ({triLower2, triUpper2} : Set (Set (Fin 2 → ℝ))).Finite :=
    Set.Finite.insert _ (Set.finite_singleton _)
  have h1poly : ∀ R ∈ ({triLower1, triUpper1} : Set (Set (Fin 2 → ℝ))), IsPolytope R := by
    rintro R (rfl | rfl) <;> exact isPolytope_convexHull (by simp)
  have h2poly : ∀ R ∈ ({triLower2, triUpper2} : Set (Set (Fin 2 → ℝ))), IsPolytope R := by
    rintro R (rfl | rfl) <;> exact isPolytope_convexHull (by simp)
  let C1 := PolytopalComplex.ofFinitePolytopes h1fin h1poly
  let C2 := PolytopalComplex.ofFinitePolytopes h2fin h2poly
  have hsp1 : C1.space = unitSquare2 := by
    rw [PolytopalComplex.space_ofFinitePolytopes, ← diag1_union]
    ext x
    simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop,
      exists_eq_or_imp, exists_eq_left, Set.mem_union]
  have hsp2 : C2.space = unitSquare2 := by
    rw [PolytopalComplex.space_ofFinitePolytopes, ← diag2_union]
    ext x
    simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop,
      exists_eq_or_imp, exists_eq_left, Set.mem_union]
  obtain ⟨K, hKfin, hKsp, href⟩ := exists_common_refinement C1 C2 (hsp1.trans hsp2.symm)
  refine ⟨K, hKfin, hKsp.trans hsp1, fun s hs => ?_⟩
  obtain ⟨⟨R1, hR1, hsub1⟩, ⟨R2, hR2, hsub2⟩⟩ := href s hs
  obtain ⟨Q1, hQ1, hRQ1⟩ := PolytopalComplex.ofFinitePolytopes_cell_subset h1fin h1poly hR1
  obtain ⟨Q2, hQ2, hRQ2⟩ := PolytopalComplex.ofFinitePolytopes_cell_subset h2fin h2poly hR2
  exact ⟨⟨Q1, hQ1, hsub1.trans hRQ1⟩, ⟨Q2, hQ2, hsub2.trans hRQ2⟩⟩

private def lShape : Set (Fin 2 → ℝ) := rect2 0 2 0 1 ∪ rect2 0 1 0 2

example : IsPolyhedron lShape ∧ ¬Convex ℝ lShape ∧
    ∃ K : Geometry.SimplicialComplex ℝ (Fin 2 → ℝ), K.faces.Finite ∧ K.space = lShape ∧
      (∀ b : Bool, ∃ Kᵢ : Geometry.SimplicialComplex ℝ (Fin 2 → ℝ),
        Kᵢ.faces = {s | s ∈ K.faces ∧ (s : Set (Fin 2 → ℝ)) ⊆
          bif b then rect2 0 2 0 1 else rect2 0 1 0 2} ∧
        Kᵢ.space = lShape ∩ (bif b then rect2 0 2 0 1 else rect2 0 1 0 2)) := by
  have hA : IsPolytope (rect2 0 2 0 1) := isPolytope_rect2 (by norm_num) zero_le_one
  have hB : IsPolytope (rect2 0 1 0 2) := isPolytope_rect2 zero_le_one (by norm_num)
  have hL : IsPolyhedron lShape := hA.isPolyhedron.union hB.isPolyhedron
  have hnconv : ¬Convex ℝ lShape := by
    intro hconv
    have hx : (![2, 1 / 2] : Fin 2 → ℝ) ∈ lShape := Or.inl (by
      simp only [rect2, Set.mem_ofPred_eq, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      norm_num)
    have hy : (![1 / 2, 2] : Fin 2 → ℝ) ∈ lShape := Or.inr (by
      simp only [rect2, Set.mem_ofPred_eq, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      norm_num)
    have hmid : ((1 / 2 : ℝ) • ![2, 1 / 2] + (1 / 2 : ℝ) • ![1 / 2, 2]) ∈ lShape :=
      hconv hx hy (by norm_num) (by norm_num) (by norm_num)
    rcases hmid with h1 | h2
    · have := h1.2.2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at this
      linarith
    · have := h2.1.2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue,
        Matrix.cons_val_zero] at this
      linarith
  obtain ⟨K, hKfin, hKsp, hcompat⟩ := exists_triangulation_compatible_with_subpolyhedra hL
    (Q := fun b : Bool => bif b then rect2 0 2 0 1 else rect2 0 1 0 2)
    (fun b => by cases b <;> [exact hB.isPolyhedron; exact hA.isPolyhedron])
  exact ⟨hL, hnconv, K, hKfin, hKsp, hcompat⟩

/-! ### Piecewise-linear closure rules and non-PL counterexample -/

private noncomputable def tent1 (x : Fin 1 → ℝ) : ℝ :=
  max 0 (min (2 * x 0) (2 - 2 * x 0))

private theorem isPLOn_tent1 : IsPLOn unitInterval1 tent1 := by
  have hP : IsPolyhedron unitInterval1 := isPolytope_unitInterval1.isPolyhedron
  have hc0 : IsPLOn unitInterval1 (fun _ : Fin 1 → ℝ => (0 : ℝ)) := IsPLOn.const hP 0
  have hc2 : IsPLOn unitInterval1 (fun _ : Fin 1 → ℝ => (2 : ℝ)) := IsPLOn.const hP 2
  have hx : IsPLOn unitInterval1 (coord0 1) := IsPLOn.affineMap hP (coord0 1)
  have h2x : IsPLOn unitInterval1 (fun x : Fin 1 → ℝ => 2 * x 0) :=
    (hx.smul 2).congr fun x _ => by simp [coord0, smul_eq_mul]
  have hsub : IsPLOn unitInterval1 (fun x : Fin 1 → ℝ => 2 - 2 * x 0) := hc2.sub h2x
  exact hc0.max (h2x.min hsub)

example : ContinuousOn tent1 unitInterval1 ∧
    IsPLOn unitInterval1 (fun x => |tent1 x - 1 / 2|) ∧
    IsPolyhedron (tent1 '' unitInterval1) := by
  have hP : IsPolyhedron unitInterval1 := isPolytope_unitInterval1.isPolyhedron
  have hc : IsPLOn unitInterval1 (fun _ : Fin 1 → ℝ => (1 / 2 : ℝ)) := IsPLOn.const hP (1 / 2)
  exact ⟨isPLOn_tent1.continuousOn, (isPLOn_tent1.sub hc).abs, isPLOn_tent1.image_isPolyhedron⟩

example : ¬IsPLOn unitInterval1 (fun x : Fin 1 → ℝ => if x 0 ≤ 1 / 2 then (0 : ℝ) else 1) := by
  intro hpl
  have hcont := hpl.continuousOn
  have hmid : (fun _ : Fin 1 => (1 / 2 : ℝ)) ∈ unitInterval1 := by
    simp only [unitInterval1, Set.mem_ofPred_eq]; norm_num
  rw [Metric.continuousOn_iff] at hcont
  obtain ⟨δ, hδ, hball⟩ := hcont _ hmid (1 / 2) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < min δ (1 / 4))
  let ε : ℝ := 1 / (n + 1 : ℝ)
  have hεpos : 0 < ε := by positivity
  have hεlt : ε < min δ (1 / 4) := by simpa [ε] using hn
  have hεδ : ε < δ := hεlt.trans_le (min_le_left _ _)
  have hεquarter : ε < 1 / 4 := hεlt.trans_le (min_le_right _ _)
  let y : Fin 1 → ℝ := fun _ => 1 / 2 + ε
  have hyP : y ∈ unitInterval1 := by
    simp only [unitInterval1, Set.mem_ofPred_eq, y]; constructor <;> linarith
  have hydist : dist y (fun _ : Fin 1 => (1 / 2 : ℝ)) < δ := by
    rw [dist_pi_lt_iff hδ]
    intro i
    fin_cases i
    simp only [y, Real.dist_eq]
    rw [show 1 / 2 + ε - 1 / 2 = ε by ring, abs_of_pos hεpos]
    exact hεδ
  have hval := hball y hyP hydist
  have hnotle : ¬y 0 ≤ 1 / 2 := by simp only [y]; linarith
  have hle : (1 / 2 : ℝ) ≤ 1 / 2 := le_rfl
  simp only [hnotle, hle, ↓reduceIte, Real.dist_eq, sub_zero, abs_one] at hval
  linarith

/-! ### Piecewise-quadratic closure rules, cell list, and non-quadratic counterexample -/

private noncomputable def reluProd2 (x : Fin 2 → ℝ) : ℝ :=
  max (x 0) 0 * max (x 1) 0

private def symSquare2 : Set (Fin 2 → ℝ) := rect2 (-1) 1 (-1) 1

private theorem isPQOn_reluProd2 : IsPQOn symSquare2 reluProd2 := by
  have hP : IsPolyhedron symSquare2 := (isPolytope_rect2 (by norm_num) (by norm_num)).isPolyhedron
  have hc0 : IsPLOn symSquare2 (fun _ : Fin 2 → ℝ => (0 : ℝ)) := IsPLOn.const hP 0
  have hx0 : IsPLOn symSquare2 (fun x : Fin 2 → ℝ => x 0) :=
    (IsPLOn.affineMap hP (coord2 0)).congr fun _ _ => rfl
  have hx1 : IsPLOn symSquare2 (fun x : Fin 2 → ℝ => x 1) :=
    (IsPLOn.affineMap hP (coord2 1)).congr fun _ _ => rfl
  exact IsPQOn.mul_of_isPLOn (hx0.max hc0) (hx1.max hc0)

example : ∃ L : List (Set (Fin 2 → ℝ) × MvPolynomial (Fin 2) ℝ),
    (∀ S p, (S, p) ∈ L → IsPolytope S ∧ p.totalDegree ≤ 2 ∧
      Set.EqOn reluProd2 (fun x => MvPolynomial.eval x p) S) ∧
    (⋃ S ∈ L.map Prod.fst, S) = symSquare2 :=
  isPQOn_reluProd2.exists_cell_list_mvPolynomial_pi

example : IsPQOn unitInterval1 (fun x : Fin 1 → ℝ => tent1 x * tent1 x) ∧
    IsPQOn unitInterval1 (fun x : Fin 1 → ℝ =>
      reluProd2 (fun i : Fin 2 => if i = 0 then tent1 x else 1 - tent1 x)) := by
  have hsq : IsPQOn unitInterval1 (fun x : Fin 1 → ℝ => tent1 x * tent1 x) :=
    IsPQOn.mul_of_isPLOn isPLOn_tent1 isPLOn_tent1
  have hP : IsPolyhedron unitInterval1 := isPolytope_unitInterval1.isPolyhedron
  let g : (Fin 1 → ℝ) → (Fin 2 → ℝ) := fun x => ![tent1 x, 1 - tent1 x]
  have hg : IsPLOn unitInterval1 g := by
    refine IsPLOn.pi hP fun i => ?_
    fin_cases i
    · exact isPLOn_tent1.congr fun x _ => rfl
    · exact ((IsPLOn.const hP 1).sub isPLOn_tent1).congr fun x _ => rfl
  have hmaps : MapsTo g unitInterval1 symSquare2 := by
    intro x hx
    have h0 : 0 ≤ tent1 x := le_max_left _ _
    have hle1 : tent1 x ≤ 1 := by
      simp only [tent1, max_le_iff, min_le_iff]
      refine ⟨by norm_num, ?_⟩
      by_cases h : x 0 ≤ 1 / 2
      · left; linarith
      · right; have := hx.2; linarith
    simp only [symSquare2, rect2, Set.mem_ofPred_eq, g, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    constructor <;> constructor <;> linarith
  exact ⟨hsq, isPQOn_reluProd2.comp_isPLOn hg hmaps⟩

example : ¬IsQuadraticOn (fun x : Fin 1 → ℝ => (x 0) ^ 3) unitInterval1 := by
  rintro ⟨n, a, b, h⟩
  let x₀ : Fin 1 → ℝ := fun _ => 0
  let x₁ : Fin 1 → ℝ := fun _ => 1 / 3
  let x₂ : Fin 1 → ℝ := fun _ => 2 / 3
  let x₃ : Fin 1 → ℝ := fun _ => 1
  have h₀ : x₀ ∈ unitInterval1 := by simp [x₀, unitInterval1]
  have h₁ : x₁ ∈ unitInterval1 := by simp only [x₁, unitInterval1, Set.mem_ofPred_eq]; norm_num
  have h₂ : x₂ ∈ unitInterval1 := by simp only [x₂, unitInterval1, Set.mem_ofPred_eq]; norm_num
  have h₃ : x₃ ∈ unitInterval1 := by simp [x₃, unitInterval1]
  have heq₀ := h h₀
  have heq₁ := h h₁
  have heq₂ := h h₂
  have heq₃ := h h₃
  have hdiff : ∀ i : Fin n,
      a i x₃ * b i x₃ - 3 * (a i x₂ * b i x₂) + 3 * (a i x₁ * b i x₁) - a i x₀ * b i x₀ = 0 := by
    intro i
    have ha1 : x₁ = (1 - (1 / 3 : ℝ)) • x₀ + (1 / 3 : ℝ) • x₃ := by
      ext j; fin_cases j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, x₀, x₁, x₃]; norm_num
    have ha2 : x₂ = (1 - (2 / 3 : ℝ)) • x₀ + (2 / 3 : ℝ) • x₃ := by
      ext j; fin_cases j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, x₀, x₂, x₃]; norm_num
    have ha_lin : ∀ c : ℝ, (a i) ((1 - c) • x₀ + c • x₃) =
        (1 - c) * a i x₀ + c * a i x₃ := by
      intro c
      have := (a i).apply_lineMap x₀ x₃ c
      simpa [AffineMap.lineMap_apply_module, smul_eq_mul] using this
    have hb_lin : ∀ c : ℝ, (b i) ((1 - c) • x₀ + c • x₃) =
        (1 - c) * b i x₀ + c * b i x₃ := by
      intro c
      have := (b i).apply_lineMap x₀ x₃ c
      simpa [AffineMap.lineMap_apply_module, smul_eq_mul] using this
    have ha1v : a i x₁ = (2 / 3 : ℝ) * a i x₀ + (1 / 3 : ℝ) * a i x₃ := by
      rw [ha1, ha_lin (1 / 3)]; ring
    have ha2v : a i x₂ = (1 / 3 : ℝ) * a i x₀ + (2 / 3 : ℝ) * a i x₃ := by
      rw [ha2, ha_lin (2 / 3)]; ring
    have hb1v : b i x₁ = (2 / 3 : ℝ) * b i x₀ + (1 / 3 : ℝ) * b i x₃ := by
      rw [ha1, hb_lin (1 / 3)]; ring
    have hb2v : b i x₂ = (1 / 3 : ℝ) * b i x₀ + (2 / 3 : ℝ) * b i x₃ := by
      rw [ha2, hb_lin (2 / 3)]; ring
    rw [ha1v, ha2v, hb1v, hb2v]
    ring
  have hsum_zero :
      (∑ i, a i x₃ * b i x₃) - 3 * (∑ i, a i x₂ * b i x₂) +
        3 * (∑ i, a i x₁ * b i x₁) - (∑ i, a i x₀ * b i x₀) = 0 := by
    calc (∑ i, a i x₃ * b i x₃) - 3 * (∑ i, a i x₂ * b i x₂) +
          3 * (∑ i, a i x₁ * b i x₁) - (∑ i, a i x₀ * b i x₀)
      _ = ∑ i, (a i x₃ * b i x₃ - 3 * (a i x₂ * b i x₂) +
          3 * (a i x₁ * b i x₁) - a i x₀ * b i x₀) := by
          simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = ∑ _ : Fin n, (0 : ℝ) := Finset.sum_congr rfl fun i _ => hdiff i
      _ = 0 := Finset.sum_const_zero
  dsimp only at heq₀ heq₁ heq₂ heq₃
  rw [← heq₀, ← heq₁, ← heq₂, ← heq₃] at hsum_zero
  simp only [x₀, x₁, x₂, x₃] at hsum_zero
  norm_num at hsum_zero

/-! ### Axiom guards -/

/--
info: 'Cslib.Polyhedra.isPolytope_iff_isHPolytope' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Polyhedra.isPolytope_iff_isHPolytope

/--
info: 'Cslib.Polyhedra.exists_common_refinement' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Polyhedra.exists_common_refinement

/--
info: 'Cslib.Polyhedra.exists_triangulation_compatible_with_subpolyhedra' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Polyhedra.exists_triangulation_compatible_with_subpolyhedra

/--
info: 'Cslib.Polyhedra.IsPLOn.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Polyhedra.IsPLOn.comp

/--
info: 'Cslib.Polyhedra.IsPQOn.mul_of_isPLOn' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Polyhedra.IsPQOn.mul_of_isPLOn

/--
info: 'Cslib.Polyhedra.IsPQOn.comp_isPLOn' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Polyhedra.IsPQOn.comp_isPLOn

/--
info: 'Cslib.Polyhedra.IsPQOn.exists_cell_list_mvPolynomial_pi' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Polyhedra.IsPQOn.exists_cell_list_mvPolynomial_pi

end CslibFrontierTests.Polyhedra
