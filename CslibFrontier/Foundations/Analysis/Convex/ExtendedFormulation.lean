/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convex/ExtendedFormulation.lean`)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.NonnegRank
public import Mathlib.Analysis.Convex.Hull
import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Extended formulations and Yannakakis's factorization theorem

Let `K` be a linearly ordered field and `P ⊆ K ^ ι` a polytope described both by inequalities and
as a convex hull: `P = {x | A *ᵥ x ≤ b} = conv (range V)` for `A : Matrix μ ι K`, `b : μ → K` and
finitely many points `V : ν → ι → K`. Its *slack matrix* with respect to these descriptions is
`S i j = b i - A i ⬝ᵥ V j` (`Matrix.slackMatrix`), which is entrywise nonnegative
(`Matrix.slackMatrix_nonneg`).

An *extended formulation* (EF) of a set `P ⊆ K ^ ι` is a system of linear inequalities
`E *ᵥ x + F *ᵥ y ≤ g` and linear equations `E' *ᵥ x + F' *ᵥ y = g'` in the original variables `x`
and finitely many extra variables `y`, such that `x ∈ P` exactly when some `y` satisfies the system
(`IsExtendedFormulation`). Its size is the number of inequalities; equations are free. The
*extension complexity* `xc P` is the least size of an EF of `P`, or `⊤` if there is none
(`extensionComplexity`). These are definition (1) and item 3 of Section 3 of
[FioriniMassarPokuttaTiwaryDeWolf2015].

**Yannakakis's factorization theorem** [Yannakakis1991] says that the extension complexity of a
polytope is the nonnegative rank of its slack matrix: `xc P = rank₊ S`
(`extensionComplexity_eq_nonnegRank_slackMatrix`). We follow the statement and proof of
[FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 3], equivalence of (i) and (iii) (arXiv version
1111.0837v4), which assumes `dim P ≥ 1`; here this is `P.Nontrivial`.

* A nonnegative factorization `S = T * U` with inner dimension `r` gives the EF in slack form
  `A *ᵥ x + T *ᵥ y = b`, `y ≥ 0`, with `r` inequalities
  (`isExtendedFormulation_of_mul_eq_slackMatrix`), so `xc P ≤ rank₊ S`
  (`extensionComplexity_le_nonnegRank_slackMatrix`). This direction needs no hypothesis on the
  dimension.
* Conversely, every inequality valid on `P` is a nonnegative combination of the inequalities of an
  EF of `P` modulo its equations, up to a nonnegative constant
  (`IsExtendedFormulation.exists_nonneg_dotProduct_eq`, the affine Farkas lemma). When `P` is
  bounded and not a single point, the constant can be absorbed
  (`IsExtendedFormulation.exists_nonneg_dotProduct_eq_one`,
  `IsExtendedFormulation.exists_nonneg_dotProduct_eq_sub`;
  [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 2]). Applied to the rows of `A *ᵥ x ≤ b`, this
  factors `S` through the slacks of the EF's inequalities at lifts of the points `V j`
  (`IsExtendedFormulation.hasNonnegFactorization_slackMatrix`), so `rank₊ S ≤ xc P`.

Both conventions matter. Equations must be free: the segment `P = conv {0, e₀} ⊆ K ^ 2` has a
slack matrix of nonnegative rank `2` (an EF `x₁ = 0`, `0 ≤ x₀`, `x₀ ≤ 1`), but no system of only
two inequalities and no equations in `x` and extra variables projects onto a nonempty bounded
subset of `K ^ 2`. And the dimension hypothesis is needed for the equality in `ℕ∞`: for the point
`P = {0} ⊆ K` described by `x ≤ 0`, `-x ≤ 0` and the redundant `x ≤ 1`, the slack matrix has
nonnegative rank `1`, while the EF `x = 0` has no inequalities, so `xc P = 0`. FMPTW state the
equivalence for a positive number `r` of inequalities, and in that form it needs no dimension
hypothesis, since the slack matrix of a set with at most one point has nonnegative rank at most `1`
(`extensionComplexity_le_iff_nonnegRank_slackMatrix_le`); the point example fails only at `r = 0`.

## Main definitions

* `Matrix.slackMatrix`: the slack matrix of `A *ᵥ x ≤ b` with respect to points `V`.
* `IsExtendedFormulation`: a system of inequalities and equations in extra variables is an EF of
  `P`.
* `HasExtendedFormulation`: `P` has an EF with `r` inequalities.
* `extensionComplexity`: the least number of inequalities in an EF.

## Main results

* `extensionComplexity_eq_nonnegRank_slackMatrix`: **Yannakakis's factorization theorem**.
* `extensionComplexity_le_iff_nonnegRank_slackMatrix_le`: the same for a positive number of
  inequalities, with no dimension hypothesis (using `nonnegRank_slackMatrix_le_one`).
* `isExtendedFormulation_of_mul_eq_slackMatrix`,
  `extensionComplexity_le_nonnegRank_slackMatrix`: nonnegative factorizations give EFs.
* `IsExtendedFormulation.hasNonnegFactorization_slackMatrix`,
  `nonnegRank_slackMatrix_le_extensionComplexity`: EFs give nonnegative factorizations.
* `IsExtendedFormulation.exists_nonneg_dotProduct_eq`,
  `IsExtendedFormulation.exists_nonneg_dotProduct_eq_one`,
  `IsExtendedFormulation.exists_nonneg_dotProduct_eq_sub`: valid inequalities are derived from
  the inequalities of an EF.
* `IsExtendedFormulation.extensionComplexity_le`, `le_extensionComplexity_iff`: bounds on the
  extension complexity through EFs.
* `extensionComplexity_setOf_mulVec_le_le`, `extensionComplexity_le_card_points`: the trivial
  bounds by the number of inequalities and of points.

## References

* [FioriniMassarPokuttaTiwaryDeWolf2015], Sections 1 and 3.1
* [Yannakakis1991]
-/

public section

open Matrix

section Defs

variable {K : Type*} {ι μ ν σ κ τ : Type*}

/-- The **slack matrix** of the system `A *ᵥ x ≤ b` with respect to the points `V j`: the entry at
`i` and `j` is the slack `b i - A i ⬝ᵥ V j` of the `i`-th inequality at the `j`-th point
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3]. -/
def Matrix.slackMatrix [Ring K] [Fintype ι] (A : Matrix μ ι K) (b : μ → K)
    (V : ν → ι → K) : Matrix μ ν K :=
  of fun i j => b i - A i ⬝ᵥ V j

/-- The system `E *ᵥ x + F *ᵥ y ≤ g`, `E' *ᵥ x + F' *ᵥ y = g'` in the variables `x : ι → K` and the
extra variables `y : κ → K` is an **extended formulation** of `P`: `x ∈ P` exactly when some `y`
satisfies it [FioriniMassarPokuttaTiwaryDeWolf2015, definition (1)]. Its size is the number of
inequalities, the cardinality of `σ`. -/
@[expose] def IsExtendedFormulation [Semiring K] [PartialOrder K] [Fintype ι] [Fintype κ]
    (P : Set (ι → K)) (E : Matrix σ ι K) (F : Matrix σ κ K) (g : σ → K)
    (E' : Matrix τ ι K) (F' : Matrix τ κ K) (g' : τ → K) : Prop :=
  ∀ x, x ∈ P ↔ ∃ y, E *ᵥ x + F *ᵥ y ≤ g ∧ E' *ᵥ x + F' *ᵥ y = g'

/-- `P` has an extended formulation with `r` inequalities (and any finite numbers of extra
variables and equations). -/
@[expose] def HasExtendedFormulation [Semiring K] [PartialOrder K] [Fintype ι] (P : Set (ι → K))
    (r : ℕ) : Prop :=
  ∃ (d e : ℕ) (E : Matrix (Fin r) ι K) (F : Matrix (Fin r) (Fin d) K) (g : Fin r → K)
    (E' : Matrix (Fin e) ι K) (F' : Matrix (Fin e) (Fin d) K) (g' : Fin e → K),
    IsExtendedFormulation P E F g E' F' g'

/-- The **extension complexity** `xc P`: the least number of inequalities in an extended
formulation of `P`, or `⊤` if `P` has none [FioriniMassarPokuttaTiwaryDeWolf2015, Section 3]. -/
noncomputable def extensionComplexity [Semiring K] [PartialOrder K] [Fintype ι]
    (P : Set (ι → K)) : ℕ∞ :=
  ⨅ r : {r : ℕ // HasExtendedFormulation P r}, (r.1 : ℕ∞)

@[simp] theorem Matrix.slackMatrix_apply [Ring K] [Fintype ι] (A : Matrix μ ι K) (b : μ → K)
    (V : ν → ι → K) (i : μ) (j : ν) : A.slackMatrix b V i j = b i - A i ⬝ᵥ V j := by
  rw [Matrix.slackMatrix, of_apply]

/-- The slack matrix is nonnegative when the points satisfy the inequalities. -/
theorem Matrix.slackMatrix_nonneg [Ring K] [PartialOrder K] [IsOrderedAddMonoid K] [Fintype ι]
    {A : Matrix μ ι K} {b : μ → K} {V : ν → ι → K} (hV : ∀ j, A *ᵥ V j ≤ b) (i : μ) (j : ν) :
    0 ≤ A.slackMatrix b V i j :=
  sub_nonneg.2 (hV j i)

end Defs

section Semiring

variable {K : Type*} [Semiring K] [PartialOrder K]
variable {ι σ κ τ σ' κ' τ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ']
variable {P : Set (ι → K)} {E : Matrix σ ι K} {F : Matrix σ κ K} {g : σ → K}
  {E' : Matrix τ ι K} {F' : Matrix τ κ K} {g' : τ → K}

omit [PartialOrder K] in
private theorem submatrix_mulVec_add_submatrix_mulVec (e : σ ≃ σ') (eκ : κ ≃ κ')
    (E : Matrix σ ι K) (F : Matrix σ κ K) (x : ι → K) (y : κ → K) :
    E.submatrix e.symm id *ᵥ x + F.submatrix e.symm eκ.symm *ᵥ (y ∘ eκ.symm) =
      (E *ᵥ x + F *ᵥ y) ∘ e.symm := by
  rw [submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_assoc, eκ.symm_comp_self,
    Function.comp_id]
  rfl

/-- Renaming the inequalities, extra variables and equations of an extended formulation gives an
extended formulation. -/
theorem IsExtendedFormulation.reindex (h : IsExtendedFormulation P E F g E' F' g')
    (eσ : σ ≃ σ') (eκ : κ ≃ κ') (eτ : τ ≃ τ') :
    IsExtendedFormulation P (E.submatrix eσ.symm id) (F.submatrix eσ.symm eκ.symm) (g ∘ eσ.symm)
      (E'.submatrix eτ.symm id) (F'.submatrix eτ.symm eκ.symm) (g' ∘ eτ.symm) := by
  intro x
  rw [h x]
  refine (Equiv.arrowCongr eκ (Equiv.refl K)).exists_congr fun y => ?_
  have hy : Equiv.arrowCongr eκ (Equiv.refl K) y = y ∘ eκ.symm := rfl
  rw [hy, submatrix_mulVec_add_submatrix_mulVec, submatrix_mulVec_add_submatrix_mulVec]
  refine and_congr ⟨fun h i => h _, fun h i => by simpa using h (eσ i)⟩
    ⟨fun h => by rw [h], fun h => funext fun i => by simpa using congrFun h (eτ i)⟩

/-- An extended formulation with inequalities indexed by `σ` shows that `P` has one with
`|σ|` inequalities. -/
theorem IsExtendedFormulation.hasExtendedFormulation [Fintype σ] [Finite τ]
    (h : IsExtendedFormulation P E F g E' F' g') :
    HasExtendedFormulation P (Fintype.card σ) := by
  have := Fintype.ofFinite τ
  exact ⟨_, _, _, _, _, _, _, _, h.reindex (Fintype.equivFin σ) (Fintype.equivFin κ)
    (Fintype.equivFin τ)⟩

/-- An extended formulation with inequalities indexed by `σ` bounds the extension complexity by
`|σ|`. -/
theorem IsExtendedFormulation.extensionComplexity_le [Fintype σ] [Finite τ]
    (h : IsExtendedFormulation P E F g E' F' g') :
    extensionComplexity P ≤ Fintype.card σ :=
  iInf_le (fun r : {r : ℕ // HasExtendedFormulation P r} => (r.1 : ℕ∞))
    ⟨_, h.hasExtendedFormulation⟩

/-- Lower bounds on the extension complexity are lower bounds on the number of inequalities of
every extended formulation. -/
theorem le_extensionComplexity_iff {c : ℕ∞} :
    c ≤ extensionComplexity P ↔ ∀ r, HasExtendedFormulation P r → c ≤ r := by
  simp [extensionComplexity, le_iInf_iff, Subtype.forall]

/-- A polyhedron `{x | A *ᵥ x ≤ b}` is its own extended formulation, with no extra variables. -/
theorem isExtendedFormulation_setOf_mulVec_le {μ : Type*} (A : Matrix μ ι K) (b : μ → K) :
    IsExtendedFormulation {x | A *ᵥ x ≤ b} A (0 : Matrix μ (Fin 0) K) b
      (0 : Matrix (Fin 0) ι K) (0 : Matrix (Fin 0) (Fin 0) K) 0 := fun x =>
  ⟨fun hx => ⟨0, by simpa using hx, Subsingleton.elim _ _⟩, fun ⟨y, hy, _⟩ => by simpa using hy⟩

/-- The extension complexity of a polyhedron is at most its number of inequalities. -/
theorem extensionComplexity_setOf_mulVec_le_le {μ : Type*} [Fintype μ] (A : Matrix μ ι K)
    (b : μ → K) : extensionComplexity {x | A *ᵥ x ≤ b} ≤ Fintype.card μ :=
  (isExtendedFormulation_setOf_mulVec_le A b).extensionComplexity_le

end Semiring

section Field

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {ι μ ν σ κ τ ρ : Type*} [Fintype ι] [Fintype σ] [Fintype κ] [Finite τ]
variable {P : Set (ι → K)} {E : Matrix σ ι K} {F : Matrix σ κ K} {g : σ → K}
  {E' : Matrix τ ι K} {F' : Matrix τ κ K} {g' : τ → K}

/-- **Valid inequalities are derived from an extended formulation**, up to a constant: if
`c ⬝ᵥ x ≤ δ` on a nonempty set `P` with an extended formulation, then some nonnegative combination
`w` of the slacks `g - (E *ᵥ x + F *ᵥ y)` of its inequalities equals `δ' - c ⬝ᵥ x` with `δ' ≤ δ`,
whenever the equations hold. This is the affine Farkas lemma
(`Matrix.exists_dual_le_of_forall_le`) for the system in the variables `x` and `y`. -/
theorem IsExtendedFormulation.exists_nonneg_dotProduct_eq
    (hEF : IsExtendedFormulation P E F g E' F' g') (hne : P.Nonempty) (c : ι → K) (δ : K)
    (hc : ∀ x ∈ P, c ⬝ᵥ x ≤ δ) :
    ∃ w : σ → K, 0 ≤ w ∧ ∃ δ' ≤ δ, ∀ x y, E' *ᵥ x + F' *ᵥ y = g' →
      w ⬝ᵥ (g - (E *ᵥ x + F *ᵥ y)) = δ' - c ⬝ᵥ x := by
  classical
  have := Fintype.ofFinite τ
  set A' : Matrix (σ ⊕ (τ ⊕ τ)) (ι ⊕ κ) K := fromBlocks E F (fromRows E' (-E')) (fromRows F' (-F'))
  set b' : σ ⊕ (τ ⊕ τ) → K := Sum.elim g (Sum.elim g' (-g'))
  have hA' : ∀ x y, A' *ᵥ Sum.elim x y =
      Sum.elim (E *ᵥ x + F *ᵥ y) (Sum.elim (E' *ᵥ x + F' *ᵥ y) (-(E' *ᵥ x + F' *ᵥ y))) := by
    intro x y
    ext (i | i | i)
    · simp [A', fromBlocks_mulVec]
    · simp [A', fromBlocks_mulVec, fromRows_mulVec]
    · simp [A', fromBlocks_mulVec, fromRows_mulVec, neg_mulVec]; ring
  have hfeas : ∀ x y, A' *ᵥ Sum.elim x y ≤ b' ↔
      E *ᵥ x + F *ᵥ y ≤ g ∧ E' *ᵥ x + F' *ᵥ y = g' := by
    intro x y
    rw [hA', Sum.elim_le_elim_iff, Sum.elim_le_elim_iff, neg_le_neg_iff, ← le_antisymm_iff]
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨y₀, hy₀⟩ := (hEF x₀).1 hx₀
  obtain ⟨Y, hY, hYA, hYb⟩ := exists_dual_le_of_forall_le A' b' (Sum.elim c 0) δ
    ⟨Sum.elim x₀ y₀, (hfeas x₀ y₀).2 hy₀⟩ fun z hz => by
      rw [← Sum.elim_comp_inl_inr z, hfeas] at hz
      rw [← Sum.elim_comp_inl_inr z, sumElim_dotProduct_sumElim, zero_dotProduct, add_zero]
      exact hc _ ((hEF _).2 ⟨_, hz⟩)
  refine ⟨Y ∘ Sum.inl, fun i => hY _, Y ⬝ᵥ b', hYb, fun x y hxy => ?_⟩
  have key : Y ⬝ᵥ (b' - A' *ᵥ Sum.elim x y) = Y ⬝ᵥ b' - c ⬝ᵥ x := by
    rw [dotProduct_sub, dotProduct_mulVec, hYA, sumElim_dotProduct_sumElim, zero_dotProduct,
      add_zero]
  rw [← key, hA', hxy]
  have hsplit : b' - Sum.elim (E *ᵥ x + F *ᵥ y) (Sum.elim g' (-g')) =
      Sum.elim (g - (E *ᵥ x + F *ᵥ y)) 0 := by
    ext (i | i | i) <;> simp [b']
  rw [hsplit, ← Sum.elim_comp_inl_inr Y, sumElim_dotProduct_sumElim, dotProduct_zero, add_zero,
    Sum.elim_comp_inl]

/-- **The constant `1` is derived from an extended formulation** of a set on which some linear
functional `u` is bounded above and below but not constant: some nonnegative combination of the
slacks of its inequalities is identically `1` whenever the equations hold. -/
theorem IsExtendedFormulation.exists_nonneg_dotProduct_eq_one
    (hEF : IsExtendedFormulation P E F g E' F' g') (u : ι → K) {β β' : K}
    (hu : ∀ x ∈ P, u ⬝ᵥ x ≤ β) (hu' : ∀ x ∈ P, β' ≤ u ⬝ᵥ x) {x₁ x₂ : ι → K} (hx₁ : x₁ ∈ P)
    (hx₂ : x₂ ∈ P) (hlt : u ⬝ᵥ x₁ < u ⬝ᵥ x₂) :
    ∃ w : σ → K, 0 ≤ w ∧ ∀ x y, E' *ᵥ x + F' *ᵥ y = g' →
      w ⬝ᵥ (g - (E *ᵥ x + F *ᵥ y)) = 1 := by
  obtain ⟨wp, hwp, δp, -, hp⟩ := hEF.exists_nonneg_dotProduct_eq ⟨_, hx₁⟩ u β hu
  obtain ⟨wm, hwm, δm, -, hm⟩ := hEF.exists_nonneg_dotProduct_eq ⟨_, hx₁⟩ (-u) (-β') fun x hx =>
    by rw [neg_dotProduct, neg_le_neg_iff]; exact hu' x hx
  obtain ⟨y₁, hy₁, hy₁'⟩ := (hEF x₁).1 hx₁
  obtain ⟨y₂, hy₂, hy₂'⟩ := (hEF x₂).1 hx₂
  have hD : 0 < δp + δm := by
    have h₁ := hp _ _ hy₂'
    have h₂ := hm _ _ hy₁'
    have h₁' := dotProduct_nonneg_of_nonneg hwp (sub_nonneg.2 hy₂)
    have h₂' := dotProduct_nonneg_of_nonneg hwm (sub_nonneg.2 hy₁)
    rw [neg_dotProduct] at h₂
    linarith
  refine ⟨(δp + δm)⁻¹ • (wp + wm), smul_nonneg (inv_nonneg.2 hD.le) (add_nonneg hwp hwm),
    fun x y hxy => ?_⟩
  rw [smul_dotProduct, add_dotProduct, hp x y hxy, hm x y hxy, neg_dotProduct, smul_eq_mul]
  field_simp
  ring

/-- **Valid inequalities are derived exactly from an extended formulation** of a set on which some
linear functional `u` is bounded above and below but not constant: if `c ⬝ᵥ x ≤ δ` on `P`, some
nonnegative combination of the slacks of the inequalities equals `δ - c ⬝ᵥ x` whenever the
equations hold [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 2]. -/
theorem IsExtendedFormulation.exists_nonneg_dotProduct_eq_sub
    (hEF : IsExtendedFormulation P E F g E' F' g') (u : ι → K) {β β' : K}
    (hu : ∀ x ∈ P, u ⬝ᵥ x ≤ β) (hu' : ∀ x ∈ P, β' ≤ u ⬝ᵥ x) {x₁ x₂ : ι → K} (hx₁ : x₁ ∈ P)
    (hx₂ : x₂ ∈ P) (hlt : u ⬝ᵥ x₁ < u ⬝ᵥ x₂) (c : ι → K) (δ : K) (hc : ∀ x ∈ P, c ⬝ᵥ x ≤ δ) :
    ∃ w : σ → K, 0 ≤ w ∧ ∀ x y, E' *ᵥ x + F' *ᵥ y = g' →
      w ⬝ᵥ (g - (E *ᵥ x + F *ᵥ y)) = δ - c ⬝ᵥ x := by
  obtain ⟨w₁, hw₁, hw₁1⟩ := hEF.exists_nonneg_dotProduct_eq_one u hu hu' hx₁ hx₂ hlt
  obtain ⟨w, hw, δ', hδ', hwδ⟩ := hEF.exists_nonneg_dotProduct_eq ⟨_, hx₁⟩ c δ hc
  refine ⟨w + (δ - δ') • w₁, add_nonneg hw (smul_nonneg (sub_nonneg.2 hδ') hw₁),
    fun x y hxy => ?_⟩
  rw [add_dotProduct, smul_dotProduct, hwδ x y hxy, hw₁1 x y hxy, smul_eq_mul, mul_one]
  ring

/-- A linear functional bounded on the points `V j` is bounded on their convex hull. -/
theorem dotProduct_le_of_mem_convexHull {V : ν → ι → K} {c : ι → K} {δ : K}
    (hV : ∀ j, c ⬝ᵥ V j ≤ δ) {x : ι → K} (hx : x ∈ convexHull K (Set.range V)) :
    c ⬝ᵥ x ≤ δ :=
  convexHull_min (Set.range_subset_iff.2 hV)
    (convex_halfSpace_le ⟨fun x y => dotProduct_add c x y, fun a x => dotProduct_smul a c x⟩ δ) hx

/-- The convex hull of points satisfying `A *ᵥ x ≤ b` satisfies it. -/
theorem convexHull_range_subset_setOf_mulVec_le {A : Matrix μ ι K} {b : μ → K}
    {V : ν → ι → K} (hV : ∀ j, A *ᵥ V j ≤ b) :
    convexHull K (Set.range V) ⊆ {x | A *ᵥ x ≤ b} := fun _ hx i =>
  dotProduct_le_of_mem_convexHull (c := A i) (fun j => hV j i) hx

omit [IsStrictOrderedRing K] in
/-- A nontrivial convex hull of finitely many points has a coordinate functional that is not
constant on the points. -/
private theorem exists_dotProduct_lt_of_nontrivial {V : ν → ι → K}
    (hP : (convexHull K (Set.range V)).Nontrivial) :
    ∃ (c : ι → K) (j₁ j₂ : ν), c ⬝ᵥ V j₁ < c ⬝ᵥ V j₂ := by
  classical
  have hne : ∃ j₁ j₂, V j₁ ≠ V j₂ := by
    by_contra! h
    refine hP.not_subsingleton ?_
    rcases isEmpty_or_nonempty ν with hν | hν
    · rw [Set.range_eq_empty, convexHull_empty]
      exact Set.subsingleton_empty
    · have j := Classical.choice hν
      have : Set.range V = {V j} := Set.range_eq_singleton_iff.2 fun j' => h j' j
      rw [this, convexHull_singleton]
      exact Set.subsingleton_singleton
  obtain ⟨j₁, j₂, hj⟩ := hne
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hj
  rcases lt_or_gt_of_ne hk with h | h
  · exact ⟨Pi.single k 1, j₁, j₂, by simpa [single_dotProduct] using h⟩
  · exact ⟨Pi.single k 1, j₂, j₁, by simpa [single_dotProduct] using h⟩

variable {A : Matrix μ ι K} {b : μ → K} {V : ν → ι → K}

/-- **Nonnegative factorizations give extended formulations**: if `S = T * U` is a nonnegative
factorization of the slack matrix of `P = {x | A *ᵥ x ≤ b} = conv (range V)`, then
`A *ᵥ x + T *ᵥ y = b`, `y ≥ 0` is an extended formulation of `P` in slack form, with one inequality
per column of `T` [FioriniMassarPokuttaTiwaryDeWolf2015, proof of Theorem 3, (i) ⇒ (ii)]. -/
theorem isExtendedFormulation_of_mul_eq_slackMatrix [Fintype ρ] [DecidableEq ρ]
    (hA : P = {x | A *ᵥ x ≤ b}) (hV : P = convexHull K (Set.range V))
    {T : Matrix μ ρ K} {U : Matrix ρ ν K} (hT : ∀ i k, 0 ≤ T i k) (hU : ∀ k j, 0 ≤ U k j)
    (hTU : T * U = A.slackMatrix b V) :
    IsExtendedFormulation P (0 : Matrix ρ ι K) (-1 : Matrix ρ ρ K) 0 A T b := by
  intro x
  simp only [zero_mulVec, zero_add, neg_mulVec, one_mulVec, Left.neg_nonpos_iff]
  constructor
  · intro hx
    rw [hV] at hx
    change x ∈ {x | ∃ y, 0 ≤ y ∧ A *ᵥ x + T *ᵥ y = b}
    refine convexHull_min ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩
      refine ⟨fun k => U k j, fun k => hU k j, funext fun i => ?_⟩
      have := congrFun (congrFun hTU i) j
      rw [Matrix.mul_apply] at this
      simp only [slackMatrix, of_apply] at this
      simp only [Pi.add_apply, mulVec, dotProduct] at this ⊢
      rw [this]
      ring
    · rintro x₁ ⟨y₁, hy₁, hxy₁⟩ x₂ ⟨y₂, hy₂, hxy₂⟩ a c ha hc hac
      refine ⟨a • y₁ + c • y₂, add_nonneg (smul_nonneg ha hy₁) (smul_nonneg hc hy₂), ?_⟩
      rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul,
        add_add_add_comm, ← smul_add, ← smul_add, hxy₁, hxy₂, ← add_smul, hac, one_smul]
  · rintro ⟨y, hy, hxy⟩
    rw [hA, Set.mem_ofPred_eq, ← hxy]
    exact le_add_of_nonneg_right fun i => dotProduct_nonneg_of_nonneg (fun k => hT i k) hy

/-- **Extended formulations give nonnegative factorizations**, even when `(A, b)` is only a family
of valid inequalities for `P` rather than a complete inequality description: an extended formulation
of a nontrivial polytope `P = conv (range V)` with valid inequalities `A *ᵥ x ≤ b` on `P` gives a
nonnegative factorization of `A.slackMatrix b V` through `σ`. -/
theorem IsExtendedFormulation.hasNonnegFactorization_slackMatrix_of_forall_le [Finite ν]
    (hEF : IsExtendedFormulation P E F g E' F' g') (hA : ∀ x ∈ P, A *ᵥ x ≤ b)
    (hV : P = convexHull K (Set.range V)) (hP : P.Nontrivial) :
    (A.slackMatrix b V).HasNonnegFactorization σ := by
  classical
  have := Fintype.ofFinite ν
  have hVP : ∀ j, V j ∈ P := fun j => hV ▸ subset_convexHull K _ ⟨j, rfl⟩
  choose w hw using fun j => (hEF (V j)).1 (hVP j)
  obtain ⟨c, j₁, j₂, hj⟩ := exists_dotProduct_lt_of_nontrivial (hV ▸ hP)
  have : Nonempty ν := ⟨j₁⟩
  obtain ⟨jp, -, hjp⟩ := Finset.exists_max_image Finset.univ (fun j => c ⬝ᵥ V j)
    Finset.univ_nonempty
  obtain ⟨jm, -, hjm⟩ := Finset.exists_min_image Finset.univ (fun j => c ⬝ᵥ V j)
    Finset.univ_nonempty
  have hrow : ∀ i, ∃ l : σ → K, 0 ≤ l ∧ ∀ x y, E' *ᵥ x + F' *ᵥ y = g' →
      l ⬝ᵥ (g - (E *ᵥ x + F *ᵥ y)) = b i - A i ⬝ᵥ x := fun i =>
    hEF.exists_nonneg_dotProduct_eq_sub c
      (fun x hx => dotProduct_le_of_mem_convexHull (fun j => hjp j (Finset.mem_univ j)) (hV ▸ hx))
      (fun x hx => by
        have := dotProduct_le_of_mem_convexHull (c := -c) (δ := -(c ⬝ᵥ V jm))
          (fun j => by rw [neg_dotProduct, neg_le_neg_iff]; exact hjm j (Finset.mem_univ j))
          (hV ▸ hx)
        rwa [neg_dotProduct, neg_le_neg_iff] at this)
      (hVP j₁) (hVP j₂) hj (A i) (b i) fun x hx => hA x hx i
  choose l hl hlrow using hrow
  refine ⟨of fun i k => l i k, of fun k j => (g - (E *ᵥ V j + F *ᵥ w j)) k,
    fun i k => hl i k, fun k j => sub_nonneg.2 (hw j).1 k, Matrix.ext fun i j => ?_⟩
  rw [mul_apply', slackMatrix_apply, ← hlrow i _ _ (hw j).2]
  rfl

/-- **Extended formulations give nonnegative factorizations**: an extended formulation of a
nontrivial polytope `P = {x | A *ᵥ x ≤ b} = conv (range V)` with inequalities indexed by `σ` gives
a nonnegative factorization of its slack matrix through `σ`
[FioriniMassarPokuttaTiwaryDeWolf2015, proof of Theorem 3, (iii) ⇒ (i)]. -/
theorem IsExtendedFormulation.hasNonnegFactorization_slackMatrix [Finite ν]
    (hEF : IsExtendedFormulation P E F g E' F' g') (hA : P = {x | A *ᵥ x ≤ b})
    (hV : P = convexHull K (Set.range V)) (hP : P.Nontrivial) :
    (A.slackMatrix b V).HasNonnegFactorization σ :=
  hEF.hasNonnegFactorization_slackMatrix_of_forall_le
    (fun _ hx => by rwa [hA] at hx) hV hP

/-- **Extension complexity is at most the nonnegative rank of the slack matrix**, for any
`P = {x | A *ᵥ x ≤ b} = conv (range V)`. -/
theorem extensionComplexity_le_nonnegRank_slackMatrix [Finite μ]
    (hA : P = {x | A *ᵥ x ≤ b}) (hV : P = convexHull K (Set.range V)) :
    extensionComplexity P ≤ (A.slackMatrix b V).nonnegRank :=
  le_nonnegRank_iff.2 fun r ⟨_, _, hT, hU, hTU⟩ => by
    simpa using (isExtendedFormulation_of_mul_eq_slackMatrix hA hV hT hU hTU).extensionComplexity_le

/-- **The nonnegative rank of a slack matrix of valid inequalities is at most the extension
complexity**, for any nontrivial polytope `P = conv (range V)` with `A *ᵥ x ≤ b` valid on `P`. -/
theorem nonnegRank_slackMatrix_le_extensionComplexity_of_forall_le [Finite ν]
    (hA : ∀ x ∈ P, A *ᵥ x ≤ b) (hV : P = convexHull K (Set.range V)) (hP : P.Nontrivial) :
    (A.slackMatrix b V).nonnegRank ≤ extensionComplexity P :=
  le_extensionComplexity_iff.2 fun _ ⟨_, _, _, _, _, _, _, _, hEF⟩ => by
    simpa using (hEF.hasNonnegFactorization_slackMatrix_of_forall_le hA hV hP).nonnegRank_le

/-- **The nonnegative rank of the slack matrix is at most the extension complexity**, for a
nontrivial polytope `P = {x | A *ᵥ x ≤ b} = conv (range V)`. -/
theorem nonnegRank_slackMatrix_le_extensionComplexity [Finite ν]
    (hA : P = {x | A *ᵥ x ≤ b}) (hV : P = convexHull K (Set.range V)) (hP : P.Nontrivial) :
    (A.slackMatrix b V).nonnegRank ≤ extensionComplexity P :=
  nonnegRank_slackMatrix_le_extensionComplexity_of_forall_le
    (fun _ hx => by rwa [hA] at hx) hV hP

/-- **Yannakakis's factorization theorem.** The extension complexity of a nontrivial polytope
`P = {x | A *ᵥ x ≤ b} = conv (range V)`, with finitely many inequalities and points, is the
nonnegative rank of its slack matrix [Yannakakis1991];
[FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 3, (i) ⇔ (iii)]. The hypothesis
`P.Nontrivial` is their `dim P ≥ 1`. FMPTW quantify over a positive number `r` of inequalities;
this equality also covers `r = 0`, where the hypothesis cannot be dropped (see the module
docstring). For positive `r` and any `P`, see
`extensionComplexity_le_iff_nonnegRank_slackMatrix_le`. -/
theorem extensionComplexity_eq_nonnegRank_slackMatrix [Finite μ] [Finite ν]
    (hA : P = {x | A *ᵥ x ≤ b}) (hV : P = convexHull K (Set.range V)) (hP : P.Nontrivial) :
    extensionComplexity P = (A.slackMatrix b V).nonnegRank :=
  le_antisymm (extensionComplexity_le_nonnegRank_slackMatrix hA hV)
    (nonnegRank_slackMatrix_le_extensionComplexity hA hV hP)

/-- The slack matrix of a set `P = {x | A *ᵥ x ≤ b} = conv (range V)` with at most one point has
nonnegative rank at most `1`: all its columns are equal and nonnegative. -/
theorem nonnegRank_slackMatrix_le_one (hA : P = {x | A *ᵥ x ≤ b})
    (hV : P = convexHull K (Set.range V)) (hP : P.Subsingleton) :
    (A.slackMatrix b V).nonnegRank ≤ 1 := by
  have hmem : ∀ j, V j ∈ P := fun j => hV ▸ subset_convexHull K _ ⟨j, rfl⟩
  rcases isEmpty_or_nonempty ν with hν | ⟨⟨j₀⟩⟩
  · rw [show A.slackMatrix b V = 0 from Matrix.ext fun _ j => hν.elim j, nonnegRank_zero]
    exact zero_le_one
  · have hS := slackMatrix_nonneg (A := A) (b := b) (V := V) fun j => (hA ▸ hmem j :)
    simpa using HasNonnegFactorization.nonnegRank_le (ρ := Unit)
      ⟨of fun i _ => A.slackMatrix b V i j₀, of fun _ _ => 1, fun i _ => hS i j₀,
        fun _ _ => zero_le_one, Matrix.ext fun i j => by
          rw [Matrix.mul_apply, slackMatrix_apply, hP (hmem j) (hmem j₀)]
          simp⟩

/-- **Yannakakis's factorization theorem, for a positive number of inequalities.** A polytope
`P = {x | A *ᵥ x ≤ b} = conv (range V)`, with finitely many inequalities and points, has an extended
formulation with at most `r > 0` inequalities exactly when its slack matrix has nonnegative rank at
most `r` [Yannakakis1991]; [FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 3, (i) ⇔ (iii)]. Unlike
`extensionComplexity_eq_nonnegRank_slackMatrix`, this needs no dimension hypothesis: when `P` has
at most one point, both sides hold (`nonnegRank_slackMatrix_le_one`). -/
theorem extensionComplexity_le_iff_nonnegRank_slackMatrix_le [Finite μ] [Finite ν]
    (hA : P = {x | A *ᵥ x ≤ b}) (hV : P = convexHull K (Set.range V)) {r : ℕ} (hr : 0 < r) :
    extensionComplexity P ≤ r ↔ (A.slackMatrix b V).nonnegRank ≤ r := by
  rcases P.subsingleton_or_nontrivial with hP | hP
  · refine ⟨fun _ => (nonnegRank_slackMatrix_le_one hA hV hP).trans ?_, fun h =>
      (extensionComplexity_le_nonnegRank_slackMatrix hA hV).trans h⟩
    exact_mod_cast hr
  · rw [extensionComplexity_eq_nonnegRank_slackMatrix hA hV hP]

/-- The extension complexity of `P = {x | A *ᵥ x ≤ b} = conv (range V)` is at most the number of
points `V j`. -/
theorem extensionComplexity_le_card_points [Finite μ] [Fintype ν]
    (hA : P = {x | A *ᵥ x ≤ b}) (hV : P = convexHull K (Set.range V)) :
    extensionComplexity P ≤ Fintype.card ν :=
  (extensionComplexity_le_nonnegRank_slackMatrix hA hV).trans <|
    nonnegRank_le_card_width <| slackMatrix_nonneg fun j =>
      (hA ▸ hV ▸ subset_convexHull K _ ⟨j, rfl⟩ : V j ∈ {x | A *ᵥ x ≤ b})

end Field
