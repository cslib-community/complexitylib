/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.Bimatrix.Basic
public import Complexity.GameTheory.Bimatrix.LemkeHowson
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# Best response polytopes and the odd number of Nash equilibria

For a bimatrix game `G` with payoff matrices `A B : Matrix M N ℝ`, the *best response polytopes*
of [vonStengel2007], equation (3.6), are
`P = {x ∈ ℝ^M | x ≥ 0, Bᵀ x ≤ 1}` and `Q = {y ∈ ℝ^N | A y ≤ 1, y ≥ 0}`.
Both are written as systems of inequalities with rows indexed by the labels `M ⊕ N`
(`BimatrixGame.matP`, `BimatrixGame.rhsP`, `BimatrixGame.matQ`, `BimatrixGame.rhsQ`): the label
`i : M` of `x ∈ P` means `x i = 0` and the label `j : N` means `(xᵀ B) j = 1`, while the label
`i : M` of `y ∈ Q` means `(A y) i = 1` and `j : N` means `y j = 0`.

When all payoffs are positive, a nonzero completely labelled pair `(x, y) ∈ P × Q` rescales to a
Nash equilibrium `(x / ∑ x, y / ∑ y)` (`BimatrixGame.isNash_of_completelyLabeled`), and every Nash
equilibrium arises this way (`BimatrixGame.IsNash.completelyLabeled`). For a nondegenerate game
the systems are nondegenerate (`BimatrixGame.IsNondegenerate.isNondegenerateSystem_matP`), so
the completely labelled vertex pairs are exactly the artificial equilibrium `(0, 0)` and the
images of the Nash equilibria (`BimatrixGame.setOf_completelyLabeled_eq`). Combined with the
parity of completely labelled vertex pairs in the Lemke–Howson graph
(`Cslib.GameTheory.LemkeHowson.even_ncard_completelyLabeled`) this gives
[vonStengel2007], Corollary 3.7: **a nondegenerate bimatrix game has an odd number of Nash
equilibria** (`BimatrixGame.odd_ncard_isNash`); in particular it has one
(`BimatrixGame.exists_isNash`).

The argument is the undirected parity argument behind the Lemke–Howson algorithm
[LemkeHowson1964]; it does not formalize the algorithm's running time, the orientation of its
paths, or the membership of two-player Nash in PPAD.

## Main definitions

* `BimatrixGame.matP`, `BimatrixGame.rhsP`: the best response polytope `P` of player 1.
* `BimatrixGame.matQ`, `BimatrixGame.rhsQ`: the best response polytope `Q` of player 2.
* `BimatrixGame.toPolytopes`: the map from Nash equilibria to completely labelled pairs.

## Main results

* `BimatrixGame.IsNondegenerate.isNondegenerateSystem_matP`,
  `BimatrixGame.IsNondegenerate.isNondegenerateSystem_matQ`: the polytopes of a nondegenerate
  game are nondegenerate.
* `BimatrixGame.isNash_of_completelyLabeled`, `BimatrixGame.IsNash.completelyLabeled`:
  completely labelled pairs and Nash equilibria.
* `BimatrixGame.setOf_completelyLabeled_eq`: the completely labelled vertex pairs of a
  nondegenerate game with positive payoffs.
* `BimatrixGame.odd_ncard_isNash`: a nondegenerate bimatrix game has an odd number of Nash
  equilibria ([vonStengel2007], Corollary 3.7).
* `BimatrixGame.exists_isNash`: a nondegenerate bimatrix game has a Nash equilibrium.

## References

* [C. E. Lemke and J. T. Howson, Jr., *Equilibrium points of bimatrix games*][LemkeHowson1964]
* [B. von Stengel, *Equilibrium computation for two-player games in strategic and extensive
  form*][vonStengel2007], Sections 3.2–3.4
-/

public section

open Finset Matrix

namespace Cslib.GameTheory.BimatrixGame

variable {M N : Type*} [Fintype M] [Fintype N] (G : BimatrixGame M N)

/-! ### The best response polytopes -/

/-- The constraint matrix of the best response polytope `P = {x | x ≥ 0, Bᵀ x ≤ 1}` of player 1,
with rows labelled by `M ⊕ N` ([vonStengel2007], equation (3.6)). -/
def matP [DecidableEq M] : Matrix (M ⊕ N) M ℝ := fromRows (-1) G.Bᵀ

omit [Fintype M] [Fintype N] in
variable (M N) in
/-- The right-hand side of the best response polytope `P`: `0` on `M`, `1` on `N`. -/
def rhsP : M ⊕ N → ℝ := Sum.elim 0 1

/-- The constraint matrix of the best response polytope `Q = {y | A y ≤ 1, y ≥ 0}` of player 2,
with rows labelled by `M ⊕ N` ([vonStengel2007], equation (3.6)). -/
def matQ [DecidableEq N] : Matrix (M ⊕ N) N ℝ := fromRows G.A (-1)

omit [Fintype M] [Fintype N] in
variable (M N) in
/-- The right-hand side of the best response polytope `Q`: `1` on `M`, `0` on `N`. -/
def rhsQ : M ⊕ N → ℝ := Sum.elim 1 0

omit [Fintype M] [Fintype N] in
@[simp] theorem rhsP_inl (i : M) : rhsP M N (.inl i) = 0 := by rw [rhsP]; rfl

omit [Fintype M] [Fintype N] in
@[simp] theorem rhsP_inr (j : N) : rhsP M N (.inr j) = 1 := by rw [rhsP]; rfl

omit [Fintype M] [Fintype N] in
@[simp] theorem rhsQ_inl (i : M) : rhsQ M N (.inl i) = 1 := by rw [rhsQ]; rfl

omit [Fintype M] [Fintype N] in
@[simp] theorem rhsQ_inr (j : N) : rhsQ M N (.inr j) = 0 := by rw [rhsQ]; rfl

variable [DecidableEq M] [DecidableEq N] {G} {x : M → ℝ} {y : N → ℝ}

omit [Fintype N] [DecidableEq N] in
theorem matP_mulVec (x : M → ℝ) : G.matP *ᵥ x = Sum.elim (-x) (x ᵥ* G.B) := by
  rw [matP, fromRows_mulVec, neg_mulVec, one_mulVec, mulVec_transpose]

omit [Fintype M] [DecidableEq M] in
theorem matQ_mulVec (y : N → ℝ) : G.matQ *ᵥ y = Sum.elim (G.A *ᵥ y) (-y) := by
  rw [matQ, fromRows_mulVec, neg_mulVec, one_mulVec]

omit [Fintype N] [DecidableEq N] in
@[simp]
theorem matP_mulVec_inl (x : M → ℝ) (i : M) : (G.matP *ᵥ x) (.inl i) = -x i := by
  rw [matP_mulVec]
  rfl

omit [Fintype N] [DecidableEq N] in
@[simp]
theorem matP_mulVec_inr (x : M → ℝ) (j : N) : (G.matP *ᵥ x) (.inr j) = (x ᵥ* G.B) j := by
  rw [matP_mulVec]
  rfl

omit [Fintype M] [DecidableEq M] in
@[simp]
theorem matQ_mulVec_inl (y : N → ℝ) (i : M) : (G.matQ *ᵥ y) (.inl i) = (G.A *ᵥ y) i := by
  rw [matQ_mulVec]
  rfl

omit [Fintype M] [DecidableEq M] in
@[simp]
theorem matQ_mulVec_inr (y : N → ℝ) (j : N) : (G.matQ *ᵥ y) (.inr j) = -y j := by
  rw [matQ_mulVec]
  rfl

omit [DecidableEq N] in
theorem inl_mem_tightRows_matP {i : M} : .inl i ∈ tightRows G.matP (rhsP M N) x ↔ x i = 0 := by
  simp

omit [DecidableEq N] in
theorem inr_mem_tightRows_matP {j : N} :
    .inr j ∈ tightRows G.matP (rhsP M N) x ↔ (x ᵥ* G.B) j = 1 := by
  simp

omit [DecidableEq M] in
theorem inl_mem_tightRows_matQ {i : M} :
    .inl i ∈ tightRows G.matQ (rhsQ M N) y ↔ (G.A *ᵥ y) i = 1 := by
  simp

omit [DecidableEq M] in
theorem inr_mem_tightRows_matQ {j : N} : .inr j ∈ tightRows G.matQ (rhsQ M N) y ↔ y j = 0 := by
  simp

omit [Fintype N] [DecidableEq N] in
/-- `x ∈ P` iff `x ≥ 0` and `Bᵀ x ≤ 1`. -/
theorem matP_mulVec_le_iff :
    G.matP *ᵥ x ≤ rhsP M N ↔ (∀ i, 0 ≤ x i) ∧ ∀ j, (x ᵥ* G.B) j ≤ 1 := by
  simp [Pi.le_def, matP_mulVec]

omit [Fintype M] [DecidableEq M] in
/-- `y ∈ Q` iff `A y ≤ 1` and `y ≥ 0`. -/
theorem matQ_mulVec_le_iff :
    G.matQ *ᵥ y ≤ rhsQ M N ↔ (∀ i, (G.A *ᵥ y) i ≤ 1) ∧ ∀ j, 0 ≤ y j := by
  simp [Pi.le_def, matQ_mulVec]

/-! ### Nondegeneracy and boundedness -/

omit [DecidableEq N] in
/-- The best response polytope `P` of a nondegenerate game is a nondegenerate system: a point of
`P` has at most `card M` labels. -/
theorem IsNondegenerate.isNondegenerateSystem_matP (hG : G.IsNondegenerate) :
    IsNondegenerateSystem G.matP (rhsP M N) := by
  classical
  rw [isNondegenerateSystem_iff]
  intro x hx
  obtain ⟨hx₀, -⟩ := matP_mulVec_le_iff.1 hx
  rw [← card_toLeft_add_card_toRight]
  have hL : (tightRows G.matP (rhsP M N) x).toLeft = univ.filter fun i => x i = 0 := by
    ext i
    simp
  have hsupp : (Function.support x).ncard = #(univ.filter fun i => ¬x i = 0) := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  have hsum := card_filter_add_card_filter_not (s := univ) fun i => x i = 0
  rw [card_univ] at hsum
  rw [hL]
  by_cases hx0 : x = 0
  · subst hx0
    have hR : (tightRows G.matP (rhsP M N) 0).toRight = ∅ := by
      ext j
      simp
    rw [hR, card_empty, add_zero]
    exact card_le_univ _
  set xn := (∑ i, x i)⁻¹ • x
  have hxn : IsMixedStrategy xn := isMixedStrategy_inv_sum_smul hx₀ hx0
  have hpos : 0 < ∑ i, x i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
    exact (sum_pos_iff_of_nonneg fun j _ => hx₀ j).2 ⟨i, mem_univ _, (hx₀ i).lt_of_ne' hi⟩
  have hsupp' : Function.support xn = Function.support x :=
    Function.support_const_smul_of_ne_zero _ _ (inv_ne_zero hpos.ne')
  have hR : ((tightRows G.matP (rhsP M N) x).toRight : Set N) ⊆
      {j | G.IsPureBestResponse₂ xn j} := by
    intro j hj
    rw [mem_coe, mem_toRight, inr_mem_tightRows_matP] at hj
    rw [Set.mem_ofPred_eq, isPureBestResponse₂_iff]
    intro j'
    simp only [xn, smul_vecMul, Pi.smul_apply, smul_eq_mul, hj, mul_one]
    exact mul_le_mul_of_nonneg_left ((matP_mulVec_le_iff.1 hx).2 j')
      (inv_nonneg.2 hpos.le) |>.trans_eq (mul_one _)
  have h1 := (Set.ncard_le_ncard hR (Set.toFinite _)).trans
    ((isNondegenerate_iff.1 hG).1 xn hxn)
  rw [Set.ncard_coe_finset, hsupp', hsupp] at h1
  omega

omit [DecidableEq M] in
/-- The best response polytope `Q` of a nondegenerate game is a nondegenerate system: a point of
`Q` has at most `card N` labels. -/
theorem IsNondegenerate.isNondegenerateSystem_matQ (hG : G.IsNondegenerate) :
    IsNondegenerateSystem G.matQ (rhsQ M N) := by
  classical
  rw [isNondegenerateSystem_iff]
  intro y hy
  obtain ⟨-, hy₀⟩ := matQ_mulVec_le_iff.1 hy
  rw [← card_toLeft_add_card_toRight]
  have hR : (tightRows G.matQ (rhsQ M N) y).toRight = univ.filter fun j => y j = 0 := by
    ext j
    simp
  have hsupp : (Function.support y).ncard = #(univ.filter fun j => ¬y j = 0) := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext j
    simp
  have hsum := card_filter_add_card_filter_not (s := univ) fun j => y j = 0
  rw [card_univ] at hsum
  rw [hR]
  by_cases hy0 : y = 0
  · subst hy0
    have hL : (tightRows G.matQ (rhsQ M N) 0).toLeft = ∅ := by
      ext i
      simp
    rw [hL, card_empty, zero_add]
    exact card_le_univ _
  set yn := (∑ j, y j)⁻¹ • y
  have hyn : IsMixedStrategy yn := isMixedStrategy_inv_sum_smul hy₀ hy0
  have hpos : 0 < ∑ j, y j := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hy0
    exact (sum_pos_iff_of_nonneg fun j _ => hy₀ j).2 ⟨j, mem_univ _, (hy₀ j).lt_of_ne' hj⟩
  have hsupp' : Function.support yn = Function.support y :=
    Function.support_const_smul_of_ne_zero _ _ (inv_ne_zero hpos.ne')
  have hL : ((tightRows G.matQ (rhsQ M N) y).toLeft : Set M) ⊆
      {i | G.IsPureBestResponse₁ yn i} := by
    intro i hi
    rw [mem_coe, mem_toLeft, inl_mem_tightRows_matQ] at hi
    rw [Set.mem_ofPred_eq, isPureBestResponse₁_iff]
    intro i'
    simp only [yn, mulVec_smul, Pi.smul_apply, smul_eq_mul, hi, mul_one]
    exact mul_le_mul_of_nonneg_left ((matQ_mulVec_le_iff.1 hy).1 i')
      (inv_nonneg.2 hpos.le) |>.trans_eq (mul_one _)
  have h1 := (Set.ncard_le_ncard hL (Set.toFinite _)).trans
    ((isNondegenerate_iff.1 hG).2 yn hyn)
  rw [Set.ncard_coe_finset, hsupp', hsupp] at h1
  omega

omit [Fintype N] [DecidableEq N] in
/-- With positive payoffs to player 2, the best response polytope `P` is bounded: its recession
cone is `{0}`. -/
theorem eq_zero_of_matP_mulVec_nonpos [Nonempty N] (hB : ∀ i j, 0 < G.B i j) {v : M → ℝ}
    (hv : G.matP *ᵥ v ≤ 0) : v = 0 := by
  have hnn : ∀ i, 0 ≤ v i := fun i => by
    simpa [matP_mulVec] using hv (.inl i)
  obtain ⟨j⟩ := ‹Nonempty N›
  have hj : (v ᵥ* G.B) j ≤ 0 := by simpa using hv (.inr j)
  have hsum : ∑ i, v i * G.B i j = 0 :=
    le_antisymm hj
      (sum_nonneg fun i _ => mul_nonneg (hnn i) (hB i j).le)
  funext i
  have := (sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hnn i) (hB i j).le).1 hsum i
    (mem_univ _)
  exact (mul_eq_zero.1 this).resolve_right (hB i j).ne'

omit [Fintype M] [DecidableEq M] in
/-- With positive payoffs to player 1, the best response polytope `Q` is bounded: its recession
cone is `{0}`. -/
theorem eq_zero_of_matQ_mulVec_nonpos [Nonempty M] (hA : ∀ i j, 0 < G.A i j) {v : N → ℝ}
    (hv : G.matQ *ᵥ v ≤ 0) : v = 0 := by
  have hnn : ∀ j, 0 ≤ v j := fun j => by
    simpa [matQ_mulVec] using hv (.inr j)
  obtain ⟨i⟩ := ‹Nonempty M›
  have hi : (G.A *ᵥ v) i ≤ 0 := by simpa using hv (.inl i)
  have hsum : ∑ j, G.A i j * v j = 0 :=
    le_antisymm hi
      (sum_nonneg fun j _ => mul_nonneg (hA i j).le (hnn j))
  funext j
  have := (sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hA i j).le (hnn j)).1 hsum j
    (mem_univ _)
  exact (mul_eq_zero.1 this).resolve_left (hA i j).ne'

omit [DecidableEq N] in
/-- The origin is a vertex of `P`. -/
theorem isVertex_matP_zero : IsVertex G.matP (rhsP M N) 0 := by
  refine isVertex_iff.2 ⟨matP_mulVec_le_iff.2 ⟨fun _ => le_rfl, fun _ => by simp⟩, ?_⟩
  intro v hv
  funext i
  simpa [matP_mulVec] using hv (.inl i) (by simp)

omit [DecidableEq M] in
/-- The origin is a vertex of `Q`. -/
theorem isVertex_matQ_zero : IsVertex G.matQ (rhsQ M N) 0 := by
  refine isVertex_iff.2 ⟨matQ_mulVec_le_iff.2 ⟨fun _ => by simp, fun _ => le_rfl⟩, ?_⟩
  intro v hv
  funext j
  simpa [matQ_mulVec] using hv (.inr j) (by simp)

/-! ### Completely labelled pairs and Nash equilibria -/

/-- A pair `(x, y)` is completely labelled for `P` and `Q` iff every row `i` is unplayed in `x`
or a best response with payoff `1` against `y`, and every column `j` is unplayed in `y` or a best
response with payoff `1` against `x`. -/
theorem completelyLabeled_iff_forall :
    LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N) x y ↔
      (∀ i, x i = 0 ∨ (G.A *ᵥ y) i = 1) ∧ ∀ j, (x ᵥ* G.B) j = 1 ∨ y j = 0 := by
  rw [LemkeHowson.completelyLabeled_iff, Sum.forall]
  simp

/-- In a feasible completely labelled pair, `x = 0` iff `y = 0`. -/
theorem eq_zero_iff_eq_zero_of_completelyLabeled (hx : G.matP *ᵥ x ≤ rhsP M N)
    (hy : G.matQ *ᵥ y ≤ rhsQ M N)
    (hcl : LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N) x y) :
    x = 0 ↔ y = 0 := by
  obtain ⟨hcl₁, hcl₂⟩ := completelyLabeled_iff_forall.1 hcl
  constructor
  · rintro rfl
    funext j
    simpa using hcl₂ j
  · rintro rfl
    funext i
    simpa using hcl₁ i

/-- A nonzero feasible completely labelled pair `(x, y)` of `P × Q` rescales to the Nash
equilibrium `(x / ∑ x, y / ∑ y)` ([vonStengel2007], Section 3.3). -/
theorem isNash_of_completelyLabeled (hx : G.matP *ᵥ x ≤ rhsP M N) (hy : G.matQ *ᵥ y ≤ rhsQ M N)
    (hcl : LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N) x y)
    (hx0 : x ≠ 0) : G.IsNash ((∑ i, x i)⁻¹ • x) ((∑ j, y j)⁻¹ • y) := by
  obtain ⟨hx₀, hx₁⟩ := matP_mulVec_le_iff.1 hx
  obtain ⟨hy₁, hy₀⟩ := matQ_mulVec_le_iff.1 hy
  obtain ⟨hcl₁, hcl₂⟩ := completelyLabeled_iff_forall.1 hcl
  have hy0 : y ≠ 0 := fun h => hx0 ((eq_zero_iff_eq_zero_of_completelyLabeled hx hy hcl).2 h)
  have hsx : 0 ≤ (∑ i, x i)⁻¹ := inv_nonneg.2 (sum_nonneg fun i _ => hx₀ i)
  have hsy : 0 ≤ (∑ j, y j)⁻¹ := inv_nonneg.2 (sum_nonneg fun j _ => hy₀ j)
  refine isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨isMixedStrategy_inv_sum_smul hx₀ hx0, ?_⟩,
    isBestResponse₂_iff.2 ⟨isMixedStrategy_inv_sum_smul hy₀ hy0, ?_⟩⟩
  · intro i hi
    rw [isPureBestResponse₁_iff]
    intro i'
    have hxi : x i ≠ 0 := fun h => by simp [h] at hi
    have h1 := (hcl₁ i).resolve_left hxi
    simp only [mulVec_smul, Pi.smul_apply, smul_eq_mul, h1, mul_one]
    exact (mul_le_mul_of_nonneg_left (hy₁ i') hsy).trans_eq (mul_one _)
  · intro j hj
    rw [isPureBestResponse₂_iff]
    intro j'
    have hyj : y j ≠ 0 := fun h => by simp [h] at hj
    have h1 := (hcl₂ j).resolve_right hyj
    simp only [smul_vecMul, Pi.smul_apply, smul_eq_mul, h1, mul_one]
    exact (mul_le_mul_of_nonneg_left (hx₁ j') hsx).trans_eq (mul_one _)

/-- A Nash equilibrium `(x, y)` of a game with positive payoffs, rescaled by the inverse
equilibrium payoffs, is a feasible completely labelled pair of `P × Q`
([vonStengel2007], Section 3.3). -/
theorem IsNash.completelyLabeled (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j)
    (h : G.IsNash x y) :
    G.matP *ᵥ ((G.payoff₂ x y)⁻¹ • x) ≤ rhsP M N ∧
      G.matQ *ᵥ ((G.payoff₁ x y)⁻¹ • y) ≤ rhsQ M N ∧
      LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N)
        ((G.payoff₂ x y)⁻¹ • x) ((G.payoff₁ x y)⁻¹ • y) := by
  obtain ⟨h₁, h₂⟩ := isNash_iff.1 h
  have hx := h₁.isMixedStrategy
  have hy := h₂.isMixedStrategy
  have hu := G.payoff₁_pos hA hx hy
  have hv := G.payoff₂_pos hB hx hy
  refine ⟨matP_mulVec_le_iff.2 ⟨fun i => smul_nonneg (inv_nonneg.2 hv.le) (hx.nonneg i),
    fun j => ?_⟩, matQ_mulVec_le_iff.2 ⟨fun i => ?_,
      fun j => smul_nonneg (inv_nonneg.2 hu.le) (hy.nonneg j)⟩,
    completelyLabeled_iff_forall.2 ⟨fun i => ?_, fun j => ?_⟩⟩
  · rw [smul_vecMul, Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hv, mul_one]
    exact h₂.le_payoff₂ j
  · rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hu, mul_one]
    exact h₁.le_payoff₁ i
  · rcases (hx.nonneg i).lt_or_eq with hi | hi
    · right
      rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, ← h₁.payoff₁_eq_of_pos hi,
        inv_mul_cancel₀ hu.ne']
    · left
      rw [Pi.smul_apply, ← hi, smul_zero]
  · rcases (hy.nonneg j).lt_or_eq with hj | hj
    · left
      rw [smul_vecMul, Pi.smul_apply, smul_eq_mul, ← h₂.payoff₂_eq_of_pos hj,
        inv_mul_cancel₀ hv.ne']
    · right
      rw [Pi.smul_apply, ← hj, smul_zero]

/-! ### The completely labelled vertex pairs -/

omit [DecidableEq M] [DecidableEq N] in
variable (G) in
/-- The completely labelled pair of a Nash equilibrium `(x, y)`: both strategies rescaled by the
inverse of the other player's equilibrium payoff. -/
noncomputable def toPolytopes (p : (M → ℝ) × (N → ℝ)) : (M → ℝ) × (N → ℝ) :=
  ((G.payoff₂ p.1 p.2)⁻¹ • p.1, (G.payoff₁ p.1 p.2)⁻¹ • p.2)

omit [DecidableEq M] [DecidableEq N] in
theorem toPolytopes_apply (p : (M → ℝ) × (N → ℝ)) :
    G.toPolytopes p = ((G.payoff₂ p.1 p.2)⁻¹ • p.1, (G.payoff₁ p.1 p.2)⁻¹ • p.2) := by
  rw [toPolytopes]

omit [DecidableEq M] [DecidableEq N] in
/-- With positive payoffs, distinct Nash equilibria give distinct completely labelled pairs. -/
theorem injOn_toPolytopes (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) :
    Set.InjOn G.toPolytopes {p | G.IsNash p.1 p.2} := by
  rintro ⟨x, y⟩ h ⟨x', y'⟩ h' he
  rw [Set.mem_ofPred_eq, isNash_iff] at h h'
  have hx := h.1.isMixedStrategy
  have hy := h.2.isMixedStrategy
  have hx' := h'.1.isMixedStrategy
  have hy' := h'.2.isMixedStrategy
  rw [toPolytopes_apply, toPolytopes_apply, Prod.mk.injEq] at he
  exact Prod.ext (hx.eq_of_smul_eq_smul hx' (inv_ne_zero (G.payoff₂_pos hB hx hy).ne') he.1)
    (hy.eq_of_smul_eq_smul hy' (inv_ne_zero (G.payoff₁_pos hA hx hy).ne') he.2)

omit [DecidableEq M] [DecidableEq N] in
/-- With positive payoffs to player 2, no Nash equilibrium gives the artificial pair `(0, 0)`. -/
theorem zero_notMem_image_toPolytopes (hB : ∀ i j, 0 < G.B i j) :
    0 ∉ G.toPolytopes '' {p | G.IsNash p.1 p.2} := by
  rintro ⟨⟨x, y⟩, h, he⟩
  rw [Set.mem_ofPred_eq, isNash_iff] at h
  have hx := h.1.isMixedStrategy
  rw [toPolytopes_apply, Prod.mk_eq_zero] at he
  exact hx.ne_zero ((smul_eq_zero.1 he.1).resolve_left
    (inv_ne_zero (G.payoff₂_pos hB hx h.2.isMixedStrategy).ne'))

/-- The equilibrium payoffs of the Nash equilibrium obtained from a nonzero completely labelled
pair `(x, y)` are `1 / ∑ y` and `1 / ∑ x`. -/
private theorem payoff_inv_sum_smul (hx : G.matP *ᵥ x ≤ rhsP M N)
    (hy : G.matQ *ᵥ y ≤ rhsQ M N)
    (hcl : LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N) x y)
    (hx0 : x ≠ 0) :
    G.payoff₁ ((∑ i, x i)⁻¹ • x) ((∑ j, y j)⁻¹ • y) = (∑ j, y j)⁻¹ ∧
      G.payoff₂ ((∑ i, x i)⁻¹ • x) ((∑ j, y j)⁻¹ • y) = (∑ i, x i)⁻¹ := by
  obtain ⟨h₁, h₂⟩ := isNash_iff.1 (isNash_of_completelyLabeled hx hy hcl hx0)
  obtain ⟨hcl₁, hcl₂⟩ := completelyLabeled_iff_forall.1 hcl
  constructor
  · rw [payoff₁_eq_dotProduct]
    refine h₁.isMixedStrategy.dotProduct_eq_of_forall_pos fun i hi => ?_
    have hxi : x i ≠ 0 := fun h => by simp [h] at hi
    rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, (hcl₁ i).resolve_left hxi, mul_one]
  · rw [payoff₂_eq_dotProduct]
    refine h₂.isMixedStrategy.dotProduct_eq_of_forall_pos fun j hj => ?_
    have hyj : y j ≠ 0 := fun h => by simp [h] at hj
    rw [smul_vecMul, Pi.smul_apply, smul_eq_mul, (hcl₂ j).resolve_right hyj, mul_one]

/-- **Completely labelled vertex pairs** ([vonStengel2007], Section 3.4). For a nondegenerate game
with positive payoffs, the completely labelled vertex pairs of `P × Q` are the artificial
equilibrium `(0, 0)` and the rescaled Nash equilibria. -/
theorem setOf_completelyLabeled_eq [Nonempty M] [Nonempty N] (hG : G.IsNondegenerate)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) :
    {p : (M → ℝ) × (N → ℝ) | IsVertex G.matP (rhsP M N) p.1 ∧ IsVertex G.matQ (rhsQ M N) p.2 ∧
      LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N) p.1 p.2} =
      insert 0 (G.toPolytopes '' {p | G.IsNash p.1 p.2}) := by
  have hnd₁ := hG.isNondegenerateSystem_matP
  have hnd₂ := hG.isNondegenerateSystem_matQ
  have hrec₁ : ∀ v, G.matP *ᵥ v ≤ 0 → v = 0 := fun _ => eq_zero_of_matP_mulVec_nonpos hB
  have hrec₂ : ∀ v, G.matQ *ᵥ v ≤ 0 → v = 0 := fun _ => eq_zero_of_matQ_mulVec_nonpos hA
  have hcard : Fintype.card (M ⊕ N) = Fintype.card M + Fintype.card N := Fintype.card_sum
  ext ⟨x, y⟩
  rw [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_image]
  constructor
  · rintro ⟨hxv, hyv, hcl⟩
    have hx := hxv.mulVec_le
    have hy := hyv.mulVec_le
    by_cases hx0 : x = 0
    · left
      rw [Prod.mk_eq_zero]
      exact ⟨hx0, (eq_zero_iff_eq_zero_of_completelyLabeled hx hy hcl).1 hx0⟩
    · right
      obtain ⟨hx₀, -⟩ := matP_mulVec_le_iff.1 hx
      obtain ⟨-, hy₀⟩ := matQ_mulVec_le_iff.1 hy
      have hy0 : y ≠ 0 := fun h => hx0 ((eq_zero_iff_eq_zero_of_completelyLabeled hx hy hcl).2 h)
      have hsx : 0 < ∑ i, x i := by
        obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
        exact (sum_pos_iff_of_nonneg fun j _ => hx₀ j).2 ⟨i, mem_univ _, (hx₀ i).lt_of_ne' hi⟩
      have hsy : 0 < ∑ j, y j := by
        obtain ⟨j, hj⟩ := Function.ne_iff.1 hy0
        exact (sum_pos_iff_of_nonneg fun j _ => hy₀ j).2 ⟨j, mem_univ _, (hy₀ j).lt_of_ne' hj⟩
      obtain ⟨hu, hv⟩ := payoff_inv_sum_smul hx hy hcl hx0
      refine ⟨((∑ i, x i)⁻¹ • x, (∑ j, y j)⁻¹ • y), isNash_of_completelyLabeled hx hy hcl hx0, ?_⟩
      rw [toPolytopes_apply, hu, hv, inv_inv, inv_inv, smul_inv_smul₀ hsx.ne',
        smul_inv_smul₀ hsy.ne']
  · rintro (h | ⟨⟨x', y'⟩, h, he⟩)
    · rw [Prod.mk_eq_zero] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨isVertex_matP_zero, isVertex_matQ_zero,
        completelyLabeled_iff_forall.2 ⟨fun _ => .inl rfl, fun _ => .inr rfl⟩⟩
    · rw [Set.mem_ofPred_eq] at h
      obtain ⟨hx, hy, hcl⟩ := h.completelyLabeled hA hB
      rw [toPolytopes_apply, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨LemkeHowson.isVertex_left_of_completelyLabeled hnd₁ hrec₁ hnd₂ hcard hx hy hcl,
        LemkeHowson.isVertex_right_of_completelyLabeled hnd₁ hnd₂ hrec₂ hcard hx hy hcl, hcl⟩

omit [DecidableEq M] [DecidableEq N] in
/-- A nondegenerate bimatrix game with positive payoffs has an odd number of Nash equilibria. -/
theorem odd_ncard_isNash_of_pos [Nonempty M] [Nonempty N] (hG : G.IsNondegenerate)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) :
    Odd {p : (M → ℝ) × (N → ℝ) | G.IsNash p.1 p.2}.ncard := by
  classical
  have heven := LemkeHowson.even_ncard_completelyLabeled hG.isNondegenerateSystem_matP
    (fun _ => eq_zero_of_matP_mulVec_nonpos hB) hG.isNondegenerateSystem_matQ
    (fun _ => eq_zero_of_matQ_mulVec_nonpos hA) (Fintype.card_sum (α := M) (β := N))
  have hfin : (G.toPolytopes '' {p | G.IsNash p.1 p.2}).Finite := by
    refine ((setOf_isVertex_finite (A := G.matP) (b := rhsP M N)).prod
      (setOf_isVertex_finite (A := G.matQ) (b := rhsQ M N))).subset ?_
    intro p hp
    have hp' : p ∈ insert 0 (G.toPolytopes '' {p | G.IsNash p.1 p.2}) := Set.mem_insert_of_mem _ hp
    rw [← setOf_completelyLabeled_eq hG hA hB, Set.mem_ofPred_eq] at hp'
    exact Set.mem_prod.2 ⟨hp'.1, hp'.2.1⟩
  rw [setOf_completelyLabeled_eq hG hA hB, Set.ncard_insert_of_notMem
    (zero_notMem_image_toPolytopes hB) hfin, (injOn_toPolytopes hA hB).ncard_image,
    Nat.even_add_one, Nat.not_even_iff_odd] at heven
  exact heven

omit [DecidableEq M] [DecidableEq N] in
/-- **A nondegenerate bimatrix game has an odd number of Nash equilibria** ([vonStengel2007],
Corollary 3.7). The proof is the parity argument behind the Lemke–Howson algorithm
[LemkeHowson1964]: after making all payoffs positive, the Nash equilibria correspond to the
completely labelled vertex pairs of the best response polytopes other than `(0, 0)`, and there is
an even number of those (`Cslib.GameTheory.LemkeHowson.even_ncard_completelyLabeled`). -/
theorem odd_ncard_isNash [Nonempty M] [Nonempty N] (hG : G.IsNondegenerate) :
    Odd {p : (M → ℝ) × (N → ℝ) | G.IsNash p.1 p.2}.ncard := by
  obtain ⟨c, hA, hB⟩ := G.exists_addConst_pos
  have := odd_ncard_isNash_of_pos (isNondegenerate_addConst.2 hG) hA hB
  simpa only [isNash_addConst] using this

omit [DecidableEq M] [DecidableEq N] in
/-- A nondegenerate bimatrix game has a Nash equilibrium. This is the special case of Nash's
theorem for nondegenerate bimatrix games, obtained here from `odd_ncard_isNash`. -/
theorem exists_isNash [Nonempty M] [Nonempty N] (hG : G.IsNondegenerate) :
    ∃ x y, G.IsNash x y := by
  obtain ⟨⟨x, y⟩, h⟩ := Set.nonempty_of_ncard_ne_zero (odd_ncard_isNash hG).pos.ne'
  exact ⟨x, y, h⟩

omit [DecidableEq M] [DecidableEq N] in
/-- A nondegenerate bimatrix game has finitely many Nash equilibria. -/
theorem finite_setOf_isNash [Nonempty M] [Nonempty N] (hG : G.IsNondegenerate) :
    {p : (M → ℝ) × (N → ℝ) | G.IsNash p.1 p.2}.Finite :=
  Set.finite_of_ncard_ne_zero (odd_ncard_isNash hG).pos.ne'

end Cslib.GameTheory.BimatrixGame
