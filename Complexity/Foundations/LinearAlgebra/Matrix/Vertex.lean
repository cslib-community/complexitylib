/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/Vertex.lean`)

public import Complexity.Init
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Vertices of polyhedra given by inequality systems

For a matrix `A : Matrix κ ι K` and a vector `b : κ → K` over a linearly ordered field, consider
the polyhedron `{x | A *ᵥ x ≤ b}`. The rows that hold with equality at `x` are its *tight rows*
(`Matrix.tightRows`), and `x` is a *vertex* (`Matrix.IsVertex`) if it is feasible and the
normals of its tight rows span the dual space, that is, only `v = 0` satisfies `(A *ᵥ v) k = 0` on
every tight row `k`. This is the algebraic description of a vertex (a basic feasible solution): a
feasible point is the unique point of a `0`-dimensional face exactly when its tight rows have
full rank ([Schrijver1986], Section 8.5; [Ziegler1995], Lecture 2).

The system is *nondegenerate* (`Matrix.IsNondegenerateSystem`) if no feasible point has more than
`card ι` tight rows; then every vertex has exactly `card ι` tight rows. A bounded nondegenerate
polyhedron is simple, and its graph has a purely combinatorial description, which is what the
Lemke–Howson algorithm walks on. Under nondegeneracy and the boundedness hypothesis
`∀ v, A *ᵥ v ≤ 0 → v = 0` (the recession cone is trivial):

* every feasible point with at least `card ι` tight rows is a vertex
  (`Matrix.isVertex_of_card_tightRows`);
* *pivoting*: for each tight row `l` of a vertex `x` there is exactly one other vertex
  `Matrix.pivotVertex A b x l` at which all tight rows of `x` except `l` stay tight
  (`Matrix.IsVertex.pivotVertex_spec`, `Matrix.IsVertex.eq_pivotVertex`); it is the other end
  of the edge obtained by relaxing row `l`, found by the minimum ratio test;
* two vertices are adjacent (`Matrix.VertexAdj`: they share `card ι - 1` tight rows) iff one is
  obtained from the other by a pivot (`Matrix.vertexAdj_iff_exists_pivotVertex`), and distinct
  dropped rows give distinct neighbours (`Matrix.IsVertex.pivotVertex_injOn`). So a vertex has
  exactly `card ι` neighbours.

Vertices are determined by their tight rows (`Matrix.IsVertex.eq_of_tightRows_subset`), so a
polyhedron has finitely many vertices (`Matrix.setOf_isVertex_finite`).

## Main definitions

* `Matrix.tightRows`: the rows of `A *ᵥ x ≤ b` that are tight at `x`.
* `Matrix.IsVertex`: `x` is a vertex of `{x | A *ᵥ x ≤ b}`.
* `Matrix.IsNondegenerateSystem`: no feasible point has more than `card ι` tight rows.
* `Matrix.pivotVertex`: the vertex reached from `x` by dropping the tight row `l`.
* `Matrix.VertexAdj`: adjacency of vertices of a nondegenerate system.

## Main results

* `Matrix.IsVertex.card_le_card_tightRows`: a vertex has at least `card ι` tight rows.
* `Matrix.IsVertex.eq_of_tightRows_subset`, `Matrix.setOf_isVertex_finite`.
* `Matrix.isVertex_iff_card_tightRows`: for a bounded nondegenerate system, the vertices are the
  feasible points with exactly `card ι` tight rows.
* `Matrix.IsVertex.exists_pivot`, `Matrix.IsVertex.eq_of_erase_subset`: existence and uniqueness
  of the pivot.
* `Matrix.vertexAdj_iff_exists_pivotVertex`, `Matrix.IsVertex.pivotVertex_injOn`.

## References

* [Schrijver1986], Sections 8.5 and 11.2
* [Ziegler1995], Lecture 2 and Section 3.2
-/

public section

open Finset

namespace Matrix

variable {K : Type*} [Field K] [LinearOrder K]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The rows of the system `A *ᵥ x ≤ b` that are tight (hold with equality) at `x`. -/
def tightRows (A : Matrix κ ι K) (b : κ → K) (x : ι → K) : Finset κ :=
  {k | (A *ᵥ x) k = b k}

/-- `x` is a *vertex* (basic feasible solution) of the polyhedron `{x | A *ᵥ x ≤ b}`: it is
feasible, and the only vector orthogonal to the normals of all its tight rows is `0`. -/
def IsVertex (A : Matrix κ ι K) (b : κ → K) (x : ι → K) : Prop :=
  A *ᵥ x ≤ b ∧ ∀ v : ι → K, (∀ k ∈ tightRows A b x, (A *ᵥ v) k = 0) → v = 0

/-- The system `A *ᵥ x ≤ b` is *nondegenerate* if no feasible point has more than `card ι` tight
rows. -/
def IsNondegenerateSystem (A : Matrix κ ι K) (b : κ → K) : Prop :=
  ∀ x, A *ᵥ x ≤ b → #(tightRows A b x) ≤ Fintype.card ι

/-- Two vertices of `A *ᵥ x ≤ b` are *adjacent* if they are distinct and share at least
`card ι - 1` tight rows. For a bounded nondegenerate system adjacent pairs correspond to the edges
of the polyhedron ([Schrijver1986], Section 8.5); that geometric statement is not formalized here.
What is proved is the pivot characterization `Matrix.vertexAdj_iff_exists_pivotVertex`. -/
def VertexAdj [DecidableEq κ] (A : Matrix κ ι K) (b : κ → K) (x y : ι → K) : Prop :=
  IsVertex A b x ∧ IsVertex A b y ∧ x ≠ y ∧
    Fintype.card ι ≤ #(tightRows A b x ∩ tightRows A b y) + 1

variable {A : Matrix κ ι K} {b : κ → K} {x y : ι → K}

@[simp]
theorem mem_tightRows {k : κ} : k ∈ tightRows A b x ↔ (A *ᵥ x) k = b k := by
  simp [tightRows]

theorem isVertex_iff :
    IsVertex A b x ↔ A *ᵥ x ≤ b ∧ ∀ v : ι → K, (∀ k ∈ tightRows A b x, (A *ᵥ v) k = 0) → v = 0 :=
  Iff.rfl

theorem isNondegenerateSystem_iff :
    IsNondegenerateSystem A b ↔ ∀ x, A *ᵥ x ≤ b → #(tightRows A b x) ≤ Fintype.card ι :=
  Iff.rfl

/-- A vertex is feasible. -/
theorem IsVertex.mulVec_le (h : IsVertex A b x) : A *ᵥ x ≤ b := h.1

theorem vertexAdj_iff [DecidableEq κ] :
    VertexAdj A b x y ↔ IsVertex A b x ∧ IsVertex A b y ∧ x ≠ y ∧
    Fintype.card ι ≤ #(tightRows A b x ∩ tightRows A b y) + 1 :=
  Iff.rfl

theorem VertexAdj.symm [DecidableEq κ] (h : VertexAdj A b x y) : VertexAdj A b y x :=
  ⟨h.2.1, h.1, h.2.2.1.symm, inter_comm (tightRows A b x) _ ▸ h.2.2.2⟩

theorem VertexAdj.ne [DecidableEq κ] (h : VertexAdj A b x y) : x ≠ y := h.2.2.1


/-- The linear map `v ↦ A *ᵥ v` followed by restriction to the rows in `s`. -/
private def restrictRows (A : Matrix κ ι K) (s : Finset κ) : (ι → K) →ₗ[K] (s → K) :=
  (LinearMap.funLeft K K ((↑) : s → κ)).comp (Matrix.mulVecLin A)

private theorem restrictRows_injective (h : IsVertex A b x) :
    Function.Injective (restrictRows A (tightRows A b x)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  exact h.2 v fun k hk => congrFun hv ⟨k, hk⟩

/-- A vertex has at least `card ι` tight rows. -/
theorem IsVertex.card_le_card_tightRows (h : IsVertex A b x) :
    Fintype.card ι ≤ #(tightRows A b x) := by
  have := LinearMap.finrank_le_finrank_of_injective (restrictRows_injective h)
  rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe] at this

/-- A vertex is the only point of the polyhedron's affine space on which its tight rows are tight:
if they are all tight at `y`, then `y = x`. -/
theorem IsVertex.eq_of_tightRows_subset (hx : IsVertex A b x)
    (h : tightRows A b x ⊆ tightRows A b y) : y = x := by
  have := hx.2 (y - x) fun k hk => by
    rw [mulVec_sub, Pi.sub_apply, mem_tightRows.1 hk, mem_tightRows.1 (h hk), sub_self]
  exact sub_eq_zero.1 this

/-- A vertex is determined by its set of tight rows. -/
theorem IsVertex.eq_of_tightRows_eq (hx : IsVertex A b x)
    (h : tightRows A b x = tightRows A b y) : x = y :=
  (hx.eq_of_tightRows_subset h.subset).symm

/-- A polyhedron has finitely many vertices. -/
theorem setOf_isVertex_finite : {x | IsVertex A b x}.Finite :=
  Set.Finite.of_finite_image (f := tightRows A b) (Set.toFinite _)
    fun _ hx _ _ h => IsVertex.eq_of_tightRows_eq hx h

/-- In a nondegenerate system, every vertex has exactly `card ι` tight rows. -/
theorem IsVertex.card_tightRows (hnd : IsNondegenerateSystem A b) (hx : IsVertex A b x) :
    #(tightRows A b x) = Fintype.card ι :=
  le_antisymm (hnd x hx.1) hx.card_le_card_tightRows

/-- If a point `y ≠ x` keeps all tight rows of the vertex `x` except `l` tight, then `l` is not
tight at `y`. -/
theorem IsVertex.notMem_tightRows_of_erase_subset [DecidableEq κ] (hx : IsVertex A b x) {l : κ}
    (hyx : y ≠ x) (hyT : (tightRows A b x).erase l ⊆ tightRows A b y) :
    l ∉ tightRows A b y := fun h =>
  hyx <| hx.eq_of_tightRows_subset fun k hk => by
    by_cases hkl : k = l
    · exact hkl ▸ h
    · exact hyT (mem_erase.2 ⟨hkl, hk⟩)

variable [IsStrictOrderedRing K]

omit [Fintype κ] in
/-- Ray shooting, the minimum ratio test: from a feasible `x`, moving in a direction `v` that
increases some row, the largest feasible step `t` makes some row `c` with `0 < (A *ᵥ v) c` tight. -/
private theorem exists_tight_add_smul [Finite κ] (hx : A *ᵥ x ≤ b) {v : ι → K} {c : κ}
    (hc : 0 < (A *ᵥ v) c) :
    ∃ t : K, ∃ c, 0 < (A *ᵥ v) c ∧ A *ᵥ (x + t • v) ≤ b ∧ (A *ᵥ (x + t • v)) c = b c := by
  have := Fintype.ofFinite κ
  have hs : ({k | 0 < (A *ᵥ v) k} : Finset κ).Nonempty := ⟨c, by simp [hc]⟩
  obtain ⟨c₀, hc₀s, hc₀⟩ :=
    exists_min_image _ (fun k => (b k - (A *ᵥ x) k) / (A *ᵥ v) k) hs
  have hpos : 0 < (A *ᵥ v) c₀ := by simpa using hc₀s
  refine ⟨(b c₀ - (A *ᵥ x) c₀) / (A *ᵥ v) c₀, c₀, hpos, fun k => ?_, ?_⟩
  · simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases le_or_gt ((A *ᵥ v) k) 0 with hk | hk
    · have := mul_nonpos_of_nonneg_of_nonpos (div_nonneg (sub_nonneg.2 (hx c₀)) hpos.le) hk
      linarith [hx k]
    · have := (le_div_iff₀ hk).1 (hc₀ k (by simp [hk]))
      linarith
  · simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- In a bounded nondegenerate system, a feasible point with at least `card ι` tight rows is a
vertex. -/
theorem isVertex_of_card_tightRows (hnd : IsNondegenerateSystem A b)
    (hrec : ∀ v, A *ᵥ v ≤ 0 → v = 0) (hx : A *ᵥ x ≤ b)
    (hcard : Fintype.card ι ≤ #(tightRows A b x)) : IsVertex A b x := by
  classical
  refine ⟨hx, fun v hv => ?_⟩
  by_contra hne
  have hv0 : ¬ A *ᵥ v ≤ 0 := fun h => hne (hrec v h)
  simp only [Pi.le_def, not_forall, not_le, Pi.zero_apply] at hv0
  obtain ⟨c, hc⟩ := hv0
  obtain ⟨t, c', hc', hle, htight⟩ := exists_tight_add_smul hx hc
  have hc'T : c' ∉ tightRows A b x := fun h => (hv c' h ▸ hc').false
  have hsub : insert c' (tightRows A b x) ⊆ tightRows A b (x + t • v) := by
    intro k hk
    rcases mem_insert.1 hk with rfl | hk
    · exact mem_tightRows.2 htight
    · rw [mem_tightRows, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, hv k hk, smul_zero,
        add_zero]
      exact mem_tightRows.1 hk
  have h1 := card_le_card hsub
  rw [card_insert_of_notMem hc'T] at h1
  have h2 := hnd _ hle
  omega

/-- The vertices of a bounded nondegenerate system are its feasible points with exactly `card ι`
tight rows. -/
theorem isVertex_iff_card_tightRows (hnd : IsNondegenerateSystem A b)
    (hrec : ∀ v, A *ᵥ v ≤ 0 → v = 0) :
    IsVertex A b x ↔ A *ᵥ x ≤ b ∧ #(tightRows A b x) = Fintype.card ι :=
  ⟨fun hx => ⟨hx.1, hx.card_tightRows hnd⟩,
    fun h => isVertex_of_card_tightRows hnd hrec h.1 h.2.ge⟩

variable [DecidableEq κ]

/-- **Pivoting, existence.** In a bounded nondegenerate system, for every tight row `l` of a vertex
`x` there is another vertex at which all other tight rows of `x` stay tight. -/
theorem IsVertex.exists_pivot (hnd : IsNondegenerateSystem A b)
    (hrec : ∀ v, A *ᵥ v ≤ 0 → v = 0) (hx : IsVertex A b x) {l : κ} (hl : l ∈ tightRows A b x) :
    ∃ y, IsVertex A b y ∧ y ≠ x ∧ (tightRows A b x).erase l ⊆ tightRows A b y := by
  set T := tightRows A b x with hTdef
  have hT : #T = Fintype.card ι := hx.card_tightRows hnd
  have hsurj : Function.Surjective (restrictRows A T) := by
    have hinj := restrictRows_injective hx
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
      hT]
  obtain ⟨v, hv⟩ := hsurj fun k => if (k : κ) = l then -1 else 0
  have hvT : ∀ k ∈ T, (A *ᵥ v) k = if k = l then -1 else 0 := fun k hk => congrFun hv ⟨k, hk⟩
  have hvl : (A *ᵥ v) l = -1 := by simpa using hvT l hl
  have hv0 : ¬ A *ᵥ v ≤ 0 := by
    intro h
    have := hrec v h
    subst this
    simp at hvl
  simp only [Pi.le_def, not_forall, not_le, Pi.zero_apply] at hv0
  obtain ⟨c, hc⟩ := hv0
  obtain ⟨t, c', hc', hle, htight⟩ := exists_tight_add_smul hx.1 hc
  have hc'T : c' ∉ T := by
    intro h
    have := hvT c' h
    split_ifs at this <;> linarith
  have hsub : insert c' (T.erase l) ⊆ tightRows A b (x + t • v) := by
    intro k hk
    rcases mem_insert.1 hk with rfl | hk
    · exact mem_tightRows.2 htight
    · obtain ⟨hkl, hkT⟩ := mem_erase.1 hk
      have hk0 : (A *ᵥ v) k = 0 := by simpa [hkl] using hvT k hkT
      rw [mem_tightRows, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, hk0, smul_zero,
        add_zero]
      exact mem_tightRows.1 hkT
  have hcard : Fintype.card ι ≤ #(tightRows A b (x + t • v)) := by
    have h1 := card_le_card hsub
    rw [card_insert_of_notMem (fun h => hc'T (mem_of_mem_erase h)), card_erase_of_mem hl, hT] at h1
    have : 0 < Fintype.card ι := hT ▸ card_pos.2 ⟨l, hl⟩
    omega
  refine ⟨x + t • v, isVertex_of_card_tightRows hnd hrec hle hcard, fun h => ?_,
    fun k hk => hsub (mem_insert_of_mem hk)⟩
  apply hc'T
  rw [h] at htight
  exact mem_tightRows.2 htight

/-- The direction from a vertex `x` to a pivot `y` (dropping `l`) strictly decreases row `l`, and
some row not tight at `x` becomes tight at `y` while strictly increasing. -/
private theorem IsVertex.pivot_aux (hnd : IsNondegenerateSystem A b) (hx : IsVertex A b x)
    {l : κ} (hl : l ∈ tightRows A b x) (hy : IsVertex A b y) (hyx : y ≠ x)
    (hyT : (tightRows A b x).erase l ⊆ tightRows A b y) :
    (A *ᵥ (y - x)) l < 0 ∧ ∃ c, 0 < (A *ᵥ (y - x)) c ∧ (A *ᵥ y) c = b c := by
  have hlnot := hx.notMem_tightRows_of_erase_subset hyx hyT
  have hl' : (A *ᵥ (y - x)) l < 0 := by
    rw [mulVec_sub, Pi.sub_apply, mem_tightRows.1 hl]
    exact sub_neg.2 (lt_of_le_of_ne (hy.1 l) (fun h => hlnot (mem_tightRows.2 h)))
  have : ¬ tightRows A b y ⊆ (tightRows A b x).erase l := by
    intro h
    have h1 := card_le_card h
    rw [card_erase_of_mem hl] at h1
    have h2 := hy.card_le_card_tightRows
    have h3 := hnd x hx.1
    have h4 : 0 < #(tightRows A b x) := card_pos.2 ⟨l, hl⟩
    omega
  obtain ⟨c, hcy, hcT⟩ := not_subset.1 this
  have hcT' : c ∉ tightRows A b x :=
    fun h => hcT (mem_erase.2 ⟨fun hcl => hlnot (hcl ▸ hcy), h⟩)
  refine ⟨hl', c, ?_, mem_tightRows.1 hcy⟩
  rw [mulVec_sub, Pi.sub_apply, mem_tightRows.1 hcy, sub_pos]
  exact lt_of_le_of_ne (hx.1 c) (fun h => hcT' (mem_tightRows.2 h))

/-- **Pivoting, uniqueness.** In a nondegenerate system, there is at most one vertex `y ≠ x` at
which all tight rows of the vertex `x` other than `l` stay tight. -/
theorem IsVertex.eq_of_erase_subset (hnd : IsNondegenerateSystem A b) (hx : IsVertex A b x)
    {l : κ} (hl : l ∈ tightRows A b x) {z : ι → K} (hy : IsVertex A b y) (hyx : y ≠ x)
    (hyT : (tightRows A b x).erase l ⊆ tightRows A b y) (hz : IsVertex A b z) (hzx : z ≠ x)
    (hzT : (tightRows A b x).erase l ⊆ tightRows A b z) : z = y := by
  obtain ⟨hyl, c, hc, hcy⟩ := hx.pivot_aux hnd hl hy hyx hyT
  obtain ⟨hzl, c', hc', hc'z⟩ := hx.pivot_aux hnd hl hz hzx hzT
  have hrow : ∀ {u}, (tightRows A b x).erase l ⊆ tightRows A b u →
      ∀ k ∈ tightRows A b x, k ≠ l → (A *ᵥ (u - x)) k = 0 := fun hu k hk hkl => by
    rw [mulVec_sub, Pi.sub_apply, mem_tightRows.1 (hu (mem_erase.2 ⟨hkl, hk⟩)),
      mem_tightRows.1 hk, sub_self]
  set s := (A *ᵥ (z - x)) l / (A *ᵥ (y - x)) l with hs
  have hw : z - x = s • (y - x) := by
    refine sub_eq_zero.1 (hx.2 _ fun k hk => ?_)
    rw [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hkl : k = l
    · subst hkl
      rw [hs, div_mul_cancel₀ _ hyl.ne, sub_self]
    · rw [hrow hyT k hk hkl, hrow hzT k hk hkl, mul_zero, sub_zero]
  have hspos : 0 < s := div_pos_of_neg_of_neg hzl hyl
  have hz' : z = x + s • (y - x) := by rw [← hw]; abel
  have hzc := hz.1 c
  have hyc' := hy.1 c'
  rw [hz', mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hzc hc'z
  rw [hw, mulVec_smul, Pi.smul_apply, smul_eq_mul] at hc'
  have hyc'' : (A *ᵥ (y - x)) c' + (A *ᵥ x) c' ≤ b c' := by
    rw [mulVec_sub, Pi.sub_apply]; linarith
  have hcy' : (A *ᵥ (y - x)) c = b c - (A *ᵥ x) c := by
    rw [mulVec_sub, Pi.sub_apply, hcy]
  have hpos' : 0 < (A *ᵥ (y - x)) c' := pos_of_mul_pos_right hc' hspos.le
  have h1 : s ≤ 1 := by nlinarith
  have h2 : 1 ≤ s := by nlinarith
  rw [hz', le_antisymm h1 h2, one_smul]
  abel

/-- The vertex reached from the vertex `x` by dropping its tight row `l`: the other vertex at which
all tight rows of `x` except `l` are tight. For a bounded nondegenerate system it exists and is
unique (`Matrix.IsVertex.pivotVertex_spec`, `Matrix.IsVertex.eq_pivotVertex`); otherwise the value
is unspecified. -/
noncomputable def pivotVertex (A : Matrix κ ι K) (b : κ → K) (x : ι → K) (l : κ) : ι → K :=
  Classical.epsilon fun y => IsVertex A b y ∧ y ≠ x ∧
    ∀ k ∈ tightRows A b x, k ≠ l → k ∈ tightRows A b y

/-- The pivot is a vertex different from `x` that keeps all tight rows of `x` except `l`. -/
theorem IsVertex.pivotVertex_spec (hnd : IsNondegenerateSystem A b)
    (hrec : ∀ v, A *ᵥ v ≤ 0 → v = 0) (hx : IsVertex A b x) {l : κ} (hl : l ∈ tightRows A b x) :
    IsVertex A b (pivotVertex A b x l) ∧ pivotVertex A b x l ≠ x ∧
      (tightRows A b x).erase l ⊆ tightRows A b (pivotVertex A b x l) := by
  obtain ⟨y, hy, hyx, hyT⟩ := hx.exists_pivot hnd hrec hl
  obtain ⟨h1, h2, h3⟩ := Classical.epsilon_spec (p := fun y => IsVertex A b y ∧ y ≠ x ∧
    ∀ k ∈ tightRows A b x, k ≠ l → k ∈ tightRows A b y)
    ⟨y, hy, hyx, fun k hk hkl => hyT (mem_erase.2 ⟨hkl, hk⟩)⟩
  exact ⟨h1, h2, fun k hk => h3 k (mem_erase.1 hk).2 (mem_erase.1 hk).1⟩

/-- Every vertex `y ≠ x` keeping all tight rows of `x` except `l` is the pivot. -/
theorem IsVertex.eq_pivotVertex (hnd : IsNondegenerateSystem A b)
    (hrec : ∀ v, A *ᵥ v ≤ 0 → v = 0) (hx : IsVertex A b x) {l : κ} (hl : l ∈ tightRows A b x)
    (hy : IsVertex A b y) (hyx : y ≠ x) (hyT : (tightRows A b x).erase l ⊆ tightRows A b y) :
    y = pivotVertex A b x l := by
  obtain ⟨h1, h2, h3⟩ := hx.pivotVertex_spec hnd hrec hl
  exact hx.eq_of_erase_subset hnd hl h1 h2 h3 hy hyx hyT

omit [DecidableEq κ] in
/-- The dropped row is not tight at the pivot. -/
theorem IsVertex.notMem_tightRows_pivotVertex (hnd : IsNondegenerateSystem A b)
    (hrec : ∀ v, A *ᵥ v ≤ 0 → v = 0) (hx : IsVertex A b x) {l : κ} (hl : l ∈ tightRows A b x) :
    l ∉ tightRows A b (pivotVertex A b x l) := by
  classical
  obtain ⟨-, h2, h3⟩ := hx.pivotVertex_spec hnd hrec hl
  exact hx.notMem_tightRows_of_erase_subset h2 h3

/-- In a bounded nondegenerate system, the neighbours of a vertex `x` are exactly its pivots. -/
theorem vertexAdj_iff_exists_pivotVertex (hnd : IsNondegenerateSystem A b)
    (hrec : ∀ v, A *ᵥ v ≤ 0 → v = 0) (hx : IsVertex A b x) :
    VertexAdj A b x y ↔ ∃ l ∈ tightRows A b x, y = pivotVertex A b x l := by
  constructor
  · rintro ⟨-, hy, hxy, hcard⟩
    have hTx := hx.card_tightRows hnd
    have hne : ¬ tightRows A b x ⊆ tightRows A b y :=
      fun h => hxy (hx.eq_of_tightRows_subset h).symm
    obtain ⟨l, hlx, hly⟩ := not_subset.1 hne
    refine ⟨l, hlx, hx.eq_pivotVertex hnd hrec hlx hy hxy.symm ?_⟩
    have hsub : tightRows A b x ∩ tightRows A b y ⊆ (tightRows A b x).erase l :=
      fun k hk => mem_erase.2 ⟨fun h => hly (h ▸ (mem_inter.1 hk).2), (mem_inter.1 hk).1⟩
    have heq := eq_of_subset_of_card_le hsub (by rw [card_erase_of_mem hlx]; omega)
    rw [← heq]
    exact inter_subset_right
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hx.pivotVertex_spec hnd hrec hl
    refine ⟨hx, h1, h2.symm, ?_⟩
    have := card_le_card (subset_inter (erase_subset l _) h3)
    rw [card_erase_of_mem hl, hx.card_tightRows hnd] at this
    omega

omit [DecidableEq κ] in
/-- Dropping different tight rows of a vertex leads to different pivots. -/
theorem IsVertex.pivotVertex_injOn (hnd : IsNondegenerateSystem A b)
    (hrec : ∀ v, A *ᵥ v ≤ 0 → v = 0) (hx : IsVertex A b x) :
    Set.InjOn (pivotVertex A b x) (tightRows A b x) := by
  classical
  intro l₁ hl₁ l₂ hl₂ h
  by_contra hne
  have h1 := hx.notMem_tightRows_pivotVertex hnd hrec hl₁
  have h2 := (hx.pivotVertex_spec hnd hrec hl₂).2.2 (mem_erase.2 ⟨hne, hl₁⟩)
  rw [← h] at h2
  exact h1 h2

end Matrix
