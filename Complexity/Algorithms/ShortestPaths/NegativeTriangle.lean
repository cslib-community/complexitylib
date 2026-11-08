/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Algebra.Tropical
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Mul

/-!
# Negative triangles

A weighted tripartite graph with parts `I`, `J`, `K` is given by three matrices over
`MinTropical R`: `A : Matrix I K _` holds the weights of the edges between `I` and `K`,
`B : Matrix K J _` those between `K` and `J`, and `C : Matrix I J _` those between `I` and `J`. The
tropical zero `0 = ⊤` means that there is no edge. A triple `(i, j, k)` is a *negative triangle*
if `w(i, k) + w(k, j) + w(i, j) < 0` in `R`; a missing edge has weight `⊤`, so a negative
triangle uses three edges. This is the negative triangle problem of Vassilevska Williams and
Williams over the (min,+) structure, in its tripartite form (Section 2, "Negative Triangles Over
Structures").

The pair `(i, j)` lies on a negative triangle exactly when `(A * B) i j + C i j < 0`, because the
(min,+) product entry `(A * B) i j` is the minimum of `w(i, k) + w(k, j)` over `k`
(`onNegTriangle_iff`). This is the link between negative triangles and (min,+) products used in
both directions of the equivalence.

Padding a graph with isolated vertices (`padIsolated`) creates no negative triangles
(`onNegTriangle_padIsolated`); it lets the blocking reduction run on any number of vertices.

## Main definitions

* `Cslib.Algorithms.ShortestPaths.IsNegTriangle`, `OnNegTriangle`, `HasNegTriangle`: a negative
  triangle; a pair on a negative triangle; a graph with a negative triangle.
* `Cslib.Algorithms.ShortestPaths.IsNegTriangleAnswer`: the specification of negative triangle
  finding.
* `Cslib.Algorithms.ShortestPaths.padIsolated`: add isolated vertices.
* `Cslib.Algorithms.ShortestPaths.FiniteEntriesBounded`: every finite entry lies in `[-W, W]`.

## Main results

* `Cslib.Algorithms.ShortestPaths.onNegTriangle_iff`: `(i, j)` lies on a negative triangle iff
  `(A * B) i j + C i j < 0`.
* `Cslib.Algorithms.ShortestPaths.hasNegTriangle_iff`: the graph has a negative triangle iff some
  `(A * B) i j + C i j < 0`.
* `Cslib.Algorithms.ShortestPaths.onNegTriangle_padIsolated`: padding preserves negative triangles.
* `Cslib.Algorithms.ShortestPaths.FiniteEntriesBounded.mul`: finite entries of a (min,+) product
  of matrices with finite entries in `[-M, M]` lie in `[-2M, 2M]`.

## References

* [Vassilevska Williams and Williams, *Subcubic Equivalences Between Path, Matrix, and Triangle
  Problems*][VassilevskaWilliamsWilliams2018], Section 2.
-/

public section

open MinTropical

namespace Cslib.Algorithms.ShortestPaths

variable {R : Type*} [LinearOrderedAddCommMonoidWithTop R] {I J K : Type*}

/-- `(i, j, k)` is a negative triangle of the tripartite graph `(A, B, C)`: the weights of the
edges `i k`, `k j` and `i j` add up to a negative number. -/
@[expose] def IsNegTriangle (A : Matrix I K (MinTropical R)) (B : Matrix K J (MinTropical R))
    (C : Matrix I J (MinTropical R)) (i : I) (j : J) (k : K) : Prop :=
  untrop (A i k) + untrop (B k j) + untrop (C i j) < 0

/-- The pair `(i, j)` lies on a negative triangle. -/
@[expose] def OnNegTriangle (A : Matrix I K (MinTropical R)) (B : Matrix K J (MinTropical R))
    (C : Matrix I J (MinTropical R)) (i : I) (j : J) : Prop :=
  ∃ k, IsNegTriangle A B C i j k

/-- The tripartite graph `(A, B, C)` has a negative triangle. -/
@[expose] def HasNegTriangle (A : Matrix I K (MinTropical R)) (B : Matrix K J (MinTropical R))
    (C : Matrix I J (MinTropical R)) : Prop :=
  ∃ i j k, IsNegTriangle A B C i j k

/-- The specification of negative triangle finding: `none` means that there is no negative
triangle, and `some (i, j, k)` means that `(i, j, k)` is one. -/
@[expose] def IsNegTriangleAnswer (A : Matrix I K (MinTropical R))
    (B : Matrix K J (MinTropical R)) (C : Matrix I J (MinTropical R)) :
    Option (I × J × K) → Prop
  | none => ¬ HasNegTriangle A B C
  | some (i, j, k) => IsNegTriangle A B C i j k

instance (A : Matrix I K (MinTropical R)) (B : Matrix K J (MinTropical R))
    (C : Matrix I J (MinTropical R)) (i : I) (j : J) (k : K) :
    Decidable (IsNegTriangle A B C i j k) :=
  inferInstanceAs (Decidable (_ < _))

instance [Fintype K] (A : Matrix I K (MinTropical R)) (B : Matrix K J (MinTropical R))
    (C : Matrix I J (MinTropical R)) (i : I) (j : J) : Decidable (OnNegTriangle A B C i j) :=
  inferInstanceAs (Decidable (∃ _, _))

instance [Fintype I] [Fintype J] [Fintype K] (A : Matrix I K (MinTropical R))
    (B : Matrix K J (MinTropical R)) (C : Matrix I J (MinTropical R)) :
    Decidable (HasNegTriangle A B C) :=
  inferInstanceAs (Decidable (∃ _, _))

theorem IsNegTriangle.ne_zero_left {A : Matrix I K (MinTropical R)}
    {B : Matrix K J (MinTropical R)} {C : Matrix I J (MinTropical R)} {i : I} {j : J} {k : K}
    (h : IsNegTriangle A B C i j k) : A i k ≠ 0 := by
  intro h0
  rw [IsNegTriangle, h0, untrop_zero, top_add, top_add] at h
  exact not_top_lt h

theorem IsNegTriangle.ne_zero_right {A : Matrix I K (MinTropical R)}
    {B : Matrix K J (MinTropical R)} {C : Matrix I J (MinTropical R)} {i : I} {j : J} {k : K}
    (h : IsNegTriangle A B C i j k) : C i j ≠ 0 := by
  intro h0
  rw [IsNegTriangle, h0, untrop_zero, add_top] at h
  exact not_top_lt h

/-- Relabelling the three parts maps negative triangles to negative triangles. -/
theorem isNegTriangle_submatrix {I' J' K' : Type*} (A : Matrix I K (MinTropical R))
    (B : Matrix K J (MinTropical R)) (C : Matrix I J (MinTropical R)) (f : I' → I) (g : J' → J)
    (h : K' → K) (i : I') (j : J') (k : K') :
    IsNegTriangle (A.submatrix f h) (B.submatrix h g) (C.submatrix f g) i j k ↔
      IsNegTriangle A B C (f i) (g j) (h k) :=
  Iff.rfl

/-! ### Padding with isolated vertices -/

section Pad

variable {α : Type*} [Zero α] {I₀ I₁ J₀ J₁ U V : Type*}

/-- Add isolated vertices: `padIsolated e e' A` is `A` on the image of `Sum.inl` and `0` (no edge)
elsewhere, relabelled along `e : U ≃ I₀ ⊕ I₁` and `e' : V ≃ J₀ ⊕ J₁`. -/
@[expose] def padIsolated (e : U ≃ I₀ ⊕ I₁) (e' : V ≃ J₀ ⊕ J₁) (A : Matrix I₀ J₀ α) :
    Matrix U V α :=
  (Matrix.fromBlocks A 0 0 0).submatrix e e'

theorem padIsolated_apply_inl (e : U ≃ I₀ ⊕ I₁) (e' : V ≃ J₀ ⊕ J₁) (A : Matrix I₀ J₀ α)
    (i : I₀) (j : J₀) : padIsolated e e' A (e.symm (.inl i)) (e'.symm (.inl j)) = A i j := by
  simp [padIsolated]

theorem padIsolated_apply_eq_zero (e : U ≃ I₀ ⊕ I₁) (e' : V ≃ J₀ ⊕ J₁) (A : Matrix I₀ J₀ α)
    {u : U} {v : V} (h : padIsolated e e' A u v ≠ 0) :
    ∃ i j, e u = .inl i ∧ e' v = .inl j := by
  simp only [padIsolated, Matrix.submatrix_apply] at h
  rcases hu : e u with i | i <;> rcases hv : e' v with j | j <;>
    simp_all [Matrix.fromBlocks]

end Pad

variable {I₁ J₁ K₁ U V W : Type*}

/-- **Isolated vertices create no negative triangles.** After padding all three parts, the
pairs of original vertices on a negative triangle are exactly the original ones. -/
theorem onNegTriangle_padIsolated (eI : U ≃ I ⊕ I₁) (eJ : V ≃ J ⊕ J₁)
    (eK : W ≃ K ⊕ K₁) (A : Matrix I K (MinTropical R)) (B : Matrix K J (MinTropical R))
    (C : Matrix I J (MinTropical R)) (i : I) (j : J) :
    OnNegTriangle (padIsolated eI eK A) (padIsolated eK eJ B) (padIsolated eI eJ C)
        (eI.symm (.inl i)) (eJ.symm (.inl j)) ↔ OnNegTriangle A B C i j := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨-, k, -, hk⟩ := padIsolated_apply_eq_zero eI eK A hw.ne_zero_left
    refine ⟨k, ?_⟩
    have hw' : eK.symm (.inl k) = w := by rw [← hk, Equiv.symm_apply_apply]
    rw [← hw', IsNegTriangle, padIsolated_apply_inl, padIsolated_apply_inl,
      padIsolated_apply_inl] at hw
    exact hw
  · rintro ⟨k, hk⟩
    refine ⟨eK.symm (.inl k), ?_⟩
    rw [IsNegTriangle, padIsolated_apply_inl, padIsolated_apply_inl, padIsolated_apply_inl]
    exact hk

variable [Fintype K]

/-- **Negative triangles and (min,+) products.** The pair `(i, j)` lies on a negative triangle
iff `(A * B) i j + C i j < 0`. -/
theorem onNegTriangle_iff (A : Matrix I K (MinTropical R)) (B : Matrix K J (MinTropical R))
    (C : Matrix I J (MinTropical R)) (i : I) (j : J) :
    OnNegTriangle A B C i j ↔ untrop ((A * B) i j) + untrop (C i j) < 0 := by
  rw [Matrix.mul_apply]
  constructor
  · rintro ⟨k, hk⟩
    refine lt_of_le_of_lt (add_le_add ?_ le_rfl) hk
    rw [← untrop_mul, untrop_le_iff]
    exact sum_le_of_mem (fun k => A i k * B k j) (Finset.mem_univ k)
  · intro h
    rcases isEmpty_or_nonempty K with hK | hK
    · rw [Finset.univ_eq_empty, Finset.sum_empty, untrop_zero, top_add] at h
      exact absurd h not_top_lt
    obtain ⟨k, -, hk⟩ := exists_sum_eq Finset.univ_nonempty (fun k => A i k * B k j)
    rw [hk, untrop_mul] at h
    exact ⟨k, h⟩

/-- The tripartite graph has a negative triangle iff `(A * B) i j + C i j < 0` for some
`(i, j)`. -/
theorem hasNegTriangle_iff (A : Matrix I K (MinTropical R)) (B : Matrix K J (MinTropical R))
    (C : Matrix I J (MinTropical R)) :
    HasNegTriangle A B C ↔ ∃ i j, untrop ((A * B) i j) + untrop (C i j) < 0 := by
  simp only [← onNegTriangle_iff]
  rfl

/-! ### Bounded entries -/

/-- Every finite entry of `A` lies in `[-W, W]`; `⊤` (no edge) entries are allowed. This is the
weight range `{-W, …, W} ∪ {∞}` of Vassilevska Williams and Williams with maxint `W`, without
`-∞`. -/
@[expose] def FiniteEntriesBounded {I J : Type*} (A : Matrix I J (MinTropical (WithTop ℤ)))
    (W : ℕ) : Prop :=
  ∀ i j (x : ℤ), untrop (A i j) = x → |x| ≤ W

/-- If the finite entries of `A` and `B` lie in `[-M, M]`, those of the (min,+) product `A * B`
lie in `[-2M, 2M]`. -/
theorem FiniteEntriesBounded.mul {A : Matrix I K (MinTropical (WithTop ℤ))}
    {B : Matrix K J (MinTropical (WithTop ℤ))} {M : ℕ} (hA : FiniteEntriesBounded A M)
    (hB : FiniteEntriesBounded B M) : FiniteEntriesBounded (A * B) (2 * M) := by
  intro i j x hx
  rw [Matrix.mul_apply] at hx
  rcases isEmpty_or_nonempty K with hK | hK
  · rw [Finset.univ_eq_empty, Finset.sum_empty, untrop_zero] at hx
    exact absurd hx WithTop.top_ne_coe
  obtain ⟨k, -, hk⟩ := exists_sum_eq Finset.univ_nonempty (fun k => A i k * B k j)
  rw [hk, untrop_mul] at hx
  obtain ⟨a, b, ha, hb, rfl⟩ := WithTop.add_eq_coe.1 hx
  have h1 := hA i k a ha.symm
  have h2 := hB k j b hb.symm
  push_cast
  calc |a + b| ≤ |a| + |b| := abs_add_le a b
    _ ≤ M + M := add_le_add h1 h2
    _ = 2 * M := (two_mul _).symm

end Cslib.Algorithms.ShortestPaths
