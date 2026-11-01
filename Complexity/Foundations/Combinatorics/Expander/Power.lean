/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Basic
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Powers of rotation maps

The `t`-th power `G ^ t` of a `D`-regular multigraph `G` has an edge for every walk of length `t` in
`G` [Reingold, Vadhan and Wigderson, Section 2.3][ReingoldVadhanWigderson2002]
[Arora and Barak, Section 21.3][AroraBarak09]. Its labels are the `t`-tuples of labels of `G`, and
its rotation map follows the walk and reverses it, so that the labels at the far end describe the
walk back. A step of the random walk on `G ^ t` is `t` steps of the random walk on `G`: the walk
operator of `G ^ t` is the `t`-th power of that of `G`, and `λ(G ^ t) = λ(G) ^ t` for `t ≠ 0`.

The bound `λ(G ^ t) ≤ λ(G) ^ t` holds as for any operator norm. For the reverse inequality, which
spectral theory would give at once, the second moments `a s = 𝔼 v, (G.walk ^ s) f v ^ 2` along the
walk from a function `f` are log-convex, as the walk operator is self-adjoint, so that
`a 0 * a 1 ^ t ≤ a 0 ^ t * a t`.

## Main definitions

* `Cslib.RotationMap.powRot`: the rotation map of the walks of length `t`.
* `Cslib.RotationMap.pow`: the `t`-th power `G ^ t`, with labels `Fin t → D`.

## Main results

* `Cslib.RotationMap.powRot_involutive`: reversing a walk twice gives it back.
* `Cslib.RotationMap.rot_pow_succ`, `Cslib.RotationMap.neighbor_pow_succ`,
  `Cslib.RotationMap.neighbor_pow_succ'`: a walk of length `t + 1` is a step followed by a walk of
  length `t`, and a walk of length `t` followed by a step.
* `Cslib.RotationMap.walk_pow`: the walk operator of `G ^ t` is the `t`-th power of that of `G`.
* `Cslib.RotationMap.spectralExpansion_pow_le`, `Cslib.RotationMap.spectralExpansion_pow`:
  `λ(G ^ t) ≤ λ(G) ^ t`, with equality for `t ≠ 0`.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V D : Type*}

/-- The rotation map of the walks of length `t` under `rotate`
[Reingold, Vadhan and Wigderson, Section 2.3][ReingoldVadhanWigderson2002]:
`powRot rotate t (v, k) = (w, ℓ)` when the walk from `v` along the labels `k 0, …, k (t - 1)` ends
at `w`, and `ℓ` lists the labels of its edges at their far ends, from the last edge back to the
first, so that `ℓ` labels the reverse walk from `w` to `v`. -/
def powRot (rotate : V × D → V × D) : (t : ℕ) → V × (Fin t → D) → V × (Fin t → D)
  | 0, p => p
  | t + 1, p =>
    let q := rotate (p.1, p.2 0)
    let r := powRot rotate t (q.1, Fin.tail p.2)
    (r.1, Fin.snoc r.2 q.2)

/-- A walk of length `0` is the identity. -/
@[simp]
theorem powRot_zero (rotate : V × D → V × D) (p : V × (Fin 0 → D)) : powRot rotate 0 p = p :=
  rfl

/-- A walk of length `t + 1` is a first step followed by a walk of length `t`. -/
theorem powRot_succ (rotate : V × D → V × D) (t : ℕ) (p : V × (Fin (t + 1) → D)) :
    powRot rotate (t + 1) p =
      ((powRot rotate t ((rotate (p.1, p.2 0)).1, Fin.tail p.2)).1,
        Fin.snoc (powRot rotate t ((rotate (p.1, p.2 0)).1, Fin.tail p.2)).2
          (rotate (p.1, p.2 0)).2) :=
  rfl

/-- A walk of length `t + 1` is a walk of length `t` followed by a last step. -/
private theorem powRot_succ' (rotate : V × D → V × D) (t : ℕ) (v : V) (k : Fin (t + 1) → D) :
    powRot rotate (t + 1) (v, k) =
      ((rotate ((powRot rotate t (v, Fin.init k)).1, k (Fin.last t))).1,
        Fin.cons (rotate ((powRot rotate t (v, Fin.init k)).1, k (Fin.last t))).2
          (powRot rotate t (v, Fin.init k)).2) := by
  induction t generalizing v with
  | zero =>
    refine Prod.ext rfl (funext fun i ↦ ?_)
    rw [Fin.fin_one_eq_zero i]
    rfl
  | succ t ih =>
    rw [powRot_succ, ih, powRot_succ rotate t (v, Fin.init k)]
    simp only [Fin.tail_init_eq_init_tail, Fin.cons_snoc_eq_snoc_cons]
    rfl

/-- Reversing a walk twice returns the original walk. -/
theorem powRot_involutive {rotate : V × D → V × D} (h : Function.Involutive rotate) :
    ∀ t, Function.Involutive (powRot rotate t)
  | 0 => fun _ ↦ rfl
  | t + 1 => fun p ↦ by
    rw [powRot_succ rotate t p, powRot_succ']
    simp [Fin.init_snoc, Fin.snoc_last, powRot_involutive h t _, h _]

variable (G : RotationMap V D)

/-- The **`t`-th power** `G ^ t`
[Reingold, Vadhan and Wigderson, Section 2.3][ReingoldVadhanWigderson2002]: the multigraph on the
same vertices with an edge for every walk of length `t` in `G`, labelled by the labels of its steps.
-/
def pow (t : ℕ) : RotationMap V (Fin t → D) where
  rot := powRot G.rot t
  rot_involutive := powRot_involutive G.rot_involutive t

/-- In `G ^ 0`, the rotation map is the identity. -/
@[simp]
theorem rot_pow_zero (p : V × (Fin 0 → D)) : (G.pow 0).rot p = p :=
  rfl

/-- In `G ^ (t + 1)`, the rotation map takes the first edge and then reverses the remaining walk,
appending the return label of the first edge at the end. -/
theorem rot_pow_succ (t : ℕ) (p : V × (Fin (t + 1) → D)) :
    (G.pow (t + 1)).rot p =
      (((G.pow t).rot ((G.rot (p.1, p.2 0)).1, Fin.tail p.2)).1,
        Fin.snoc ((G.pow t).rot ((G.rot (p.1, p.2 0)).1, Fin.tail p.2)).2
          (G.rot (p.1, p.2 0)).2) :=
  rfl

/-- In `G ^ 0`, every edge is a self-loop. -/
@[simp]
theorem neighbor_pow_zero (v : V) (k : Fin 0 → D) : (G.pow 0).neighbor v k = v :=
  rfl

/-- In `G ^ (t + 1)`, the walk along `k` takes the edge `k 0` and then the walk along the remaining
labels. -/
theorem neighbor_pow_succ (t : ℕ) (v : V) (k : Fin (t + 1) → D) :
    (G.pow (t + 1)).neighbor v k = (G.pow t).neighbor (G.neighbor v (k 0)) (Fin.tail k) :=
  rfl

/-- In `G ^ (t + 1)`, the walk along `k` takes the walk along all labels but the last, then the edge
labelled by the last. -/
theorem neighbor_pow_succ' (t : ℕ) (v : V) (k : Fin (t + 1) → D) :
    (G.pow (t + 1)).neighbor v k =
      G.neighbor ((G.pow t).neighbor v (Fin.init k)) (k (Fin.last t)) :=
  congrArg Prod.fst (powRot_succ' G.rot t v k)

variable [Fintype D]

/-- The walk operator of `G ^ t` is the `t`-th power of that of `G`. -/
theorem walk_pow (t : ℕ) : (G.pow t).walk = G.walk ^ t := by
  induction t with
  | zero => exact LinearMap.ext fun f ↦ funext fun v ↦ by simp [walk_apply]
  | succ t ih =>
    refine LinearMap.ext fun f ↦ funext fun v ↦ ?_
    rw [pow_succ', mul_apply_eq_comp, ← ih, walk_apply, walk_apply]
    simp only [neighbor_pow_succ, walk_apply]
    -- a tuple of `t + 1` labels is a first label and a tuple of `t` labels
    rw [Fin.expect_univ_cons]
    rfl

variable [Fintype V]

/-- The spectral expansion of `G ^ t` is at most `λ(G) ^ t`
[Reingold, Vadhan and Wigderson, Proposition 2.3][ReingoldVadhanWigderson2002]. -/
theorem spectralExpansion_pow_le (t : ℕ) :
    (G.pow t).spectralExpansion ≤ G.spectralExpansion ^ t := by
  refine spectralExpansion_le (pow_nonneg G.spectralExpansion_nonneg t) fun f hf ↦ ?_
  rw [walk_pow, ← pow_mul, mul_comm t]
  exact G.expect_walk_pow_sq_le_spectralExpansion_pow_mul hf t

/-- A nonnegative log-convex sequence grows at least geometrically with the ratio of its first two
terms: `a 0 * a 1 ^ t ≤ a 0 ^ t * a t`. -/
private theorem mul_pow_le_pow_mul_of_sq_le_mul {a : ℕ → ℝ} (ha : ∀ s, 0 ≤ a s)
    (h : ∀ s, a (s + 1) ^ 2 ≤ a s * a (s + 2)) (t : ℕ) : a 0 * a 1 ^ t ≤ a 0 ^ t * a t := by
  have hmono (s : ℕ) : a 1 * a s ≤ a 0 * a (s + 1) := by
    induction s with
    | zero => rw [mul_comm]
    | succ s ih =>
      rcases (ha (s + 1)).eq_or_lt with h0 | hpos
      · rw [← h0, mul_zero]
        exact mul_nonneg (ha 0) (ha _)
      · refine le_of_mul_le_mul_left ?_ hpos
        calc a (s + 1) * (a 1 * a (s + 1)) = a 1 * a (s + 1) ^ 2 := by ring
          _ ≤ a 1 * (a s * a (s + 2)) := mul_le_mul_of_nonneg_left (h s) (ha 1)
          _ = a 1 * a s * a (s + 2) := by ring
          _ ≤ a 0 * a (s + 1) * a (s + 2) := mul_le_mul_of_nonneg_right ih (ha _)
          _ = a (s + 1) * (a 0 * a (s + 1 + 1)) := by ring
  induction t with
  | zero => simp
  | succ t ih =>
    calc a 0 * a 1 ^ (t + 1) = a 1 * (a 0 * a 1 ^ t) := by ring
      _ ≤ a 1 * (a 0 ^ t * a t) := mul_le_mul_of_nonneg_left ih (ha 1)
      _ = a 0 ^ t * (a 1 * a t) := by ring
      _ ≤ a 0 ^ t * (a 0 * a (t + 1)) :=
        mul_le_mul_of_nonneg_left (hmono t) (pow_nonneg (ha 0) t)
      _ = a 0 ^ (t + 1) * a (t + 1) := by ring

/-- The second moments along the walk from a function are log-convex. -/
private theorem sq_expect_walk_pow_succ_sq_le (f : V → ℝ) (s : ℕ) :
    (𝔼 v, (G.walk ^ (s + 1)) f v ^ 2) ^ 2 ≤
      (𝔼 v, (G.walk ^ s) f v ^ 2) * 𝔼 v, (G.walk ^ (s + 2)) f v ^ 2 := by
  have h : 𝔼 v, (G.walk ^ (s + 1)) f v ^ 2 =
      𝔼 v, (G.walk ^ s) f v * (G.walk ^ (s + 2)) f v := by
    rw [show s + 2 = s + 1 + 1 from rfl, pow_succ' _ (s + 1), pow_succ' _ s]
    simp only [mul_apply_eq_comp, sq]
    exact (G.expect_mul_walk_comm _ _).symm
  rw [h]
  exact expect_mul_sq_le_sq_mul_sq _ _ _

/-- The spectral expansion of `G ^ t` is `λ(G) ^ t`, for `t ≠ 0`
[Reingold, Vadhan and Wigderson, Proposition 2.3][ReingoldVadhanWigderson2002]. -/
theorem spectralExpansion_pow {t : ℕ} (ht : t ≠ 0) :
    (G.pow t).spectralExpansion = G.spectralExpansion ^ t := by
  refine (G.spectralExpansion_pow_le t).antisymm ?_
  have hc := (G.pow t).spectralExpansion_nonneg
  suffices h : G.spectralExpansion ≤ (G.pow t).spectralExpansion ^ (t⁻¹ : ℝ) by
    calc G.spectralExpansion ^ t ≤ ((G.pow t).spectralExpansion ^ (t⁻¹ : ℝ)) ^ t := by
          have := G.spectralExpansion_nonneg
          gcongr
      _ = _ := Real.rpow_inv_natCast_pow hc ht
  refine spectralExpansion_le (by positivity) fun f hf ↦ ?_
  -- the second moments along the walk from `f` grow at least geometrically
  have key := mul_pow_le_pow_mul_of_sq_le_mul (a := fun s ↦ 𝔼 v, (G.walk ^ s) f v ^ 2)
    (fun s ↦ expect_nonneg fun v _ ↦ sq_nonneg _) (G.sq_expect_walk_pow_succ_sq_le f) t
  have hat := (G.pow t).expect_walk_sq_le_spectralExpansion_sq_mul hf
  simp only [pow_zero, pow_one, one_apply_eq_self] at key
  rw [walk_pow] at hat
  have h₀ : 0 ≤ 𝔼 v, f v ^ 2 := expect_nonneg fun v _ ↦ sq_nonneg (f v)
  rcases h₀.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact h0 ▸ G.expect_walk_sq_le f
  refine (pow_le_pow_iff_left₀ (expect_nonneg fun v _ ↦ sq_nonneg _) (by positivity) ht).1 ?_
  rw [mul_pow, ← pow_mul, mul_comm 2 t, pow_mul, Real.rpow_inv_natCast_pow hc ht]
  refine le_of_mul_le_mul_left ?_ hpos
  calc
    _ ≤ (𝔼 v, f v ^ 2) ^ t * ((G.pow t).spectralExpansion ^ 2 * 𝔼 v, f v ^ 2) :=
      key.trans (mul_le_mul_of_nonneg_left hat (pow_nonneg h₀ t))
    _ = _ := by ring


end Cslib.RotationMap
