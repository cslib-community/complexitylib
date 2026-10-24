/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Complexity
public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Circuit complexity as a distance

Let `I` interpret a signature over a carrier `U` with an additive group structure, so that the
functions `(Fin n → U) → U` form a group under pointwise operations. The *difference distance*
`Cslib.Circuits.diffDist I c f g` is `0` when `f = g`, and otherwise the circuit complexity of
`f - g` plus a constant `c`. Two circuit facts make it a distance:

* combining two outputs by an operation costs at most the complexity of that operation on two
  inputs (`Cslib.Circuits.complexity_single_binary_le`). Since `f - h = (f - g) + (g - h)`, the
  triangle inequality holds once `c` pays for an addition circuit
  (`Cslib.Circuits.diffDist_triangle`);
* since `g - f = -(f - g)`, exchanging the arguments costs at most a negation circuit
  (`Cslib.Circuits.diffDist_comm_le`).

So `diffDist I c` is a right-translation-invariant quasi-metric when `c` is positive and pays for
addition. It need not be symmetric: over a complete basis in which negation costs a gate,
the projection `x ↦ x 0` is computed by no gates while its negation needs one. It is symmetric
when negation leaves complexity unchanged, as in a group of exponent two, where `-u = u`. A
negation circuit of cost zero only exists in that case, since circuits without gates compute
projections (`Cslib.Circuits.one_le_complexity_single`).

When `c` is positive and pays for addition, and negation leaves complexity unchanged, the map
sending `0` to `0` and every other `f` to `C(f) + c` is a norm on the group of functions
(`Cslib.Circuits.diffNorm`). For commutative groups its distance is the difference distance
(`Cslib.Circuits.dist_diffNorm`). Circuit complexity is then, up to the constant, a norm on a
translation-invariant metric group. Boolean functions with the De Morgan basis are the case
`c = 4`, with addition the exclusive or; see `Complexity.Computability.Circuit.Boolean.Metric`.

## Main definitions

* `Cslib.Circuits.diffDist`: the difference distance.
* `Cslib.Circuits.diffNorm`: the corresponding norm, under negation invariance.

## Main results

* `Cslib.Circuits.diffDist_eq_zero_iff`, `Cslib.Circuits.diffDist_triangle`,
  `Cslib.Circuits.diffDist_comm_le`: a quasi-metric.
* `Cslib.Circuits.diffDist_add_right`, `Cslib.Circuits.diffDist_add_left`: translation invariance.
* `Cslib.Circuits.diffDist_comm`: symmetry under negation invariance.
* `Cslib.Circuits.dist_diffNorm`: the norm induces the difference distance.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {U : Type*} {I : Interpretation σ U} [I.IsComplete] {n : ℕ}

/-! ### The difference distance -/

section AddGroup

variable [AddGroup U] {c : ℕ}

open Classical in
/-- The difference distance between `f` and `g`: `0` if they are equal, and otherwise the circuit
complexity of `f - g` plus `c`. -/
noncomputable def diffDist (I : Interpretation σ U) [I.IsComplete] (c : ℕ)
    (f g : (Fin n → U) → U) : ℕ :=
  if f = g then 0 else complexity I (single (f - g)) + c

/-- The difference distance from a function to itself is `0`. -/
@[simp] theorem diffDist_self (f : (Fin n → U) → U) : diffDist I c f f = 0 := by
  simp [diffDist]

/-- For distinct functions `f ≠ g`, `diffDist I c f g` is the circuit complexity of `f - g`
plus `c`. -/
theorem diffDist_of_ne {f g : (Fin n → U) → U} (h : f ≠ g) :
    diffDist I c f g = complexity I (single (f - g)) + c := by
  simp [diffDist, h]

/-- The difference distance separates functions when `c` is positive. -/
theorem diffDist_eq_zero_iff (hc : 0 < c) {f g : (Fin n → U) → U} :
    diffDist I c f g = 0 ↔ f = g := by
  refine ⟨fun h => ?_, fun h => h ▸ diffDist_self f⟩
  by_contra hfg
  rw [diffDist_of_ne hfg] at h
  omega

/-- The difference distance is invariant under translation on the right. -/
@[simp] theorem diffDist_add_right (f g a : (Fin n → U) → U) :
    diffDist I c (f + a) (g + a) = diffDist I c f g := by
  by_cases h : f = g
  · simp [h]
  rw [diffDist_of_ne h, diffDist_of_ne fun h' => h (add_right_cancel h'),
    add_sub_add_right_eq_sub]

/-- **The triangle inequality**, when `c` pays for a circuit adding two inputs. -/
theorem diffDist_triangle (hadd : complexity I (single fun y : Fin 2 → U => y 0 + y 1) ≤ c)
    (f g h : (Fin n → U) → U) : diffDist I c f h ≤ diffDist I c f g + diffDist I c g h := by
  by_cases hfg : f = g
  · simp [hfg]
  by_cases hgh : g = h
  · simp [hgh]
  by_cases hfh : f = h
  · simp [hfh]
  rw [diffDist_of_ne hfh, diffDist_of_ne hfg, diffDist_of_ne hgh]
  have hsum := complexity_single_binary_le (I := I) (· + ·) (f - g) (g - h)
  have heq : (fun x => (f - g) x + (g - h) x) = f - h :=
    funext fun x => by simp only [Pi.sub_apply, sub_add_sub_cancel]
  rw [heq] at hsum
  omega

/-- Exchanging the arguments costs at most a circuit negating its input. -/
theorem diffDist_comm_le {e : ℕ} (hneg : complexity I (single fun y : Fin 1 → U => -y 0) ≤ e)
    (f g : (Fin n → U) → U) : diffDist I c g f ≤ diffDist I c f g + e := by
  by_cases hfg : f = g
  · simp [hfg]
  rw [diffDist_of_ne (Ne.symm hfg), diffDist_of_ne hfg]
  have hneg' := complexity_single_unary_le (I := I) (fun u => -u) (f - g)
  have heq : (fun x => -(f - g) x) = g - f := funext fun x => by simp
  rw [heq] at hneg'
  omega

/-- The difference distance is symmetric when negation leaves complexity unchanged. -/
theorem diffDist_comm
    (hneg : ∀ f : (Fin n → U) → U, complexity I (single (-f)) = complexity I (single f))
    (f g : (Fin n → U) → U) : diffDist I c f g = diffDist I c g f := by
  by_cases hfg : f = g
  · simp [hfg]
  rw [diffDist_of_ne hfg, diffDist_of_ne (Ne.symm hfg), ← neg_sub, hneg]

end AddGroup

/-- The difference distance is invariant under translation on the left, for commutative
groups. -/
@[simp] theorem diffDist_add_left [AddCommGroup U] {c : ℕ} (a f g : (Fin n → U) → U) :
    diffDist I c (a + f) (a + g) = diffDist I c f g := by
  simp only [add_comm a, diffDist_add_right]

/-! ### The norm -/

section Norm

variable [AddGroup U] {c : ℕ}

open Classical in
/-- Circuit complexity as a norm: `0` at `0`, and otherwise the complexity plus `c`, when `c` is
positive and pays for a circuit adding two inputs, and negation leaves complexity unchanged. -/
noncomputable def diffNorm (I : Interpretation σ U) [I.IsComplete] (c : ℕ) (hc : 0 < c)
    (hadd : complexity I (single fun y : Fin 2 → U => y 0 + y 1) ≤ c)
    (hneg : ∀ f : (Fin n → U) → U, complexity I (single (-f)) = complexity I (single f)) :
    AddGroupNorm ((Fin n → U) → U) where
  toFun f := ((if f = 0 then 0 else complexity I (single f) + c : ℕ) : ℝ)
  map_zero' := by simp
  add_le' f g := by
    norm_cast
    by_cases hf : f = 0
    · simp [hf]
    by_cases hg : g = 0
    · simp [hg]
    by_cases hfg : f + g = 0
    · simp [hfg]
    simp only [hf, hg, hfg, ↓reduceIte]
    have := complexity_single_binary_le (I := I) (· + ·) f g
    change complexity I (single (f + g)) ≤ _ at this
    omega
  neg' f := by simp [hneg]
  eq_zero_of_map_eq_zero' f h := by
    by_contra hf
    simp only [hf, ↓reduceIte, Nat.cast_eq_zero] at h
    omega

/-- Applying `diffNorm` to `f` gives `diffDist I c f 0` cast to `ℝ`. -/
theorem diffNorm_apply {hc : 0 < c}
    {hadd : complexity I (single fun y : Fin 2 → U => y 0 + y 1) ≤ c}
    {hneg : ∀ f : (Fin n → U) → U, complexity I (single (-f)) = complexity I (single f)}
    (f : (Fin n → U) → U) :
    diffNorm I c hc hadd hneg f = ((diffDist I c f 0 : ℕ) : ℝ) := by
  classical
  change ((if f = 0 then 0 else complexity I (single f) + c : ℕ) : ℝ) = _
  rw [diffDist, sub_zero]

end Norm

/-- **The norm induces the difference distance** on the normed group of functions. -/
theorem dist_diffNorm [AddCommGroup U] {c : ℕ} (hc : 0 < c)
    (hadd : complexity I (single fun y : Fin 2 → U => y 0 + y 1) ≤ c)
    (hneg : ∀ f : (Fin n → U) → U, complexity I (single (-f)) = complexity I (single f))
    (f g : (Fin n → U) → U) :
    letI := (diffNorm I c hc hadd hneg).toNormedAddCommGroup
    dist f g = diffDist I c f g := by
  change diffNorm I c hc hadd hneg (-f + g) = _
  rw [← map_neg_eq_map (diffNorm I c hc hadd hneg) (-f + g), neg_add_rev, neg_neg,
    neg_add_eq_sub, diffNorm_apply, ← diffDist_add_right (c := c) f g (-g)]
  simp [sub_eq_add_neg]

end Cslib.Circuits
