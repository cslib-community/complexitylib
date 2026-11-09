/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, basis-coordinate lattice fibers)

public import CslibFrontier.Init
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Coefficient fibers of an integer lattice

Reducing the integer coordinates of a basis modulo a positive integer partitions a lattice
into translates of its pointwise scalar image. No primality, topology, or full-rank hypothesis
is needed.

## Main definitions

* `ZLattice.coefficientMod`: reduction of basis coordinates modulo an integer.
* `ZLattice.coefficientLift`: a lattice representative of each residue vector.
* `ZLattice.coefficientFiberEquiv`: translation from the scalar lattice to a residue fiber.

## Main results

* `ZLattice.coefficientMod_coefficientLift`: every residue vector has a representative.
* `ZLattice.coefficientMod_eq_zero_iff`: the kernel is the actual pointwise scalar image.
* `ZLattice.coefficientMod_eq_iff_sub_mem`: equal residues characterize lattice cosets.

## References

The coefficient fibers are used in [Regev2009], Lemma 3.11, printed pages 23–24 of the
May 2, 2009 author version. The algebraic statements here are independent of its analytic
and algorithmic assumptions.
-/

public section

noncomputable section

open scoped Pointwise

namespace ZLattice

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
variable (L : Submodule ℤ E) (b : Module.Basis ι ℤ L) (p : ℕ)

/-- Reduce the integer basis coordinates modulo `p`. -/
@[expose] def coefficientMod : L →+ (ι → ZMod p) where
  toFun v i := b.equivFun v i
  map_zero' := by ext i; simp
  map_add' v w := by ext i; simp

/-- The representative whose basis coordinates are the least nonnegative residue values. -/
@[expose] def coefficientLift (a : ι → ZMod p) : L :=
  b.equivFun.symm (fun i ↦ ((a i).val : ℤ))

omit [Module ℝ E] in
/-- Every residue vector is attained, including for composite moduli. -/
@[simp] theorem coefficientMod_coefficientLift [NeZero p] (a : ι → ZMod p) :
    coefficientMod L b p (coefficientLift L b p a) = a := by
  ext i
  change ((b.equivFun (b.equivFun.symm (fun i ↦ ((a i).val : ℤ))) i : ℤ) : ZMod p) = a i
  rw [b.equivFun.apply_symm_apply]
  simp

omit [Module ℝ E] in
/-- The coefficient reduction is surjective. -/
theorem coefficientMod_surjective [NeZero p] :
    Function.Surjective (coefficientMod L b p) :=
  fun a ↦ ⟨coefficientLift L b p a, coefficientMod_coefficientLift L b p a⟩

/-- The integer scalar image of a lattice is contained in the original lattice. -/
theorem natCast_smul_le : (p : ℝ) • L ≤ L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x (p : ℝ) L).mp hx
  rw [Nat.cast_smul_eq_nsmul]
  exact L.nsmul_mem hy p

/-- The zero coefficient fiber is the actual pointwise scalar image. -/
theorem coefficientMod_eq_zero_iff (v : L) :
    coefficientMod L b p v = 0 ↔ (v : E) ∈ (p : ℝ) • L := by
  constructor
  · intro hv
    have hd : ∀ i, (p : ℤ) ∣ b.equivFun v i := fun i ↦
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (congrFun hv i)
    choose q hq using hd
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨(b.equivFun.symm q : L), (b.equivFun.symm q).property, ?_⟩
    have he : (p : ℤ) • b.equivFun.symm q = v := by
      apply b.equivFun.injective
      ext i
      rw [map_smul, b.equivFun.apply_symm_apply]
      exact (hq i).symm
    have hc := congrArg (fun z : L ↦ (z : E)) he
    change (p : ℤ) • ((b.equivFun.symm q : L) : E) = (v : E) at hc
    simpa only [Nat.cast_smul_eq_nsmul] using hc
  · intro hv
    obtain ⟨y, hy, he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv
    have hv' : v = (p : ℤ) • (⟨y, hy⟩ : L) := by
      apply Subtype.ext
      change (v : E) = (p : ℤ) • y
      simpa only [Nat.cast_smul_eq_nsmul] using he.symm
    rw [hv']
    ext i
    change ((b.equivFun ((p : ℤ) • (⟨y, hy⟩ : L)) i : ℤ) : ZMod p) = 0
    rw [map_smul]
    simp

/-- Two coefficient vectors agree exactly when the lattice points differ by the scalar image. -/
theorem coefficientMod_eq_iff_sub_mem (v u : L) :
    coefficientMod L b p v = coefficientMod L b p u ↔
      (v : E) - (u : E) ∈ (p : ℝ) • L := by
  rw [← sub_eq_zero, ← map_sub, coefficientMod_eq_zero_iff]
  rfl

/-- Translation by the chosen representative identifies the scalar lattice with a coefficient
fiber. This equivalence carries counting sums without an index or covolume factor. -/
@[expose] def coefficientFiberEquiv [NeZero p] (a : ι → ZMod p) :
    ↥((p : ℝ) • L) ≃ {v : L // coefficientMod L b p v = a} where
  toFun w := ⟨⟨(w : E) + (coefficientLift L b p a : E),
    L.add_mem (natCast_smul_le L p w.property) (coefficientLift L b p a).property⟩, by
      apply Eq.trans _ (coefficientMod_coefficientLift L b p a)
      apply (coefficientMod_eq_iff_sub_mem L b p _ _).mpr
      simpa only [add_sub_cancel_right] using w.property⟩
  invFun v := ⟨(v.val : E) - (coefficientLift L b p a : E), by
    apply (coefficientMod_eq_iff_sub_mem L b p _ _).mp
    rw [v.property, coefficientMod_coefficientLift]⟩
  left_inv w := by ext; simp
  right_inv v := by ext; simp

/-- The fiber equivalence is the expected translation in the ambient space. -/
@[simp] theorem coe_coefficientFiberEquiv [NeZero p] (a : ι → ZMod p)
    (w : ↥((p : ℝ) • L)) :
    (((coefficientFiberEquiv L b p a w).val : L) : E) =
      (w : E) + (coefficientLift L b p a : E) := rfl

end ZLattice
