/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily.Matrix
public import CslibFrontier.Probability.RejectionSampling
public import CslibFrontier.Probability.UniversalHash
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Probability.PMF.Uniform

/-!
# Hashing uniform integer boxes by modular matrices

Reduction modulo `q` is injective on `[-r,r]^m` when `2r < q`. For prime `q`, the existing
finite-field matrix universality and leftover-hash theorem therefore bound the joint law of the
public matrix and the image of an actual uniform box sample. The distance is half the L1 distance.

## Main results

* `intCast_injective_intBox`: reduction of bounded integer vectors is injective.
* `dist_intBox_mulVec_le`: an explicit joint leftover-hash bound for the box source.

These original finite-probability applications assume ideal uniform matrix and box sampling.
They do not assert an efficient sampler or a bound for every fixed public matrix.
-/

public section

namespace Cslib.Probability

open Cslib.Probability.PMF
open scoped Matrix ENNReal Cslib.Probability.PMF

/-- Integer vectors in a box of width at most `q` have distinct reductions modulo `q`. -/
theorem intCast_injective_intBox {m q r : ℕ} (hr : 2 * r < q) :
    Function.Injective (fun x : intBox (Fin m) r =>
      (Int.cast ∘ (x : Fin m → ℤ) : Fin m → ZMod q)) := by
  intro x y h
  apply Subtype.ext
  funext i
  have hd : (q : ℤ) ∣ (y : Fin m → ℤ) i - (x : Fin m → ℤ) i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun h i)
  have hx := abs_le.mp (mem_intBox.mp x.property i)
  have hy := abs_le.mp (mem_intBox.mp y.property i)
  have hq : 2 * (r : ℤ) < q := by exact_mod_cast hr
  have habs : |(y : Fin m → ℤ) i - (x : Fin m → ℤ) i| < q :=
    abs_lt.mpr ⟨by omega, by omega⟩
  exact (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd habs)).symm

/-- The public matrix is retained in the box-image leftover-hash bound. The bound averages over
the ideal uniform matrix; it need not hold after conditioning on a particular matrix. -/
theorem dist_intBox_mulVec_le (n m q r : ℕ) [Fact q.Prime] (hr : 2 * r < q) :
    dist
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun A =>
        (uniformOfFinset (intBox (Fin m) r) (intBox_nonempty r)).map
          (fun y => (A, A *ᵥ (Int.cast ∘ y))))
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun A =>
        (PMF.uniformOfFintype (Fin n → ZMod q)).map (A, ·)) ≤
      Real.sqrt ((q : ℝ) ^ n / ((2 * r + 1 : ℕ) : ℝ) ^ m) / 2 := by
  classical
  let : Nonempty (intBox (Fin m) r) := ⟨⟨0, zero_mem_intBox r⟩⟩
  have hh := (isDeltaUniversalHash_mulVec (ι := Fin n) (κ := Fin m)
    (F := ZMod q)).isTwoUniversal.precompose (intCast_injective_intBox hr)
  have h := IsTwoUniversal.leftover_hash_of_mass_le hh
    (PMF.uniformOfFintype (intBox (Fin m) r))
    (mass := (((2 * r + 1) ^ m : ℕ) : ℝ)⁻¹) (by
      intro x
      simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        Fintype.card_coe, card_intBox, Fintype.card_fin, le_refl])
  rw [← uniformOfFintype_finset_map_val (intBox (Fin m) r)]
  simpa only [seededHash, PMF.map_comp, Function.comp_def, Fintype.card_fun,
    Fintype.card_fin, ZMod.card, Nat.cast_pow, div_eq_mul_inv] using h

end Cslib.Probability
