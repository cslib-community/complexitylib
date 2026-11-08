/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Interactive.GKR.Layered

/-!
# The GKR summand

For a point `z` of layer `i + 1`, the GKR protocol runs sumcheck on the polynomial
`f_z (y, w) = ãdd_i(z, y, w) (W̃_i(y) + W̃_i(w)) + m̃ult_i(z, y, w) W̃_i(y) W̃_i(w)` in the
`2 · width i` variables `(y, w)` (`Cslib.Interactive.GKR.LayeredCircuit.summand`). Its sum over the
cube is `W̃_{i+1}(z)` (`sum_eval_summand`, from the GKR identity), its value at any point is
computed from the wiring extensions and the two values `W̃_i(y)` and `W̃_i(w)` (`eval_summand`),
and each variable has degree at most two (`degreeOf_summand_le`), so each sumcheck round has
soundness error `2 / |F|` [Thaler, §4.6][Thaler2022].

## Main definitions

* `Cslib.Interactive.GKR.LayeredCircuit.summand`: the polynomial `f_z`.

## Main results

* `Cslib.Interactive.GKR.LayeredCircuit.eval_summand`: the value of `f_z` at `(y, w)`.
* `Cslib.Interactive.GKR.LayeredCircuit.sum_eval_summand`: the sum of `f_z` over the cube.
* `Cslib.Interactive.GKR.LayeredCircuit.degreeOf_summand_le`: every variable has degree at most
  two.

## References

* [J. Thaler, *Proofs, Arguments, and Zero-Knowledge*][Thaler2022], Section 4.6
-/

@[expose] public section

namespace Cslib.Interactive.GKR

open MvPolynomial Cslib.BitString

/-- The indicator polynomial of the bit string `a`, in the variables `e j`. -/
noncomputable def indicatorAt {R : Type*} [CommRing R] {k n : ℕ} (e : Fin k → Fin n)
    (a : Fin k → Bool) : MvPolynomial (Fin n) R :=
  ∏ j, if a j then X (e j) else 1 - X (e j)

section Indicator

variable {R : Type*} [CommRing R] {k n : ℕ}

theorem eval_indicatorAt (e : Fin k → Fin n) (a : Fin k → Bool) (v : Fin n → R) :
    eval v (indicatorAt e a : MvPolynomial (Fin n) R) = eval (v ∘ e) (indicatorPoly a) := by
  simp [indicatorAt, indicatorPoly, map_prod, apply_ite]

/-- The degree of a variable `v` in an indicator polynomial is at most the number of `j` with
`e j = v`. -/
theorem degreeOf_indicatorAt_le [Nontrivial R] (e : Fin k → Fin n) (a : Fin k → Bool)
    (v : Fin n) :
    (indicatorAt e a : MvPolynomial (Fin n) R).degreeOf v ≤ ∑ j, if e j = v then 1 else 0 := by
  classical
  refine (degreeOf_prod_le _ _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hX : (X (e j) : MvPolynomial (Fin n) R).degreeOf v ≤ if e j = v then 1 else 0 := by
    grind [degreeOf_X]
  by_cases ha : a j = true
  · rw [ite_eq_left ha]
    exact hX
  · rw [ite_eq_right ha]
    exact (degreeOf_sub_le _ _ _).trans (max_le (by simp [degreeOf_one]) hX)

end Indicator

/-- Every variable of `Fin (k + k)` lies in exactly one of the two halves. -/
theorem sum_castAdd_add_sum_natAdd {k : ℕ} (v : Fin (k + k)) :
    ((∑ j : Fin k, if Fin.castAdd k j = v then 1 else 0) +
      ∑ j : Fin k, if Fin.natAdd k j = v then 1 else 0) = 1 := by
  refine Fin.addCases (fun j₀ => ?_) (fun j₀ => ?_) v
  · rw [Finset.sum_eq_single j₀, Finset.sum_eq_zero]
    · simp
    · intro j _
      simp only [Fin.natAdd_eq_addNat, Fin.ext_iff, Fin.val_addNat, Fin.val_castAdd,
        ite_eq_right_iff, one_ne_zero, imp_false]
      omega
    · intro j _ hj
      simp [Fin.castAdd_inj, hj]
    · simp
  · rw [Finset.sum_eq_zero, Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
    · intro j _
      simp only [Fin.natAdd_eq_addNat, Fin.ext_iff, Fin.val_addNat, Fin.val_castAdd,
        ite_eq_right_iff, one_ne_zero, imp_false]
      omega

/-- A bit string of length `k + k` is a pair of bit strings of length `k`. -/
def splitEquiv (k : ℕ) : (Fin (k + k) → Bool) ≃ (Fin k → Bool) × (Fin k → Bool) where
  toFun x := (x ∘ Fin.castAdd k, x ∘ Fin.natAdd k)
  invFun p := Fin.append p.1 p.2
  left_inv x := Fin.append_castAdd_natAdd
  right_inv p := by
    ext j
    · exact Fin.append_left p.1 p.2 j
    · exact Fin.append_right p.1 p.2 j

namespace LayeredCircuit

variable (C : LayeredCircuit) {R : Type*} [CommRing R]

/-- The wiring extension of the gate kind `g`, as a polynomial in the in-neighbour variables, with
the gate of layer `i + 1` fixed to the point `z`. -/
noncomputable def wiringPoly (g : Gate) (i : ℕ) (z : Fin (C.width (i + 1)) → R) :
    MvPolynomial (Fin (C.width i + C.width i)) R :=
  ∑ a, if C.gate i a = g then
    MvPolynomial.C (eval z (indicatorPoly a)) *
      (indicatorAt (Fin.castAdd (C.width i)) (C.left i a) *
        indicatorAt (Fin.natAdd (C.width i)) (C.right i a))
  else 0

/-- The multilinear extension of the values `W` of layer `i`, in the variables `e j`. -/
noncomputable def valuePoly {k n : ℕ} (e : Fin k → Fin n) (W : (Fin k → Bool) → R) :
    MvPolynomial (Fin n) R :=
  ∑ a, MvPolynomial.C (W a) * indicatorAt e a

/-- **The GKR summand**
`f_z (y, w) = ãdd_i(z, y, w) (W̃(y) + W̃(w)) + m̃ult_i(z, y, w) W̃(y) W̃(w)`, for the values `W` of
layer `i` and a point `z` of layer `i + 1`. -/
noncomputable def summand (i : ℕ) (W : (Fin (C.width i) → Bool) → R)
    (z : Fin (C.width (i + 1)) → R) : MvPolynomial (Fin (C.width i + C.width i)) R :=
  C.wiringPoly .add i z * (valuePoly (Fin.castAdd _) W + valuePoly (Fin.natAdd _) W) +
    C.wiringPoly .mul i z * (valuePoly (Fin.castAdd _) W * valuePoly (Fin.natAdd _) W)

theorem eval_valuePoly_castAdd {k : ℕ} (W : (Fin k → Bool) → R) (y w : Fin k → R) :
    eval (Fin.append y w) (valuePoly (Fin.castAdd k) W) = eval y (multilinearExtension W) := by
  have : (Fin.append y w ∘ Fin.castAdd k) = y := funext fun j => Fin.append_left y w j
  simp [valuePoly, eval_indicatorAt, this, eval_multilinearExtension_eq_sum]

theorem eval_valuePoly_natAdd {k : ℕ} (W : (Fin k → Bool) → R) (y w : Fin k → R) :
    eval (Fin.append y w) (valuePoly (Fin.natAdd k) W) = eval w (multilinearExtension W) := by
  have : (Fin.append y w ∘ Fin.natAdd k) = w := funext fun j => Fin.append_right y w j
  simp [valuePoly, eval_indicatorAt, this, eval_multilinearExtension_eq_sum]

/-- The wiring polynomial at `(y, w)` is the multilinear extension of the wiring predicate at
`(z, y, w)`. -/
theorem eval_wiringPoly (g : Gate) (i : ℕ) (z : Fin (C.width (i + 1)) → R)
    (y w : Fin (C.width i) → R) :
    eval (Fin.append y w) (C.wiringPoly g i z) =
      eval (Sum.elim z (Sum.elim y w)) (multilinearExtension (C.wiringPred (R := R) g i)) := by
  have hl : (Fin.append y w ∘ Fin.castAdd (C.width i)) = y :=
    funext fun j => Fin.append_left y w j
  have hr : (Fin.append y w ∘ Fin.natAdd (C.width i)) = w :=
    funext fun j => Fin.append_right y w j
  rw [eval_multilinearExtension_wiringPred, wiringPoly, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · simp [eval_indicatorAt, hl, hr, mul_assoc]
  · simp

/-- **The value of the GKR summand** at `(y, w)`, from the wiring extensions and the values of the
multilinear extension of layer `i` at `y` and `w`. -/
theorem eval_summand (i : ℕ) (W : (Fin (C.width i) → Bool) → R) (z : Fin (C.width (i + 1)) → R)
    (y w : Fin (C.width i) → R) :
    eval (Fin.append y w) (C.summand i W z) =
      eval (Sum.elim z (Sum.elim y w)) (multilinearExtension (C.addPred (R := R) i)) *
          (eval y (multilinearExtension W) + eval w (multilinearExtension W)) +
        eval (Sum.elim z (Sum.elim y w)) (multilinearExtension (C.multPred (R := R) i)) *
          (eval y (multilinearExtension W) * eval w (multilinearExtension W)) := by
  simp only [summand, map_add, map_mul, eval_wiringPoly, eval_valuePoly_castAdd,
    eval_valuePoly_natAdd]

/-- **The sum of the GKR summand** over the cube is the multilinear extension of layer `i + 1` at
`z`. -/
theorem sum_eval_summand (i : ℕ) (W : (Fin (C.width i) → Bool) → R)
    (z : Fin (C.width (i + 1)) → R) :
    ∑ b : Fin (C.width i + C.width i) → Bool, eval (bitPoint b) (C.summand i W z) =
      eval z (multilinearExtension (C.step i W)) := by
  rw [eval_multilinearExtension_step]
  have hsplit : ∀ b : Fin (C.width i + C.width i) → Bool, (bitPoint b : _ → R) =
      Fin.append (bitPoint (b ∘ Fin.castAdd _)) (bitPoint (b ∘ Fin.natAdd _)) := by
    intro b
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]
      rfl
    · rw [Fin.append_right]
      rfl
  simp only [hsplit, eval_summand, eval_multilinearExtension]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (splitEquiv _) _ _ fun _ => rfl
section Degree

variable [Nontrivial R]

theorem degreeOf_valuePoly_le {k n : ℕ} (e : Fin k → Fin n) (W : (Fin k → Bool) → R)
    (v : Fin n) : (valuePoly e W).degreeOf v ≤ ∑ j, if e j = v then 1 else 0 :=
  (degreeOf_sum_le _ _ _).trans <| Finset.sup_le fun a _ =>
    (degreeOf_C_mul_le _ _ _).trans (degreeOf_indicatorAt_le e a v)

theorem degreeOf_wiringPoly_le (g : Gate) (i : ℕ) (z : Fin (C.width (i + 1)) → R)
    (v : Fin (C.width i + C.width i)) : (C.wiringPoly g i z).degreeOf v ≤ 1 := by
  refine (degreeOf_sum_le _ _ _).trans <| Finset.sup_le fun a _ => ?_
  split_ifs
  · refine (degreeOf_C_mul_le _ _ _).trans ((degreeOf_mul_le _ _ _).trans ?_)
    rw [← sum_castAdd_add_sum_natAdd v]
    exact add_le_add (degreeOf_indicatorAt_le _ _ v) (degreeOf_indicatorAt_le _ _ v)
  · simp

/-- **Every variable of the GKR summand has degree at most two.** -/
theorem degreeOf_summand_le (i : ℕ) (W : (Fin (C.width i) → Bool) → R)
    (z : Fin (C.width (i + 1)) → R) (v : Fin (C.width i + C.width i)) :
    (C.summand i W z).degreeOf v ≤ 2 := by
  have hl := degreeOf_valuePoly_le (Fin.castAdd (C.width i)) W v
  have hr := degreeOf_valuePoly_le (Fin.natAdd (C.width i)) W v
  have h1 := sum_castAdd_add_sum_natAdd v
  refine (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  · have hw := C.degreeOf_wiringPoly_le .add i z v
    have hs := degreeOf_add_le v (valuePoly (Fin.castAdd (C.width i)) W)
      (valuePoly (Fin.natAdd (C.width i)) W)
    refine (degreeOf_mul_le _ _ _).trans ?_
    have : max (degreeOf v (valuePoly (Fin.castAdd (C.width i)) W))
        (degreeOf v (valuePoly (Fin.natAdd (C.width i)) W)) ≤ 1 := max_le (by omega) (by omega)
    omega
  · have hw := C.degreeOf_wiringPoly_le .mul i z v
    have hs := degreeOf_mul_le v (valuePoly (Fin.castAdd (C.width i)) W)
      (valuePoly (Fin.natAdd (C.width i)) W)
    refine (degreeOf_mul_le _ _ _).trans ?_
    omega

end Degree

end LayeredCircuit

end Cslib.Interactive.GKR
