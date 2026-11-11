/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, the Wronskian of a derivation)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination

/-!
# The Wronskian of a derivation

For a derivation `δ` of a commutative `F`-algebra `A` and a family `g : Fin r → A`, the
`δ`-Wronskian is the determinant of the matrix with entries `δ^[i] (g j)`. For `A = F[X]` and the
ordinary derivative this is the classical Wronskian.

If `A` is a domain and `F` is its field of constants, in the fraction-free form
`b * δ a = a * δ b → a ∈ F • b`, then the Wronskian of an `F`-linearly independent family is
nonzero (`Derivation.wronskian_ne_zero`). The proof is the classical induction on the size of the
family [Bhardwaj et al., Lemma 2.2 of the first version][BhardwajEtAl2026], with a kernel
vector over `A` instead of over its fraction field.

A derivation applied to a determinant is the sum of the determinants in which one column is
replaced by its derivative (`Derivation.map_det`).

## Main definitions

* `Derivation.wronskianMatrix`, `Derivation.wronskian`: the Wronskian of a family.

## Main results

* `Derivation.wronskian_ne_zero`: independent families have nonzero Wronskian.
* `Derivation.map_det`: the derivative of a determinant.

## References

* [S. Bhardwaj, F. Lakhani, P. Mukhopadhyay, R. Saptharishi, P. Shastri,
  A. K. Sinhababu, *Hitting sets from derivations: Waring rank and noncommutative
  ABPs*][BhardwajEtAl2026]
-/

@[expose] public section

namespace Derivation

open Matrix Finset

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A] (δ : Derivation F A A)

/-- The matrix with entries `δ^[i] (g j)`. -/
def wronskianMatrix {r : ℕ} (g : Fin r → A) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun i j => δ^[i] (g j)

/-- The `δ`-Wronskian of a family: the determinant of `δ^[i] (g j)`. -/
def wronskian {r : ℕ} (g : Fin r → A) : A := (δ.wronskianMatrix g).det

private theorem map_prod_erase {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → A) :
    δ (∏ i ∈ s, a i) = ∑ j ∈ s, (∏ i ∈ s.erase j, a i) * δ (a j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [prod_insert hk, leibniz, ih, sum_insert hk, erase_insert hk, smul_eq_mul, smul_eq_mul,
      mul_sum, add_comm]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    have hjk : k ≠ j := fun h => hk (h ▸ hj)
    rw [erase_insert_of_ne hjk, prod_insert (fun h => hk (mem_of_mem_erase h))]
    ring

/-- A derivation applied to a determinant is the sum over the columns of the determinant in
which that column is replaced by its derivative. -/
theorem map_det {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n A) :
    δ M.det = ∑ j, (M.updateCol j fun i => δ (M i j)).det := by
  simp only [det_apply', map_sum]
  rw [sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  have hsign : δ (((Equiv.Perm.sign σ : ℤ) : A) * ∏ i, M (σ i) i) =
      ((Equiv.Perm.sign σ : ℤ) : A) * δ (∏ i, M (σ i) i) := by
    rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  rw [hsign, map_prod_erase, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_prod_erase univ _ (mem_univ j), updateCol_self]
  have h : ∀ i ∈ univ.erase j, (M.updateCol j fun i => δ (M i j)) (σ i) i = M (σ i) i :=
    fun i hi => updateCol_ne (ne_of_mem_erase hi)
  rw [prod_congr rfl h]
  ring

/-- If `F` is the field of constants of `δ` on the domain `A`, the `δ`-Wronskian of an
`F`-linearly independent family is nonzero. -/
theorem wronskian_ne_zero {F : Type*} [Field F] [Algebra F A] (δ : Derivation F A A) [IsDomain A]
    (hδ : ∀ a b : A, b ≠ 0 → b * δ a = a * δ b → ∃ c : F, a = c • b) :
    ∀ {r : ℕ} {g : Fin r → A}, LinearIndependent F g → δ.wronskian g ≠ 0
  | 0, g, _ => by simp [wronskian]
  | r + 1, g, hg => by
    intro hW
    obtain ⟨v, hv0, hv⟩ := (exists_mulVec_eq_zero_iff (M := δ.wronskianMatrix g)).2 hW
    have hrow (i : Fin (r + 1)) : ∑ j, δ^[i] (g j) * v j = 0 := congrFun hv i
    have hM' := wronskian_ne_zero δ hδ (hg.comp _ (Fin.castSucc_injective r))
    -- the derivatives of the kernel vector are killed by all rows but the last
    have hrow' (i : Fin r) : ∑ j, δ^[i] (g j) * δ (v j) = 0 := by
      have h₁ := congrArg δ (hrow i.castSucc)
      rw [map_sum, map_zero] at h₁
      have h₂ := hrow i.succ
      simp only [Fin.val_succ, Function.iterate_succ_apply'] at h₂
      simp only [Fin.val_castSucc, leibniz, smul_eq_mul, sum_add_distrib] at h₁
      rwa [sum_congr rfl fun x _ => mul_comm (v x) (δ (δ^[i] (g x))), h₂, add_zero] at h₁
    have hkill {u : Fin (r + 1) → A} (hu : ∀ i : Fin r, ∑ j, δ^[i] (g j) * u j = 0)
        (hlast : u (Fin.last r) = 0) (j : Fin r) : u j.castSucc = 0 := by
      have h0 : (fun j : Fin r => u j.castSucc) = 0 :=
        eq_zero_of_mulVec_eq_zero hM' (funext fun i => by
          have h := hu i
          rw [Fin.sum_univ_castSucc, hlast, mul_zero, add_zero] at h
          exact h)
      exact congrFun h0 j
    set c := v (Fin.last r) with hc
    by_cases hc0 : c = 0
    · refine hv0 (funext fun j => ?_)
      induction j using Fin.lastCases with
      | last => exact hc0
      | cast j => exact hkill (fun i => hrow i.castSucc) hc0 j
    · have hprop (j : Fin (r + 1)) : c * δ (v j) = v j * δ c := by
        induction j using Fin.lastCases with
        | last => rw [← hc, mul_comm]
        | cast j =>
          have h := hkill (u := fun j => c * δ (v j) - δ c * v j)
            (fun i => by
              have h₁ := hrow' i
              have h₂ := hrow i.castSucc
              simp only [Fin.val_castSucc] at h₂
              simp only [mul_sub, sum_sub_distrib]
              have e₁ : ∑ j, δ^[i] (g j) * (c * δ (v j)) = c * ∑ j, δ^[i] (g j) * δ (v j) := by
                rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
              have e₂ : ∑ j, δ^[i] (g j) * (δ c * v j) = δ c * ∑ j, δ^[i] (g j) * v j := by
                rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
              rw [e₁, e₂, h₁, h₂, mul_zero, mul_zero, sub_zero])
            (by simp only [← hc]; ring) j
          linear_combination h
      choose l hl using fun j => hδ (v j) c hc0 (hprop j)
      have h0 := hrow 0
      simp only [Fin.val_zero, Function.iterate_zero, id_eq] at h0
      have hsum : c * ∑ j, l j • g j = 0 := by
        rw [mul_sum, ← h0]
        refine sum_congr rfl fun j _ => ?_
        rw [hl j, Algebra.smul_def, Algebra.smul_def]
        ring
      have hl0 := Fintype.linearIndependent_iff.1 hg l ((mul_eq_zero.1 hsum).resolve_left hc0)
      exact hv0 (funext fun j => by rw [hl j, hl0 j, zero_smul, Pi.zero_apply])

end Derivation
