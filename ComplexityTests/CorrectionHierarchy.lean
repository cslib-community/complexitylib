/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Foundations.LinearAlgebra.Matrix.CorrectionHierarchy

/-!
# Tests for corrections, copies and reward transport
-/

namespace ComplexityTests.CorrectionHierarchy

open Matrix

/-- A walk on three time layers: from `0` to `1` and from `1` to `2`, each with probability
`1 / 2`; it stops otherwise. -/
private def C : Matrix (Fin 3) (Fin 3) ℚ := !![0, 1 / 2, 0; 0, 0, 1 / 2; 0, 0, 0]

/-- The reward is collected at `2`. -/
private def e : Fin 3 → ℚ := ![0, 0, 1]

/-- The expected rewards: `1 / 4` from `0`, `1 / 2` from `1`. -/
private def p : Fin 3 → ℚ := ![1 / 4, 1 / 2, 1]

private theorem one_sub_C_mulVec_p : (1 - C) *ᵥ p = e := by
  ext i; fin_cases i <;>
    norm_num [C, p, e, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]

/-- The correction removes the second transition. -/
private def E : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, 0; 0, 0, 1 / 2; 0, 0, 0]

private theorem E_strict : E.IsStrictUpperTriangular := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [E]

-- The corrected matrix keeps only the first transition.
example : C - E + E * C = !![0, 1 / 2, 0; 0, 0, 0; 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [C, E]

-- The removed weight `1 / 2` reappears as a reward at `1`, and `p` still solves the corrected
-- equation.
example : (1 - (C - E + E * C)) *ᵥ p = ![0, 1 / 2, 1] := by
  rw [one_sub_correction_mulVec, one_sub_C_mulVec_p]
  ext i; fin_cases i <;> simp [E, e, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]

private theorem inv_one_sub_C : (1 - C)⁻¹ = 1 + C + C * C :=
  inv_eq_left_inv <| by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [C, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

-- The acceptance probabilities of the corrected walk with the corrected reward are those of
-- the original walk: `1 / 4` from `0`.
example : ((1 - (C - E + E * C))⁻¹ *ᵥ (e + E *ᵥ e)) 0 = 1 / 4 := by
  rw [E_strict.inv_one_sub_correction_mulVec, inv_one_sub_C]
  simp [C, e, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]
  norm_num

-- A nonnegative correction does not increase the row sums.
example : (C - E + E * C) *ᵥ 1 ≤ C *ᵥ 1 :=
  correction_mulVec_one_le (fun i j => by fin_cases i <;> fin_cases j <;> simp [E]) fun i => by
    fin_cases i <;> simp [C, mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

/-! ### Copies -/

/-- Both copies of every vertex are active. -/
private def r : Fin 2 → Fin 3 → ℚ := fun _ _ => 1

/-- Every entry is split evenly between the two copies of its target. -/
private def s : Fin 3 → Fin 3 → Fin 2 → ℚ := fun _ _ _ => 1 / 2

-- Splitting halves the entries and intertwines with the copy projection.
example : copySplit r s C ((0 : Fin 3), (0 : Fin 2)) ((1 : Fin 3), (1 : Fin 2)) = 1 / 4 := by
  norm_num [copySplit, r, s, C]

example : copySplit r s C * copyWeight r = copyWeight r * C :=
  copySplit_mul_copyWeight fun _ _ _ => by simp [r, s]

example : copySplit r s C *ᵥ 1 ≤ 1 :=
  copySplit_mulVec_one_le (fun _ _ => by simp [r]) (fun _ _ => le_rfl)
    (fun _ _ => by simp [s])
    (fun i j => by fin_cases i <;> fin_cases j <;> simp [C])
    fun i => by fin_cases i <;> norm_num [C, mulVec, dotProduct, Fin.sum_univ_three]

/-! ### Reward transport

A one-step hierarchy: the correction `C + C ^ 2` removes every transition of `C`, since
`C ^ 3 = 0`, so the stage-`1` matrix is zero and the stage-`1` reward is exact. -/

private def Cs (l : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := if l = 0 then C else 0

private def Es (l : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := if l = 0 then C + C * C else 0

private def Ps (_ : ℕ) : Matrix (Fin 3) (Fin 3) ℚ := 1

private theorem C_cube : C * C * C = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [C, Matrix.mul_apply, Fin.sum_univ_three]

private theorem hstep (l : ℕ) : Cs (l + 1) * Ps l = Ps l * (Cs l - Es l + Es l * Cs l) := by
  rcases l with _ | l
  · simp only [Cs, Es, Ps, ↓reduceIte, Nat.add_one_ne_zero, Matrix.zero_mul, Matrix.one_mul]
    rw [← C_cube]; noncomm_ring
  · simp [Cs, Es, Ps]

private theorem nonneg_C : ∀ i j, 0 ≤ C i j := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [C]

-- From `0`, the stage-`1` reward equals the acceptance probability `1 / 4`: the error bound is
-- the row sum of the zero matrix.
example : (rewardTransport (V := fun _ => Fin 3) Ps Es 1 *ᵥ e) 0 = 1 / 4 := by
  have h := sub_rewardTransport_mulVec_mem_Icc (V := fun _ => Fin 3) (C := Cs) (E := Es)
    (P := Ps) (z := fun _ => 0) (fun _ i j => by simp [Ps, Matrix.one_apply]; split_ifs <;> simp)
    (fun _ => by simp [Ps]) (fun l i j => by unfold Cs; split_ifs <;> simp [nonneg_C])
    hstep (p := p) (e := e) (by simpa [Cs] using one_sub_C_mulVec_p)
    (fun i => by fin_cases i <;> norm_num [p])
    (fun i => by fin_cases i <;> norm_num [p])
    (fun _ w => by simp [Ps, Matrix.one_apply, eq_comm]) 1
  have hp0 : p 0 = 1 / 4 := rfl
  simp only [Cs, Nat.add_one_ne_zero, ↓reduceIte, Matrix.zero_apply, Finset.sum_const_zero,
    Set.mem_Icc] at h
  linarith [h.1, h.2]

-- The transported rewards are nonnegative.
example : 0 ≤ rewardTransport (V := fun _ => Fin 3) Ps Es 1 *ᵥ e :=
  rewardTransport_mulVec_nonneg (V := fun _ => Fin 3)
    (fun _ i j => by simp only [Ps, Matrix.one_apply]; split_ifs <;> simp)
    (fun l i j => by
      unfold Es; split_ifs
      · fin_cases i <;> fin_cases j <;> norm_num [C, Matrix.mul_apply, Fin.sum_univ_three]
      · simp)
    (fun i => by fin_cases i <;> simp [e]) 1

end ComplexityTests.CorrectionHierarchy
