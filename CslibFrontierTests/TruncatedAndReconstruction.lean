/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.TruncatedAlgebraBridge
public import CslibFrontier.Foundations.Data.Polynomial.RationalReconstruction
public import CslibFrontier.Foundations.Data.Polynomial.TruncatedAlgebra
public import CslibFrontier.Foundations.Data.Polynomial.TruncatedJetBridge
public import CslibFrontier.Foundations.Data.Rat.Reconstruction

/-!
# Truncated polynomial algebra and rational / finite-field reconstruction clients

Strict `module` kernel-checked examples exercising `Polynomial.Truncated R r`, `Rat.reconstruct`,
`Rat.reconstructPi`, and `Polynomial.PolyRat.reconstruct` / `Polynomial.PolyRat.cauchy`,
including exposed body unfolding (`geomInv`, `unitInv`, `subst`, `substZeroConst`, `toPoly`,
`coeffs`, `Rat.height`, `PolyRat.height`), non-unit and bound-failure boundary cases, and
bridges to `JetTable` and `B_{P,ℓ}`.
-/

public section

namespace CslibFrontierTests.TruncatedAndReconstruction

section TruncatedAlgebraTests

open Polynomial (Truncated)
open Polynomial.Truncated

example :
    let T := var ℤ 4
    let f : Truncated ℤ 4 := 1 + (2 : ℤ) • T + (3 : ℤ) • T ^ 2
    let g : Truncated ℤ 4 := 1 - T + T ^ 3
    coeff 0 (f * g) = 1 ∧ coeff 1 (f * g) = 1 ∧ coeff 2 (f * g) = 1 ∧ coeff 3 (f * g) = -2 ∧
      T ^ 4 = 0 := by
  intro T f g
  have h1 : f * g = 1 + T + T ^ 2 - (2 : ℤ) • T ^ 3 := by
    have h4 : T ^ 4 = 0 := var_pow_eq_zero
    have hlin : (1 + (2 : ℤ) * T + (3 : ℤ) * T ^ 2) * (1 - T + T ^ 3) -
        (1 + T + T ^ 2 - (2 : ℤ) * T ^ 3) = T ^ 4 * (2 + 3 * T) := by ring
    simp only [f, g, zsmul_eq_mul]
    exact sub_eq_zero.mp (by rw [hlin, h4, zero_mul])
  rw [h1]
  refine ⟨?_, ?_, ?_, ?_, var_pow_eq_zero⟩
  · simp [T, -zsmul_eq_mul]
  · simp [T, -zsmul_eq_mul]
  · simp [T, -zsmul_eq_mul]
  · simp [T, -zsmul_eq_mul]

example :
    let T := var ℤ 4
    (1 - T) * geomInv T = 1 ∧
      geomInv T = 1 + T + T ^ 2 + T ^ 3 := by
  intro T
  have hT0 : coeff 0 T = 0 := by simp [T]
  refine ⟨one_sub_mul_geomInv hT0, ?_⟩
  simp only [geomInv, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]

example : ¬ IsUnit (var ℚ 3) := by
  rw [isUnit_iff (by omega : 0 < 3)]
  simp

example :
    let T := var ℚ 3
    let x : Truncated ℚ 3 := algebraMap ℚ (Truncated ℚ 3) 2 + (3 : ℚ) • T
    x * unitInv (Units.mk0 (2 : ℚ) (by norm_num)) x = 1 := by
  intro T x
  refine mul_unitInv ?_
  have h0 : coeff 0 T = 0 := by simp [T]
  simp [x, Truncated.coeff_add, Truncated.coeff_algebraMap, Truncated.coeff_smul, h0]

example :
    let T := var ℤ 4
    let f : Truncated ℤ 4 := 1 + T + T ^ 2
    let g : Truncated ℤ 4 := T + T ^ 2
    let hg : coeff 0 g = 0 := by simp [g, T]
    let res := substZeroConst hg f
    coeff 0 res = 1 ∧ coeff 1 res = 1 ∧ coeff 2 res = 2 ∧ coeff 3 res = 2 := by
  intro T f g hg res
  have hsub : res = 1 + T + (2 : ℤ) • T ^ 2 + (2 : ℤ) • T ^ 3 := by
    have h4 : T ^ 4 = 0 := var_pow_eq_zero
    simp only [res, substZeroConst, subst, liftAlgHom_eq_sum, f, g]
    have hc0 : coeff 0 (1 + T + T ^ 2) = 1 := by simp [T]
    have hc1 : coeff 1 (1 + T + T ^ 2) = 1 := by simp [T]
    have hc2 : coeff 2 (1 + T + T ^ 2) = 1 := by simp [T]
    have hc3 : coeff 3 (1 + T + T ^ 2) = 0 := by simp [T]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hc0, hc1, hc2, hc3]
    simp only [zero_smul, add_zero, one_smul, pow_zero, pow_one, zsmul_eq_mul]
    have hlin : 1 + (T + T ^ 2) + (T + T ^ 2) ^ 2 -
        (1 + T + (2 : ℤ) * T ^ 2 + (2 : ℤ) * T ^ 3) = T ^ 4 := by ring
    exact sub_eq_zero.mp (by rw [hlin, h4])
  rw [hsub]
  simp [T, -zsmul_eq_mul]

example (p q : Polynomial ℤ) :
    equivJetTableR1 ℤ 4 (mk 4 (p * q)) =
      Cslib.JetTable.ofPolyZ 4 1 p * Cslib.JetTable.ofPolyZ 4 1 q := by
  rw [map_mul (mk 4), map_mul, equivJetTableR1_mk, equivJetTableR1_mk]

example (p q : Polynomial ℤ) :
    Cslib.Circuits.Frontier.truncEquivTruncated 3 4
        (mk 4 (p.map (Int.castRingHom (ZMod (2 ^ 3)))) *
          mk 4 (q.map (Int.castRingHom (ZMod (2 ^ 3))))) =
      Cslib.Circuits.Frontier.truncRingHom 3 4 p *
        Cslib.Circuits.Frontier.truncRingHom 3 4 q := by
  rw [map_mul, Cslib.Circuits.Frontier.truncEquivTruncated_mk,
    Cslib.Circuits.Frontier.truncEquivTruncated_mk]

example (p : Polynomial ℤ) :
    (equivAdjoinRoot ℤ 4).symm (equivAdjoinRoot ℤ 4 (mk 4 p)) = mk 4 p := by
  rw [equivAdjoinRoot_mk, equivAdjoinRoot_symm_mk]

example (A : Cslib.JetTable 4 1 ℤ) (B : Cslib.JetTable 1 4 ℤ) (i : Fin 4) :
    coeff i.val ((equivJetTableR1 ℤ 4).symm A) = A i 0 ∧
      coeff i.val ((equivJetTable1R ℤ 4).symm B) = B 0 i := by
  simp [i.isLt]

example (p : Polynomial (ZMod (2 ^ 3))) :
    (Cslib.Circuits.Frontier.truncEquivTruncated 3 4).symm
        (Cslib.Circuits.Frontier.truncEquivTruncated 3 4 (mk 4 p)) =
      mk 4 p := by
  rw [Cslib.Circuits.Frontier.truncEquivTruncated_mk_zmod,
    Cslib.Circuits.Frontier.truncEquivTruncated_symm_mk]

end TruncatedAlgebraTests

section RatReconstructionTests

example : Rat.reconstruct 101 75 5 5 = some (-3 / 4 : ℚ) := by
  have hnum : (-3 / 4 : ℚ).num = -3 := by norm_num
  have hden : (-3 / 4 : ℚ).den = 4 := by norm_num
  refine Rat.reconstruct_of_eq (M := 101) (u := 75) (N := 5) (D := 5) (q := (-3 / 4 : ℚ))
    ?_ ?_ (by norm_num) ?_ ?_
  · norm_num
  · norm_num
  · rw [hden]; decide
  · rw [hnum, hden]; decide

example : Rat.reconstruct 101 69 5 5 = some (5 / 3 : ℚ) := by
  have hnum : (5 / 3 : ℚ).num = 5 := by norm_num
  have hden : (5 / 3 : ℚ).den = 3 := by norm_num
  refine Rat.reconstruct_of_eq (M := 101) (u := 69) (N := 5) (D := 5) (q := (5 / 3 : ℚ))
    ?_ ?_ (by norm_num) ?_ ?_
  · norm_num
  · norm_num
  · rw [hden]; decide
  · rw [hnum, hden]; decide

-- Boundary test: `2 * N * D < M` fails (`2 * 2 * 2 = 8 ≥ 5`), so distinct bounded rationals
-- `1 / 2` and `-2 / 1` share the same cross-product modulo `5`; also `reconstruct 8 3 2 1 = none`.
example :
    (1 : ℤ) * (1 : ℤ) ≡ (-2 : ℤ) * (2 : ℤ) [ZMOD 5] ∧ (1 / 2 : ℚ) ≠ (-2 / 1 : ℚ) := by
  constructor
  · decide
  · norm_num

example : Rat.reconstruct 8 3 2 1 = none := by
  by_contra hne
  rcases Option.ne_none_iff_exists'.mp hne with ⟨q, hq⟩
  rcases Rat.reconstruct_eq_some hq with ⟨_, hN, hD, hcop, hmod⟩
  have hsmall : q = 0 ∨ q = 1 ∨ q = -1 ∨ q = 2 ∨ q = -2 := by
    have hpos := q.den_pos
    have hq1 : q.den = 1 := by omega
    have hnum : q.num = -2 ∨ q.num = -1 ∨ q.num = 0 ∨ q.num = 1 ∨ q.num = 2 := by omega
    have hqeq : q = (q.num : ℚ) := by
      rw [← Rat.num_div_den q, hq1]
      simp
    rw [hqeq]
    rcases hnum with h | h | h | h | h <;> simp [h]
  rcases hsmall with rfl | rfl | rfl | rfl | rfl <;> revert hmod <;> decide

example :
    let m : Fin 3 → ℕ := ![5, 7, 11]
    have hcop : Pairwise (Function.onFun Nat.Coprime m) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
    let q : ℚ := 7 / 13
    let res : ∀ i, ZMod (m i) := fun i => (q.num : ZMod (m i)) * (q.den : ZMod (m i))⁻¹
    Rat.reconstructPi m hcop res 10 15 = some q := by
  intro m hcop q res
  refine Rat.reconstructPi_of_eq hcop ?_ ?_ ?_ ?_ ?_
  · norm_num [q]
  · norm_num [q]
  · norm_num [m, Fin.prod_univ_succ]
  · intro i
    fin_cases i <;> norm_num [q, m, Nat.Coprime]
  · intro i
    have hunit : IsUnit ((q.den : ZMod (m i))) := by
      rw [ZMod.isUnit_iff_coprime]
      fin_cases i <;> norm_num [q, m, Nat.Coprime]
    fin_cases i <;>
      simp [res, mul_assoc, ZMod.inv_mul_of_unit _ hunit]

example :
    Rat.height (-3 / 4 : ℚ) = 4 ∧
      Rat.height ((1 / 2 : ℚ) * (-3 / 4 : ℚ)) ≤
        Rat.height (1 / 2 : ℚ) * Rat.height (-3 / 4 : ℚ) := by
  constructor
  · norm_num [Rat.height]
  · exact Rat.height_mul_le _ _

end RatReconstructionTests

section PolyRatReconstructionTests

open Polynomial Polynomial.PolyRat

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example :
    let M : (ZMod 5)[X] := X ^ 3 + C 1
    let p : PolyRat (ZMod 5) := ⟨X + C 1, X + C 2⟩
    let u : (ZMod 5)[X] := (X + C 1) * (C 3 * X ^ 2 + C 4 * X + C 2)
    reconstruct M u 1 1 = some p := by
  intro M p u
  refine reconstruct_zmod_of_eq (p := 5) (M := M) (u := u) (N := 1) (D := 1) (q := p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact monic_X_add_C 2
  · refine ⟨-1, 1, ?_⟩
    dsimp [p]
    simp only [C_1, map_ofNat]
    ring
  · refine ⟨C 3 * X ^ 2 + C 4 * X + C 2, C 2, ?_⟩
    have h32 : C (3 : ZMod 5) + C 2 = 0 := by
      rw [← C_add, show (3 + 2 : ZMod 5) = 0 by decide, map_zero]
    have h324 : C (3 : ZMod 5) * C 2 + C 4 = 0 := by
      rw [← C_mul, ← C_add, show (3 * 2 + 4 : ZMod 5) = 0 by decide, map_zero]
    have h422 : C (4 : ZMod 5) * C 2 + C 2 = 0 := by
      rw [← C_mul, ← C_add, show (4 * 2 + 2 : ZMod 5) = 0 by decide, map_zero]
    have h222 : C (2 : ZMod 5) * C 2 + C 2 = 1 := by
      rw [← C_mul, ← C_add, show (2 * 2 + 2 : ZMod 5) = 1 by decide, map_one]
    calc
      (C 3 * X ^ 2 + C 4 * X + C 2) * p.den + C 2 * M
          = (C 3 + C 2) * X ^ 3 + (C 3 * C 2 + C 4) * X ^ 2 +
              (C 4 * C 2 + C 2) * X + (C 2 * C 2 + C 2) := by
            dsimp [p, M]
            simp only [C_1]
            ring
      _ = 1 := by rw [h32, h324, h422, h222]; ring
  · have hdeg : (X + C (1 : ZMod 5)).natDegree ≤ 1 := by simp
    exact le_trans degree_le_natDegree (WithBot.coe_le_coe.mpr hdeg)
  · simp [p]
  · have hMdeg : M.natDegree = 3 := by
      dsimp [M]
      compute_degree!
    omega
  · refine ⟨C 2 * (X + C 1), ?_⟩
    have ha : -(C (3 : ZMod 5)) = C 2 := by
      rw [← C_neg, show -(3 : ZMod 5) = 2 by decide]
    have hb : -(C (3 : ZMod 5) * C 2 + C 4) = 0 := by
      rw [← C_mul, ← C_add, ← C_neg, show -(3 * 2 + 4 : ZMod 5) = 0 by decide, map_zero]
    have hc : -(C (4 : ZMod 5) * C 2 + C 2) = 0 := by
      rw [← C_mul, ← C_add, ← C_neg, show -(4 * 2 + 2 : ZMod 5) = 0 by decide, map_zero]
    have hd : C (1 : ZMod 5) - C 2 * C 2 = C 2 := by
      rw [← C_mul, ← C_sub, show (1 - 2 * 2 : ZMod 5) = 2 by decide]
    calc
      p.num - p.den * u
          = (X + C 1) * (-C 3 * X ^ 3 + -(C 3 * C 2 + C 4) * X ^ 2 +
              -(C 4 * C 2 + C 2) * X + (C 1 - C 2 * C 2)) := by
            dsimp [p, u]
            simp only [C_1]
            ring
      _ = M * (C 2 * (X + C 1)) := by
            rw [ha, hb, hc, hd]
            dsimp [M]
            simp only [C_1]
            ring

example :
    let s : Finset (ZMod 7) := {0, 1, 2}
    let p : PolyRat (ZMod 7) := ⟨X + C 1, X + C 2⟩
    let vals : ZMod 7 → ZMod 7 := fun a => p.num.eval a / p.den.eval a
    cauchy s vals 1 1 = some p := by
  intro s p vals
  refine cauchy_of_eq (F := ZMod 7) (s := s) (vals := vals) (N := 1) (D := 1) (p := p)
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact monic_X_add_C 2
  · refine ⟨-1, 1, ?_⟩
    dsimp [p]
    simp only [C_1, map_ofNat]
    ring
  · have hdeg : (X + C (1 : ZMod 7)).natDegree ≤ 1 := by simp
    exact le_trans degree_le_natDegree (WithBot.coe_le_coe.mpr hdeg)
  · simp [p]
  · decide
  · intro a ha
    refine ⟨?_, rfl⟩
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;>
      simp only [p, eval_add, eval_X, eval_C, ne_eq] <;> decide

example (p q : PolyRat (ZMod 5)) (u : (ZMod 5)[X]) :
    p.height = max p.num.natDegree p.den.natDegree →
      p.den.Monic → q.den.Monic → IsCoprime p.num p.den → IsCoprime q.num q.den →
      p.height + q.height < (X ^ 4 + C (1 : ZMod 5)).natDegree →
      (X ^ 4 + C 1) ∣ p.num - p.den * u → (X ^ 4 + C 1) ∣ q.num - q.den * u → p = q := by
  intro _ hMp hMq hcp hcq hM hp hq
  exact eq_of_dvd_sub_of_height_lt hMp hMq hcp hcq hM hp hq

example :
    let p : PolyRat (ZMod 5) := ⟨X + C 1, X + C 2⟩
    p.height = 1 := by
  intro p
  have h1 : p.num.natDegree = 1 := by simp [p]
  have h2 : p.den.natDegree = 1 := by simp [p]
  simp [PolyRat.height, h1, h2]

end PolyRatReconstructionTests

section StrictModuleSurfaceTests

open Polynomial (Truncated X C)
open Polynomial.Truncated

theorem strict_geomInv_rfl (y : Truncated ℤ 4) :
    geomInv y = ∑ k ∈ Finset.range 4, y ^ k :=
  rfl

theorem strict_unitInv_rfl (u : ℚˣ) (x : Truncated ℚ 3) :
    unitInv u x =
      algebraMap ℚ (Truncated ℚ 3) (u⁻¹ : ℚˣ) *
        geomInv (1 - algebraMap ℚ (Truncated ℚ 3) (u⁻¹ : ℚˣ) * x) :=
  rfl

theorem strict_toPoly_coeffs_rfl (x : Truncated ℤ 4) :
    toPoly x = ∑ i ∈ Finset.range 4, C (coeff i x) * X ^ i ∧
      coeffs x = (toPoly x).coeffsBelow 4 :=
  ⟨rfl, rfl⟩

theorem strict_height_rfl (q : ℚ) (p : Polynomial.PolyRat ℚ) :
    q.height = max q.num.natAbs q.den ∧ p.height = max p.num.natDegree p.den.natDegree :=
  ⟨rfl, rfl⟩

theorem strict_subst_rfl (g : Truncated ℤ 4) (hg : coeff 0 g = 0) (f : Truncated ℤ 4) :
    subst (pow_eq_zero_of_coeff_zero hg) f = liftAlgHom (pow_eq_zero_of_coeff_zero hg) f ∧
      substZeroConst hg f = subst (pow_eq_zero_of_coeff_zero hg) f :=
  ⟨rfl, rfl⟩

end StrictModuleSurfaceTests

end CslibFrontierTests.TruncatedAndReconstruction
