/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.TotalIsolation
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.Isolation
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.RootBound
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.RatPoly
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.Sturm
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.GetD
import Mathlib.Tactic.ComputeDegree

/-!
# Real-root isolation and Mignotte separation tests

Kernel-checked evaluations (`decide +kernel`, without `native_decide`) and nonvacuous
theorem instantiations for the computable Sturm real-root isolators (`isolateRoots`,
`isolateRootsM`, `isolatePolyRoots`, and the end-to-end `TimeM ℕ`-charged `isolateRootsTotal`,
`isolateRootsTotalM`, `isolatePolyRootsTotal`, `isolatePolyRootsTotalM` producing strictly disjoint
closed intervals), coefficient bit-length bounds (`HasCoeffBitBound`, `coeffBitBound`), Hadamard's
inequality (`Matrix.hadamard_det_sq_le`), and Mignotte-type root-separation bounds
(`Polynomial.mignotte_sep_sqNorm_real`, `Polynomial.mignotte_sep_sqNorm_rat`).
-/

public section

namespace CslibFrontierTests.RealRootIsolation

open Cslib.RealRoot Polynomial

/-! ### Kernel-checked executable evaluations (`decide +kernel`) -/

example :
    isolateRoots [] = [] ∧
      isolateRoots [5] = [] ∧
      isolateRoots [-3, 2] = [{ lower := -3, upper := 3 }] := by
  decide +kernel

-- `x^2 - 2` isolates `-√2` in `[-4, 0]` and `√2` in `[0, 4]`.
example :
    isolateRoots [-2, 0, 1] =
        [{ lower := -4, upper := 0 }, { lower := 0, upper := 4 }] ∧
      cauchyBoundNat [-2, 0, 1] = 4 ∧
      mignotteBisectionDepth [-2, 0, 1] = 6 ∧
      (isolateRootsM [-2, 0, 1]).time = 39 := by
  decide +kernel

-- `x^2 - x` has `0` at the first bisection midpoint, exercising left-endpoint refinement.
example :
    isolateRoots [0, -1, 1] =
        [{ lower := 0, upper := 0 }, { lower := 3 / 4, upper := 3 / 2 }] ∧
      evalCoeffList (0 : ℚ) [0, -1, 1] = 0 ∧
      evalCoeffList (3 / 4 : ℚ) [0, -1, 1] * evalCoeffList (3 / 2 : ℚ) [0, -1, 1] < 0 := by
  decide +kernel

-- Multi-root cubic `x^3 - 7x + 7` with two close positive roots near `1.357` and `1.692`.
example :
    isolateRoots [7, -7, 0, 1] =
        [{ lower := -9, upper := 0 },
         { lower := 9 / 8, upper := 27 / 16 },
         { lower := 27 / 16, upper := 9 / 4 }] ∧
      mignotteBisectionDepth [7, -7, 0, 1] = 14 ∧
      (isolateRootsM [7, -7, 0, 1]).time = 122 ∧
      sturmVariationsList (sturmSeqList [7, -7, 0, 1]) (-9) -
        sturmVariationsList (sturmSeqList [7, -7, 0, 1]) 0 = 1 ∧
      sturmVariationsList (sturmSeqList [7, -7, 0, 1]) (9 / 8) -
        sturmVariationsList (sturmSeqList [7, -7, 0, 1]) (27 / 16) = 1 ∧
      sturmVariationsList (sturmSeqList [7, -7, 0, 1]) (27 / 16) -
        sturmVariationsList (sturmSeqList [7, -7, 0, 1]) (9 / 4) = 1 := by
  decide +kernel

-- Multi-root cubic `(x - 1)(x - 2)(x - 3) = x^3 - 6x^2 + 11x - 6`.
example :
    isolateRoots [-6, 11, -6, 1] =
        [{ lower := 0, upper := 13 / 8 },
         { lower := 13 / 8, upper := 39 / 16 },
         { lower := 39 / 16, upper := 13 / 4 }] ∧
      (isolateRoots [-6, 11, -6, 1]).length = 3 := by
  decide +kernel

-- Mixed rational/irrational cubic `(x - 1)(x^2 - 2) = x^3 - x^2 - 2x + 2`.
example :
    isolateRoots [2, -2, -1, 1] =
        [{ lower := -4, upper := 0 },
         { lower := 1, upper := 1 },
         { lower := 5 / 4, upper := 3 / 2 }] ∧
      evalCoeffList (1 : ℚ) [2, -2, -1, 1] = 0 ∧
      evalCoeffList (5 / 4 : ℚ) [2, -2, -1, 1] * evalCoeffList (3 / 2 : ℚ) [2, -2, -1, 1] < 0 := by
  decide +kernel

/-! ### Nonvacuous theorem instantiations -/

private theorem ofCoeffList_sqSubTwo :
    ofCoeffList [(-2 : ℚ), 0, 1] = X ^ 2 - 2 := by
  simp only [ofCoeffList_cons, ofCoeffList_nil, C_0, C_1, C_neg, mul_zero, add_zero, mul_one]
  rw [← map_ofNat C 2]
  ring

private theorem squarefree_sqSubTwo :
    Squarefree (ofCoeffList [(-2 : ℚ), 0, 1]) := by
  rw [ofCoeffList_sqSubTwo]
  refine PerfectField.separable_iff_squarefree.mp ?_
  change IsCoprime (X ^ 2 - (2 : ℚ[X])) (derivative (X ^ 2 - (2 : ℚ[X])))
  have hderiv : derivative (X ^ 2 - (2 : ℚ[X])) = 2 * X := by
    rw [← map_ofNat C 2]
    simp only [derivative_sub, derivative_X_pow, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one,
      derivative_C, sub_zero]
  rw [hderiv]
  refine ⟨C (-1 / 2 : ℚ), C (1 / 4 : ℚ) * X, ?_⟩
  have hid : C (-1 / 2 : ℚ) * (X ^ 2 - 2) + C (1 / 4 : ℚ) * X * (2 * X) =
      C (-1 / 2 : ℚ) * (-(2 : ℚ[X])) + (C (-1 / 2 : ℚ) + C (1 / 4 : ℚ) * 2) * X ^ 2 := by ring
  rw [hid, ← map_ofNat C 2, ← map_neg, ← map_mul, ← map_mul, ← map_add]
  norm_num

-- `x^2 - 2` has two distinct real roots `-√2 < √2` matched bijectively with `[-4, 0]` and
-- `[0, 4]`, and satisfies the proved operation-count bound `≤ 312`.
example :
    ((ofCoeffList [(-2 : ℚ), 0, 1]).map (algebraMap ℚ ℝ)).roots.toFinset.card = 2 ∧
      (-4 : ℝ) ≤ -√2 ∧ -√2 ≤ (0 : ℝ) ∧
      (0 : ℝ) ≤ √2 ∧ √2 ≤ (4 : ℝ) ∧
      (isolateRootsM [(-2 : ℚ), 0, 1]).time ≤ 312 := by
  have hsep : (ofCoeffList [(-2 : ℚ), 0, 1]).Separable :=
    PerfectField.separable_iff_squarefree.mpr squarefree_sqSubTwo
  have hlen := isolateRoots_length_eq_card_roots hsep
  have heval_list : isolateRoots [(-2 : ℚ), 0, 1] =
      [{ lower := -4, upper := 0 }, { lower := 0, upper := 4 }] := by decide +kernel
  have hcard : ((ofCoeffList [(-2 : ℚ), 0, 1]).map (algebraMap ℚ ℝ)).roots.toFinset.card = 2 := by
    rw [← hlen, heval_list]
    rfl
  have hsqrt2 : √2 ≤ 4 := by
    calc √2 ≤ √((4 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 4 := Real.sqrt_sq (by norm_num)
  have htime := isolateRootsM_time_le_of_squarefree squarefree_sqSubTwo
  have hdeg : (ofCoeffList [(-2 : ℚ), 0, 1]).natDegree = 2 := by
    rw [ofCoeffList_sqSubTwo]
    compute_degree!
  have hdepth : mignotteBisectionDepth [(-2 : ℚ), 0, 1] = 6 := by decide +kernel
  rw [hdeg, hdepth] at htime
  exact ⟨hcard, by linarith, neg_nonpos.mpr (Real.sqrt_nonneg 2), Real.sqrt_nonneg 2, hsqrt2,
    htime.trans (by decide)⟩

-- The bijection `isolatedRoot` recovers the two ordered roots `-√2` and `√2` of `x^2 - 2`.
example :
    let hsep := PerfectField.separable_iff_squarefree.mpr squarefree_sqSubTwo
    have hlen : (isolateRoots [(-2 : ℚ), 0, 1]).length = 2 := by decide +kernel
    let r₀ := isolatedRoot hsep ⟨0, by omega⟩
    let r₁ := isolatedRoot hsep ⟨1, by omega⟩
    r₀.1 = -√2 ∧ r₁.1 = √2 ∧ r₀.1 < r₁.1 := by
  intro hsep hlen r₀ r₁
  have hmono : r₀.1 < r₁.1 :=
    isolatedRoot_strictMono hsep (by decide : (⟨0, by omega⟩ : Fin _) < ⟨1, by omega⟩)
  have heval_list : isolateRoots [(-2 : ℚ), 0, 1] =
      [{ lower := -4, upper := 0 }, { lower := 0, upper := 4 }] := by decide +kernel
  have hiso0 : ({ lower := -4, upper := 0 } : RootInterval).IsIsolatingFor
      ((ofCoeffList [(-2 : ℚ), 0, 1]).map (algebraMap ℚ ℝ)) :=
    isolateRoots_isIsolatingFor hsep _ (by rw [heval_list]; exact List.mem_cons_self)
  have hiso1 : ({ lower := 0, upper := 4 } : RootInterval).IsIsolatingFor
      ((ofCoeffList [(-2 : ℚ), 0, 1]).map (algebraMap ℚ ℝ)) :=
    isolateRoots_isIsolatingFor hsep _
      (by rw [heval_list]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hmem0 := isolatedRoot_mem hsep ⟨0, by omega⟩
  have hmem1 := isolatedRoot_mem hsep ⟨1, by omega⟩
  simp only [Fin.getElem_fin, heval_list, List.getElem_cons_zero, List.getElem_cons_succ]
    at hmem0 hmem1
  have hmap : (ofCoeffList [(-2 : ℚ), 0, 1]).map (algebraMap ℚ ℝ) = X ^ 2 - 2 := by
    rw [ofCoeffList_sqSubTwo, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat]
  have hsqrt2 : √2 ≤ 4 := by
    calc √2 ≤ √((4 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 4 := Real.sqrt_sq (by norm_num)
  have hpos_root : ((ofCoeffList [(-2 : ℚ), 0, 1]).map (algebraMap ℚ ℝ)).IsRoot (√2) := by
    rw [IsRoot.def, hmap, eval_sub, eval_pow, eval_X, eval_ofNat, Real.sq_sqrt (by norm_num),
      sub_self]
  have hneg_root : ((ofCoeffList [(-2 : ℚ), 0, 1]).map (algebraMap ℚ ℝ)).IsRoot (-√2) := by
    rw [IsRoot.def, hmap, eval_sub, eval_pow, eval_X, eval_ofNat, neg_sq,
      Real.sq_sqrt (by norm_num), sub_self]
  have hr0_eq : r₀.1 = -√2 := hiso0.2.unique ⟨hmem0.1, hmem0.2, r₀.2⟩
    ⟨by norm_num; exact hsqrt2, by norm_num, hneg_root⟩
  have hr1_eq : r₁.1 = √2 := hiso1.2.unique ⟨hmem1.1, hmem1.2, r₁.2⟩
    ⟨by norm_num, by norm_num; exact hsqrt2, hpos_root⟩
  exact ⟨hr0_eq, hr1_eq, hmono⟩

-- Concrete `isolatePolyRoots` and `mignotte_sep_sqNorm_real` instantiation on `x^3 - 7x + 7`.
private noncomputable def wilkCubicZ : ℤ[X] := X ^ 3 - 7 * X + 7

private noncomputable def wilkCubicQ : ℚ[X] := wilkCubicZ.map (algebraMap ℤ ℚ)

private theorem separable_wilkCubicQ : wilkCubicQ.Separable := by
  change IsCoprime wilkCubicQ (derivative wilkCubicQ)
  have hmap : wilkCubicQ = X ^ 3 - 7 * X + 7 := by
    simp only [wilkCubicQ, wilkCubicZ, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul, Polynomial.map_ofNat]
  rw [hmap]
  have hderiv : derivative (X ^ 3 - (7 : ℚ[X]) * X + 7) = 3 * X ^ 2 - 7 := by
    rw [← map_ofNat C 7]
    simp only [derivative_add, derivative_sub, derivative_X_pow, Nat.cast_ofNat,
      derivative_C_mul_X, derivative_C, add_zero]
    rw [map_ofNat]
  rw [hderiv]
  refine ⟨C (1 / 7 : ℚ) * (-3 * (6 * X + 9)), C (1 / 7 : ℚ) * (6 * X ^ 2 + 9 * X - 28), ?_⟩
  have hbez : (-3 * (6 * X + 9)) * (X ^ 3 - (7 : ℚ[X]) * X + 7) +
      (6 * X ^ 2 + 9 * X - 28) * (3 * X ^ 2 - 7) = 7 := by ring
  calc C (1 / 7 : ℚ) * (-3 * (6 * X + 9)) * (X ^ 3 - 7 * X + 7) +
        C (1 / 7 : ℚ) * (6 * X ^ 2 + 9 * X - 28) * (3 * X ^ 2 - 7)
      = C (1 / 7 : ℚ) * ((-3 * (6 * X + 9)) * (X ^ 3 - 7 * X + 7) +
          (6 * X ^ 2 + 9 * X - 28) * (3 * X ^ 2 - 7)) := by ring
    _ = C (1 / 7 : ℚ) * 7 := by rw [hbez]
    _ = 1 := by
        rw [← map_ofNat C 7, ← map_mul]
        norm_num

example :
    (∀ I ∈ isolatePolyRoots wilkCubicQ, I.IsIsolatingFor (wilkCubicQ.map (algebraMap ℚ ℝ))) ∧
      (∀ {α β : ℝ}, (wilkCubicZ.map (algebraMap ℤ ℝ)).IsRoot α →
        (wilkCubicZ.map (algebraMap ℤ ℝ)).IsRoot β → α ≠ β →
        (3 : ℝ) ≤ |α - β| ^ 2 *
          ((wilkCubicZ.natDegree ^ (wilkCubicZ.natDegree + 2) *
            coeffSqNorm wilkCubicZ ^ (wilkCubicZ.natDegree - 1) : ℕ) : ℝ)) := by
  have hsq : Squarefree wilkCubicQ := PerfectField.separable_iff_squarefree.mp separable_wilkCubicQ
  refine ⟨isolatePolyRoots_isIsolatingFor hsq, fun {α β} hα hβ hne => ?_⟩
  have hd : 2 ≤ wilkCubicZ.natDegree := by
    rw [wilkCubicZ]
    have hdeg : (X ^ 3 - 7 * X + (7 : ℤ[X])).natDegree = 3 := by compute_degree!
    omega
  exact Polynomial.mignotte_sep_sqNorm_real hd separable_wilkCubicQ hα hβ hne

-- Concrete instantiation of `mignotte_sep_sqNorm_rat` on `x^2 - 2` at `±√2`.
example : (3 : ℝ) ≤ |√2 - (-√2)| ^ 2 * ((2 ^ 4 * 5 : ℕ) : ℝ) := by
  let q : ℚ[X] := ofCoeffList [-2, 0, 1]
  let p : ℤ[X] := X ^ 2 - C 2
  have hd : 2 ≤ q.natDegree := by
    have hdeg : q.natDegree = 2 := by
      dsimp only [q]
      rw [ofCoeffList_sqSubTwo]
      compute_degree!
    omega
  have hsep : q.Separable := PerfectField.separable_iff_squarefree.mpr squarefree_sqSubTwo
  have hpq : p.map (algebraMap ℤ ℚ) = C 1 * q := by
    dsimp only [p, q]
    rw [ofCoeffList_sqSubTwo, C_1, one_mul, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    rfl
  have hmap : q.map (algebraMap ℚ ℝ) = X ^ 2 - 2 := by
    dsimp only [q]
    rw [ofCoeffList_sqSubTwo, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat]
  have hpos : (q.map (algebraMap ℚ ℝ)).IsRoot (√2) := by
    rw [IsRoot.def, hmap, eval_sub, eval_pow, eval_X, eval_ofNat, Real.sq_sqrt (by norm_num),
      sub_self]
  have hneg : (q.map (algebraMap ℚ ℝ)).IsRoot (-√2) := by
    rw [IsRoot.def, hmap, eval_sub, eval_pow, eval_X, eval_ofNat, neg_sq,
      Real.sq_sqrt (by norm_num), sub_self]
  have hne : √2 ≠ -√2 := by
    have hsqrt : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  have hbound := Polynomial.mignotte_sep_sqNorm_rat hd hsep one_ne_zero hpq hpos hneg hne
  have hdeg : q.natDegree = 2 := by
    dsimp only [q]
    rw [ofCoeffList_sqSubTwo]
    compute_degree!
  have hnorm : coeffSqNorm p = 5 := by
    dsimp only [p]
    rw [coeffSqNorm_eq_sum_range]
    have hpdeg : (X ^ 2 - C (2 : ℤ)).natDegree = 2 := by compute_degree!
    rw [hpdeg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num [coeff_X_pow]
  rw [hdeg, hnorm] at hbound
  exact hbound

-- Concrete instantiation of Hadamard's determinant inequality `Matrix.hadamard_det_sq_le`.
example :
    let A : Matrix (Fin 2) (Fin 2) ℂ := !![1, 2; 3, 4]
    ‖A.det‖ ^ 2 ≤ 125 := by
  intro A
  have hhad := Matrix.hadamard_det_sq_le A
  have hrhs : (∏ i : Fin 2, ∑ j : Fin 2, ‖A i j‖ ^ 2) = 125 := by
    simp only [Fin.prod_univ_two, Fin.sum_univ_two, A, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, norm_one, one_pow]
    norm_num
  exact hhad.trans_eq hrhs

-- Instantiation of `isolateRoots_bijective` and `isolateRoots_bijective_of_squarefree` on
-- `x^2 - 2`.
example :
    ∃! i : Fin (isolateRoots [(-2 : ℚ), 0, 1]).length,
      (isolatedRoot (PerfectField.separable_iff_squarefree.mpr squarefree_sqSubTwo) i).1 = √2 := by
  have hbij₁ := isolateRoots_bijective
    (PerfectField.separable_iff_squarefree.mpr squarefree_sqSubTwo)
  have hbij₂ := isolateRoots_bijective_of_squarefree squarefree_sqSubTwo
  have hmap : (ofCoeffList [(-2 : ℚ), 0, 1]).map (algebraMap ℚ ℝ) = X ^ 2 - 2 := by
    rw [ofCoeffList_sqSubTwo, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat]
  have hroot : ((ofCoeffList [(-2 : ℚ), 0, 1]).map (algebraMap ℚ ℝ)).IsRoot (√2) := by
    rw [IsRoot.def, hmap, eval_sub, eval_pow, eval_X, eval_ofNat, Real.sq_sqrt (by norm_num),
      sub_self]
  obtain ⟨i, hi, huniq⟩ := hbij₂.existsUnique ⟨√2, hroot⟩
  refine ⟨i, congrArg Subtype.val hi, fun j hj => hbij₁.1 (congrArg (isolatedRoot _) ?_)⟩
  exact huniq j (Subtype.ext hj)

-- Concrete instantiations of `polyIsolatedRoot`, `polyIsolatedRoot_mem`,
-- `polyIsolatedRoot_strictMono`, `isolatePolyRoots_bijective`, and `isolatePolyRootsM_time_le` on
-- `x^3 - 7x + 7`.
private theorem wilkCubicQ_natDegree : wilkCubicQ.natDegree = 3 := by
  have hmap : wilkCubicQ = X ^ 3 - 7 * X + 7 := by
    simp only [wilkCubicQ, wilkCubicZ, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul, Polynomial.map_ofNat]
  rw [hmap]
  compute_degree!

private theorem wilkCubicQ_coeffsBelow :
    wilkCubicQ.coeffsBelow (wilkCubicQ.natDegree + 1) = [7, -7, 0, 1] := by
  refine coeffsBelow_eq_of_ofCoeffList ?_ (by rw [wilkCubicQ_natDegree]; rfl)
  have hmap : wilkCubicQ = X ^ 3 - 7 * X + 7 := by
    simp only [wilkCubicQ, wilkCubicZ, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul, Polynomial.map_ofNat]
  rw [hmap]
  simp only [ofCoeffList_cons, ofCoeffList_nil, C_0, C_1, C_neg, mul_zero, add_zero, mul_one]
  rw [← map_ofNat C 7]
  ring

example :
    let hsq : Squarefree wilkCubicQ :=
      PerfectField.separable_iff_squarefree.mp separable_wilkCubicQ
    have hlen : (isolatePolyRoots wilkCubicQ).length = 3 := by
      rw [isolatePolyRoots_eq, wilkCubicQ_coeffsBelow]
      decide +kernel
    let r₀ := (polyIsolatedRoot hsq ⟨0, by omega⟩).1
    let r₁ := (polyIsolatedRoot hsq ⟨1, by omega⟩).1
    let r₂ := (polyIsolatedRoot hsq ⟨2, by omega⟩).1
    (-9 : ℝ) ≤ r₀ ∧ r₀ ≤ (0 : ℝ) ∧
      ((9 / 8 : ℚ) : ℝ) ≤ r₁ ∧ r₁ ≤ ((27 / 16 : ℚ) : ℝ) ∧
      ((27 / 16 : ℚ) : ℝ) ≤ r₂ ∧ r₂ ≤ ((9 / 4 : ℚ) : ℝ) ∧
      r₀ < r₁ ∧ r₁ < r₂ ∧
      Function.Bijective (polyIsolatedRoot hsq) ∧
      (isolatePolyRootsM wilkCubicQ).time ≤ 1352 := by
  intro hsq hlen r₀ r₁ r₂
  have hmem0 := polyIsolatedRoot_mem hsq ⟨0, by omega⟩
  have hmem1 := polyIsolatedRoot_mem hsq ⟨1, by omega⟩
  have hmem2 := polyIsolatedRoot_mem hsq ⟨2, by omega⟩
  have hlist : isolatePolyRoots wilkCubicQ =
      [{ lower := -9, upper := 0 },
       { lower := 9 / 8, upper := 27 / 16 },
       { lower := 27 / 16, upper := 9 / 4 }] := by
    rw [isolatePolyRoots_eq, wilkCubicQ_coeffsBelow]
    decide +kernel
  simp only [Fin.getElem_fin, hlist, List.getElem_cons_zero, List.getElem_cons_succ]
    at hmem0 hmem1 hmem2
  have h01 : r₀ < r₁ :=
    polyIsolatedRoot_strictMono hsq (by decide : (⟨0, by omega⟩ : Fin _) < ⟨1, by omega⟩)
  have h12 : r₁ < r₂ :=
    polyIsolatedRoot_strictMono hsq (by decide : (⟨1, by omega⟩ : Fin _) < ⟨2, by omega⟩)
  have hbij : Function.Bijective (polyIsolatedRoot hsq) := isolatePolyRoots_bijective hsq
  have htime := isolatePolyRootsM_time_le hsq
  have hcb : wilkCubicQ.coeffsBelow (3 + 1) = [7, -7, 0, 1] := by
    rw [← wilkCubicQ_natDegree]
    exact wilkCubicQ_coeffsBelow
  have hdepth : mignotteBisectionDepth [7, -7, 0, 1] = 14 := by decide +kernel
  rw [wilkCubicQ_natDegree] at htime
  dsimp only at htime
  rw [hcb, hdepth] at htime
  exact ⟨by simpa only [Rat.cast_neg, Rat.cast_ofNat] using hmem0.1,
    by simpa only [Rat.cast_zero] using hmem0.2,
    hmem1.1, hmem1.2, hmem2.1, hmem2.2, h01, h12, hbij, htime.trans (by decide)⟩

/-! ### End-to-end `TimeM ℕ`-charged disjoint isolation (`isolateRootsTotalM` / `isolateRootsTotal`)
-/

example :
    isolateRootsTotal [] = [] ∧ (isolateRootsTotalM []).time = 2 ∧
      isolateRootsTotal [5] = [] ∧ (isolateRootsTotalM [5]).time = 62 ∧
      isolateRootsTotal [-3, 2] = [{ lower := -3, upper := 3 }] ∧
      (isolateRootsTotalM [-3, 2]).time = 215 := by
  decide +kernel

-- `x^2 - 2`: `isolateRoots` returned `[-4, 0]` and `[0, 4]` touching at `0`, whereas
-- `isolateRootsTotal` separates them into strictly disjoint closed intervals `[-4, -1]` and
-- `[0, 4]` (`-1 < 0`), charging all preprocessing, bisection, refinement, and separation (`627`).
example :
    isolateRootsTotal [-2, 0, 1] =
        [{ lower := -4, upper := -1 }, { lower := 0, upper := 4 }] ∧
      (isolateRootsTotalM [-2, 0, 1]).time = 627 ∧
      coeffBitBound [-2, 0, 1] = 2 ∧
      isolateRootsTotal [0, -1, 1] =
        [{ lower := 0, upper := 0 }, { lower := 3 / 4, upper := 3 / 2 }] ∧
      (isolateRootsTotalM [0, -1, 1]).time = 610 := by
  decide +kernel

-- `x^3 - 7x + 7` and `(x - 1)(x - 2)(x - 3)`: adjacent intervals touching at non-root dyadic
-- midpoints are separated (`45/32 < 27/16`, `39/32 < 13/8`, `65/32 < 39/16`).
example :
    isolateRootsTotal [7, -7, 0, 1] =
        [{ lower := -9, upper := 0 },
         { lower := 9 / 8, upper := 45 / 32 },
         { lower := 27 / 16, upper := 9 / 4 }] ∧
      (isolateRootsTotalM [7, -7, 0, 1]).time = 1102 ∧
      coeffBitBound [7, -7, 0, 1] = 3 ∧
      isolateRootsTotal [-6, 11, -6, 1] =
        [{ lower := 0, upper := 39 / 32 },
         { lower := 13 / 8, upper := 65 / 32 },
         { lower := 39 / 16, upper := 13 / 4 }] ∧
      (isolateRootsTotalM [-6, 11, -6, 1]).time = 1373 ∧
      isolateRootsTotal [2, -2, -1, 1] =
        [{ lower := -4, upper := 0 },
         { lower := 1, upper := 1 },
         { lower := 5 / 4, upper := 3 / 2 }] ∧
      (isolateRootsTotalM [2, -2, -1, 1]).time = 1026 := by
  decide +kernel

/-- Full end-to-end specification `isolateRootsTotal_spec_of_eq`, `totalIsolatedRoot`,
disjointness, dyadic endpoint bit bounds, and bit-parameterized `TimeM ℕ` cost bound on
`x^2 - 2`. -/
theorem isolateRootsTotal_sqSubTwo_spec :
    (isolateRootsTotal [(-2 : ℚ), 0, 1]).Pairwise (fun J₁ J₂ => J₁.upper < J₂.lower) ∧
      (isolateRootsTotal [(-2 : ℚ), 0, 1]).Pairwise
        (Function.onFun Disjoint fun J => Set.Icc (J.lower : ℝ) (J.upper : ℝ)) ∧
      (∃ f : Fin (isolateRootsTotal [(-2 : ℚ), 0, 1]).length →
          {x : ℝ // Polynomial.aeval x (X ^ 2 - (2 : ℚ[X])) = 0},
        Function.Bijective f ∧ StrictMono (fun i => (f i).1)) ∧
      mignotteBisectionDepth [(-2 : ℚ), 0, 1] ≤ 5 ^ 2 * 4 ∧
      (isolateRootsTotalM [(-2 : ℚ), 0, 1]).time ≤ 84 * 5 ^ 5 * 4 := by
  have hB : HasCoeffBitBound 2 [(-2 : ℚ), 0, 1] := by
    have hcb : coeffBitBound [(-2 : ℚ), 0, 1] = 2 := by decide +kernel
    exact hcb ▸ hasCoeffBitBound_coeffBitBound [(-2 : ℚ), 0, 1]
  have hsq_poly : Squarefree (X ^ 2 - (2 : ℚ[X])) := ofCoeffList_sqSubTwo ▸ squarefree_sqSubTwo
  have hspec := isolateRootsTotal_spec_of_eq ofCoeffList_sqSubTwo hsq_poly hB
  obtain ⟨_, hpw_lt, hpw_disj, ⟨f, hf_bij, hf_mono, _⟩, _, htime⟩ := hspec
  have hmig := mignotteBisectionDepth_le_of_bitBound hB
  exact ⟨hpw_lt, hpw_disj, ⟨f, hf_bij, hf_mono⟩, hmig, htime⟩

-- `Polynomial ℚ` wrapper `isolatePolyRootsTotal`, `polyTotalIsolatedRoot`, disjointness, and
-- bit-parameterized `TimeM ℕ` / endpoint bounds on `wilkCubicQ = x^3 - 7x + 7`.
example :
    let hsq : Squarefree wilkCubicQ :=
      PerfectField.separable_iff_squarefree.mp separable_wilkCubicQ
    have hlen : (isolatePolyRootsTotal wilkCubicQ).length = 3 := by
      rw [isolatePolyRootsTotal_eq, wilkCubicQ_coeffsBelow]
      decide +kernel
    let r₀ := (polyTotalIsolatedRoot hsq ⟨0, by omega⟩).1
    let r₁ := (polyTotalIsolatedRoot hsq ⟨1, by omega⟩).1
    let r₂ := (polyTotalIsolatedRoot hsq ⟨2, by omega⟩).1
    r₀ ∈ Set.Icc (-9 : ℝ) (0 : ℝ) ∧
      r₁ ∈ Set.Icc ((9 / 8 : ℚ) : ℝ) ((45 / 32 : ℚ) : ℝ) ∧
      r₂ ∈ Set.Icc ((27 / 16 : ℚ) : ℝ) ((9 / 4 : ℚ) : ℝ) ∧
      r₀ < r₁ ∧ r₁ < r₂ ∧
      (isolatePolyRootsTotal wilkCubicQ).Pairwise
        (Function.onFun Disjoint fun J => Set.Icc (J.lower : ℝ) (J.upper : ℝ)) ∧
      Function.Bijective (polyTotalIsolatedRoot hsq) ∧
      (isolatePolyRootsTotalM wilkCubicQ).time ≤ 84 * 6 ^ 5 * 5 := by
  intro hsq hlen r₀ r₁ r₂
  have hmem0 := polyTotalIsolatedRoot_mem hsq ⟨0, by omega⟩
  have hmem1 := polyTotalIsolatedRoot_mem hsq ⟨1, by omega⟩
  have hmem2 := polyTotalIsolatedRoot_mem hsq ⟨2, by omega⟩
  have hlist : isolatePolyRootsTotal wilkCubicQ =
      [{ lower := -9, upper := 0 },
       { lower := 9 / 8, upper := 45 / 32 },
       { lower := 27 / 16, upper := 9 / 4 }] := by
    rw [isolatePolyRootsTotal_eq, wilkCubicQ_coeffsBelow]
    decide +kernel
  simp only [Fin.getElem_fin, hlist, List.getElem_cons_zero, List.getElem_cons_succ]
    at hmem0 hmem1 hmem2
  have h01 : r₀ < r₁ :=
    polyTotalIsolatedRoot_strictMono hsq (by decide : (⟨0, by omega⟩ : Fin _) < ⟨1, by omega⟩)
  have h12 : r₁ < r₂ :=
    polyTotalIsolatedRoot_strictMono hsq (by decide : (⟨1, by omega⟩ : Fin _) < ⟨2, by omega⟩)
  have hB : ∀ i ≤ wilkCubicQ.natDegree,
      Int.natAbs (wilkCubicQ.coeff i).num ≤ 2 ^ 3 ∧ (wilkCubicQ.coeff i).den ≤ 2 ^ 3 := by
    have hcb_list : HasCoeffBitBound 3 [7, -7, 0, 1] := by
      have hc : coeffBitBound [(7 : ℚ), -7, 0, 1] = 3 := by decide +kernel
      exact hc ▸ hasCoeffBitBound_coeffBitBound [(7 : ℚ), -7, 0, 1]
    have hpoly_eq : ofCoeffList [(7 : ℚ), -7, 0, 1] = wilkCubicQ := by
      have h1 := Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self wilkCubicQ.natDegree)
      rwa [wilkCubicQ_coeffsBelow] at h1
    intro i hi
    rw [wilkCubicQ_natDegree] at hi
    rw [← hpoly_eq, Polynomial.coeff_ofCoeffList]
    have hmem : ([(7 : ℚ), -7, 0, 1].getD i 0) ∈ [(7 : ℚ), -7, 0, 1] := by
      have hi4 : i < [(7 : ℚ), -7, 0, 1].length := by
        simp only [List.length_cons, List.length_nil]
        omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi4, Option.getD_some]
      exact List.getElem_mem hi4
    exact hcb_list _ hmem
  have htime := isolatePolyRootsTotalM_time_le_of_bitBound hsq hB
  rw [wilkCubicQ_natDegree] at htime
  have hmem0' : r₀ ∈ Set.Icc (-9 : ℝ) (0 : ℝ) := by
    simpa only [Rat.cast_neg, Rat.cast_ofNat, Rat.cast_zero] using hmem0
  exact ⟨hmem0', hmem1, hmem2, h01, h12, isolatePolyRootsTotal_pairwise_disjoint hsq,
    isolatePolyRootsTotal_bijective hsq, htime⟩

end CslibFrontierTests.RealRootIsolation
