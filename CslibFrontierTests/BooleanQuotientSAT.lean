/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.BooleanAnalysis.BooleanQuotient
import CslibFrontier.Logics.Propositional.Algebraic.CNF.Counting
import CslibFrontier.Computability.Complexity.Problems.SAT.Space
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

/-!
# Tests for the Boolean-cube quotient, clause-indicator counting, and poly-space SAT enumeration

Checks:
* `Cslib.BitString.boolQuotientAlgEquiv`, `existsUnique_mem_restrictDegree_sub_mem_boolIdeal`,
  `boolIdeal_isRadical`, `finrank_boolQuotient`, and `finrank_restrictDegree_one`, including a
  non-reduced commutative ring `ZMod 4` where uniqueness of multilinear representatives holds
  while radicality fails (`(2 * X 0) ^ 2 ∈ boolIdeal`, `2 * X 0 ∉ boolIdeal`).
* `Cslib.Logic.PL.Algebraic.one_mem_sup_boolIdeal_iff`, `CNF.satIndicatorPoly`, cube sums over
  declared, occurring, finite-ambient, and `distinctVars` Boolean cubes matching `CNF.modelCount`
  and `CNF.modelCountOn` (including an unused ambient variable).
* `Cslib.Complexity.SAT.streamAcceptCount_distinctVerifier_eq`,
  `SharpSAT.computableInPolySpace_numVars`, `SAT.mem_PSPACE_of_enumeration`,
  `UNSAT.mem_PSPACE_of_enumeration`, and `USAT.mem_PSPACE_of_enumeration` on concrete `CNF ℕ`
  instances with gapped labels, unique models, zero models, and zero variables.
-/

section BooleanQuotientTests

open MvPolynomial Cslib.BitString

/-- Squaring a variable collapses in the Boolean-cube quotient over `ℤ`. -/
example :
    Ideal.Quotient.mk (boolIdeal (Fin 2) ℤ) (X 0 ^ 2 * X 1) =
      Ideal.Quotient.mk (boolIdeal (Fin 2) ℤ) (X 0 * X 1) := by
  apply (boolQuotientAlgEquiv (Fin 2) ℤ).injective
  funext x
  rw [boolQuotientAlgEquiv_mk, boolQuotientAlgEquiv_mk, map_mul, map_pow, map_mul, eval_X,
    eval_X, bitPoint]
  cases x 0 <;> simp [bitVal]

local instance : Fact (1 < 4) := ⟨by decide⟩

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem three_mul_X_mem_restrictDegree :
    (3 * X 0 : MvPolynomial (Fin 1) (ZMod 4)) ∈ restrictDegree (Fin 1) (ZMod 4) 1 := by
  have hsmul : (3 * X 0 : MvPolynomial (Fin 1) (ZMod 4)) = (3 : ZMod 4) • X 0 := by
    rw [Algebra.smul_def, map_ofNat]
  rw [hsmul]
  refine Submodule.smul_mem _ (3 : ZMod 4) ?_
  rw [mem_restrictDegree]
  intro s hs j
  have hs' : s = Finsupp.single 0 1 := by
    by_contra hne
    apply mem_support_iff.1 hs
    rw [coeff_X, ite_eq_right fun h => hne h.symm]
  subst hs'
  by_cases hj : j = 0 <;> simp [hj]

/-- Over the non-reduced ring `ZMod 4`, multilinear representatives remain unique modulo
`boolIdeal`: `X 0 ^ 3 + 2 * X 0 ^ 2` reduces uniquely to `3 * X 0` in `restrictDegree`. -/
example :
    (3 * X 0 : MvPolynomial (Fin 1) (ZMod 4)) ∈ restrictDegree (Fin 1) (ZMod 4) 1 ∧
      ((X 0 ^ 3 + 2 * X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 4)) - 3 * X 0) ∈
        boolIdeal (Fin 1) (ZMod 4) ∧
      ∀ q ∈ restrictDegree (Fin 1) (ZMod 4) 1,
        ((X 0 ^ 3 + 2 * X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 4)) - q) ∈
          boolIdeal (Fin 1) (ZMod 4) → q = 3 * X 0 := by
  have hmem := three_mul_X_mem_restrictDegree
  have hsub :
      ((X 0 ^ 3 + 2 * X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 4)) - 3 * X 0) ∈
        boolIdeal (Fin 1) (ZMod 4) := by
    rw [mem_boolIdeal_iff_forall_eval_bitPoint]
    intro x
    simp only [map_sub, map_add, map_pow, map_mul, map_ofNat, eval_X, bitPoint]
    cases x 0 <;> decide
  refine ⟨hmem, hsub, fun q hq hqsub => ?_⟩
  obtain ⟨r, _, huniq⟩ :=
    existsUnique_mem_restrictDegree_sub_mem_boolIdeal
      (X 0 ^ 3 + 2 * X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 4))
  exact (huniq q ⟨hq, hqsub⟩).trans (huniq _ ⟨hmem, hsub⟩).symm

/-- `boolIdeal` is radical over `ℚ`, `ℤ`, and `ZMod 2`, and is NOT radical over `ZMod 4` where
`(2 * X 0) ^ 2 = 0` lies in the ideal while `2 * X 0` does not vanish at `1`. -/
example :
    (boolIdeal (Fin 2) ℚ).IsRadical ∧
      (boolIdeal (Fin 2) ℤ).IsRadical ∧
      (boolIdeal (Fin 2) (ZMod 2)).IsRadical ∧
      ¬ (boolIdeal (Fin 1) (ZMod 4)).IsRadical := by
  refine ⟨boolIdeal_isRadical, boolIdeal_isRadical, boolIdeal_isRadical, fun hrad => ?_⟩
  have hsq : ((2 * X 0 : MvPolynomial (Fin 1) (ZMod 4)) ^ 2) ∈ boolIdeal (Fin 1) (ZMod 4) := by
    rw [mem_boolIdeal_iff_forall_eval_bitPoint]
    intro x
    simp only [map_pow, map_mul, map_ofNat, eval_X, bitPoint]
    cases x 0 <;> decide
  have hmem := hrad ⟨2, hsq⟩
  have h2 := mem_boolIdeal_iff_forall_eval_bitPoint.1 hmem (fun _ => true)
  simp only [map_mul, map_ofNat, eval_X, bitPoint, bitVal, ↓reduceIte, mul_one] at h2
  exact absurd h2 (by decide)

/-- Dimension of the Boolean-cube quotient and multilinear space over `ℚ`. -/
example :
    Module.finrank ℚ (MvPolynomial (Fin 2) ℚ ⧸ boolIdeal (Fin 2) ℚ) = 4 ∧
      Module.finrank ℚ (restrictDegree (Fin 2) ℚ 1) = 4 := by
  rw [finrank_boolQuotient, finrank_restrictDegree_one]
  norm_num

/-- Forward and inverse `restrictDegreeOneLinearEquiv` and `restrictDegreeOneQuotientEquiv`
evaluations and canonical representatives work across the `module` boundary. -/
example (p : restrictDegree (Fin 1) (ZMod 4) 1) (x : Fin 1 → Bool) :
    restrictDegreeOneLinearEquiv (Fin 1) (ZMod 4) p x = eval (bitPoint x) p.1 ∧
      ((restrictDegreeOneLinearEquiv (Fin 1) (ZMod 4)).symm (fun y => if y 0 then 3 else 0) :
        MvPolynomial (Fin 1) (ZMod 4)) =
        multilinearExtension (fun y => if y 0 then 3 else 0) ∧
      restrictDegreeOneQuotientEquiv (Fin 1) (ZMod 4) p =
        Ideal.Quotient.mk (boolIdeal (Fin 1) (ZMod 4)) p.1 ∧
      ((restrictDegreeOneQuotientEquiv (Fin 1) (ZMod 4)).symm
          (Ideal.Quotient.mk (boolIdeal (Fin 1) (ZMod 4)) (X 0 ^ 3 + 2 * X 0 ^ 2)) :
        MvPolynomial (Fin 1) (ZMod 4)) = 3 * X 0 := by
  refine ⟨restrictDegreeOneLinearEquiv_apply p x,
    coe_restrictDegreeOneLinearEquiv_symm _,
    restrictDegreeOneQuotientEquiv_apply p, ?_⟩
  rw [coe_restrictDegreeOneQuotientEquiv_symm_mk]
  refine eq_of_mem_restrictDegree_of_forall_eval_bitPoint
    (multilinearExtension_mem_restrictDegree _) three_mul_X_mem_restrictDegree fun y => ?_
  rw [eval_multilinearExtension]
  simp only [map_add, map_pow, map_mul, map_ofNat, eval_X, bitPoint]
  cases y 0 <;> decide

end BooleanQuotientTests

section AlgebraicCountingTests

open MvPolynomial Cslib.BitString Cslib.Logic.PL

private def unsatFin1 : CNF (Fin 1) := [[(0, true)], [(0, false)]]

private def sparseFin3 : CNF (Fin 3) := [[(0, true), (1, false)]]

local instance : Fact (1 < 4) := ⟨by decide⟩

/-- An unsatisfiable formula yields `1 ∈ span F ⊔ boolIdeal` over `ℚ`, its satisfaction indicator
lies in `boolIdeal`, and its Boolean-cube sum is `0`. -/
example :
    (1 : MvPolynomial (Fin 1) ℚ) ∈
        Ideal.span {p | p ∈ unsatFin1.toBoolPolys ℚ} ⊔ boolIdeal (Fin 1) ℚ ∧
      unsatFin1.satIndicatorPoly ℚ ∈ boolIdeal (Fin 1) ℚ ∧
      Ideal.Quotient.mk (boolIdeal (Fin 1) ℚ) (unsatFin1.satIndicatorPoly ℚ) = 0 ∧
      (∑ x : Fin 1 → Bool,
        MvPolynomial.eval (bitPoint (R := ℚ) x) (unsatFin1.satIndicatorPoly ℚ)) = 0 := by
  have hunsat : ¬ unsatFin1.Satisfiable := by
    rintro ⟨σ, hσ⟩
    have h0 := (CNF.eval_eq_true_iff σ unsatFin1).1 hσ [(0, true)] (by simp [unsatFin1])
    have h1 := (CNF.eval_eq_true_iff σ unsatFin1).1 hσ [(0, false)] (by simp [unsatFin1])
    cases hσ0 : σ 0 <;> simp [Clause.eval, Literal.eval, hσ0] at h0 h1
  have h1 : (1 : MvPolynomial (Fin 1) ℚ) ∈
      Ideal.span {p | p ∈ unsatFin1.toBoolPolys ℚ} ⊔ boolIdeal (Fin 1) ℚ :=
    CNF.one_mem_span_toBoolPolys_sup_boolIdeal_iff.2 hunsat
  have hind : unsatFin1.satIndicatorPoly ℚ ∈ boolIdeal (Fin 1) ℚ :=
    (CNF.satIndicatorPoly_mem_boolIdeal_iff unsatFin1).2 hunsat
  have hmk : Ideal.Quotient.mk (boolIdeal (Fin 1) ℚ) (unsatFin1.satIndicatorPoly ℚ) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 hind
  have hsum :
      (∑ x : Fin 1 → Bool,
        MvPolynomial.eval (bitPoint (R := ℚ) x) (unsatFin1.satIndicatorPoly ℚ)) = 0 := by
    rw [CNF.sum_eval_satIndicatorPoly]
    have hmc : unsatFin1.modelCount = 0 := by
      by_contra hne
      exact hunsat (CNF.modelCount_pos_iff.1 (Nat.pos_of_ne_zero hne))
    simp [hmc]
  exact ⟨h1, hind, hmk, hsum⟩

/-- On a 3-variable CNF whose clauses only touch variables `0` and `1`:
* `distinctVars` enumeration recovers `modelCount = 3`,
* the full `Fin 3 → Bool` cube sum over `ℤ` equals `2 ^ (3 - 2) * 3 = 6`,
* the clause polynomial annihilates `satIndicatorPoly` modulo `boolIdeal`, and
* `satIndicatorPoly` does not lie in `boolIdeal (Fin 3) (ZMod 4)`. -/
example :
    sparseFin3.numVars = 2 ∧
      sparseFin3.modelCount = 3 ∧
      (sparseFin3.satIndicatorPoly ℤ).totalDegree ≤ 2 ∧
      (∑ x : Fin 3 → Bool,
        MvPolynomial.eval (bitPoint (R := ℤ) x) (sparseFin3.satIndicatorPoly ℤ)) = 6 ∧
      [(0, true), (1, false)] ∈ sparseFin3 ∧
      Clause.toBoolPoly ℤ [(0, true), (1, false)] * sparseFin3.satIndicatorPoly ℤ ∈
        boolIdeal (Fin 3) ℤ ∧
      sparseFin3.satIndicatorPoly (ZMod 4) ∉ boolIdeal (Fin 3) (ZMod 4) := by
  have hdistinct : sparseFin3.distinctVars = [0, 1] := by decide
  have hnv : sparseFin3.numVars = 2 := by
    rw [← CNF.length_distinctVars, hdistinct]
    rfl
  have hmc : sparseFin3.modelCount = 3 := by
    have hsum := sparseFin3.sum_range_eval_satIndicatorPoly_distinctVars (R := ℤ)
    rw [hnv, hdistinct] at hsum
    have b0 : sparseFin3.eval (bitsAssignment [0, 1] 0) = true := by decide
    have b1 : sparseFin3.eval (bitsAssignment [0, 1] 1) = true := by decide
    have b2 : sparseFin3.eval (bitsAssignment [0, 1] 2) = false := by decide
    have b3 : sparseFin3.eval (bitsAssignment [0, 1] 3) = true := by decide
    have hev :
        (∑ i ∈ Finset.range (2 ^ 2),
          MvPolynomial.eval (bitPoint (R := ℤ) (bitsAssignment [0, 1] i))
            (sparseFin3.satIndicatorPoly ℤ)) = 3 := by
      rw [show (2 ^ 2 : ℕ) = 4 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
      simp only [CNF.eval_satIndicatorPoly, b0, b1, b2, b3, Bool.false_eq_true, ↓reduceIte]
      norm_num
    have heqz : (sparseFin3.modelCount : ℤ) = 3 := hsum.symm.trans hev
    exact_mod_cast heqz
  have hdeg : (sparseFin3.satIndicatorPoly ℤ).totalDegree ≤ 2 :=
    (CNF.totalDegree_satIndicatorPoly_le_mul (w := 2) fun c hc => by
      simp only [sparseFin3, List.mem_singleton] at hc
      subst hc
      decide).trans (by simp [sparseFin3])
  have hfull :
      (∑ x : Fin 3 → Bool,
        MvPolynomial.eval (bitPoint (R := ℤ) x) (sparseFin3.satIndicatorPoly ℤ)) = 6 := by
    rw [CNF.sum_eval_satIndicatorPoly, hnv, hmc]
    norm_num
  have hc : ([(0, true), (1, false)] : Clause (Fin 3)) ∈ sparseFin3 := by simp [sparseFin3]
  have hann := CNF.toBoolPoly_mul_satIndicatorPoly_mem_boolIdeal (R := ℤ) hc
  have hnotmem : sparseFin3.satIndicatorPoly (ZMod 4) ∉ boolIdeal (Fin 3) (ZMod 4) := by
    rw [← CNF.satisfiable_iff_satIndicatorPoly_notMem_boolIdeal]
    exact CNF.modelCount_pos_iff.1 (by omega)
  exact ⟨hnv, hmc, hdeg, hfull, hc, hann, hnotmem⟩

end AlgebraicCountingTests

section PolySpaceSATTests

open Cslib.Logic.PL Cslib.Complexity

private def gapFormula : CNF ℕ := [[(10, true), (3, false)]]

private def uniqueFormula : CNF ℕ := [[(4, true)], [(7, false)]]

private def unsatNatFormula : CNF ℕ := [[(0, true)], [(0, false)]]

/-- Concrete `CNF ℕ` counts via `streamAcceptCount SAT.distinctVerifier φ φ.numVars` and
complexity endpoints `SAT / UNSAT / USAT ∈ PSPACE encCNF` and `#SAT` in polynomial space. -/
example :
    gapFormula.numVars = 2 ∧
      streamAcceptCount SAT.distinctVerifier gapFormula gapFormula.numVars = 3 ∧
      streamAcceptCount SAT.distinctVerifier uniqueFormula uniqueFormula.numVars = 1 ∧
      streamAcceptCount SAT.distinctVerifier ([] : CNF ℕ) (CNF.numVars ([] : CNF ℕ)) = 1 ∧
      streamAcceptCount SAT.distinctVerifier unsatNatFormula unsatNatFormula.numVars = 0 ∧
      gapFormula ∈ SAT ∧
      gapFormula ∉ USAT ∧
      uniqueFormula ∈ USAT ∧
      unsatNatFormula ∈ UNSAT ∧
      SAT ∈ PSPACE encCNF ∧
      UNSAT ∈ PSPACE encCNF ∧
      USAT ∈ PSPACE encCNF ∧
      Turing.MultiTapeTM.ComputableInPolySpace SharpSAT encCNF Turing.MultiTapeTM.encNat := by
  have hg_nv : gapFormula.numVars = 2 := by
    rw [← CNF.length_distinctVars]
    decide
  have hu_nv : uniqueFormula.numVars = 2 := by
    rw [← CNF.length_distinctVars]
    decide
  have huns_nv : unsatNatFormula.numVars = 1 := by
    rw [← CNF.length_distinctVars]
    decide
  have hstream_gap :
      streamAcceptCount SAT.distinctVerifier gapFormula gapFormula.numVars = 3 := by
    rw [hg_nv]
    decide
  have hstream_unique :
      streamAcceptCount SAT.distinctVerifier uniqueFormula uniqueFormula.numVars = 1 := by
    rw [hu_nv]
    decide
  have hstream_empty :
      streamAcceptCount SAT.distinctVerifier ([] : CNF ℕ) (CNF.numVars ([] : CNF ℕ)) = 1 := by
    have hnv0 : CNF.numVars ([] : CNF ℕ) = 0 := by
      rw [← CNF.length_distinctVars]
      rfl
    rw [hnv0]
    decide
  have hstream_unsat :
      streamAcceptCount SAT.distinctVerifier unsatNatFormula unsatNatFormula.numVars = 0 := by
    rw [huns_nv]
    decide
  have hsharp_gap : SharpSAT gapFormula = 3 :=
    (SAT.streamAcceptCount_distinctVerifier_eq gapFormula).symm.trans hstream_gap
  have hsharp_unique : SharpSAT uniqueFormula = 1 :=
    (SAT.streamAcceptCount_distinctVerifier_eq uniqueFormula).symm.trans hstream_unique
  have hsharp_unsat : SharpSAT unsatNatFormula = 0 :=
    (SAT.streamAcceptCount_distinctVerifier_eq unsatNatFormula).symm.trans hstream_unsat
  exact ⟨hg_nv, hstream_gap, hstream_unique, hstream_empty, hstream_unsat,
    SharpSAT.mem_SAT_iff.2 (by omega),
    fun h => by rw [SharpSAT.mem_USAT_iff, hsharp_gap] at h; omega,
    SharpSAT.mem_USAT_iff.2 hsharp_unique,
    fun h => by have := SharpSAT.mem_SAT_iff.1 h; omega,
    SAT.mem_PSPACE_of_enumeration,
    UNSAT.mem_PSPACE_of_enumeration,
    USAT.mem_PSPACE_of_enumeration,
    SharpSAT.computableInPolySpace_numVars⟩

end PolySpaceSATTests
