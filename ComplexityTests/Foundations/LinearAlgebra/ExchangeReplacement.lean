/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Init
public import Complexity.Foundations.LinearAlgebra.ExchangeReplacement
import Mathlib.Tactic.NormNum

/-!
# Tests for auxiliary exchange matrices and polynomial replacement rows

Verifies the interfaces of `Complexity.Foundations.LinearAlgebra.ExchangeReplacement` (Lemmas 4.1,
4.2, 4.3, Remark 4.4, and Lemma 4.6 of `openai/math@7ef5c0cc`), including concrete nonvacuity
witnesses for `Q = 2, r = 2, A₀ = 0, R = 2`.
-/

@[expose] public section

namespace Cslib.LinearAlgebra.Tests

open Finset Matrix Polynomial

-- 1. Dimension of the auxiliary coordinate space `B = ([r]^Q)²` for `Q = 2, r = 2`.
example : Fintype.card (AuxLabel 2 2) = 16 := by
  simp

-- 2. Parity interpolation polynomial `fI 0 2` on `I = {0, 1}` (Remark 4.4, p. 30).
example :
    (fI 0 2).natDegree ≤ 1 ∧ (fI 0 2).eval 0 = 1 ∧ (fI 0 2).eval 1 = -1 := by
  refine ⟨natDegree_fI_le 0 2, ?_, ?_⟩
  · simpa using eval_fI_of_mem_Ico (A₀ := 0) (R := 2) (k := 0) (by decide)
  · simpa using eval_fI_of_mem_Ico (A₀ := 0) (R := 2) (k := 1) (by decide)

-- 3. Nontrivial eigenvector in `I = {0, 1}` lies in `ker C^B` and is fixed by `M_0` (Lemma 4.1).
section NontrivialKernelWitness

/-- The diagonal label `β₀ = (00, 00) ∈ AuxLabel 2 2` has `antisymCount β₀ = 0 ∈ Ico 0 2`. -/
def β₀ : AuxLabel 2 2 := (fun _ => 0, fun _ => 0)

example : antisymCount β₀ ∈ Ico 0 2 := by
  decide

/-- Because the basis `eigenvec ℚ β` is pairwise orthogonal, `eigenvec ℚ β₀` is in the kernel of
`measurementMatrix 2 2 0 2 ℚ` and is a nonzero fixed point of `M0 2 2 0 2`. -/
example :
    eigenvec ℚ β₀ β₀ = 1 ∧
      (measurementMatrix 2 2 0 2 ℚ).mulVec (eigenvec ℚ β₀) = 0 ∧
      (M0 2 2 0 2).mulVec (eigenvec ℚ β₀) = eigenvec ℚ β₀ := by
  have hval : eigenvec ℚ β₀ β₀ = 1 := by
    change (eigenvecInt β₀ β₀ : ℚ) = 1
    have hZ : eigenvecInt β₀ β₀ = 1 := by decide
    exact_mod_cast hZ
  have hker : (measurementMatrix 2 2 0 2 ℚ).mulVec (eigenvec ℚ β₀) = 0 := by
    rw [measurementMatrix_mulVec_eq_zero_iff]
    intro β hβ
    have hne : β ≠ β₀ := by
      intro hEq
      subst hEq
      exact hβ (by decide)
    change (∑ u : AuxLabel 2 2, (eigenvecInt β u : ℚ) * (eigenvecInt β₀ u : ℚ)) = 0
    have horth := congrArg (Int.cast : ℤ → ℚ) (sum_eigenvecInt_mul_eigenvecInt β β₀)
    push_cast at horth
    simpa [hne] using horth
  exact ⟨hval, hker, M0_mulVec_eq_self_of_measurementMatrix_mulVec_eq_zero hker⟩

end NontrivialKernelWitness

-- 4. Remark 4.4 (p. 30): 4-coordinate exchange orbit starting from `u₀ = (00, 11)`.
section Remark44

/-- `u₀ = (00, 11)` in `AuxLabel 2 2`. -/
def u₀ : AuxLabel 2 2 := (fun _ => 0, fun _ => 1)

/-- `u₁ = ϑ₀(u₀) = (10, 01)`. -/
def u₁ : AuxLabel 2 2 := slotSwap 0 u₀

/-- `u₂ = ϑ₁(u₀) = (01, 10)`. -/
def u₂ : AuxLabel 2 2 := slotSwap 1 u₀

/-- `u₁₂ = ū₀ = (11, 00)`. -/
def u₁₂ : AuxLabel 2 2 := fullSwap u₀

/-- On the 4-coordinate orbit of `u₀ = (00, 11)`, `M0ScaledInt 2 2 0 2` (which equals `M0 2 2 0 2`
since `(R - 1)! = 1! = 1`) has row entries `0, 1, 1, -1` on `u₀, u₁, u₂, u₁₂`, matching
`M_0 = Π_1 + Π_2 - Π_1 Π_2` in Remark 4.4 (p. 30). -/
example :
    M0ScaledInt 2 2 0 2 u₀ u₀ = 0 ∧
      M0ScaledInt 2 2 0 2 u₀ u₁ = 1 ∧
      M0ScaledInt 2 2 0 2 u₀ u₂ = 1 ∧
      M0ScaledInt 2 2 0 2 u₀ u₁₂ = -1 := by
  decide

/-- Mismatch sets `E_{u₀, y}` on the 4-coordinate orbit in Remark 4.4 (p. 30):
`u₁` mismatches at slot `1` (`nodePoint 1 = 2`), `u₂` mismatches at slot `0` (`nodePoint 0 = 1`),
and `u₁₂` has no mismatches (`E_{u₀, u₁₂} = ∅`). -/
example :
    mismatchSet u₀ u₁ = {1} ∧
      mismatchSet u₀ u₂ = {0} ∧
      mismatchSet u₀ u₁₂ = ∅ := by
  decide

/-- At `t = nodePoint 0 = 1`, `mismatchAnnihilator u₀ u₂` vanishes (`u₂.1 0 = 0 ≠ 1 = u₀.2 0`);
at `t = nodePoint 1 = 2`, `mismatchAnnihilator u₀ u₁` vanishes (`u₁.1 1 = 0 ≠ 1 = u₀.2 1`). -/
example :
    (mismatchAnnihilator u₀ u₂).eval (nodePoint (0 : Fin 2)) = 0 ∧
      (mismatchAnnihilator u₀ u₁).eval (nodePoint (1 : Fin 2)) = 0 :=
  ⟨eval_mismatchAnnihilator_nodePoint_of_ne (by decide),
   eval_mismatchAnnihilator_nodePoint_of_ne (by decide)⟩

end Remark44

-- 5. Degree bound, value at zero, and common-denominator clearing (Lemmas 4.3 & 4.6).
example (u y : AuxLabel 2 2) :
    (auxReplacementRow 2 2 0 2 u y).natDegree ≤ 1 ∧
      (auxReplacementRow 2 2 0 2 u y).eval 0 = (if u = y then 1 else 0) ∧
      (auxReplacementRowScaledInt 2 2 0 2 u y).map (Int.castRingHom ℚ) =
        (commonDenom 2 2 : ℚ) • auxReplacementRow 2 2 0 2 u y :=
  ⟨natDegree_auxReplacementRow_le 2 2 0 2 u y,
   eval_auxReplacementRow_zero 2 2 0 2 u y,
   map_auxReplacementRowScaledInt 2 2 0 2 u y⟩

end Cslib.LinearAlgebra.Tests
