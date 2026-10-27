/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseHermiteRecovery

/-!
# Stage-1/Stage-2 jet-table Hermite–Cramer recovery

This module connects `clearedParityJetTable` to the Hermite–Cramer recovery API in
`Complexity.Foundations.BooleanAnalysis.SparseHermiteRecovery`. It proves coordinate recovery
for finite parity systems and branch-summed recovery over arbitrary finite variable types,
independently of CNF formulas. The CNF specializations and examination bounds are in
`Complexity.Computability.Complexity.FineGrained.GeneralCNFHermiteRecovery`.

## Main results

* `Cslib.BitString.hermiteCramerNumerator_clearedParityJetTable_eq_mul`,
  `Cslib.BitString.emod_sum_hermiteCramerNumerator_clearedParityJetTable_ediv_eq_commonZeroCount`,
  `Cslib.BitString.emod_sum_hermiteCramerNumerator_clearedParityJetTable_design_eq_commonZeroCount`,
  `Cslib.BitString.commonZeroCount_eq_sum_branch_hermiteCramerNumerator_design_of_fintype`,
  `Cslib.BitString.commonZeroCount_eq_sum_branch_clearedParityJetTable_design`

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
  (Sections 5.4–5.5 and Appendix B.2–B.3, printed pp. 37–39, 48–50)
-/

@[expose] public noncomputable section

open Finset Polynomial
open scoped BigOperators

namespace Cslib.BitString

open Cslib.LinearAlgebra

variable {ι κ : Type*}

/-- **Cramer numerator factorization for `clearedParityJetTable` (Appendix B.2–B.3, eq. `(B.1)`,
pp. 48–50)**: when `(k * R_deg) * (#I + 2 * (ℓ - 1)) < Q * J`, the Cramer determinant of the
`s`-th `V`-degree coordinate (`s : Fin ℓ`) of the Stage-1/Stage-2 integer Taylor-jet table
`clearedParityJetTable I P d_den k ℓ J θ` at `nodes` equals
`(Polynomial.hermiteMatrix nodes J).det *`
`(univariateClearedParityCoord I P d_den k ℓ θ s.1).eval 0`. -/
theorem hermiteCramerNumerator_clearedParityJetTable_eq_mul [Fintype ι] [DecidableEq ι]
    (I : Finset κ) (P : κ → Finset (Finset ι)) (d_den : ℤ) {k ℓ R_deg Q J : ℕ}
    (nodes : Fin Q → ℤ) (hQ : 0 < Q) (hJ : 0 < J)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (θ x i v).natDegree ≤ R_deg)
    (hQJ : (k * R_deg) * (#I + 2 * (ℓ - 1)) < Q * J) (s : Fin ℓ) :
    hermiteCramerNumerator nodes hQ hJ
        (fun t j => clearedParityJetTable I P d_den k ℓ J θ (nodes t) j s) =
      (Polynomial.hermiteMatrix nodes J).det *
        (univariateClearedParityCoord I P d_den k ℓ θ s.1).eval 0 := by
  simp only [clearedParityJetTable_apply]
  exact hermiteCramerNumerator_univariateClearedParityCoord_eq_mul I P d_den nodes hQ hJ θ hk hθ
    hQJ s.2

/-- **Unconditional Stage-1/Stage-2 `clearedParityJetTable` Hermite–Cramer coordinate recovery of
`commonZeroCount` (Appendix B.2–B.3, eq. `(B.1)`, pp. 48–50)**: at distinct integer nodes
`nodes : Fin Q → ℤ` with `(k * R_deg) * (#I + 2 * (ℓ - 1)) < Q * J`, `d_den ≠ 0`, and
`Fintype.card ι < ℓ`, summing the exact integer Cramer quotients of `clearedParityJetTable` over
`s : Fin ℓ` and reducing modulo `2 ^ ℓ` recovers `commonZeroCount I P`. -/
theorem emod_sum_hermiteCramerNumerator_clearedParityJetTable_ediv_eq_commonZeroCount
    [Fintype ι] [DecidableEq ι] (I : Finset κ) (P : κ → Finset (Finset ι)) {d_den : ℤ}
    (hd : d_den ≠ 0) {k ℓ R_deg Q J : ℕ} {nodes : Fin Q → ℤ} (hnodes : Function.Injective nodes)
    (hQ : 0 < Q) (hJ : 0 < J) (hℓ : Fintype.card ι < ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hdeg : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (θ x i v).natDegree ≤ R_deg)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M,
      (θ x i v).eval 0 = d_den * bitVal ℤ (x v))
    (hQJ : (k * R_deg) * (#I + 2 * (ℓ - 1)) < Q * J) :
    (∑ s : Fin ℓ,
      hermiteCramerNumerator nodes hQ hJ
        (fun t j => clearedParityJetTable I P d_den k ℓ J θ (nodes t) j s) /
        (clearedProductDenom d_den k ℓ #I * (Polynomial.hermiteMatrix nodes J).det)) %
          ((2 : ℤ) ^ ℓ) =
      commonZeroCount I P := by
  simp only [clearedParityJetTable_apply]
  rw [Fin.sum_univ_eq_sum_range (fun s =>
    hermiteCramerNumerator nodes hQ hJ
      (fun t j =>
        (Polynomial.taylor (nodes t)
          (univariateClearedParityCoord I P d_den k ℓ θ s)).coeff j.1) /
      (clearedProductDenom d_den k ℓ #I * (Polynomial.hermiteMatrix nodes J).det))]
  exact emod_sum_hermiteCramerNumerator_ediv_eq_commonZeroCount I P hd hnodes hQ hJ hℓ θ hk hdeg
    hθ hQJ

/-- **Concrete `ReplacementDesign` Stage-1/Stage-2 `clearedParityJetTable` Hermite–Cramer
coordinate recovery of `commonZeroCount` (§5.4 & Appendix B.2–B.3, eq. `(B.1)`, pp. 48–50)**:
for any `D : ReplacementDesign scope Q r A₀ R τ` with `0 < Q`, `0 < J`, `n < ℓ`,
`∀ i ∈ I, ∀ M ∈ P i, #M ≤ k`, and `(k * (R - 1)) * (#I + 2 * (ℓ - 1)) < Q * J`, summing the
Cramer quotients of `clearedParityJetTable` at `nodeInt` over `s : Fin ℓ` and reducing modulo
`2 ^ ℓ` recovers `commonZeroCount I P`. -/
theorem emod_sum_hermiteCramerNumerator_clearedParityJetTable_design_eq_commonZeroCount
    {n Q r A₀ R : ℕ} {τ : ℚ} {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (D : ReplacementDesign scope Q r A₀ R τ) (emb : κ → F)
    (I : Finset κ) (P : κ → Finset (Finset (Fin n))) {k ℓ J : ℕ}
    (hQ : 0 < Q) (hJ : 0 < J) (hℓ : n < ℓ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hQJ : (k * (R - 1)) * (#I + 2 * (ℓ - 1)) < Q * J) :
    (∑ s : Fin ℓ,
      hermiteCramerNumerator (nodeInt (Q := Q)) hQ hJ
        (fun t j =>
          clearedParityJetTable I P (commonDenom Q R : ℤ) k ℓ J
            (designReplacementScaledIntMap D emb) (nodeInt t) j s) /
        (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I *
          (Polynomial.hermiteMatrix (nodeInt (Q := Q)) J).det)) % ((2 : ℤ) ^ ℓ) =
      commonZeroCount I P := by
  simp only [clearedParityJetTable_apply]
  rw [Fin.sum_univ_eq_sum_range (fun s =>
    hermiteCramerNumerator (nodeInt (Q := Q)) hQ hJ
      (fun t j =>
        (Polynomial.taylor (nodeInt t)
          (univariateClearedParityCoord I P (commonDenom Q R : ℤ) k ℓ
            (designReplacementScaledIntMap D emb) s)).coeff j.1) /
      (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I *
        (Polynomial.hermiteMatrix (nodeInt (Q := Q)) J).det))]
  exact emod_sum_hermiteCramerNumerator_design_eq_commonZeroCount D emb I P hQ hJ hℓ hk hQJ

/-- **§5.5 & Appendix B.3 branch-summed Hermite–Cramer truncated-sum recovery of `commonZeroCount`
over arbitrary finite variable types `[Fintype ι] [DecidableEq ι]`**: given a heavy-variable subset
`S : Finset ι`, a free-variable relabeling `e : ↥(univ \ S) ≃ Fin n'`, and a per-branch
`ReplacementDesign` family `D b` (`0 < Q`), summing the branch modular residues of the concrete
`hermiteCramerNumerator` quotients at `nodeInt` and canonical jet order
`J = sparseParityJetOrder k R Q #I (branchPrecision (Fintype.card ι))` across
`b ∈ branchAssignments S` recovers `commonZeroCount I P`. -/
theorem commonZeroCount_eq_sum_branch_hermiteCramerNumerator_design_of_fintype
    [Fintype ι] [DecidableEq ι] {n' Q r A₀ R : ℕ} {τ : ℚ}
    {F : (ι → Bool) → Type*} [∀ b, Fintype (F b)]
    (S : Finset ι) (e : ↥(univ \ S) ≃ Fin n')
    (I : Finset κ) (P : κ → Finset (Finset ι)) {k : ℕ}
    (scope : (b : ι → Bool) → F b → Finset (Fin n'))
    (D : (b : ι → Bool) → ReplacementDesign (scope b) Q r A₀ R τ)
    (emb : (b : ι → Bool) → κ → F b)
    (hQ : 0 < Q) (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k) :
    let ℓ := branchPrecision (Fintype.card ι)
    let J := sparseParityJetOrder k R Q #I ℓ
    (commonZeroCount I P : ℤ) =
      ∑ b ∈ branchAssignments S,
        (hermiteCramerNumerator (nodeInt (Q := Q)) hQ (sparseParityJetOrder_pos k R Q #I ℓ)
          (fun t j =>
            (Polynomial.taylor (nodeInt t)
              (univariateClearedParityTruncatedSum I
                (fun i => relabelRestrictedMonomials S e b (P i))
                (commonDenom Q R : ℤ) k ℓ
                (designReplacementScaledIntMap (D b) (emb b)))).coeff j) /
          (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I *
            (Polynomial.hermiteMatrix (nodeInt (Q := Q)) J).det)) % ((2 : ℤ) ^ ℓ) := by
  intro ℓ J
  rw [commonZeroCount_eq_sum_branch_emod_ediv_cleared S e I P (commonDenom_intCast_ne_zero Q R)
    (fun b => designReplacementScaledIntMap (D b) (emb b)) hk
    (fun b _ x j _ _ _ v _ => eval_zero_designReplacementScaledIntMap (D b) (emb b) x j v)]
  refine sum_congr rfl fun b _ => ?_
  have hlt : n' < ℓ := by
    have hle : n' ≤ Fintype.card ι := by
      simpa only [Fintype.card_fin] using
        (Fintype.card_congr e).symm.trans_le (Fintype.card_subtype_le _)
    change n' < Fintype.card ι + 1
    omega
  have hk_branch : ∀ i ∈ I, ∀ M ∈ relabelRestrictedMonomials S e b (P i), #M ≤ k :=
    fun i hi M hM => card_mem_relabelRestrictedMonomials_le (hk i hi) M hM
  rw [emod_hermiteCramerNumerator_truncatedSum_design_eq_commonZeroCount (D b) (emb b) I
    (fun i => relabelRestrictedMonomials S e b (P i)) hQ (sparseParityJetOrder_pos k R Q #I ℓ)
    hlt hk_branch (lt_mul_sparseParityJetOrder k R #I ℓ hQ)]
  exact emod_ediv_eval_zero_clearedParityTruncatedSum_design_eq_commonZeroCount (D b) (emb b) I
    (fun i => relabelRestrictedMonomials S e b (P i)) hlt hk_branch

/-- **§5.5 & Appendix B.2–B.3 branch-summed Stage-1/Stage-2 `clearedParityJetTable` Hermite–Cramer
coordinate recovery of `commonZeroCount` over arbitrary finite variable types**: under the same
hypotheses, summing the coordinate Cramer quotients of `clearedParityJetTable` over `s : Fin ℓ`
modulo `2 ^ ℓ` on each branch and summing across `b ∈ branchAssignments S` recovers
`commonZeroCount I P`. -/
theorem commonZeroCount_eq_sum_branch_clearedParityJetTable_design
    [Fintype ι] [DecidableEq ι] {n' Q r A₀ R : ℕ} {τ : ℚ}
    {F : (ι → Bool) → Type*} [∀ b, Fintype (F b)]
    (S : Finset ι) (e : ↥(univ \ S) ≃ Fin n')
    (I : Finset κ) (P : κ → Finset (Finset ι)) {k : ℕ}
    (scope : (b : ι → Bool) → F b → Finset (Fin n'))
    (D : (b : ι → Bool) → ReplacementDesign (scope b) Q r A₀ R τ)
    (emb : (b : ι → Bool) → κ → F b)
    (hQ : 0 < Q) (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k) :
    let ℓ := branchPrecision (Fintype.card ι)
    let J := sparseParityJetOrder k R Q #I ℓ
    (commonZeroCount I P : ℤ) =
      ∑ b ∈ branchAssignments S,
        (∑ s : Fin ℓ,
          hermiteCramerNumerator (nodeInt (Q := Q)) hQ (sparseParityJetOrder_pos k R Q #I ℓ)
            (fun t j =>
              clearedParityJetTable I
                (fun i => relabelRestrictedMonomials S e b (P i))
                (commonDenom Q R : ℤ) k ℓ J
                (designReplacementScaledIntMap (D b) (emb b)) (nodeInt t) j s) /
            (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #I *
              (Polynomial.hermiteMatrix (nodeInt (Q := Q)) J).det)) % ((2 : ℤ) ^ ℓ) := by
  intro ℓ J
  rw [commonZeroCount_eq_sum_branch_emod_ediv_cleared S e I P (commonDenom_intCast_ne_zero Q R)
    (fun b => designReplacementScaledIntMap (D b) (emb b)) hk
    (fun b _ x j _ _ _ v _ => eval_zero_designReplacementScaledIntMap (D b) (emb b) x j v)]
  refine sum_congr rfl fun b _ => ?_
  have hlt : n' < ℓ := by
    have hle : n' ≤ Fintype.card ι := by
      simpa only [Fintype.card_fin] using
        (Fintype.card_congr e).symm.trans_le (Fintype.card_subtype_le _)
    change n' < Fintype.card ι + 1
    omega
  have hk_branch : ∀ i ∈ I, ∀ M ∈ relabelRestrictedMonomials S e b (P i), #M ≤ k :=
    fun i hi M hM => card_mem_relabelRestrictedMonomials_le (hk i hi) M hM
  rw [emod_sum_hermiteCramerNumerator_clearedParityJetTable_design_eq_commonZeroCount (D b) (emb b)
    I (fun i => relabelRestrictedMonomials S e b (P i)) hQ (sparseParityJetOrder_pos k R Q #I ℓ)
    hlt hk_branch (lt_mul_sparseParityJetOrder k R #I ℓ hQ)]
  exact emod_ediv_eval_zero_clearedParityTruncatedSum_design_eq_commonZeroCount (D b) (emb b) I
    (fun i => relabelRestrictedMonomials S e b (P i)) hlt hk_branch

end Cslib.BitString
