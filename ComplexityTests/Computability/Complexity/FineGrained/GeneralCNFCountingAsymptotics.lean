/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.GeneralCNFCountingAsymptotics

/-!
# Tests for `Complexity.Computability.Complexity.FineGrained.GeneralCNFCountingAsymptotics`

Exercises the normalized Proposition 6.4 leaf decomposition (`CNF.prop64NormalizedLeaves`),
leaf-count bounds against `numGroups` and `interpolationScale`, Lemma 6.2 candidate-query indexing
and bounds (`CNF.LeafCandidateQueryIndex`, `CNF.candidateQueryRows`,
`CNF.card_leafCandidateQueryIndex_eq`, `CNF.card_leafCandidateQueryIndex_le`,
`CNF.candidateQueryRows_length_and_weight_le`, `CNF.greedyRowListLength_le_mul_pow_clog`), and the
end-to-end candidate-indexed and tree-wide `ReplacementDesign` recovery and actual
`toCountingDesign` examination bounds on concrete 3-CNF formulas containing tautological clauses.
-/

public noncomputable section

namespace CslibTests

open Finset
open Cslib.BitString
open Cslib.LinearAlgebra
open Cslib.Logic.PL
open Cslib.Logic.PL.ClauseSet.Sparsification
open Cslib.Complexity.SubexponentialSAT
open Cslib.Complexity.SubexponentialSAT.ReplacementParams

/-- Concrete 3-CNF on `Fin 4` containing a width-3 tautological clause
`[(0, true), (0, false), (1, true)]` together with two non-tautological clauses
`(x₀ ∨ ¬x₁ ∨ x₂) ∧ (¬x₁ ∨ ¬x₃)`. -/
def sampleTaut3CNF : CNF (Fin 4) :=
  [[(0, true), (0, false), (1, true)],
   [(0, true), (1, false), (2, true)],
   [(1, false), (3, false)]]

theorem sampleTaut3CNF_width_le_three :
    ∀ c ∈ sampleTaut3CNF, c.length ≤ 3 := by
  decide

theorem sampleTaut3CNF_modelCountOn_eq_eleven :
    sampleTaut3CNF.modelCountOn Finset.univ = 11 := by
  decide

/-- Summing `L.toCNF.modelCountOn Finset.univ` across `sampleTaut3CNF.prop64NormalizedLeaves 3`
recovers the exact model count `11` despite the tautological clause in `sampleTaut3CNF`. -/
theorem sampleTaut3CNF_sum_modelCountOn_prop64NormalizedLeaves :
    ((sampleTaut3CNF.prop64NormalizedLeaves 3).map
      fun L => L.toCNF.modelCountOn Finset.univ).sum = 11 := by
  rw [CNF.sum_modelCountOn_prop64NormalizedLeaves, sampleTaut3CNF_modelCountOn_eq_eleven]

/-- On the satisfying assignment `fun _ => false`, exactly `1` normalized leaf formula of
`sampleTaut3CNF` evaluates to `true`. -/
theorem sampleTaut3CNF_countP_eval_prop64NormalizedLeaves_true :
    ((sampleTaut3CNF.prop64NormalizedLeaves 3).map ClauseSet.toCNF).countP
      (fun F => F.eval (fun _ : Fin 4 => false)) = 1 := by
  rw [CNF.countP_eval_toCNF_prop64NormalizedLeaves]
  decide

/-- On the falsifying assignment `fun _ => true`, `0` normalized leaf formulas of
`sampleTaut3CNF` evaluate to `true`. -/
theorem sampleTaut3CNF_countP_eval_prop64NormalizedLeaves_false :
    ((sampleTaut3CNF.prop64NormalizedLeaves 3).map ClauseSet.toCNF).countP
      (fun F => F.eval (fun _ : Fin 4 => true)) = 0 := by
  rw [CNF.countP_eval_toCNF_prop64NormalizedLeaves]
  decide

/-- Every leaf `L ∈ sampleTaut3CNF.prop64NormalizedLeaves 3` is reduced, free of complementary
literals within each clause (the tautological clause has been filtered out), has clause width at
most `3`, and satisfies `L.toCNF.length ≤ CNF.prop64LeafClauseRatio 3 4 * 4`. -/
theorem sampleTaut3CNF_leaf_nontautological_and_length_le
    {L : ClauseSet (Fin 4)} (hL : L ∈ sampleTaut3CNF.prop64NormalizedLeaves 3) :
    Reduced L ∧
    (∀ C ∈ L, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C) ∧
    (∀ c ∈ L.toCNF, c.length ≤ 3) ∧
    L.toCNF.length ≤ CNF.prop64LeafClauseRatio 3 4 * 4 := by
  obtain ⟨_, hred, hnt, hk_L, _, hlen_L⟩ :=
    CNF.length_le_of_mem_prop64NormalizedLeaves sampleTaut3CNF_width_le_three hL
  exact ⟨hred, hnt, hk_L, hlen_L (by decide : 1 ≤ Fintype.card (Fin 4))⟩

/-- Concrete check of `CNF.card_leafCandidateQueryIndex_eq`, `CNF.card_leafCandidateQueryIndex_le`,
`CNF.greedyRowListLength_le_mul_pow_clog`, and `CNF.candidateQueryRows_length_and_weight_le` on
both a round-`0` candidate query `Sum.inl (0, γ₀)` and the final query `Sum.inr ()` for
`sampleTaut3CNF`. -/
theorem sampleTaut3CNF_candidateQueryIndex_and_rows_bounds :
    Fintype.card (CNF.LeafCandidateQueryIndex (Fin 4) 2 sampleTaut3CNF) =
      12 * 6 ^ (Cslib.BitString.greedyRowListLength 2 3) + 1 ∧
    Fintype.card (CNF.LeafCandidateQueryIndex (Fin 4) 2 sampleTaut3CNF) ≤
      CNF.leafCandidateQueryBound 2 sampleTaut3CNF ∧
    Cslib.BitString.greedyRowListLength 2 sampleTaut3CNF.length ≤
      20000 * 2 ^ 2 * (Nat.clog 2 (2 * sampleTaut3CNF.length + 4)) ^ 2 ∧
    let γ₀ : Fin (Cslib.BitString.greedyRowListLength 2 sampleTaut3CNF.length) →
        Fin sampleTaut3CNF.length × Bool :=
      fun _ => (⟨0, by decide⟩, true)
    let A : ℕ → List (Fin sampleTaut3CNF.length → Bool) :=
      fun i => List.replicate i (testRow γ₀)
    let q_cand : CNF.LeafCandidateQueryIndex (Fin 4) 2 sampleTaut3CNF :=
      Sum.inl (⟨0, by decide⟩, γ₀)
    let q_final : CNF.LeafCandidateQueryIndex (Fin 4) 2 sampleTaut3CNF := Sum.inr ()
    (CNF.candidateQueryRows A q_cand).length ≤ 24 ∧
    (∀ r ∈ CNF.candidateQueryRows A q_cand,
      weight r ≤ Cslib.BitString.initialRowWeightBound 2 sampleTaut3CNF.length) ∧
    (CNF.candidateQueryRows A q_final).length ≤ 24 ∧
    (∀ r ∈ CNF.candidateQueryRows A q_final,
      weight r ≤ Cslib.BitString.initialRowWeightBound 2 sampleTaut3CNF.length) := by
  refine ⟨?_, CNF.card_leafCandidateQueryIndex_le 2 sampleTaut3CNF,
    CNF.greedyRowListLength_le_mul_pow_clog 2 sampleTaut3CNF.length, ?_⟩
  · rw [CNF.card_leafCandidateQueryIndex_eq, Fintype.card_fin,
      show sampleTaut3CNF.length = 3 by rfl, show 3 * 4 = 12 by rfl, show 2 * 3 = 6 by rfl]
  · intro γ₀ A q_cand q_final
    have hA : ∀ i, A (i + 1) = A i ++ [testRow γ₀] := fun i => List.replicate_succ'
    have hcand := CNF.candidateQueryRows_length_and_weight_le (B := 2) (ψ := sampleTaut3CNF)
      (A₀ := []) (Nat.zero_le _) (fun _ hr => nomatch hr) (A := A) (γ := fun _ => γ₀) rfl hA q_cand
    have hfinal := CNF.candidateQueryRows_length_and_weight_le (B := 2) (ψ := sampleTaut3CNF)
      (A₀ := []) (Nat.zero_le _) (fun _ hr => nomatch hr) (A := A) (γ := fun _ => γ₀) rfl hA q_final
    simpa only [Fintype.card_fin] using ⟨hcand.1, hcand.2, hfinal.1, hfinal.2⟩

/-- At `k = 3`, the Proposition 6.4 `interpolationScale` exponent multipliers form a strictly
increasing chain. -/
theorem prop64_scale_coeffs_strict_mono_k3 :
    CNF.prop64BranchExamScaleCoeff 3 < CNF.prop64LeafQueryExamScaleCoeff 3 ∧
    CNF.prop64LeafQueryExamScaleCoeff 3 < CNF.prop64TreeExamScaleCoeff 3 ∧
    CNF.prop64TreeExamScaleCoeff 3 < CNF.prop64TotalExamScaleCoeff 3 := by
  unfold CNF.prop64LeafQueryExamScaleCoeff CNF.prop64TreeExamScaleCoeff
    CNF.prop64TotalExamScaleCoeff
  omega

/-- Concrete 3-CNF on `Fin N` (`1 ≤ N`) with one tautological clause and one width-3 clause. -/
def sampleLargeTaut3CNF (N : ℕ) [NeZero N] : CNF (Fin N) :=
  [[(0, true), (0, false), (0, true)],
   [(0, true), (0, true), (0, true)]]

theorem sampleLargeTaut3CNF_width_le_three (N : ℕ) [NeZero N] :
    ∀ c ∈ sampleLargeTaut3CNF N, c.length ≤ 3 := by
  intro c hc
  simp only [sampleLargeTaut3CNF, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp

private theorem pos_of_two_pow_le {m n : ℕ} (h : 2 ^ m ≤ n) : 0 < n :=
  lt_of_lt_of_le (Nat.pow_pos two_pos) h

/-- Nonvacuous instantiation of
`CNF.exists_prop64NormalizedLeaves_total_recovery_and_examBound` at `k = 3` on a concrete 3-CNF
with a tautological clause over `V = Fin N₃`, exercising:
1. exact normalized leaf-summed model-count conservation,
2. the per-leaf greedy trajectory `A` and per-query `ReplacementDesign` recovery and actual
   branch-summed `toCountingDesign` examination bound for **every** evaluated query
   `q : CNF.LeafCandidateQueryIndex (Fin N₃) B L.toCNF` (including discarded candidates
   `Sum.inl (i, γ')` and the final query `Sum.inr ()`), and
3. the candidate-indexed leaf examination sum (`CNF.prop64LeafQueryExamScaleCoeff 3`),
   tree-wide final-query examination sum (`CNF.prop64TreeExamScaleCoeff 3`), and
   total candidate-indexed tree-wide examination sum (`CNF.prop64TotalExamScaleCoeff 3`)
   evaluated on the **actual** `toCountingDesign` examination costs of each query `q`. -/
theorem nonvacuous_prop64NormalizedLeaves_total_recovery_and_actual_candidate_examBound_k3 :
    ∃ (N₃ : ℕ) (_ : NeZero N₃), 2 ^ 640000 ≤ N₃ ∧
      let φ := sampleLargeTaut3CNF N₃
      let B := CNF.prop64LeafClauseRatio 3 (Fintype.card (Fin N₃))
      ((φ.prop64NormalizedLeaves 3).map fun L => L.toCNF.modelCountOn Finset.univ).sum =
        φ.modelCountOn Finset.univ ∧
      2 ≤ numGroups (Fintype.card (Fin N₃)) ∧
      (φ.prop64NormalizedLeaves 3).length ≤
        2 ^ (Fintype.card (Fin N₃) / numGroups (Fintype.card (Fin N₃)) + 1) ∧
      ((φ.prop64NormalizedLeaves 3).length : ℝ) ≤
        (2 : ℝ) ^ (17 * interpolationScale (Fintype.card (Fin N₃))) ∧
      ∃ (actualQueryExam : (L : ClauseSet (Fin N₃)) →
          CNF.LeafCandidateQueryIndex (Fin N₃) B L.toCNF → ℝ),
        (∀ L ∈ φ.prop64NormalizedLeaves 3,
          let ψ := L.toCNF
          let D₀ := Cslib.BitString.initialRowWeightBound B ψ.length
          let P := Cslib.BitString.greedyRowListLength B ψ.length
          let b₀ := CNF.parityBranchThreshold 3 D₀ (Fintype.card (Fin N₃))
          (∀ c ∈ ψ, c.length ≤ 3) ∧
          ψ.length ≤ B * Fintype.card (Fin N₃) ∧
          ∃ A : ℕ → List (Fin ψ.length → Bool),
            commonZeroCount univ
                (ψ.parityRowSystem (CNF.candidateQueryRows (B := B) A (Sum.inr ()))) =
              ψ.modelCountOn Finset.univ ∧
            (∀ (i : Fin (3 * Fintype.card (Fin N₃))) (γ' : Fin P → Fin ψ.length × Bool),
              commonZeroCount univ (ψ.parityRowSystem (A (i.1 + 1))) ≤
                commonZeroCount univ
                  (ψ.parityRowSystem (CNF.candidateQueryRows A (Sum.inl (i, γ'))))) ∧
            (∀ q : CNF.LeafCandidateQueryIndex (Fin N₃) B ψ,
              let rows := CNF.candidateQueryRows A q
              rows.length ≤ 6 * Fintype.card (Fin N₃) ∧
              (∀ r ∈ rows, weight r ≤ D₀) ∧
              let S := heavyVars univ (univ : Finset (Fin rows.length))
                (fun j => equationScope (ψ.parityRowSystem rows j)) b₀
              let n' := Fintype.card ↥(univ \ S)
              let e : ↥(univ \ S) ≃ Fin n' := Fintype.equivFin ↥(univ \ S)
              ∃ (hF : ∀ b : Fin N₃ → Bool,
                    Feasible (CNF.prop64ScheduleExponent 3) n' (b₀ + 1)
                      (max (3 * (D₀ * 2 ^ 3)) 1)
                      (∑ f : {j : Fin rows.length //
                          j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                        #(branchAugmentedScope S e univ (ψ.parityRowSystem rows) b f)))
                  (D : ∀ b : Fin N₃ → Bool,
                    ReplacementDesign
                      (branchAugmentedScope S e univ (ψ.parityRowSystem rows) b)
                      (numNodes n') (numGroups n')
                      (intervalStart (CNF.prop64ScheduleExponent 3) n')
                      (rowBound (CNF.prop64ScheduleExponent 3) n') (tauRat n')),
                (commonZeroCount (univ : Finset (Fin rows.length))
                    (ψ.parityRowSystem rows) : ℤ) =
                  (∑ b ∈ branchAssignments S,
                    ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                      (ψ.branchParityRowSystem rows S e b)
                      (commonDenom (numNodes n')
                        (rowBound (CNF.prop64ScheduleExponent 3) n') : ℤ) 3
                      (branchPrecision (Fintype.card (Fin N₃)))
                      (designReplacementScaledIntMap (D b)
                        (fun j => Sum.inl ⟨j, mem_univ j⟩))).eval 0 /
                        clearedProductDenom
                          (commonDenom (numNodes n')
                            (rowBound (CNF.prop64ScheduleExponent 3) n') : ℤ) 3
                          (branchPrecision (Fintype.card (Fin N₃)))
                          #(univ : Finset (Fin rows.length))) %
                            ((2 : ℤ) ^ branchPrecision (Fintype.card (Fin N₃)))) ∧
                actualQueryExam L q =
                  ∑ b ∈ branchAssignments S,
                    let d := 3 * (rows.length + 2 * (branchPrecision (Fintype.card (Fin N₃)) - 1))
                    let q_ord := (d * rowBound (CNF.prop64ScheduleExponent 3) n') / numNodes n'
                    let C := (hF b).toCountingDesign (D b) univ
                    ∑ t : Fin (numNodes n'),
                      (#{p : Finset (Fin n') × Finset (Fin n') |
                          #p.1 ≤ q_ord ∧ p.2 ⊆ p.1} : ℝ) *
                        (2 * (#(C.measurementBox t) : ℝ) *
                          ∑ g : Fin (numGroups n'),
                            (Fintype.card (C.LocalCube t g) : ℝ))) ∧
            (∑ q : CNF.LeafCandidateQueryIndex (Fin N₃) B ψ, actualQueryExam L q) ≤
              (2 : ℝ) ^ ((CNF.prop64LeafQueryExamScaleCoeff 3 : ℝ) *
                interpolationScale (Fintype.card (Fin N₃)))) ∧
        ((φ.prop64NormalizedLeaves 3).map fun (L : ClauseSet (Fin N₃)) =>
            actualQueryExam L (Sum.inr ())).sum ≤
          (2 : ℝ) ^ ((CNF.prop64TreeExamScaleCoeff 3 : ℝ) *
            interpolationScale (Fintype.card (Fin N₃))) ∧
        ((φ.prop64NormalizedLeaves 3).map fun (L : ClauseSet (Fin N₃)) =>
            ∑ q : CNF.LeafCandidateQueryIndex (Fin N₃) B L.toCNF, actualQueryExam L q).sum ≤
          (2 : ℝ) ^ ((CNF.prop64TotalExamScaleCoeff 3 : ℝ) *
            interpolationScale (Fintype.card (Fin N₃))) := by
  obtain ⟨N₃, hN₃, hprop64⟩ :=
    CNF.exists_prop64NormalizedLeaves_total_recovery_and_examBound (by decide : 2 ≤ 3)
  have hpos : 0 < N₃ := pos_of_two_pow_le hN₃
  have : NeZero N₃ := ⟨Nat.ne_of_gt hpos⟩
  have hcard : N₃ ≤ Fintype.card (Fin N₃) := by rw [Fintype.card_fin]
  set φ := sampleLargeTaut3CNF N₃
  set B := CNF.prop64LeafClauseRatio 3 (Fintype.card (Fin N₃))
  obtain ⟨hsum, hs2, hlen_pow, hlen_scale, hleaf, htree, htotal⟩ :=
    hprop64 φ (sampleLargeTaut3CNF_width_le_three N₃) hcard
  classical
  let actualQueryExam : (L : ClauseSet (Fin N₃)) →
      CNF.LeafCandidateQueryIndex (Fin N₃) B L.toCNF → ℝ :=
    fun L q =>
      if hL : L ∈ φ.prop64NormalizedLeaves 3 then
        let ψ := L.toCNF
        let D₀ := Cslib.BitString.initialRowWeightBound B ψ.length
        let b₀ := CNF.parityBranchThreshold 3 D₀ (Fintype.card (Fin N₃))
        let A := (hleaf L hL).2.2.2.choose
        let hA_spec := (hleaf L hL).2.2.2.choose_spec
        let rows := CNF.candidateQueryRows A q
        let S := heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (ψ.parityRowSystem rows j)) b₀
        let n' := Fintype.card ↥(univ \ S)
        let e : ↥(univ \ S) ≃ Fin n' := Fintype.equivFin ↥(univ \ S)
        let hpack := ((hA_spec.2.2.1 q).2.2 e).2.1
        let hF := hpack.choose
        let D := hpack.choose_spec.choose
        ∑ b ∈ branchAssignments S,
          let d := 3 * (rows.length + 2 * (branchPrecision (Fintype.card (Fin N₃)) - 1))
          let q_ord := (d * rowBound (CNF.prop64ScheduleExponent 3) n') / numNodes n'
          let C := (hF b).toCountingDesign (D b) univ
          ∑ t : Fin (numNodes n'),
            (#{p : Finset (Fin n') × Finset (Fin n') |
                #p.1 ≤ q_ord ∧ p.2 ⊆ p.1} : ℝ) *
              (2 * (#(C.measurementBox t) : ℝ) *
                ∑ g : Fin (numGroups n'),
                  (Fintype.card (C.LocalCube t g) : ℝ))
      else 0
  have hactual_bound : ∀ L ∈ φ.prop64NormalizedLeaves 3,
      ∀ q : CNF.LeafCandidateQueryIndex (Fin N₃) B L.toCNF,
        actualQueryExam L q ≤
          (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff 3 + 32 : ℕ) : ℝ) *
            interpolationScale (Fintype.card (Fin N₃))) := by
    intro L hL q
    dsimp only [actualQueryExam]
    rw [dite_eq_left_of_eq_true (eq_true hL)]
    let ψ := L.toCNF
    let D₀ := Cslib.BitString.initialRowWeightBound B ψ.length
    let b₀ := CNF.parityBranchThreshold 3 D₀ (Fintype.card (Fin N₃))
    let A := (hleaf L hL).2.2.2.choose
    let hA_spec := (hleaf L hL).2.2.2.choose_spec
    let rows := CNF.candidateQueryRows A q
    let S := heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (ψ.parityRowSystem rows j)) b₀
    let n' := Fintype.card ↥(univ \ S)
    let e : ↥(univ \ S) ≃ Fin n' := Fintype.equivFin ↥(univ \ S)
    have hq_e := (hA_spec.2.2.1 q).2.2 e
    have hexam := hq_e.2.1.choose_spec.choose_spec.2.2
    exact hq_e.2.2 _ fun b _ => hexam b univ
  refine ⟨N₃, inferInstance, hN₃, hsum, hs2, hlen_pow, hlen_scale, actualQueryExam,
    fun L hL => ?_,
    htree (fun L => actualQueryExam L (Sum.inr ())) (fun L hL => hactual_bound L hL (Sum.inr ())),
    htotal actualQueryExam hactual_bound⟩
  have hk_ψ := (hleaf L hL).1
  have hm_ψ := (hleaf L hL).2.1
  let A := (hleaf L hL).2.2.2.choose
  have hA_spec := (hleaf L hL).2.2.2.choose_spec
  refine ⟨hk_ψ, hm_ψ, A, hA_spec.1, hA_spec.2.1, fun q => ?_,
    hA_spec.2.2.2 (actualQueryExam L) (hactual_bound L hL)⟩
  obtain ⟨hlen_q, hw_q, hq_all_e⟩ := hA_spec.2.2.1 q
  refine ⟨hlen_q, hw_q, ?_⟩
  intro S n' e
  have hpack := (hq_all_e e).2.1
  let hF := hpack.choose
  let D := hpack.choose_spec.choose
  have hrec := hpack.choose_spec.choose_spec.1
  refine ⟨hF, D, hrec, ?_⟩
  dsimp only [actualQueryExam]
  rw [dite_eq_left_of_eq_true (eq_true hL)]

end CslibTests
