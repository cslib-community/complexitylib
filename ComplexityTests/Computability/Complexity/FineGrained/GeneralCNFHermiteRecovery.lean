/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.GeneralCNFHermiteRecovery

/-!
# Tests for `Complexity.Computability.Complexity.FineGrained.GeneralCNFHermiteRecovery`

Exercises the Stage-1/Stage-2 `clearedParityJetTable` Hermite–Cramer coordinate recovery
(`hermiteCramerNumerator_clearedParityJetTable_eq_mul`,
`emod_sum_hermiteCramerNumerator_clearedParityJetTable_ediv_eq_commonZeroCount`),
`Feasible.numNodes_pos`, the Section 6.3 compiled CNF parity-row schedule Hermite–Cramer and
`clearedParityJetTable` recovery
(`CNF.exists_parityRowSystem_modelCountOn_hermiteCramer_recovery_and_examBound_of_le_clog_pow`),
and the Proposition 6.4 tree-wide candidate-indexed Hermite–Cramer and `clearedParityJetTable`
recovery and actual `toCountingDesign` examination bounds
(`CNF.exists_prop64NormalizedLeaves_total_hermiteCramer_recovery_and_examBound`) on concrete
systems and 3-CNF formulas.
-/

public noncomputable section

namespace CslibTests

open Finset Polynomial
open Cslib
open Cslib.BitString
open Cslib.LinearAlgebra
open Cslib.Logic.PL
open Cslib.Logic.PL.ClauseSet.Sparsification
open Cslib.Complexity.SubexponentialSAT
open Cslib.Complexity.SubexponentialSAT.ReplacementParams
open scoped BigOperators

/-- Concrete linear parity system `x₀ + x₁ = 0` on `Fin 2` (`1` equation with monomials `{0}` and
`{1}`), which has `commonZeroCount univ sampleParitySystem2 = 2`. -/
def sampleParitySystem2 : Fin 1 → Finset (Finset (Fin 2)) :=
  fun _ => {{0}, {1}}

theorem commonZeroCount_sampleParitySystem2 :
    commonZeroCount (univ : Finset (Fin 1)) sampleParitySystem2 = 2 := by
  decide

/-- Concrete check of `hermiteCramerNumerator_clearedParityJetTable_eq_mul` and
`emod_sum_hermiteCramerNumerator_clearedParityJetTable_ediv_eq_commonZeroCount` on
`sampleParitySystem2` (`commonZeroCount = 2`) with constant replacement map
`θ x i v = Polynomial.C (bitVal ℤ (x v))` (`d_den = 1`, `R_deg = 0`), single interpolation node
`nodes 0 = 0` (`Q = 1`), jet order `J = 1`, and precision `ℓ = 3`: the Stage-1/Stage-2
`clearedParityJetTable` coordinate Cramer quotients sum modulo `2 ^ 3 = 8` to the exact common-zero
count `2`. -/
theorem clearedParityJetTable_hermiteCramer_recovers_sampleParitySystem2 :
    let I : Finset (Fin 1) := univ
    let θ : (Fin 2 → Bool) → Fin 1 → Fin 2 → Polynomial ℤ :=
      fun x _ v => Polynomial.C (bitVal ℤ (x v))
    let nodes : Fin 1 → ℤ := fun _ => 0
    (∀ s : Fin 3,
      hermiteCramerNumerator nodes Nat.one_pos Nat.one_pos
          (fun t j =>
            clearedParityJetTable I sampleParitySystem2 1 1 3 1 θ (nodes t) j s) =
        (Polynomial.hermiteMatrix nodes 1).det *
          (univariateClearedParityCoord I sampleParitySystem2 1 1 3 θ s.1).eval 0) ∧
    (∑ s : Fin 3,
      hermiteCramerNumerator nodes Nat.one_pos Nat.one_pos
        (fun t j =>
          clearedParityJetTable I sampleParitySystem2 1 1 3 1 θ (nodes t) j s) /
        (clearedProductDenom 1 1 3 #I *
          (Polynomial.hermiteMatrix nodes 1).det)) % ((2 : ℤ) ^ 3) = 2 := by
  intro I θ nodes
  have hk : ∀ i ∈ I, ∀ M ∈ sampleParitySystem2 i, #M ≤ 1 := by decide
  have hdeg : ∀ x : Fin 2 → Bool, ∀ i ∈ I, ∀ M ∈ sampleParitySystem2 i, ∀ v ∈ M,
      (θ x i v).natDegree ≤ 0 := by
    intro x _ _ _ _ v _
    exact (Polynomial.natDegree_C (bitVal ℤ (x v))).le
  have hθ : ∀ x : Fin 2 → Bool, ∀ i ∈ I, ∀ M ∈ sampleParitySystem2 i, ∀ v ∈ M,
      (θ x i v).eval 0 = 1 * bitVal ℤ (x v) := by
    intro x _ _ _ _ v _
    simp [θ]
  have hQJ : (1 * 0) * (#I + 2 * (3 - 1)) < 1 * 1 := by decide
  have hnodes : Function.Injective nodes := fun a b _ => Subsingleton.elim a b
  have hℓ : Fintype.card (Fin 2) < 3 := by decide
  refine ⟨fun s =>
    hermiteCramerNumerator_clearedParityJetTable_eq_mul I sampleParitySystem2 1 nodes
      Nat.one_pos Nat.one_pos θ hk hdeg hQJ s, ?_⟩
  rw [emod_sum_hermiteCramerNumerator_clearedParityJetTable_ediv_eq_commonZeroCount
    I sampleParitySystem2 one_ne_zero hnodes Nat.one_pos Nat.one_pos hℓ θ hk hdeg hθ hQJ,
    commonZeroCount_sampleParitySystem2]
  rfl

/-- Concrete 3-CNF on `Fin N` (`1 ≤ N`) with one tautological clause and one width-3 clause. -/
def sampleHermiteTaut3CNF (N : ℕ) [NeZero N] : CNF (Fin N) :=
  [[(0, true), (0, false), (0, true)],
   [(0, true), (0, true), (0, true)]]

theorem sampleHermiteTaut3CNF_width_le_three (N : ℕ) [NeZero N] :
    ∀ c ∈ sampleHermiteTaut3CNF N, c.length ≤ 3 := by
  intro c hc
  simp only [sampleHermiteTaut3CNF, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp

private theorem pos_of_le {m n : ℕ} (hm : 0 < m) (h : m ≤ n) : 0 < n :=
  lt_of_lt_of_le hm h

private theorem pos_of_two_pow_le {m n : ℕ} (h : 2 ^ m ≤ n) : 0 < n :=
  lt_of_lt_of_le (Nat.pow_pos two_pos) h

/-- Nonvacuous Section 6.3 instantiation of
`CNF.exists_parityRowSystem_modelCountOn_hermiteCramer_recovery_and_examBound_of_le_clog_pow`
at `k = 3`, `C_B = 1`, `β_B = 2` on `sampleHermiteTaut3CNF N₁`, verifying `0 < numNodes n'`,
both the Hermite–Cramer truncated-sum determinant recovery and the Stage-1/Stage-2
`clearedParityJetTable` coordinate recovery of `(φ.modelCountOn Finset.univ : ℤ)`, and the
branch-summed `interpolationScale` examination bound on the actual `toCountingDesign` sum. -/
theorem nonvacuous_sec63_modelCountOn_hermiteCramer_and_clearedParityJetTable_recovery_k3 :
    ∃ (N₁ : ℕ) (_ : NeZero N₁), 16384 ≤ N₁ ∧
      let φ := sampleHermiteTaut3CNF N₁
      let D₀ := CNF.initialRowWeightBound 1 φ.length
      let b₀ := CNF.parityBranchThreshold 3 D₀ (Fintype.card (Fin N₁))
      ∃ rows : List (Fin φ.length → Bool),
        rows.length ≤ 6 * Fintype.card (Fin N₁) ∧
        commonZeroCount univ (φ.parityRowSystem rows) = φ.modelCountOn Finset.univ ∧
        let S := heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀
        let n' := Fintype.card ↥(univ \ S)
        let e : ↥(univ \ S) ≃ Fin n' := Fintype.equivFin ↥(univ \ S)
        ∃ (hQ : 0 < numNodes n')
          (hF : ∀ b : Fin N₁ → Bool,
            Feasible 9 n' (b₀ + 1) (max (3 * (D₀ * 2 ^ 3)) 1)
              (∑ f : {j : Fin rows.length //
                  j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                #(branchAugmentedScope S e univ (φ.parityRowSystem rows) b f)))
          (D : ∀ b : Fin N₁ → Bool,
            ReplacementDesign
              (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
              (numNodes n') (numGroups n') (intervalStart 9 n')
              (rowBound 9 n') (tauRat n')),
          let ℓ := branchPrecision (Fintype.card (Fin N₁))
          let J := sparseParityJetOrder 3 (rowBound 9 n') (numNodes n')
            #(univ : Finset (Fin rows.length)) ℓ
          (φ.modelCountOn Finset.univ : ℤ) =
            (∑ b ∈ branchAssignments S,
              (hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                (sparseParityJetOrder_pos 3 (rowBound 9 n') (numNodes n')
                  #(univ : Finset (Fin rows.length)) ℓ)
                (fun t j =>
                  (Polynomial.taylor (nodeInt t)
                    (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                      (φ.branchParityRowSystem rows S e b)
                      (commonDenom (numNodes n') (rowBound 9 n') : ℤ) 3 ℓ
                      (designReplacementScaledIntMap (D b)
                        (fun j => Sum.inl ⟨j, mem_univ j⟩)))).coeff j) /
                (clearedProductDenom
                  (commonDenom (numNodes n') (rowBound 9 n') : ℤ) 3 ℓ
                  #(univ : Finset (Fin rows.length)) *
                  (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                    ((2 : ℤ) ^ ℓ)) ∧
          (φ.modelCountOn Finset.univ : ℤ) =
            (∑ b ∈ branchAssignments S,
              (∑ s : Fin ℓ,
                hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                  (sparseParityJetOrder_pos 3 (rowBound 9 n') (numNodes n')
                    #(univ : Finset (Fin rows.length)) ℓ)
                  (fun t j =>
                    clearedParityJetTable (univ : Finset (Fin rows.length))
                      (φ.branchParityRowSystem rows S e b)
                      (commonDenom (numNodes n') (rowBound 9 n') : ℤ) 3 ℓ J
                      (designReplacementScaledIntMap (D b)
                        (fun j => Sum.inl ⟨j, mem_univ j⟩)) (nodeInt t) j s) /
                  (clearedProductDenom
                    (commonDenom (numNodes n') (rowBound 9 n') : ℤ) 3 ℓ
                    #(univ : Finset (Fin rows.length)) *
                    (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                      ((2 : ℤ) ^ ℓ)) ∧
          (∑ b ∈ branchAssignments S,
              let d := 3 * (rows.length + 2 * (branchPrecision (Fintype.card (Fin N₁)) - 1))
              let q_ord := (d * rowBound 9 n') / numNodes n'
              let C := (hF b).toCountingDesign (D b) univ
              ∑ t : Fin (numNodes n'),
                (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q_ord ∧ p.2 ⊆ p.1} : ℝ) *
                  (2 * (#(C.measurementBox t) : ℝ) *
                    ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
            (2 : ℝ) ^ (((CNF.parityBranchExamScaleCoeff 3 2 + 32 : ℕ) : ℝ) *
              interpolationScale (Fintype.card (Fin N₁))) := by
  obtain ⟨N₁, hN₁, hsec63⟩ :=
    CNF.exists_parityRowSystem_modelCountOn_hermiteCramer_recovery_and_examBound_of_le_clog_pow
      3 1 2
  have hpos : 0 < N₁ := pos_of_le (by decide : 0 < 16384) hN₁
  have : NeZero N₁ := ⟨Nat.ne_of_gt hpos⟩
  set φ := sampleHermiteTaut3CNF N₁
  have hcard : N₁ ≤ Fintype.card (Fin N₁) := by rw [Fintype.card_fin]
  have hB_le : 1 ≤ 1 * Nat.clog 2 (Fintype.card (Fin N₁)) ^ 2 := by
    rw [Fintype.card_fin, one_mul]
    have hclog : 1 ≤ Nat.clog 2 N₁ :=
      (Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by omega : 2 ^ 0 < N₁)
    exact Nat.one_le_pow 2 _ hclog
  have hm : φ.length ≤ 1 * Fintype.card (Fin N₁) := by
    rw [Fintype.card_fin, one_mul]
    change 2 ≤ N₁
    omega
  obtain ⟨rows, hlen, hcount, hstage⟩ :=
    hsec63 φ (sampleHermiteTaut3CNF_width_le_three N₁) hcard le_rfl hB_le hm
  refine ⟨N₁, inferInstance, hN₁, rows, hlen, hcount, ?_⟩
  intro S n' e
  obtain ⟨_, ⟨hQ, hF, D, hrec_trunc, hrec_jet, _, hexam⟩, hsum⟩ := hstage e
  exact ⟨hQ, hF, D, hrec_trunc, hrec_jet, hsum _ fun b _ => hexam b univ⟩

/-- Nonvacuous Proposition 6.4 instantiation of
`CNF.exists_prop64NormalizedLeaves_total_hermiteCramer_recovery_and_examBound` at `k = 3` on
`sampleHermiteTaut3CNF N₃`, certifying for every normalized leaf `L ∈ φ.prop64NormalizedLeaves 3`
and every candidate query `q : CNF.LeafCandidateQueryIndex (Fin N₃) B L.toCNF` (including
discarded candidates with list multiplicity and the final query `Sum.inr ()`) both the
Hermite–Cramer truncated-sum determinant recovery and the Stage-1/Stage-2 `clearedParityJetTable`
coordinate recovery at `nodeInt` and canonical jet order `sparseParityJetOrder`, together with the
per-leaf candidate-summed, tree-wide final-query, and tree-wide total candidate-indexed
`interpolationScale` bounds evaluated on the **actual** `toCountingDesign` examination costs. -/
theorem nonvacuous_prop64NormalizedLeaves_total_hermiteCramer_and_jetTable_recovery_k3 :
    ∃ (N₃ : ℕ) (_ : NeZero N₃), 2 ^ 640000 ≤ N₃ ∧
      let φ := sampleHermiteTaut3CNF N₃
      let B := CNF.prop64LeafClauseRatio 3 (Fintype.card (Fin N₃))
      ((φ.prop64NormalizedLeaves 3).map fun L => L.toCNF.modelCountOn Finset.univ).sum =
        φ.modelCountOn Finset.univ ∧
      ((φ.prop64NormalizedLeaves 3).length : ℝ) ≤
        (2 : ℝ) ^ (17 * interpolationScale (Fintype.card (Fin N₃))) ∧
      ∃ (actualQueryExam : (L : ClauseSet (Fin N₃)) →
          CNF.LeafCandidateQueryIndex (Fin N₃) B L.toCNF → ℝ),
        (∀ L ∈ φ.prop64NormalizedLeaves 3,
          let ψ := L.toCNF
          let D₀ := CNF.initialRowWeightBound B ψ.length
          let P := CNF.greedyRowListLength B ψ.length
          let b₀ := CNF.parityBranchThreshold 3 D₀ (Fintype.card (Fin N₃))
          Fintype.card (CNF.LeafCandidateQueryIndex (Fin N₃) B ψ) =
            3 * Fintype.card (Fin N₃) * (2 * ψ.length) ^ P + 1 ∧
          ∃ A : ℕ → List (Fin ψ.length → Bool),
            commonZeroCount univ
                (ψ.parityRowSystem (CNF.candidateQueryRows (B := B) A (Sum.inr ()))) =
              ψ.modelCountOn Finset.univ ∧
            (∀ q : CNF.LeafCandidateQueryIndex (Fin N₃) B ψ,
              let rows := CNF.candidateQueryRows A q
              let S := heavyVars univ (univ : Finset (Fin rows.length))
                (fun j => equationScope (ψ.parityRowSystem rows j)) b₀
              let n' := Fintype.card ↥(univ \ S)
              let e : ↥(univ \ S) ≃ Fin n' := Fintype.equivFin ↥(univ \ S)
              ∃ (hQ : 0 < numNodes n')
                (hF : ∀ b : Fin N₃ → Bool,
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
                let ℓ := branchPrecision (Fintype.card (Fin N₃))
                let J := sparseParityJetOrder 3 (rowBound (CNF.prop64ScheduleExponent 3) n')
                  (numNodes n') #(univ : Finset (Fin rows.length)) ℓ
                (commonZeroCount (univ : Finset (Fin rows.length))
                    (ψ.parityRowSystem rows) : ℤ) =
                  (∑ b ∈ branchAssignments S,
                    (hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                      (sparseParityJetOrder_pos 3
                        (rowBound (CNF.prop64ScheduleExponent 3) n') (numNodes n')
                        #(univ : Finset (Fin rows.length)) ℓ)
                      (fun t j =>
                        (Polynomial.taylor (nodeInt t)
                          (univariateClearedParityTruncatedSum
                            (univ : Finset (Fin rows.length))
                            (ψ.branchParityRowSystem rows S e b)
                            (commonDenom (numNodes n')
                              (rowBound (CNF.prop64ScheduleExponent 3) n') : ℤ) 3 ℓ
                            (designReplacementScaledIntMap (D b)
                              (fun j => Sum.inl ⟨j, mem_univ j⟩)))).coeff j) /
                      (clearedProductDenom
                        (commonDenom (numNodes n')
                          (rowBound (CNF.prop64ScheduleExponent 3) n') : ℤ) 3 ℓ
                        #(univ : Finset (Fin rows.length)) *
                        (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                          ((2 : ℤ) ^ ℓ)) ∧
                (commonZeroCount (univ : Finset (Fin rows.length))
                    (ψ.parityRowSystem rows) : ℤ) =
                  (∑ b ∈ branchAssignments S,
                    (∑ s : Fin ℓ,
                      hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                        (sparseParityJetOrder_pos 3
                          (rowBound (CNF.prop64ScheduleExponent 3) n') (numNodes n')
                          #(univ : Finset (Fin rows.length)) ℓ)
                        (fun t j =>
                          clearedParityJetTable (univ : Finset (Fin rows.length))
                            (ψ.branchParityRowSystem rows S e b)
                            (commonDenom (numNodes n')
                              (rowBound (CNF.prop64ScheduleExponent 3) n') : ℤ) 3 ℓ J
                            (designReplacementScaledIntMap (D b)
                              (fun j => Sum.inl ⟨j, mem_univ j⟩)) (nodeInt t) j s) /
                        (clearedProductDenom
                          (commonDenom (numNodes n')
                            (rowBound (CNF.prop64ScheduleExponent 3) n') : ℤ) 3 ℓ
                          #(univ : Finset (Fin rows.length)) *
                          (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                            ((2 : ℤ) ^ ℓ)) ∧
                actualQueryExam L q =
                  ∑ b ∈ branchAssignments S,
                    let d := 3 * (rows.length + 2 * (branchPrecision (Fintype.card (Fin N₃)) - 1))
                    let q_jet := (d * rowBound (CNF.prop64ScheduleExponent 3) n') / numNodes n'
                    let C := (hF b).toCountingDesign (D b) univ
                    ∑ t : Fin (numNodes n'),
                      (#{p : Finset (Fin n') × Finset (Fin n') |
                          #p.1 ≤ q_jet ∧ p.2 ⊆ p.1} : ℝ) *
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
    CNF.exists_prop64NormalizedLeaves_total_hermiteCramer_recovery_and_examBound
      (by decide : 2 ≤ 3)
  have hpos : 0 < N₃ := pos_of_two_pow_le hN₃
  have : NeZero N₃ := ⟨Nat.ne_of_gt hpos⟩
  have hcard : N₃ ≤ Fintype.card (Fin N₃) := by rw [Fintype.card_fin]
  set φ := sampleHermiteTaut3CNF N₃
  set B := CNF.prop64LeafClauseRatio 3 (Fintype.card (Fin N₃))
  obtain ⟨hsum, _, _, hlen_scale, hleaf, htree, htotal⟩ :=
    hprop64 φ (sampleHermiteTaut3CNF_width_le_three N₃) hcard
  classical
  let actualQueryExam : (L : ClauseSet (Fin N₃)) →
      CNF.LeafCandidateQueryIndex (Fin N₃) B L.toCNF → ℝ :=
    fun L q =>
      if hL : L ∈ φ.prop64NormalizedLeaves 3 then
        let ψ := L.toCNF
        let D₀ := CNF.initialRowWeightBound B ψ.length
        let b₀ := CNF.parityBranchThreshold 3 D₀ (Fintype.card (Fin N₃))
        let A := (hleaf L hL).2.2.2.2.2.choose
        let hA_spec := (hleaf L hL).2.2.2.2.2.choose_spec
        let rows := CNF.candidateQueryRows A q
        let S := heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (ψ.parityRowSystem rows j)) b₀
        let n' := Fintype.card ↥(univ \ S)
        let e : ↥(univ \ S) ≃ Fin n' := Fintype.equivFin ↥(univ \ S)
        let hpack := ((hA_spec.2.2.1 q).2.2 e).2.1
        let hF := hpack.choose_spec.choose
        let D := hpack.choose_spec.choose_spec.choose
        ∑ b ∈ branchAssignments S,
          let d := 3 * (rows.length + 2 * (branchPrecision (Fintype.card (Fin N₃)) - 1))
          let q_jet := (d * rowBound (CNF.prop64ScheduleExponent 3) n') / numNodes n'
          let C := (hF b).toCountingDesign (D b) univ
          ∑ t : Fin (numNodes n'),
            (#{p : Finset (Fin n') × Finset (Fin n') |
                #p.1 ≤ q_jet ∧ p.2 ⊆ p.1} : ℝ) *
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
    let D₀ := CNF.initialRowWeightBound B ψ.length
    let b₀ := CNF.parityBranchThreshold 3 D₀ (Fintype.card (Fin N₃))
    let A := (hleaf L hL).2.2.2.2.2.choose
    let hA_spec := (hleaf L hL).2.2.2.2.2.choose_spec
    let rows := CNF.candidateQueryRows A q
    let S := heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (ψ.parityRowSystem rows j)) b₀
    let n' := Fintype.card ↥(univ \ S)
    let e : ↥(univ \ S) ≃ Fin n' := Fintype.equivFin ↥(univ \ S)
    have hq_e := (hA_spec.2.2.1 q).2.2 e
    have hexam := hq_e.2.1.choose_spec.choose_spec.choose_spec.2.2.2
    exact hq_e.2.2 _ fun b _ => hexam b univ
  refine ⟨N₃, inferInstance, hN₃, hsum, hlen_scale, actualQueryExam,
    fun L hL => ?_,
    htree (fun L => actualQueryExam L (Sum.inr ())) (fun L hL => hactual_bound L hL (Sum.inr ())),
    htotal actualQueryExam hactual_bound⟩
  have hcard_eq := (hleaf L hL).2.2.1
  let A := (hleaf L hL).2.2.2.2.2.choose
  have hA_spec := (hleaf L hL).2.2.2.2.2.choose_spec
  refine ⟨hcard_eq, A, hA_spec.1, fun q => ?_,
    hA_spec.2.2.2 (actualQueryExam L) (hactual_bound L hL)⟩
  obtain ⟨_, _, hq_all_e⟩ := hA_spec.2.2.1 q
  intro rows S n' e
  have hpack := (hq_all_e e).2.1
  let hQ := hpack.choose
  let hF := hpack.choose_spec.choose
  let D := hpack.choose_spec.choose_spec.choose
  have hrec_trunc := hpack.choose_spec.choose_spec.choose_spec.1
  have hrec_jet := hpack.choose_spec.choose_spec.choose_spec.2.1
  refine ⟨hQ, hF, D, hrec_trunc, hrec_jet, ?_⟩
  dsimp only [actualQueryExam]
  rw [dite_eq_left_of_eq_true (eq_true hL)]

end CslibTests
