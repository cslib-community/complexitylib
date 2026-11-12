/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.KickTree.QuotientPerm

/-!
# Tests for universal key-quotienting bijection (`KickTree.QuotientPerm`)

Verifies:
* concrete forward/inverse round-trip bijectivity (`quotientPermDecode ∘ quotientPermEncode` and
  `quotientPermEncode ∘ quotientPermDecode`, plus bit-level `caseBEquiv` evaluation) in both
  **Case A** (`m + caseAGap c n ≤ a`) and **Case B** (`a < m + caseAGap c n`, including tight
  `a = m` with `0`-bit quotients and odd intra-shard suffix width `suffixBits a m`);
* concrete doubly-stochastic matrix identity `(P₁ - U) * (P₂ - U) = P₁ * P₂ - U` and
  intra-shard suffix injectivity (`injOn_yR_of_caseBShard_eq`);
* universal full-quotient bit-width bound `mul_fullQuotBits_le_clog_choose` across `n = 0`,
  `U < n`, `U = n`, `U = 2 * n`, and super-exponential `U = 2 ^ (2 ^ n)`;
* non-vacuity of `prob_fullQuotientPerm_forall_mem_le`,
  `prob_fullQuotientPerm_forall_mem_perKey_le`, and `prob_concreteCaseB_shardLoad_outside_le`
  across both tight small universes (`U = n`, `U = 2 * n`) and super-exponential universes
  (`U = 2 ^ (2 ^ n)`).
-/

public section

namespace CslibFrontierTests.DataStructure.KickTreeQuotientPerm

open Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.KickTree
open Cslib.Probability Finset

/-! ## 1. Concrete round-trip bijectivity in Case A and Case B -/

/-- Sample round bundle in **Case A** (`c = 0, n = 2, m = 1, a = 5`, where
`m + caseAGap 0 2 = 1 + 3 = 4 ≤ 5 = a`). -/
def sampleCaseARounds : QuotientPermRounds 5 1 0 2 where
  caseA :=
    { g₀ := fun x => ⟨(11 * x.val + 5) % 16, Nat.mod_lt _ (by decide)⟩
      g₁ := fun q => ⟨(q.val + 1) % 2, Nat.mod_lt _ (by decide)⟩ }
  caseB :=
    { fShard := fun _ => 0
      nrBlocks := fun _ => ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ }

example : 1 + caseAGap 0 2 ≤ 5 := by decide

/-- Case A forward-then-inverse and inverse-then-forward bijectivity on all `32` keys, plus a
concrete check that `quotientPermEncode` scrambles keys nontrivially. -/
theorem caseA_roundtrip_and_nontrivial :
    (∀ u : Fin 32,
      quotientPermDecode (by decide : 1 ≤ 5) sampleCaseARounds
        (quotientPermEncode (by decide : 1 ≤ 5) sampleCaseARounds u) = u) ∧
    (∀ p : Fin 2 × Fin 16,
      quotientPermEncode (by decide : 1 ≤ 5) sampleCaseARounds
        (quotientPermDecode (by decide : 1 ≤ 5) sampleCaseARounds p) = p) ∧
    quotientPermEncode (by decide : 1 ≤ 5) sampleCaseARounds ⟨13, by decide⟩ ≠
      (⟨1, by decide⟩, ⟨6, by decide⟩) := by
  decide

/-- Concrete 2-block **Case B** round functions at tight `a = m = 2` (`0`-bit quotients, odd
`suffixBits 2 2 = 1`). -/
def sampleCaseBTight2 : CaseBRounds 2 2 2 where
  fShard := fun y => ⟨(y.val + 1) % 2, Nat.mod_lt _ (by decide)⟩
  nrBlocks := fun r =>
    { f₀ := fun _ => ⟨r.val % 2, Nat.mod_lt _ (by decide)⟩
      f₁ := fun _ => 0
      f₂ := fun _ => ⟨(r.val + 1) % 2, Nat.mod_lt _ (by decide)⟩ }

example : 2 < 2 + caseAGap 0 4 ∧ suffixBits 2 2 % 2 = 1 := by decide

/-- Concrete bit-level evaluation and round-trip bijectivity of `caseBEquiv` at tight `a = m = 2`
across all `4` keys and `Fin 4 × Fin 1` pairs. -/
theorem caseB_tight_roundtrip :
    (∀ u : Fin 4,
      (caseBEquiv (by decide : 2 ≤ 2) sampleCaseBTight2).symm
        (caseBEquiv (by decide : 2 ≤ 2) sampleCaseBTight2 u) = u) ∧
    (∀ p : Fin 4 × Fin 1,
      caseBEquiv (by decide : 2 ≤ 2) sampleCaseBTight2
        ((caseBEquiv (by decide : 2 ≤ 2) sampleCaseBTight2).symm p) = p) ∧
    (caseBEquiv (by decide : 2 ≤ 2) sampleCaseBTight2 ⟨0, by decide⟩).1 ≠ ⟨0, by decide⟩ := by
  simp only [caseBEquiv, Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.prodCongr_symm,
    Equiv.refl_symm, Equiv.prodCongr_apply, Equiv.coe_refl, id_eq, nrComposedEquiv_succ,
    nrComposedEquiv_zero]
  decide

/-- Concrete 2-block **Case B** round functions with odd `suffixBits 4 3 = 3` (`m = 3, a = 4`). -/
def sampleCaseBOdd2 : CaseBRounds 4 3 2 where
  fShard := fun y => ⟨(y.val + 1) % 2, Nat.mod_lt _ (by decide)⟩
  nrBlocks := fun r =>
    { f₀ := fun zL => ⟨(zL.val + r.val + 1) % 4, Nat.mod_lt _ (by decide)⟩
      f₁ := fun zR => ⟨(zR.val + r.val) % 2, Nat.mod_lt _ (by decide)⟩
      f₂ := fun wL => ⟨(3 * wL.val + 2) % 4, Nat.mod_lt _ (by decide)⟩ }

example : 4 < 3 + caseAGap 0 8 ∧ suffixBits 4 3 = 3 := by decide

/-- Odd-suffix (`a' = 3`) Case B bit-level round-trip across all `16` keys, nontrivial key
scrambling, `quotientPermDecode` / `quotientPermEncode` round-trip, and intra-shard suffix
injectivity. -/
theorem caseB_oddSuffix_roundtrip (rFull : QuotientPermRounds 4 3 0 8) :
    (caseBEquiv (by decide : 3 ≤ 4) sampleCaseBOdd2).symm
      (caseBEquiv (by decide : 3 ≤ 4) sampleCaseBOdd2 ⟨11, by decide⟩) = ⟨11, by decide⟩ ∧
    caseBEquiv (by decide : 3 ≤ 4) sampleCaseBOdd2
      ((caseBEquiv (by decide : 3 ≤ 4) sampleCaseBOdd2).symm (⟨5, by decide⟩, ⟨1, by decide⟩)) =
        (⟨5, by decide⟩, ⟨1, by decide⟩) ∧
    caseBEquiv (by decide : 3 ≤ 4) sampleCaseBOdd2 ⟨11, by decide⟩ ≠
      (⟨3, by decide⟩, ⟨1, by decide⟩) ∧
    (∀ u : Fin 16,
      quotientPermDecode (by decide : 3 ≤ 4) rFull
        (quotientPermEncode (by decide : 3 ≤ 4) rFull u) = u) ∧
    Set.InjOn (keySuffix (by decide : 3 ≤ 4))
      {u : Fin 16 | caseBShard (by decide : 3 ≤ 4) sampleCaseBOdd2 u = 0} := by
  refine ⟨?_, ?_, ?_,
    fun u => quotientPermDecode_quotientPermEncode (by decide : 3 ≤ 4) rFull u,
    injOn_yR_of_caseBShard_eq (by decide : 3 ≤ 4) sampleCaseBOdd2 0⟩
  · simp only [caseBEquiv, Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.prodCongr_symm,
      Equiv.refl_symm, Equiv.prodCongr_apply, Equiv.coe_refl, id_eq, nrComposedEquiv_succ,
      nrComposedEquiv_zero]
    decide
  · simp only [caseBEquiv, Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.prodCongr_symm,
      Equiv.refl_symm, Equiv.prodCongr_apply, Equiv.coe_refl, id_eq, nrComposedEquiv_succ,
      nrComposedEquiv_zero]
    decide
  · simp only [caseBEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, id_eq,
      nrComposedEquiv_succ, nrComposedEquiv_zero]
    decide

/-! ## 2. Full-quotient bit-width bound across boundary regimes -/

/-- Concrete evaluation of `fullQuotBits` and `mul_fullQuotBits_le_clog_choose` at `n = 0`,
`U < n`, `U = n = 8` (`fullQuotBits 8 8 = 0`), and `U = 8, n = 4` (`fullQuotBits 8 4 = 1`). -/
example :
    0 * fullQuotBits 100 0 ≤ Nat.clog 2 ((100 : ℕ).choose 0) + 2 * 0 ∧
    fullQuotBits 8 8 = 0 ∧
    fullQuotBits 8 4 = 1 ∧
    8 * fullQuotBits 8 8 ≤ Nat.clog 2 ((8 : ℕ).choose 8) + 2 * 8 ∧
    8 * fullQuotBits 5 8 ≤ Nat.clog 2 ((5 : ℕ).choose 8) + 2 * 8 ∧
    4 * fullQuotBits 8 4 ≤ Nat.clog 2 ((8 : ℕ).choose 4) + 2 * 4 := by
  decide

/-- Symbolic check at super-exponential `U = 2 ^ (2 ^ n)` for both `mul_fullQuotBits_le_clog_choose`
and `mul_fullQuotBits_add_valBits_le_optBits`. -/
theorem fullQuotBits_superexponential_bound (n V : ℕ) :
    n * fullQuotBits (2 ^ (2 ^ n)) n ≤ Nat.clog 2 ((2 ^ (2 ^ n)).choose n) + 2 * n ∧
    n * (fullQuotBits (2 ^ (2 ^ n)) n + FeistelQuotient.valBits V) ≤
      Dynamic.optBits (2 ^ (2 ^ n)) V n + 2 * n :=
  ⟨mul_fullQuotBits_le_clog_choose _ _, mul_fullQuotBits_add_valBits_le_optBits _ _ _⟩

/-! ## 3. Doubly-stochastic matrix identity on a concrete `2 × 2` pair -/

theorem doublyStochastic_two_by_two_identity :
    let P₁ : Matrix (Fin 2) (Fin 2) ℝ := !![3 / 4, 1 / 4; 1 / 4, 3 / 4]
    let P₂ : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 3, 2 / 3; 2 / 3, 1 / 3]
    (P₁ - unifMatrix (Fin 2)) * (P₂ - unifMatrix (Fin 2)) =
      P₁ * P₂ - unifMatrix (Fin 2) := by
  let P₁ : Matrix (Fin 2) (Fin 2) ℝ := !![3 / 4, 1 / 4; 1 / 4, 3 / 4]
  let P₂ : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 3, 2 / 3; 2 / 3, 1 / 3]
  have h₁ : IsDoublyStochastic P₁ :=
    ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp [P₁] <;> norm_num,
     fun i => by fin_cases i <;> simp [P₁, Fin.sum_univ_two] <;> norm_num,
     fun j => by fin_cases j <;> simp [P₁, Fin.sum_univ_two] <;> norm_num⟩
  have h₂ : IsDoublyStochastic P₂ :=
    ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp [P₂] <;> norm_num,
     fun i => by fin_cases i <;> simp [P₂, Fin.sum_univ_two] <;> norm_num,
     fun j => by fin_cases j <;> simp [P₂, Fin.sum_univ_two] <;> norm_num⟩
  exact sub_unifMatrix_mul_sub_unifMatrix h₁ h₂

/-! ## 4. Non-vacuity of concrete high-probability transfer across `U = n`, `U = 2n`, and `2^(2^n)` -/

/-- Tight `U = n` (`0`-bit quotients, Case B) non-vacuity of `prob_fullQuotientPerm_forall_mem_le`
and `fullDecode` round-trip key recovery. -/
theorem fullQuotientPerm_tight_universe_nonvacuous :
    let n := quotientPermThreshold 0
    let u₀ : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 4) (four_le_quotientPermThreshold 0)⟩
    let u₁ : Fin n := ⟨1, lt_of_lt_of_le (by decide : 1 < 4) (four_le_quotientPermThreshold 0)⟩
    let T : Finset (Fin n) := {u₀, u₁}
    ∃ hnU : n ≤ n,
      (∀ (θ : QuotientPermSeed (FeistelQuotient.keyBits n) (bucketIndexBits n) 2 0 n) (u : Fin n),
        fullDecode hnU θ (fullBucket hnU θ u, fullQuot hnU θ u) = embedKey u) ∧
      ((PMF.uniformOfFintype
          (QuotientPermSeed (FeistelQuotient.keyBits n) (bucketIndexBits n) 2 0 n)).toOuterMeasure
        {θ | ∀ u ∈ T,
          fullBucket hnU θ u ∈ ({0} : Finset (Fin (2 ^ bucketIndexBits n))) ∧
          fullAux hnU θ u ∈ ({0} : Finset (Fin (2 ^ 2)))}).toReal ≤
        (((1 : ℝ) / (2 ^ bucketIndexBits n : ℝ)) * ((1 : ℝ) / (2 ^ 2 : ℝ))) ^ 2 +
          1 / (n : ℝ) := by
  intro n u₀ u₁ T
  refine ⟨le_rfl, fun θ u => fullDecode_fullBucket_fullQuot le_rfl θ u, ?_⟩
  have h4n : 4 ≤ n := four_le_quotientPermThreshold 0
  have h2κ : 2 ≤ quotientPermInd 0 n := (quotientPermInd_le_self_of_threshold le_rfl).2.1
  have hne : u₀ ≠ u₁ := fun h => absurd (congrArg Fin.val h) (by decide)
  have hT_card : #T = 2 := card_pair hne
  have hbound := prob_fullQuotientPerm_forall_mem_le (U := n) (b_aux := 2) (c := 0) (n := n)
    le_rfl le_rfl (S := T) (T := T) (by omega) Subset.rfl (by omega)
    (bucketShard (bucketIndexBits n) 0) {0}
    (fun b hb => by rw [mem_singleton.mp hb]) ({0} : Finset (Fin (2 ^ 2)))
  simpa only [hT_card, card_singleton, Nat.cast_one, zero_add, pow_one] using hbound

/-- Per-key multiplicative bound `prob_fullQuotientPerm_forall_mem_perKey_le` across both
`U = 2 * n` (Case B) and super-exponential `U = 2 ^ (2 ^ n)` (Case A, strictly violating
`log U ≤ poly(log n)`). -/
theorem fullQuotientPerm_perKey_small_and_huge_nonvacuous :
    let n := quotientPermThreshold 0
    ∀ U : ℕ, (U = 2 * n ∨ U = 2 ^ (2 ^ n)) →
      ∃ hnU : n ≤ U,
        ∀ (B : Fin U → Finset (Fin (2 ^ bucketIndexBits n)))
          (hB : ∀ u : Fin U, ∀ b ∈ B u, bucketShard (bucketIndexBits n) b = 0)
          (A : Fin U → Finset (Fin (2 ^ 3)))
          (T : Finset (Fin U)),
          #T ≤ quotientPermInd 0 n →
          ((PMF.uniformOfFintype
              (QuotientPermSeed (FeistelQuotient.keyBits U) (bucketIndexBits n) 3 0 n)).toOuterMeasure
            {θ | ∀ u ∈ T, fullBucket hnU θ u ∈ B u ∧ fullAux hnU θ u ∈ A u}).toReal ≤
            2 * (∏ u ∈ T, (((#(B u) : ℝ) / (2 ^ bucketIndexBits n : ℝ)) *
              ((#(A u) : ℝ) / (2 ^ 3 : ℝ)))) + 1 / (n : ℝ) := by
  intro n U hU
  have hnU : n ≤ U := by
    rcases hU with rfl | rfl
    · omega
    · exact Nat.lt_two_pow_self.le.trans Nat.lt_two_pow_self.le
  refine ⟨hnU, fun B hB A T hT => ?_⟩
  obtain ⟨_, _, hκ_n, _⟩ := quotientPermInd_le_self_of_threshold (c := 0) (n := n) le_rfl
  have hbound := prob_fullQuotientPerm_forall_mem_perKey_le (b_aux := 3) (c := 0)
    hnU le_rfl (S := T) (T := T) (hT.trans hκ_n) Subset.rfl hT 0 B (fun u _ => hB u) A
  simpa only [zero_add, pow_one] using hbound

/-- Non-vacuity of `prob_concreteCaseB_shardLoad_outside_le` at `n = quotientPermThreshold 0`,
`a = m = bucketIndexBits n`, `k_mom = 1`, `S = univ`. -/
theorem shardLoad_concentration_nonvacuous :
    let n := quotientPermThreshold 0
    let m := bucketIndexBits n
    ((PMF.uniformOfFintype (QuotientPermSeed m m 1 0 n)).toOuterMeasure
      {θ | ∃ σ : Fin (2 ^ shardBits m),
        (1 : ℝ) ≤ |(#((univ : Finset (Fin (2 ^ m))).filter
            fun u => bucketShard m (concreteBucket le_rfl θ u) = σ) : ℝ) -
          (2 ^ m : ℝ) / (2 ^ shardBits m : ℝ)|}).toReal ≤
      1 / (8 * (n : ℝ) ^ 2) +
        (2 ^ (shardBits m + 1) : ℝ) * (3 * ((2 ^ m : ℝ) / (2 ^ shardBits m : ℝ))) := by
  intro n m
  have h4n : 4 ≤ n := four_le_quotientPermThreshold 0
  obtain ⟨hb_log, h2κ, _, _⟩ := quotientPermInd_le_self_of_threshold (c := 0) (n := n) le_rfl
  have hb_pos : 1 ≤ quotientPermCharBits n := by rw [quotientPermCharBits_eq]; omega
  have hm_hi : m ≤ 8 * quotientPermCharBits n := by
    dsimp only [m, bucketIndexBits]; rw [quotientPermCharBits_eq]; omega
  have hcaseB : m < m + caseAGap 0 n := by
    have : 1 ≤ Nat.clog 2 (max n 2) := Nat.clog_pos (by decide) (by omega)
    unfold caseAGap; omega
  have hmu : (2 : ℝ) ≤ 3 * ((2 ^ m : ℝ) / (2 ^ shardBits m : ℝ)) := by
    have hle : shardBits m + 1 ≤ m := by dsimp only [m, bucketIndexBits, shardBits]; omega
    have hpow : (2 : ℝ) ≤ (2 ^ m : ℝ) / (2 ^ shardBits m : ℝ) := by
      rw [le_div_iff₀ (by positivity)]
      have : 2 * 2 ^ shardBits m ≤ 2 ^ m := by
        calc 2 * 2 ^ shardBits m = 2 ^ (shardBits m + 1) := by rw [pow_succ']
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hle
      exact_mod_cast this
    linarith
  have h := prob_concreteCaseB_shardLoad_outside_le (b_aux := 1) (c := 0) (k_mom := 1)
    (a := m) (m := m) (n := n) le_rfl hcaseB le_rfl hm_hi le_rfl h2κ univ (a_dev := 1)
    (by simpa using hmu) zero_lt_one
  simpa using h

end CslibFrontierTests.DataStructure.KickTreeQuotientPerm
