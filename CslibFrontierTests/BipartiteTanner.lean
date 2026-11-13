/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.PolyTime.BitString.TannerSearch
import CslibFrontier.Foundations.Combinatorics.Expander.BipartiteTanner
import CslibFrontier.Foundations.Data.BitString.Parity.DotProduct
import CslibFrontier.Probability.SmallBias.Random
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option linter.privateModule false

/-!
Nonvacuous kernel-checked tests for:
- `⌈4 (r + 1) / ε²⌉` small-bias sample spaces (`BitString` and `ZMod 2` multisets);
- linear and parity-check code API (`Code.Linear`, `Code.ParityCheck`);
- general regular bipartite multigraphs retaining parallel-edge multiplicity, singular values,
  eigenvalues, and bipartite mixing (`BipartiteRotationMap`);
- general bipartite Tanner code distance `δ (δ - λ)`, asymmetric bounds, rate `rL + rR - 1`, LDPC
  check matrices, and shortening (`BipartiteTanner`);
- unconditional small-bias + local-code parity-test composition (`TannerSearch`).
-/

namespace CslibFrontierTests.BipartiteTanner

open Finset Matrix Cslib Cslib.BitString Cslib.Complexity

/-! ### 1. Small-bias `⌈4 (r + 1) / ε²⌉` bounds -/

/-- Explicit `⌈4 (r + 1) / ε²⌉` construction gives an `ε = 1/2` biased multiset of `48` vectors in
`(ZMod 2)^2`, and a corresponding `Fin 48 → BitString 2` shift family. -/
example :
    (∃ M : Multiset (Fin 2 → ZMod 2),
      Multiset.card M = Nat.ceil (4 * ((2 : ℝ) + 1) / ((1 / 2 : ℚ) : ℝ) ^ 2) ∧
      IsSmallBiasMultiset 2 (((1 / 2 : ℚ) : ℝ)) M) ∧
    (0 < Nat.ceil (4 * ((2 : ℝ) + 1) / (1 / 2 : ℝ) ^ 2) ∧
      ∃ (_ : NeZero (Nat.ceil (4 * ((2 : ℝ) + 1) / (1 / 2 : ℝ) ^ 2)))
        (s : Fin (Nat.ceil (4 * ((2 : ℝ) + 1) / (1 / 2 : ℝ) ^ 2)) → BitString 2),
        IsSmallBias (1 / 2 : ℝ)
          ((Probability.PMF.uniformOfFintype _).map s)) :=
  ⟨exists_isSmallBiasMultiset_of_rat 2 (by norm_num),
   exists_isSmallBias_bitString_of_ceil 2 (ε := (1 / 2 : ℝ)) (by norm_num)⟩

example :
    ∃ M : Multiset (Fin 2 → ZMod 2),
      0 < Multiset.card M ∧
        ∀ a : Fin 2 → ZMod 2, a ≠ 0 →
          |(M.map fun x => (-1 : ℝ) ^ (a ⬝ᵥ x).val).sum / Multiset.card M| ≤
            ((1 / 2 : ℚ) : ℝ) := by
  obtain ⟨M, _, hM⟩ := exists_isSmallBiasMultiset_of_rat 2 (ε := (1 / 2 : ℚ)) (by norm_num)
  exact ⟨M, isSmallBiasMultiset_iff.1 hM⟩

/-! ### 2. General linear and binary parity-check code API -/

/-- Check matrix of the `[3, 2, 2]` binary single-parity-check code. -/
def spcMatrix : Matrix (Fin 1) (Fin 3) Bool :=
  Matrix.of ![![true, true, true]]

/-- Check matrix of the `[3, 1, 3]` binary repetition code. -/
def repMatrix : Matrix (Fin 2) (Fin 3) Bool :=
  Matrix.of ![![true, true, false], ![false, true, true]]

theorem spcMatrix_minWeight :
    ∀ w : Fin 3 → Bool, w ≠ 0 → spcMatrix *ᵥ w = 0 →
      (2 / 3 : ℝ) * Fintype.card (Fin 3) ≤ hammingNorm w := by
  intro w hw0 hw
  have h2 : 2 ≤ hammingNorm w := by
    decide +revert
  rw [Fintype.card_fin]
  norm_num
  exact_mod_cast h2

theorem repMatrix_minDist :
    ∀ w₁ w₂ : Fin 3 → Bool, repMatrix *ᵥ w₁ = 0 → repMatrix *ᵥ w₂ = 0 → w₁ ≠ w₂ →
      3 ≤ hammingDist w₁ w₂ := by
  decide

private def emb2 : Fin 2 ↪ Fin 3 :=
  ⟨fun i => ⟨i.val, by omega⟩, fun _ _ h => Fin.ext (Fin.mk.inj h)⟩

/-- The `[3, 2, 2]` single-parity-check code has rate at least `1 - 1 / 3 = 2 / 3`, `ZMod 2` rank
+ nullity equal to `3`, and minimum distance at least `2` preserved under shortening. -/
example :
    (2 / 3 : ℝ) ≤ Code.rate (Code.parityCheckCode spcMatrix : Set (Fin 3 → Bool)) ∧
      Matrix.rank (spcMatrix.map bitEquiv.symm) +
        Module.finrank (ZMod 2) (Code.parityCheckCode (spcMatrix.map bitEquiv.symm)) = 3 ∧
      (2 : ℕ∞) ≤ Code.minDist
        (Code.shortenLinear (Code.parityCheckCode spcMatrix) emb2 :
          Set (Fin 2 → Bool)) := by
  have hrate : (2 / 3 : ℝ) ≤ Code.rate (Code.parityCheckCode spcMatrix : Set (Fin 3 → Bool)) := by
    have hr := Code.one_sub_card_div_card_le_rate_parityCheckCode
      (by decide : 0 < Fintype.card (Fin 3)) spcMatrix
    simp only [Fintype.card_fin] at hr
    norm_num at hr
    exact hr
  have hdist : (2 : ℕ∞) ≤ Code.minDist (Code.parityCheckCode spcMatrix : Set (Fin 3 → Bool)) := by
    refine (Code.le_minDist_iff_hammingNorm (Code.parityCheckCode spcMatrix)).2 fun w hw hw0 => ?_
    have h := spcMatrix_minWeight w hw0 (Code.mem_parityCheckCode.1 hw)
    rw [Fintype.card_fin] at h
    exact Nat.cast_le.2 (Nat.cast_le.1 (by norm_num at h; exact h))
  refine ⟨hrate, Code.finrank_parityCheckCode_add_rank _, ?_⟩
  simpa only [Code.coe_shortenLinear] using
    hdist.trans
      (Code.le_minDist_shorten (Code.parityCheckCode spcMatrix : Set (Fin 3 → Bool)) emb2)

example :
    (fun _ : Fin 2 => true) ∈
      Code.punctureLinear (Code.parityCheckCode spcMatrix) emb2 ∧
    (Code.punctureLinear (Code.parityCheckCode spcMatrix) emb2 : Set (Fin 2 → Bool)) =
      Code.puncture (Code.parityCheckCode spcMatrix : Set (Fin 3 → Bool)) emb2 ∧
    Code.syndrome spcMatrix ![true, true, false] = 0 := by
  refine ⟨?_, Code.coe_punctureLinear _ _, ?_⟩
  · refine Code.mem_punctureLinear.2 ⟨![true, true, false], ?_, ?_⟩
    · rw [Code.mem_parityCheckCode]
      decide
    · funext i
      fin_cases i <;> rfl
  · rw [Code.syndrome_eq]
    decide

/-! ### 3. General `BipartiteRotationMap` with parallel edges (`L ≠ R`) -/

/-- A `3`-regular bipartite multigraph between `L = Bool` and `R = Fin 2` with parallel edges of
multiplicity `2` (`false ↔ 0` and `true ↔ 1` via ports `0, 1`) and single cross edges on port `2`.
-/
def parallelBipartite : BipartiteRotationMap Bool (Fin 2) (Fin 3) where
  toRight :=
    { toFun := fun (u, i) => match i with
        | 0 => (if u then 1 else 0, 0)
        | 1 => (if u then 1 else 0, 1)
        | 2 => (if u then 0 else 1, 2)
      invFun := fun (v, j) => match j with
        | 0 => (v == 1, 0)
        | 1 => (v == 1, 1)
        | 2 => (v == 0, 2)
      left_inv := fun (u, i) => by cases u <;> fin_cases i <;> rfl
      right_inv := fun (v, j) => by fin_cases v <;> fin_cases j <;> rfl }

/-- Parallel edges retain multiplicity `2`: `#(E({false}, {0})) = 2`. -/
example : #(parallelBipartite.interedges {false} {0}) = 2 := by
  decide

/-- On mean-zero vectors, `parallelBipartite.walkLeft` scales by `1 / 3`, so `σ₂ ≤ 1 / 3`. -/
theorem parallelBipartite_singularValue_le :
    parallelBipartite.nontrivialSingularValue ≤ 1 / 3 := by
  refine (BipartiteRotationMap.nontrivialSingularValue_le_iff (by norm_num)).2 fun g hg => ?_
  have hsum : g 0 + g 1 = 0 := by
    rw [Fintype.expect_eq_sum_div_card, Fin.sum_univ_two, Fintype.card_fin] at hg
    linarith
  have hg1 : g 1 = -g 0 := eq_neg_of_add_eq_zero_right hsum
  have hwF : parallelBipartite.walkLeft g false = g 0 / 3 := by
    rw [BipartiteRotationMap.walkLeft_apply, Fintype.expect_eq_sum_div_card, Fin.sum_univ_three,
      Fintype.card_fin]
    simp only [BipartiteRotationMap.neighborRight, parallelBipartite, Equiv.coe_fn_mk,
      Bool.false_eq_true, ↓reduceIte]
    linarith
  have hwT : parallelBipartite.walkLeft g true = -(g 0) / 3 := by
    rw [BipartiteRotationMap.walkLeft_apply, Fintype.expect_eq_sum_div_card, Fin.sum_univ_three,
      Fintype.card_fin]
    simp only [BipartiteRotationMap.neighborRight, parallelBipartite, Equiv.coe_fn_mk, ↓reduceIte]
    linarith
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  simp only [Fintype.sum_bool, Fin.sum_univ_two, Fintype.card_bool, Fintype.card_fin, hwF, hwT,
    hg1]
  push_cast
  ring_nf
  exact le_rfl

/-- An explicit balanced `1/3`-eigenfunction of `parallelBipartite.toRotationMap` shows
`σ₂ = 1 / 3` and exercises `abs_eigenvalue_le_nontrivialSingularValue_of_isBipartiteBalanced`. -/
example : parallelBipartite.nontrivialSingularValue = 1 / 3 := by
  refine le_antisymm parallelBipartite_singularValue_le ?_
  let f : Bool ⊕ Fin 2 → ℝ :=
    Sum.elim (fun u => if u then -1 else 1) (fun v => if v = 0 then 1 else -1)
  have hf0 : f ≠ 0 := fun h => by
    have := congrFun h (.inl false)
    simp [f] at this
  have hfbal : BipartiteRotationMap.IsBipartiteBalanced f := by
    constructor <;> rw [Fintype.expect_eq_sum_div_card] <;> norm_num [f, Fin.sum_univ_two]
  have hwalk : parallelBipartite.toRotationMap.walk f = (1 / 3 : ℝ) • f := by
    funext x
    rcases x with u | v
    · (cases u <;>
        simp [f, RotationMap.walk_apply, RotationMap.neighbor,
          BipartiteRotationMap.toRotationMap, parallelBipartite,
          Fintype.expect_eq_sum_div_card, Fin.sum_univ_three])
      norm_num
    · (fin_cases v <;>
        simp [f, RotationMap.walk_apply, RotationMap.neighbor,
          BipartiteRotationMap.toRotationMap, parallelBipartite,
          Fintype.expect_eq_sum_div_card, Fin.sum_univ_three])
      norm_num
  have hle := parallelBipartite.abs_eigenvalue_le_nontrivialSingularValue_of_isBipartiteBalanced
    hf0 hfbal hwalk
  norm_num at hle
  exact hle

/-! ### 4. General bipartite Tanner codes: `δ (δ - λ)`, rate, nonvacuity, and shortening -/

/-- Nonzero codeword of weight `2` in the Tanner code of `parallelBipartite` with `spcMatrix`. -/
def parallelCodeword : Bool × Fin 3 → Bool :=
  fun (u, i) => !u && (i == 0 || i == 1)

theorem parallelCodeword_mem :
    parallelCodeword ∈
      BipartiteTanner.submodule parallelBipartite
        (Code.parityCheckCode spcMatrix) (Code.parityCheckCode spcMatrix) := by
  rw [BipartiteTanner.mem_submodule]
  constructor
  · intro u
    cases u <;> refine Code.mem_parityCheckCode.2 ?_ <;> funext k <;> fin_cases k <;> decide
  · intro v
    fin_cases v <;> refine Code.mem_parityCheckCode.2 ?_ <;> funext k <;> fin_cases k <;> decide

theorem parallelCodeword_ne_zero : parallelCodeword ≠ 0 := fun h => by
  have := congrFun h (false, 0)
  simp [parallelCodeword] at this

private theorem emb5_inj : Function.Injective (fun e : Fin 5 =>
    (decide (3 ≤ e.val), (⟨e.val % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3))) := by
  decide

/-- For `parallelBipartite` (`d = 3`, `N = 2`, `σ₂ = 1 / 3`) and local `[3, 2, 2]` check matrix
`spcMatrix` (`δ = 2 / 3`), we have:
- global Tanner distance `minDist ≥ δ (δ - σ₂) · 6 = 4 / 3`, hence `minDist = 2` (tight via
  `parallelCodeword`),
- rate at least `1 / 3` (matching both `one_sub_card_div_card_le_rate_parityCheck` and
  `rate_submodule_ge`),
- LDPC row weight at most `3`, and
- shortening along `Fin 5 ↪ Bool × Fin 3` preserves `minDist ≥ 2` and row weight `≤ 3`. -/
example :
    let C := BipartiteTanner.submodule parallelBipartite
      (Code.parityCheckCode spcMatrix) (Code.parityCheckCode spcMatrix)
    Code.minDist (C : Set (Bool × Fin 3 → Bool)) = 2 ∧
      (1 / 3 : ℝ) ≤ Code.rate (C : Set (Bool × Fin 3 → Bool)) ∧
      Code.rate (Code.parityCheckCode spcMatrix : Set (Fin 3 → Bool)) +
        Code.rate (Code.parityCheckCode spcMatrix : Set (Fin 3 → Bool)) - 1 ≤
        Code.rate (C : Set (Bool × Fin 3 → Bool)) ∧
      (∀ r, hammingNorm (BipartiteTanner.checkMatrix parallelBipartite spcMatrix spcMatrix r) ≤ 3) ∧
      let emb : Fin 5 ↪ Bool × Fin 3 :=
        ⟨fun e => (decide (3 ≤ e.val), ⟨e.val % 3, Nat.mod_lt _ (by decide)⟩), emb5_inj⟩
      (∀ r,
        hammingNorm
          (((BipartiteTanner.checkMatrix parallelBipartite spcMatrix spcMatrix).submatrix
            id emb) r) ≤ 3) ∧
      (2 : ℕ∞) ≤ Code.minDist
        (Code.shortenLinear
          (Code.parityCheckCode (BipartiteTanner.checkMatrix parallelBipartite spcMatrix spcMatrix))
          emb : Set (Fin 5 → Bool)) := by
  let C := BipartiteTanner.submodule parallelBipartite
    (Code.parityCheckCode spcMatrix) (Code.parityCheckCode spcMatrix)
  have hge : (2 : ℕ∞) ≤ Code.minDist (C : Set (Bool × Fin 3 → Bool)) := by
    refine (Code.le_minDist_iff_hammingNorm C).2 fun x hx hx0 => Nat.cast_le.2 ?_
    have hrel := BipartiteTanner.relDist_mul_sub_le_hammingNorm_of_submodule parallelBipartite
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (fun w hw hw0 => spcMatrix_minWeight w hw0 (Code.mem_parityCheckCode.1 hw))
      (fun w hw hw0 => spcMatrix_minWeight w hw0 (Code.mem_parityCheckCode.1 hw))
      parallelBipartite_singularValue_le hx hx0
    have hcard : Fintype.card (Bool × Fin 3) = 6 := by decide
    rw [hcard] at hrel
    have h2 : (4 / 3 : ℝ) ≤ hammingNorm x := by linarith
    have hn : 1 < hammingNorm x := by
      rw [← @Nat.cast_lt ℝ]
      push_cast
      linarith
    exact hn
  have hle : Code.minDist (C : Set (Bool × Fin 3 → Bool)) ≤ 2 := by
    have hw : hammingNorm parallelCodeword = 2 := by decide
    rw [show (2 : ℕ∞) = (hammingNorm parallelCodeword : ℕ∞) from by simp [hw],
      ← hammingDist_zero_right parallelCodeword]
    exact Code.minDist_le_hammingDist parallelCodeword_mem C.zero_mem parallelCodeword_ne_zero
  have hrate : (1 / 3 : ℝ) ≤ Code.rate (C : Set (Bool × Fin 3 → Bool)) := by
    have hr := BipartiteTanner.one_sub_card_div_card_le_rate_parityCheck parallelBipartite
      (by decide : 0 < Fintype.card Bool) (by decide : 0 < Fintype.card (Fin 3))
      spcMatrix spcMatrix
    simp only [Fintype.card_fin] at hr
    norm_num at hr
    exact hr
  have hrateSub := BipartiteTanner.rate_submodule_ge parallelBipartite
    (by decide : 0 < Fintype.card Bool) (by decide : 0 < Fintype.card (Fin 3))
    (Code.parityCheckCode spcMatrix) (Code.parityCheckCode spcMatrix)
  refine ⟨le_antisymm hle hge, hrate, hrateSub, fun r => ?_, ?_⟩
  · simpa only [Fintype.card_fin] using
      BipartiteTanner.hammingNorm_checkMatrix_row_le parallelBipartite spcMatrix spcMatrix r
  · let emb : Fin 5 ↪ Bool × Fin 3 :=
      ⟨fun e => (decide (3 ≤ e.val), ⟨e.val % 3, Nat.mod_lt _ (by decide)⟩), emb5_inj⟩
    refine ⟨fun r => (BipartiteTanner.hammingNorm_submatrix_row_le _ emb r).trans ?_, ?_⟩
    · simpa only [Fintype.card_fin] using
        BipartiteTanner.hammingNorm_checkMatrix_row_le parallelBipartite spcMatrix spcMatrix r
    · rw [Code.shortenLinear_parityCheckCode, Code.le_minDist_iff_hammingNorm]
      intro z hz hz0
      have hrel := BipartiteTanner.relDist_mul_sub_le_hammingNorm_of_submatrix parallelBipartite
        spcMatrix spcMatrix (by norm_num : (0 : ℝ) ≤ 2 / 3)
        spcMatrix_minWeight spcMatrix_minWeight parallelBipartite_singularValue_le emb
        (Code.mem_parityCheckCode.1 hz) hz0
      have hcard : Fintype.card (Bool × Fin 3) = 6 := by decide
      rw [hcard] at hrel
      have h2 : (4 / 3 : ℝ) ≤ hammingNorm z := by linarith
      have hn : 1 < hammingNorm z := by
        rw [← @Nat.cast_lt ℝ]
        push_cast
        linarith
      exact Nat.cast_le.2 hn

/-- Asymmetric bipartite Tanner distance bound combining `[3, 2, 2]` on the left (`kL = 2`) and the
`[3, 1, 3]` repetition code on the right (`kR = 3`). -/
example :
    let C := BipartiteTanner.submodule parallelBipartite
      (Code.parityCheckCode spcMatrix) (Code.parityCheckCode repMatrix)
    ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
      √6 * (√6 - 1) * 2 ≤ 3 * hammingDist x y := by
  intro C x hx y hy hxy
  have hL : ∀ w₁ ∈ (Code.parityCheckCode spcMatrix : Set (Fin 3 → Bool)),
      ∀ w₂ ∈ (Code.parityCheckCode spcMatrix : Set (Fin 3 → Bool)), w₁ ≠ w₂ →
        (2 : ℝ) ≤ hammingDist w₁ w₂ := by
    intro w₁ hw₁ w₂ hw₂ hne
    have h := (Code.le_minDist_iff_hammingNorm (Code.parityCheckCode spcMatrix) (d := 2)).2
      (fun w hw hw0 => by
        have hm := spcMatrix_minWeight w hw0 (Code.mem_parityCheckCode.1 hw)
        rw [Fintype.card_fin] at hm
        exact Nat.cast_le.2 (Nat.cast_le.1 (by norm_num at hm; exact hm)))
    rw [Code.le_minDist_iff] at h
    exact Nat.cast_le.2 (ENat.natCast_le_natCast.1 (h w₁ hw₁ w₂ hw₂ hne))
  have hR : ∀ w₁ ∈ (Code.parityCheckCode repMatrix : Set (Fin 3 → Bool)),
      ∀ w₂ ∈ (Code.parityCheckCode repMatrix : Set (Fin 3 → Bool)), w₁ ≠ w₂ →
        (3 : ℝ) ≤ hammingDist w₁ w₂ := by
    intro w₁ hw₁ w₂ hw₂ hne
    rw [SetLike.mem_coe, Code.mem_parityCheckCode] at hw₁ hw₂
    exact_mod_cast repMatrix_minDist w₁ w₂ hw₁ hw₂ hne
  have hx' : x ∈ BipartiteTanner.code parallelBipartite
      (Code.parityCheckCode spcMatrix : Set (Fin 3 → Bool))
      (Code.parityCheckCode repMatrix : Set (Fin 3 → Bool)) := hx
  have hy' : y ∈ BipartiteTanner.code parallelBipartite
      (Code.parityCheckCode spcMatrix : Set (Fin 3 → Bool))
      (Code.parityCheckCode repMatrix : Set (Fin 3 → Bool)) := hy
  have h := BipartiteTanner.sqrt_mul_sub_card_le_of_hammingDist parallelBipartite
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3) hL hR
    parallelBipartite_singularValue_le hx' hy' hxy
  simp only [Fintype.card_bool, Fintype.card_fin] at h
  push_cast at h
  linarith

/-! ### 5. Unconditional M20 constructive search & parity tests (`TannerSearch`) -/

/-- Nonvacuous concrete instantiation of `TannerSearch.tannerParityTests_spec`: for `r = 1`,
`ε = 1 / 3`, `d = 72 = smallBiasCeil 1 1 3`, `h = 35` (`δ = 36 / 72 = 1 / 2`), `c = 217`, and
`m = 144`, every produced row has weight at most `72`, and every nonzero kernel word has weight at
least `δ (δ - ε) · 144 = (1 / 2) · (1 / 6) · 144 = 12`. -/
example :
    let rows := TannerSearch.tannerParityTests 144 1 72 217 35 1 3
    rows.length = 868 ∧
      (∀ row ∈ rows, row.length = 144 ∧ row.count true ≤ 72) ∧
      ∀ z : Fin 144 → Bool, z ≠ 0 →
        (∀ row ∈ rows, ofList 144 row ⬝ᵥ z = false) → 12 ≤ weight z := by
  have hceil : TannerSearch.smallBiasCeil 1 1 3 ≤ 72 := by
    rw [TannerSearch.smallBiasCeil]
    decide
  have hGV : (72 + 1) ^ 35 ≤ 2 ^ 217 := by
    calc
      (72 + 1) ^ 35 = ((72 + 1) ^ 5) ^ 7 := by ring
      _ ≤ (2 ^ 31) ^ 7 := Nat.pow_le_pow_left (by decide) 7
      _ = 2 ^ 217 := (Nat.pow_mul 2 31 7).symm
  have hm : 144 ≤ 2 ^ 1 * 72 := by decide
  obtain ⟨hlen, hrows, hdist⟩ := TannerSearch.tannerParityTests_spec hm (by decide) (by decide)
    hceil hGV
  refine ⟨hlen, hrows, fun z hz0 hz => ?_⟩
  have hrel := (hdist z hz0 hz).2
  norm_num at hrel
  exact hrel

/-- `ComputableInO` search complexity certificates for small-bias shifts and end-to-end M20 parity
tests are nonvacuous. -/
example :
    (∃ eT eS : ℕ,
      Turing.MultiTapeTM.ComputableInO
        (fun q : TannerSearch.SmallBiasCeilParams =>
          TannerSearch.findSmallBiasShiftsCeil q.r q.p q.q)
        TannerSearch.encSmallBiasCeilParams
        (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encBits)
        (fun q =>
          2 ^ (TannerSearch.smallBiasCeil q.r q.p q.q * q.r + q.r) *
            ((TannerSearch.encSmallBiasCeilParams q).length + 1) ^ eT)
        (fun q => ((TannerSearch.encSmallBiasCeilParams q).length + 1) ^ eS)) ∧
    (∃ e : ℕ,
      Turing.MultiTapeTM.ComputableInO
        (fun q : TannerSearch.TannerParityParams =>
          TannerSearch.tannerParityTestsWithBound q.maxVerts q.m q.r q.d q.c q.h q.p q.q)
        TannerSearch.encTannerParityParams
        (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encBits)
        (fun q =>
          2 ^ (q.d * q.r + q.r + (q.c * q.d + q.d)) *
            ((TannerSearch.encTannerParityParams q).length + 1) ^ e)
        (fun q => ((TannerSearch.encTannerParityParams q).length + 1) ^ e)) :=
  ⟨TannerSearch.findSmallBiasShiftsCeil_computableInO, TannerSearch.tannerParityTests_computableInO⟩

end CslibFrontierTests.BipartiteTanner
