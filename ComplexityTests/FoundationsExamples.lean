/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Code.HintDecoding
import Complexity.Foundations.Data.Code.LowDegreeExtension
import Complexity.Foundations.GroupTheory.Perm.Fin
import Complexity.Foundations.GroupTheory.Perm.FiveCycle
import Complexity.Foundations.GroupTheory.Perm.Last
import Complexity.Foundations.LinearAlgebra.Interpolation
import Complexity.Foundations.LinearAlgebra.KernelVector
import Complexity.Foundations.LinearAlgebra.Matrix.Rank
import Complexity.Foundations.LinearAlgebra.Rank
import Complexity.Probability.ApproximateCounting.Relative
import Complexity.Probability.BitString.LinearHash
import Complexity.Probability.Entropy
import Complexity.Probability.EntropyExtraction
import Complexity.Probability.PairwiseIndependentHash.Shift
import Complexity.Probability.PairwiseIndependentHash.Toeplitz
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Concrete instances of linear algebra, codes, permutations and hashing

Elimination computes the all-ones kernel vector of a `2 × 3` matrix over `ZMod 2`, and the zero
vector for an invertible matrix. Hint decoding over `ZMod 5` applies to a word with two errors,
and the low-degree extensions of conjunction and disjunction over `ZMod 3` are Reed–Muller
codewords at distance at least three. The rotation of `Fin 5` is a five-cycle while a
transposition is not, and half of the orders of `Fin 3` put `2` after `0`. A block matrix has rank
at most two, both by subadditivity and by rank budgets for linear maps. On the probability side,
Toeplitz matrices reach every value at a nonzero vector, both shift criteria apply to hash families
over `ZMod 3` (one with a key entering non-additively), the entropy chain rule and the
conditional-entropy average are evaluated on two uniform bits, binary matrix hashing extracts with
error below `1 / 2`, and Toeplitz and affine hash families meet the hypotheses of relative-error
approximate counting. The examples apply headline theorems to objects satisfying their
hypotheses, so these theorems are not vacuous, and `decide` checks the computed values.
-/

namespace ComplexityTests.FoundationsExamples

open Cslib Finset
open scoped Matrix

/-! ### Kernel vectors by elimination -/

section KernelVector

open Cslib.LinearAlgebra

/-- With more columns than rows, the output of elimination is a nonzero kernel vector. -/
private theorem kernelVec_spec_of_lt {F : Type*} [Field F] [DecidableEq F] {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) F) (h : r < n) : A *ᵥ kernelVec A = 0 ∧ kernelVec A ≠ 0 := by
  refine ⟨mulVec_kernelVec A, kernelVec_ne_zero A ?_⟩
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := A.mulVecLin) (by simpa using h))
  exact ⟨v, hv0, hv⟩

/-- The rows `x₀ + x₁` and `x₁ + x₂` over `ZMod 2`: two equations in three unknowns. -/
private def kerMat : Matrix (Fin 2) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 1]

-- Two rows and three columns: the output is a nonzero kernel vector, namely the all-ones vector,
-- while a matrix with trivial kernel yields the zero vector.
example :
    kerMat *ᵥ kernelVec kerMat = 0 ∧
    kernelVec kerMat ≠ 0 ∧
    kernelVec kerMat = ![1, 1, 1] ∧
    kernelVec (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 0 :=
  ⟨(kernelVec_spec_of_lt kerMat (by decide)).1,
    (kernelVec_spec_of_lt kerMat (by decide)).2,
    by decide +kernel,
    by decide +kernel⟩

end KernelVector

/-! ### Sudan decoding with a hint -/

section HintDecoding

open Cslib.Code Polynomial

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The five points of `ZMod 5`. -/
private def pts5 : Fin 5 → ZMod 5 := fun i => (i : ℕ)

/-- A received word agreeing with `X + 1` at the points `0, 1, 2` and wrong at `3` and `4`. -/
private def word5 : Fin 5 → ZMod 5 := ![1, 2, 3, 0, 1]

-- Six monomials of `(1, 1)`-weighted degree at most `2` exceed the five points, so elimination
-- yields a Sudan interpolant; and the hint `τ + 1` at `τ` decodes `1` at `0` for all but at most
-- `D - d = 1` hint points.
example :
    Sudan.IsInterpolant pts5 word5 1 2 (Sudan.interpolant pts5 word5 1 2) ∧
    #{τ : ZMod 5 | hintDecode pts5 word5 1 2 τ (τ + 1) ≠ 1} ≤ 1 := by
  refine ⟨Sudan.isInterpolant_interpolant pts5 word5 le_rfl (by decide), ?_⟩
  have h := card_hintDecode_ne_le (α := pts5) (w := word5) (d := 1) (D := 2) (by decide) le_rfl
    (by decide) (by simp [ZMod.card]) (P := X + C 1) (natDegree_X_add_C 1).le (by
      simp only [eval_add, eval_X, eval_C]
      decide)
  simpa using h

end HintDecoding

/-! ### Low-degree extensions -/

section LowDegreeExtension

open Cslib.Code

/-- The bits as the elements `0` and `1` of `ZMod 3`. -/
private def boolEmb : Bool ↪ ZMod 3 := ⟨fun b => if b then 1 else 0, by decide⟩

/-- The conjunction of two bits, with values in `ZMod 3`. -/
private def andF (u : Fin 2 → Bool) : ZMod 3 := if u 0 && u 1 then 1 else 0

/-- The disjunction of two bits, with values in `ZMod 3`. -/
private def orF (u : Fin 2 → Bool) : ZMod 3 := if u 0 || u 1 then 1 else 0

-- The extension agrees with the function on `{0, 1} ^ 2`, is a Reed–Muller codeword of degree
-- `2 * (2 - 1) = 2`, and differs from `lowDegreeExtension boolEmb orF` on at least `3` points.
example :
    lowDegreeExtension boolEmb andF ![1, 1] = 1 ∧
    lowDegreeExtension boolEmb andF ∈ reedMuller (ZMod 3) 2 2 ∧
    3 ≤ hammingDist (lowDegreeExtension boolEmb andF) (lowDegreeExtension boolEmb orF) := by
  refine ⟨by
      rw [show (![1, 1] : Fin 2 → ZMod 3) = fun i => boolEmb (![true, true] i) by decide,
        lowDegreeExtension_apply_embed]
      rfl,
    by simpa using lowDegreeExtension_mem_reedMuller boolEmb andF, ?_⟩
  have hne : lowDegreeExtension boolEmb andF ≠ lowDegreeExtension boolEmb orF := fun h => by
    have := congrFun h fun i => boolEmb (![true, false] i)
    rw [lowDegreeExtension_apply_embed, lowDegreeExtension_apply_embed] at this
    exact absurd this (by decide)
  have := card_sub_mul_pow_le_mul_hammingDist_of_mem_reedMuller
    (lowDegreeExtension_mem_reedMuller boolEmb andF)
    (lowDegreeExtension_mem_reedMuller boolEmb orF) hne
  simp [ZMod.card] at this
  omega

end LowDegreeExtension

/-! ### Permutations -/

section Perm

open Equiv Equiv.Perm
open scoped commutatorElement

private theorem isFiveCycle_finRotate : IsFiveCycle (finRotate 5) := by
  have h := isFiveCycle_formPerm (l := ([0, 1, 2, 3, 4] : List (Fin 5))) (by decide) rfl
  rwa [show ([0, 1, 2, 3, 4] : List (Fin 5)).formPerm = finRotate 5 by decide] at h

-- The rotation of `Fin 5` is an even five-cycle and a commutator of two five-cycles, while a
-- transposition is not a five-cycle; stepping forward from `4` wraps to `0` in one cycle.
example :
    finRotate 5 ∈ alternatingGroup (Fin 5) ∧
    (∃ τ₁ τ₂ : Perm (Fin 5), IsFiveCycle τ₁ ∧ IsFiveCycle τ₂ ∧ ⁅τ₁, τ₂⁆ = finRotate 5) ∧
    ¬ IsFiveCycle (swap (0 : Fin 5) 1) ∧
    (finRotate 5 4 : ℕ) = 0 ∧
    (finRotate 5).SameCycle 1 4 :=
  ⟨isFiveCycle_finRotate.mem_alternatingGroup,
    isFiveCycle_finRotate.exists_commutator,
    fun h => by
      have := h.sign
      rw [sign_swap (by decide)] at this
      exact absurd this (by decide),
    by rw [val_finRotate]; rfl,
    sameCycle_finRotate 1 4⟩

-- Of the `3! = 6` orders of `Fin 3`, half put `2` after `0`.
example : #{σ : Perm (Fin 3) | ∀ u ∈ ({0, 2} : Finset (Fin 3)), σ u ≤ σ 2} = 3 := by
  have h := card_mul_card_filter_forall_le_eq_factorial (S := ({0, 2} : Finset (Fin 3)))
    (i := 2) (by decide)
  rw [show #({0, 2} : Finset (Fin 3)) = 2 by decide, Fintype.card_fin,
    show (3 : ℕ).factorial = 6 by rfl] at h
  convert Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (h.trans (by norm_num : 6 = 2 * 3))

end Perm

/-! ### Interpolation -/

section Interpolation

open Cslib.LinearAlgebra

/-- The constant `1` and the identity on `ℚ`, which span the lines `a + b x`. -/
private def lineBasis : Fin 2 → ℚ → ℚ := ![1, id]

/-- Every function agrees on `{0, 1}` with a line. -/
private theorem lines_interpolate (f : ℚ → ℚ) :
    ∃ g ∈ Submodule.span ℚ (lineBasis '' (univ : Finset (Fin 2))),
      ∀ x ∈ ({0, 1} : Finset ℚ), g x = f x := by
  refine ⟨f 0 • lineBasis 0 + (f 1 - f 0) • lineBasis 1,
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp, rfl⟩)), fun x hx => ?_⟩
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl <;> simp [lineBasis]

/-- The interpolation bound is attained on `{0, 1}` and fails on `{0, 1, 2}`. -/
example :
    #({0, 1} : Finset ℚ) ≤ #(univ : Finset (Fin 2)) ∧
    ¬∀ f : ℚ → ℚ, ∃ g ∈ Submodule.span ℚ (lineBasis '' (univ : Finset (Fin 2))),
      ∀ x ∈ ({0, 1, 2} : Finset ℚ), g x = f x :=
  ⟨card_le_of_forall_exists_mem_span_eq _ _ lineBasis lines_interpolate,
    fun h => absurd (card_le_of_forall_exists_mem_span_eq _ _ lineBasis h) (by simp)⟩

end Interpolation

/-! ### Rank -/

section Rank

open Matrix

/-- A block matrix: an all-ones `2 × 2` block and a `1 × 1` block. -/
private def blockMat : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 1, 1, 0; 0, 0, 1]

private theorem blockMat_eq :
    blockMat = vecMulVec ![1, 1, 0] ![1, 1, 0] + vecMulVec ![0, 0, 1] ![0, 0, 1] := by decide

-- Subadditivity bounds its rank by the number of rank-one summands.
example : blockMat.rank ≤ 2 := by
  rw [blockMat_eq]
  exact (rank_add_le _ _).trans (add_le_add (rank_vecMulVec_le _ _) (rank_vecMulVec_le _ _))

-- The same bound from rank budgets for the linear maps of the summands.
example : blockMat.rank ≤ 2 := by
  let summand : Fin 2 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
    ![vecMulVec ![1, 1, 0] ![1, 1, 0], vecMulVec ![0, 0, 1] ![0, 0, 1]]
  have hmem : blockMat.toLin' ∈
      Submodule.span (ZMod 2) (Set.range fun i => (summand i).toLin') := by
    rw [blockMat_eq, map_add]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨0, rfl⟩) (Submodule.subset_span ⟨1, rfl⟩)
  have h := LinearMap.rank_le_sum_of_mem_span _ _ (fun _ => 1) hmem fun i => by
    rw [← Matrix.natCast_rank_eq_rank_toLin', Nat.cast_le]
    fin_cases i
    · exact rank_vecMulVec_le (R := ZMod 2) ![1, 1, 0] ![1, 1, 0]
    · exact rank_vecMulVec_le (R := ZMod 2) ![0, 0, 1] ![0, 0, 1]
  rw [← Matrix.natCast_rank_eq_rank_toLin'] at h
  simpa using h

end Rank

/-! ### Toeplitz hashing -/

section Toeplitz

open Cslib.Probability Matrix

-- `2 × 3` Toeplitz matrices reach every value at the nonzero vector `(0, 1, 0)`, but not at `0`,
-- and Toeplitz seeds from `(ZMod 2) ^ 3` to `(ZMod 2) ^ 2` have `6` bits.
example :
    (∃ a : Fin (2 + 3 - 1) → ZMod 2, toeplitz a *ᵥ ![0, 1, 0] = ![1, 0]) ∧
    (¬ Function.Surjective fun a : Fin (2 + 3 - 1) → ZMod 2 =>
      toeplitz a *ᵥ (0 : Fin 3 → ZMod 2)) ∧
    Fintype.card ((Fin (2 + 3 - 1) → ZMod 2) × (Fin 2 → ZMod 2)) = 2 ^ 6 :=
  ⟨toeplitz_mulVec_surjective (by decide) ![1, 0],
    fun h => by
      obtain ⟨a, ha⟩ := h ![1, 0]
      simp only [mulVec_zero] at ha
      exact absurd ha (by decide),
    by rw [card_toeplitzHash_seed, ZMod.card]⟩

end Toeplitz

/-! ### The shift criteria for pairwise independence -/

section Shift

open Cslib.Probability

-- Multiplying by a uniform key spreads every nonzero difference uniformly over `ZMod 3`.
example : IsPairwiseIndependentHash fun (p : ZMod 3 × ZMod 3) (x : ZMod 3) => p.1 * x + p.2 := by
  refine isPairwiseIndependentHash_add_of_dens_filter_sub_eq (fun k x => k * x) ?_
  have h : ∀ x₁ x₂ c : ZMod 3, x₁ ≠ x₂ → #{k : ZMod 3 | k * x₁ - k * x₂ = c} = 1 := by decide
  intro x₁ x₂ hx c
  rw [dens_eq_card_div_card, h x₁ x₂ c hx]
  simp [ZMod.card]

/-- The key enters `k * x + k ^ 2` non-additively, but translating it shifts the difference. -/
private theorem hash_sq : IsPairwiseIndependentHash
    fun (p : ZMod 3 × ZMod 3) (x : ZMod 3) => p.1 * x + p.1 ^ 2 + p.2 :=
  isPairwiseIndependentHash_add_of_shift (fun k x => k * x + k ^ 2) fun x₁ x₂ hx c => by
    have : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
    refine ⟨Equiv.addRight (c / (x₁ - x₂)), fun k => ?_⟩
    simp only [Equiv.coe_addRight]
    field_simp
    ring

-- So its values at `0` and `1` are independent and uniform.
example : dens {p : ZMod 3 × ZMod 3 |
    p.1 * 0 + p.1 ^ 2 + p.2 = 1 ∧ p.1 * 1 + p.1 ^ 2 + p.2 = 2} = 1 / 9 := by
  rw [hash_sq.dens_filter_apply_eq_and_apply_eq (by decide)]
  norm_num [ZMod.card]

end Shift

/-! ### Entropy -/

section Entropy

open Cslib.Probability Cslib.Probability.PMF

private theorem logb_two_four : Real.logb 2 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one] <;> norm_num

-- Exposing the parity and then the first bit of a uniform two-bit word accounts for both bits.
example : entropy ((PMF.uniformOfFintype (Bool × Bool)).map fun w => xor w.1 w.2) +
    conditionalEntropy ((PMF.uniformOfFintype (Bool × Bool)).map
      fun w => (xor w.1 w.2, w.1)) +
    conditionalEntropy ((PMF.uniformOfFintype (Bool × Bool)).map
      fun w => ((xor w.1 w.2, w.1), w)) = 2 := by
  rw [entropy_chain_rule_deterministic, entropy_uniform]
  simp [logb_two_four]

/-- Two independent uniform bits. -/
private noncomputable def twoBits : PMF (Bool × Bool) :=
  (PMF.uniformOfFintype Bool).bind fun a => (PMF.uniformOfFintype Bool).map (a, ·)

-- The second bit keeps one bit of entropy given the first, on average over the first.
example : ∑ a, ((twoBits.map Prod.fst) a).toReal * entropy (conditionalSnd twoBits a) = 1 := by
  rw [← conditionalEntropy_eq_sum, twoBits, conditionalEntropy_bind_pair]
  simp [PMF.uniformOfFintype_apply]

end Entropy

/-! ### Leftover hashing -/

section LeftoverHash

open Cslib.Probability Cslib.Probability.PMF Cslib.BitString

-- Hashing two uniform bits to one with a uniform `1 × 2` Boolean matrix, given a public side
-- bit, comes within `√(1 / 2) / 2 < 1 / 2` of a uniform bit.
example : dist
    ((PMF.uniformOfFintype Bool).bind fun info =>
      (seededHash (PMF.uniformOfFintype (Fin 1 → BitString 2))
        (PMF.uniformOfFintype (BitString 2)) LinearHash.hash).map (info, ·))
    ((PMF.uniformOfFintype Bool).bind fun info =>
      ((PMF.uniformOfFintype (Fin 1 → BitString 2)).bind
        fun s => (PMF.uniformOfFintype (BitString 1)).map (s, ·)).map (info, ·)) < 1 / 2 := by
  refine (((LinearHash.isTwoUniversal 2 1).leftover_hash_conditional _ fun _ => _).trans
    (le_of_eq ?_)).trans_lt (b := √(1 / 2) / 2) ?_
  · congr 2
    simp only [Fintype.card_pi, univ_unique, Fin.default_eq_zero, Fin.isValue, Fintype.card_bool,
        prod_const, card_singleton, pow_one, Nat.cast_ofNat, Fintype.univ_bool,
        uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
        collisionProbability_uniform, card_univ, Fintype.card_fin, Nat.reducePow, sum_const,
        mem_singleton, Bool.true_eq_false, not_false_eq_true, card_insert_of_notMem, Nat.reduceAdd,
        nsmul_eq_mul, ne_eq, OfNat.ofNat_ne_zero, mul_inv_cancel_left₀, one_div]
    norm_num
  · have : √(1 / 2 : ℝ) < 1 := (Real.sqrt_lt' one_pos).2 (by norm_num)
    linarith

-- A uniform three-bit source has no outcome heavier than `1 / 8`, so smoothing costs nothing.
example : dist (seededHash (PMF.uniformOfFintype (Fin 1 → BitString 3))
      (PMF.uniformOfFintype (BitString 3)) LinearHash.hash)
    ((PMF.uniformOfFintype (Fin 1 → BitString 3)).bind
      fun s => (PMF.uniformOfFintype (BitString 1)).map (s, ·)) < 1 / 2 := by
  refine ((LinearHash.isTwoUniversal 3 1).leftover_hash_of_heavy_probability _
    (mass := 1 / 8) (by norm_num)).trans_lt ?_
  have hheavy : {x : BitString 3 |
      (1 / 8 : ℝ) < (PMF.uniformOfFintype (BitString 3) x).toReal} = ∅ := by
    ext x
    simp [PMF.uniformOfFintype_apply]
  have hs : √((Fintype.card (BitString 1) : ℝ) * (2 * (1 / 8))) = √(1 / 2) := by
    congr 1
    simp only [Fintype.card_pi, univ_unique, Fin.default_eq_zero, Fin.isValue, Fintype.card_bool,
        prod_const, card_singleton, pow_one, Nat.cast_ofNat, one_div]
    norm_num
  have : √(1 / 2 : ℝ) < 1 := (Real.sqrt_lt' one_pos).2 (by norm_num)
  rw [hheavy, hs, MeasureTheory.measure_empty, ENNReal.toReal_zero, mul_zero, zero_add]
  linarith

end LeftoverHash

/-! ### Approximate counting with relative error -/

section ApproximateCounting

open Cslib.Probability Cslib.Probability.ApproximateCounting

/-- Toeplitz hashing of `7`-tuples of bits to `j` bits. -/
private def toeplitzLevel (j : ℕ) :
    (Fin (j + 7 - 1) → ZMod 2) × (Fin j → ZMod 2) → (Fin 7 → ZMod 2) → Fin j → ZMod 2 :=
  toeplitzHash

-- Toeplitz families satisfy the hypotheses of relative-error counting: with `7` copies and
-- `t = 2`, the estimate of `#(ZMod 2) = 2` lies in `[2, 4]` with probability at least `3 / 4`.
example : 3 / 4 ≤ dens {ω : ∀ j : Fin (7 + 1), Fin (2 * (6 * (7 + 1 + 2))) →
      (Fin (j + 7 - 1) → ZMod 2) × (Fin j → ZMod 2) |
    #(univ : Finset (ZMod 2)) ≤ relativeHashEstimate toeplitzLevel (fun _ => 0) univ ω ∧
      1 * relativeHashEstimate toeplitzLevel (fun _ => 0) univ ω ≤
        (1 + 1) * #(univ : Finset (ZMod 2))} := by
  refine le_of_eq_of_le (tsub_eq_of_eq_add (by norm_num)).symm
    (one_sub_inv_two_pow_le_dens_filter_relativeHashEstimate
    (n := 7) (k := 7) (p := 1) toeplitzLevel _ univ
    (fun _ => isPairwiseIndependentHash_toeplitzHash) (fun _ => by simp [ZMod.card])
    (by simp [ZMod.card]) (by norm_num) 2)

-- The affine version needs only `p ≠ 0`; here for two vectors in `(ZMod 2) ^ 2` and `p = 1`.
example : 3 / 4 ≤ dens {ω : ∀ j : Fin (7 * 1 * 2 + 1),
      Fin (2 * (6 * (7 * 1 * 2 + 1 + 2))) →
        Matrix (Fin j) (Fin (7 * 1) × Fin 2) (ZMod 2) × (Fin j → ZMod 2) |
    #({0, 1} : Finset (Fin 2 → ZMod 2)) ≤ relativeHashEstimate
        (fun _ A x => affineHash A (Function.uncurry x)) (fun _ => 0) {0, 1} ω ∧
      1 * relativeHashEstimate (fun _ A x => affineHash A (Function.uncurry x)) (fun _ => 0)
        {0, 1} ω ≤ (1 + 1) * #({0, 1} : Finset (Fin 2 → ZMod 2))} :=
  le_of_eq_of_le (tsub_eq_of_eq_add (by norm_num)).symm
    (one_sub_inv_two_pow_le_dens_filter_affineRelativeHashEstimate one_ne_zero 2 _)

end ApproximateCounting

end ComplexityTests.FoundationsExamples
