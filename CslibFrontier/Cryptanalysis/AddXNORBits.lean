/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORChain
public import CslibFrontier.Cryptanalysis.AddXNORRuns
public import Mathlib.Data.FinEnum
import Mathlib.Tactic.Ring

/-!
# Arbitrary-bit Add/XNOR correlations

The run factorization in [WangLvShenZhang2027], Theorem 5(i), PDF p. 17.
All operands are independent uniform full-width words, and every operation is
an actual `BitVec` operation. The comparison is the affine model of the chain.
The proof derives the reset at each XNOR by a permutation of its fresh operand;
independence of runs is not supplied as a hypothesis. This module does not
assert the spectral formula or quantitative decay claims of Theorem 5(ii–iv).
-/

public section

open scoped BigOperators

namespace Cslib.Cryptanalysis.AddXNOR

/-- Signed error at any bit, relative to an independently tracked affine word. -/
@[expose] def bitFrom {m : ℕ} (j : ℕ) : List Bool → BitVec m → BitVec m → ℚ
  | [], s, ell => sign ((s ^^^ ell).getLsbD j)
  | b :: bs, s, ell => 𝔼 a : BitVec m,
      bitFrom j bs (step b s a) (if b then ~~~(ell ^^^ a) else ell ^^^ a)

/-- Signed bit correlation with the XOR-of-operands/operator-parity model. -/
@[expose] def bitCorrelation (m j : ℕ) (bs : List Bool) : ℚ :=
  𝔼 s : BitVec m, bitFrom j bs s s

/-- Backward transfer on a function of the actual running state. -/
@[expose] def bitTransfer {m : ℕ} (j : ℕ) (b : Bool) (f : BitVec m → ℚ)
    (s : BitVec m) : ℚ :=
  𝔼 a : BitVec m, (if b then 1 else sign ((carryWord s a).getLsbD j)) *
    f (step b s a)

/-- Coefficients of the signed carry process for a fixed operator string. -/
@[expose] def bitCoefficients {m : ℕ} (j : ℕ) : List Bool → BitVec m → ℚ
  | [] => fun _ => 1
  | b :: bs => bitTransfer j b (bitCoefficients j bs)

private theorem sign_xor (a b : Bool) : sign (a ^^ b) = sign a * sign b := by
  cases a <;> cases b <;> norm_num [sign]

/-- The transfer process equals the actual word experiment, state by state. -/
theorem bitFrom_coefficients {m : ℕ} (j : ℕ) (bs : List Bool) (s ell : BitVec m) :
    bitFrom j bs s ell = sign ((s ^^^ ell).getLsbD j) * bitCoefficients j bs s := by
  induction bs generalizing s ell with
  | nil => simp [bitFrom, bitCoefficients]
  | cons b bs ih =>
    simp only [bitFrom, ih, bitCoefficients, bitTransfer, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro a _
    have he : (step b s a ^^^ (if b then ~~~(ell ^^^ a) else ell ^^^ a)).getLsbD j =
        ((s ^^^ ell).getLsbD j ^^ (if b then false else (carryWord s a).getLsbD j)) := by
      cases b with
      | false =>
        simp only [step, Bool.false_eq_true, ↓reduceIte, carryWord, BitVec.getLsbD_xor]
        cases s.getLsbD j <;> cases ell.getLsbD j <;>
          cases a.getLsbD j <;> cases (s + a).getLsbD j <;> rfl
      | true =>
        by_cases hj : j < m
        · simp only [step, ↓reduceIte, BitVec.getLsbD_xor, BitVec.getLsbD_not,
            hj, decide_true, Bool.true_and]
          cases s.getLsbD j <;> cases ell.getLsbD j <;> cases a.getLsbD j <;> rfl
        · simp [BitVec.getLsbD_of_ge, Nat.le_of_not_gt hj]
    rw [he, sign_xor]
    cases b <;> simp [sign]

/-- Exact correlation is the uniform average of the carry coefficients. -/
theorem bitCorrelation_coefficients (m j : ℕ) (bs : List Bool) :
    bitCorrelation m j bs = 𝔼 s : BitVec m, bitCoefficients j bs s := by
  simp [bitCorrelation, bitFrom_coefficients, sign]

private theorem operand_xnor_bijective {m : ℕ} (s : BitVec m) :
    Function.Bijective (step true s) := by
  have hc (a : BitVec m) : step true s a = step true a s := by
    simp only [step, ↓reduceIte, BitVec.xor_comm]
  have he : (fun a => eval [(true, s)] a) = step true s := by
    funext a
    simp only [eval, hc a]
  rw [← he]
  exact eval_bijective [(true, s)]

/-- A fresh uniform XNOR operand resets the running state exactly. -/
theorem bitTransfer_xnor {m : ℕ} (j : ℕ) (f : BitVec m → ℚ) (s : BitVec m) :
    bitTransfer j true f s = 𝔼 t : BitVec m, f t := by
  simp only [bitTransfer, ↓reduceIte, one_mul]
  exact Fintype.expect_bijective _ (operand_xnor_bijective s) _ _ (fun _ => rfl)

private theorem bitTransfer_scale {m : ℕ} (j : ℕ) (b : Bool) (c : ℚ)
    (f : BitVec m → ℚ) :
    bitTransfer j b (fun s => c * f s) = fun s => c * bitTransfer j b f s := by
  funext s
  simp only [bitTransfer, Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro a _
  ring

private theorem bitCoefficients_append {m : ℕ} (j : ℕ) (xs ys : List Bool) :
    @bitCoefficients m j (xs ++ ys) = xs.foldr (bitTransfer j) (bitCoefficients j ys) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.cons_append, bitCoefficients, ih, List.foldr_cons]

private theorem bitCoefficients_scale {m : ℕ} (j : ℕ) (xs : List Bool)
    (c : ℚ) (f : BitVec m → ℚ) :
    xs.foldr (bitTransfer j) (fun s => c * f s) =
      fun s => c * xs.foldr (bitTransfer j) f s := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.foldr_cons, ih, bitTransfer_scale]

/-- Correlation of one addition run, with a uniform initial word. -/
@[expose] def bitRunFactor (m j z : ℕ) : ℚ :=
  bitCorrelation m j (List.replicate z false)

/-- Theorem 5(i): arbitrary-bit correlation factors over all addition runs.
The result also covers bit zero, out-of-width bits, zero runs and width zero. -/
theorem bitCorrelation_runs (m j : ℕ) (zs : List ℕ) :
    bitCorrelation m j (runs zs) = (zs.map (bitRunFactor m j)).prod := by
  induction zs with
  | nil => simp [runs, bitCorrelation, bitFrom, sign]
  | cons z zs ih =>
    rw [bitCorrelation_coefficients] at ih ⊢
    simp only [runs, bitCoefficients_append, bitCoefficients]
    rw [show bitTransfer j true (bitCoefficients j (runs zs)) =
        (fun _ : BitVec m => (zs.map (bitRunFactor m j)).prod * 1) by
          funext s
          simp [bitTransfer_xnor, ih]]
    rw [bitCoefficients_scale]
    simp only [List.map_cons, List.prod_cons, ← Finset.mul_expect]
    rw [mul_comm]
    congr 1
    rw [bitRunFactor, bitCorrelation_coefficients]
    have hc := bitCoefficients_append (m := m) j (List.replicate z false) []
    simpa only [List.append_nil, bitCoefficients] using
      congrArg (fun f => 𝔼 s, f s) hc.symm

/-- Appending a fresh XNOR does not change arbitrary-bit correlation. -/
theorem bitCorrelation_append_xnor (m j : ℕ) (bs : List Bool) :
    bitCorrelation m j (bs ++ [true]) = bitCorrelation m j bs := by
  have hc : @bitCoefficients m j [true] = bitCoefficients j [] := by
    funext s
    simp [bitCoefficients, bitTransfer_xnor]
  simp only [bitCorrelation_coefficients, bitCoefficients_append, hc]
  rw [← bitCoefficients_append, List.append_nil]

/-- Every fixed operator string has the arbitrary-bit product formula. -/
theorem bitCorrelation_run_product (m j : ℕ) (bs : List Bool) :
    ∃ zs, runs zs = bs ++ [true] ∧
      bitCorrelation m j bs = (zs.map (bitRunFactor m j)).prod := by
  obtain ⟨zs, hz⟩ := exists_runs bs
  refine ⟨zs, hz, ?_⟩
  rw [← bitCorrelation_append_xnor, ← hz, bitCorrelation_runs]

private theorem expect_word (h : ℕ) (f : BitVec (h + 2) → ℚ) :
    (𝔼 s, f s) = 𝔼 hi : Fin (2 ^ h), 𝔼 lo : Fin 4, f (word hi lo) := by
  rw [← Fintype.expect_bijective _ (word_bijective h)
    (fun p => f (word p.1 p.2)) f (fun _ => rfl)]
  exact Finset.expect_product _ _ _

/-- Agreement with the existing bit-one experiment, including its exact uniform sampler. -/
theorem bitFrom_bit_one (h : ℕ) (bs : List Bool) (s ell : BitVec (h + 2)) :
    bitFrom 1 bs s ell = fixedFrom h bs s (ell.getLsbD 1) := by
  induction bs generalizing s ell with
  | nil => simp [bitFrom, fixedFrom]
  | cons b bs ih =>
    simp only [bitFrom, ih, expect_word, fixedFrom]
    apply Finset.expect_congr rfl
    intro hi _
    apply Finset.expect_congr rfl
    intro lo _
    congr 1
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_xor,
      BitVec.getLsbD_not, show 1 < h + 2 by omega, decide_true, Bool.true_and]
    all_goals cases ell.getLsbD 1 <;> cases (word hi lo).getLsbD 1 <;> rfl

/-- The new all-bit API preserves the previously proved bit-one correlation. -/
theorem bitCorrelation_bit_one (h : ℕ) (bs : List Bool) :
    bitCorrelation (h + 2) 1 bs = fixedCorrelation h bs := by
  simp only [bitCorrelation, bitFrom_bit_one, expect_word, fixedCorrelation]

/-- The arbitrary-bit run factor specializes to the established cosine factor. -/
theorem bitRunFactor_bit_one (h z : ℕ) : bitRunFactor (h + 2) 1 z = runFactor z := by
  rw [bitRunFactor, bitCorrelation_bit_one, ← fixedCorrelation_append_xnor]
  have he := fixedCorrelation_runs h [z]
  simpa only [runs, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one] using he

end Cslib.Cryptanalysis.AddXNOR
