/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.PMF.Event
import Complexity.Computability.Communication.Corruption
import Complexity.Computability.Communication.Distributional
import Complexity.Computability.Communication.Functions
import Complexity.Probability.Minimax
import Complexity.Probability.PMF

/-!
Regression clients for distributional complexity and Yao's minimax principle, for the averaging
and minimax lemmas on finite distributions behind them, for the corruption bound, and for the
consolidated protocol API.
-/

open Cslib Cslib.Communication Finset

namespace CommunicationComplexity3Tests

/-! ### Averaging and minimax on finite distributions -/

/-- Matching pennies: guessing the input `j` costs one. Against every distribution on the inputs
some guess has expected cost at most one half. -/
private theorem pennies (ν : PMF Bool) :
    ∃ i, ∑ j, (ν j).toReal * (if i = j then 1 else 0 : ℝ) ≤ 1 / 2 := by
  have h := Probability.PMF.sum_toReal ν
  simp only [Fintype.sum_bool] at h
  by_cases hν : (ν true).toReal ≤ 1 / 2
  · exact ⟨true, by simpa using hν⟩
  · exact ⟨false, by simp only [Fintype.sum_bool]; norm_num; linarith⟩

-- Distributions on a finite type are points of the standard simplex.
example (μ : PMF Bool) : Probability.PMF.ofStdSimplex (Probability.PMF.toStdSimplex μ) = μ := by
  simp

-- So some mixed guess has probability at most `1 / 2` on both outcomes (hence is a fair coin).
example : ∃ μ : PMF Bool, (μ true).toReal = 1 / 2 := by
  obtain ⟨μ, hμ⟩ := Probability.PMF.exists_forall_sum_mul_le _ pennies
  have ht := hμ true
  have hf := hμ false
  have hsum := Probability.PMF.sum_toReal μ
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, mul_one,
    mul_zero, add_zero, zero_add] at ht hf hsum
  exact ⟨μ, by linarith⟩

-- The failure form allows infinitely many strategies: here, guesses indexed by `ℕ` that only look
-- at their parity.
example : ∃ μ : PMF ℕ, μ.support.Finite ∧
    ∀ j : Bool, (μ.toOuterMeasure {i | decide (i % 2 = 0) = j}).toReal ≤ 1 / 2 := by
  refine Probability.PMF.exists_forall_toOuterMeasure_le _ fun ν => ?_
  have h := Probability.PMF.toOuterMeasure_toReal_add_compl ν {true}
  by_cases hν : (ν.toOuterMeasure {true}).toReal ≤ 1 / 2
  · exact ⟨0, by simpa using hν⟩
  · refine ⟨1, ?_⟩
    have : ({j | decide (1 % 2 = 0) = j} : Set Bool) = {true}ᶜ := by
      ext j
      cases j <;> simp
    rw [this]
    linarith

/-! ### Distributional complexity -/

-- Under a point mass, computing `f` needs no communication: output the value at that point.
example {X Y : Type*} (f : X → Y → Bool) (x : X) (y : Y) :
    Protocol.distributionalComplexity 0 (fun x y b => f x y = b) (PMF.pure (x, y)) = 0 := by
  refine le_antisymm ?_ bot_le
  refine (Protocol.distributionalComplexity_le_depth (p := .output (f x y)) ?_).trans_eq rfl
  simp [Protocol.distributionalError, PMF.toOuterMeasure_pure_apply]

/-- Under every distribution, one of the two constant protocols errs with probability at most one
half. -/
private theorem distributionalComplexity_half {X Y : Type*} (f : X → Y → Bool)
    (ν : PMF (X × Y)) :
    Protocol.distributionalComplexity (1 / 2) (fun x y b => f x y = b) ν ≤ (0 : ℕ) := by
  rw [Protocol.distributionalComplexity_le_iff]
  have h := Probability.PMF.toOuterMeasure_toReal_add_compl ν {q | f q.1 q.2 = true}
  by_cases hν : (ν.toOuterMeasure {q | f q.1 q.2 = true}).toReal ≤ 1 / 2
  · refine ⟨.output false, ?_, le_rfl⟩
    simpa [Protocol.distributionalError] using hν
  · refine ⟨.output true, ?_, le_rfl⟩
    have : {q : X × Y | ¬f q.1 q.2 = (Protocol.output true : Protocol X Y Bool).run q.1 q.2} =
        {q | f q.1 q.2 = true}ᶜ := by
      ext q
      simp
    rw [Protocol.distributionalError, this]
    linarith

-- Yao's principle, hard direction: so with error one half every Boolean function on finite inputs
-- needs no communication with public coins. The minimax theorem finds the coin flip.
example {X Y : Type*} [Finite X] [Finite Y] (f : X → Y → Bool) :
    PublicCoin.ecomplexityFun (1 / 2) f = 0 := by
  refine le_antisymm ?_ bot_le
  exact_mod_cast PublicCoin.ecomplexity_le_of_forall_distributionalComplexity_le (c := 0)
    fun ν _ => distributionalComplexity_half f ν

-- By Yao's minimax principle, the trivial deterministic upper bound `n + 1` bounds the supremum of
-- the error-`ε` distributional complexity over all input distributions on `BitString 3`.
example {ε : ℝ} (hε : 0 ≤ ε) (f : BitString 3 → BitString 3 → Bool) :
    (⨆ ν : PMF (BitString 3 × BitString 3),
      Protocol.distributionalComplexity ε (fun x y b => f x y = b) ν) ≤ 4 := by
  rw [← PublicCoin.ecomplexityFun_eq_iSup_distributionalComplexity]
  exact (PublicCoin.ecomplexityFun_le_privateCoin.trans
    (PrivateCoin.ecomplexityFun_le_protocol hε)).trans (Protocol.ecomplexityFun_le_succ f)

/-! ### The corruption bound -/

/-- Equality on `Fin N` under the uniform distribution is `(1, 1 / N ^ 2)`-corrupted on `true`:
a rectangle `A × B` contains `|A ∩ B|` pairs on the diagonal and `|A| |B| - |A ∩ B|` off it, and
`2 |A ∩ B| ≤ |A| |B| + 1`. -/
private theorem corrupted_equality (N : ℕ) [NeZero N] :
    Corrupted (Probability.PMF.uniformOfFintype (Fin N × Fin N))
      (equality : Fin N → Fin N → Bool) true 1 (1 / N ^ 2) := by
  intro A B
  set c : ℝ := 1 / N ^ 2
  have hc (q : Fin N × Fin N) :
      (Probability.PMF.uniformOfFintype (Fin N × Fin N) q).toReal = c := by
    simp [Probability.PMF.uniformOfFintype_apply, c, Fintype.card_prod, sq]
  have hdiag : ∑ x ∈ A, ∑ y ∈ B, (if equality x y = true then c else 0) = c * #(A ∩ B) := by
    simp only [equality, decide_eq_true_eq, sum_ite_eq, ← sum_filter, sum_const, nsmul_eq_mul]
    rw [mul_comm, filter_mem_eq_inter]
  have hoff : ∑ x ∈ A, ∑ y ∈ B, (if equality x y = true then 0 else c) =
      c * (#A * #B) - c * #(A ∩ B) := by
    rw [← hdiag]
    have h (x y : Fin N) : (if equality x y = true then 0 else c) =
        c - if equality x y = true then c else 0 := by
      split_ifs <;> simp
    simp only [h, sum_sub_distrib, sum_const, nsmul_eq_mul]
    ring
  simp only [hc]
  rw [hdiag, hoff, one_mul]
  have hk₁ : (#(A ∩ B) : ℝ) ≤ #A := by exact_mod_cast card_le_card inter_subset_left
  have hk₂ : (#(A ∩ B) : ℝ) ≤ #B := by exact_mod_cast card_le_card inter_subset_right
  have hc0 : 0 ≤ c := by positivity
  have hk : 2 * (#(A ∩ B) : ℝ) ≤ #A * #B + 1 := by
    nlinarith [sq_nonneg ((#(A ∩ B) : ℝ) - 1), mul_le_mul hk₁ hk₂ (Nat.cast_nonneg _)
      (Nat.cast_nonneg _)]
  nlinarith

-- With zero error, the corruption bound gives back `N ≤ 2 ^ c` for equality on `Fin N`, with
-- public coins.
example (N c : ℕ) [NeZero N]
    (hc : PublicCoin.ecomplexityFun 0 (equality : Fin N → Fin N → Bool) ≤ c) :
    (N : ℝ) ≤ 2 ^ c := by
  have h := (corrupted_equality N).mul_sub_le_of_ecomplexityFun_le zero_le_one hc
  have hz : ((Probability.PMF.uniformOfFintype (Fin N × Fin N)).toOuterMeasure
      {q | equality q.1 q.2 = true}).toReal = 1 / N := by
    rw [Probability.PMF.toOuterMeasure_apply_toReal, Fintype.sum_prod_type]
    simp only [equality, decide_eq_true_eq, Set.mem_ofPred_eq,
      Probability.PMF.uniformOfFintype_apply, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_inv_rev, sum_ite_eq,
      mem_univ, ↓reduceIte, sum_const, card_univ, nsmul_eq_mul, one_div]
    field_simp
  rw [hz] at h
  have hN : (0 : ℝ) < N := by
    have := NeZero.pos N
    positivity
  field_simp at h
  nlinarith

/-! ### The consolidated protocol API -/

-- Leaves, their labels and their rectangles by simp.
example : (Protocol.alice id (.output 0) (.output 1) : Protocol Bool Unit ℕ).leafOutput
    ((Protocol.alice id (.output 0) (.output 1) : Protocol Bool Unit ℕ).leaf true ()) = 1 := by
  simp only [Protocol.leaf_alice, id, Bool.cond_true, Protocol.leafOutput_alice_natAdd,
    Protocol.leafOutput_output]

example (send : Bool → Bool) (p₀ p₁ : Protocol Bool Unit ℕ) (i : Fin p₁.leafCount) :
    (Protocol.alice send p₀ p₁).leafAlice (Fin.natAdd p₀.leafCount i) ×ˢ
        (Protocol.alice send p₀ p₁).leafBob (Fin.natAdd p₀.leafCount i) =
      ({x | send x = true} ∩ p₁.leafAlice i) ×ˢ p₁.leafBob i := by
  simp

-- Because the leaf rectangles of `p` partition `Fin 3 × Fin 2`, any protocol with at most 2 leaves
-- has a leaf rectangle containing at least 3 of the 6 input pairs.
open Classical in
example (p : Protocol (Fin 3) (Fin 2) Bool) (hl : p.leafCount ≤ 2) :
    ∃ i, 3 ≤ #{x | x ∈ p.leafAlice i} * #{y | y ∈ p.leafBob i} := by
  by_contra! h
  have hsum := p.sum_eq_sum_leaves (fun _ _ => (1 : ℕ))
  simp only [sum_const, smul_eq_mul, mul_one, card_univ, Fintype.card_fin] at hsum
  have hle : ∑ i : Fin p.leafCount, #{x | x ∈ p.leafAlice i} * #{y | y ∈ p.leafBob i} ≤
      p.leafCount * 2 := by
    simpa using sum_le_card_nsmul univ
      (fun i => #{x | x ∈ p.leafAlice i} * #{y | y ∈ p.leafBob i}) 2 fun i _ =>
        Nat.le_of_lt_succ (h i)
  omega

-- The area bound: rectangles on which equality is `true` have one entry, so a protocol computing
-- equality on three elements has at least three leaves labelled `true`.
example (p : Protocol (Fin 3) (Fin 3) Bool) (hp : p.run = equality) :
    3 ≤ #{i | p.leafOutput i = true} := by
  have h := Protocol.card_filter_le_mul hp true (K := 1) fun A B h => by
    rcases A.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    have hB : B ⊆ {x} := fun y hy => by simpa [equality, eq_comm] using h x hx y hy
    rcases B.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
    · simp
    have hA : A ⊆ {y} := fun x' hx' => by simpa [equality] using h x' hx' y hy
    calc #A * #B ≤ 1 * 1 := Nat.mul_le_mul ((card_le_card hA).trans_eq (card_singleton y))
          ((card_le_card hB).trans_eq (card_singleton x))
      _ = 1 := rfl
  have h3 : #{q : Fin 3 × Fin 3 | equality q.1 q.2 = true} = 3 := by decide
  omega

end CommunicationComplexity3Tests
