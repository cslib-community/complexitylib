/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.BitVec
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Average signed correlation of Add/XNOR chains

[WangLvShenZhang2027], Theorem 4, PDF p. 16, with the chain model on pp. 6–7
and the bit-1 affine approximation on pp. 14–15. A word has width h + 2; the h
high bits and two low bits are sampled independently and uniformly. `word`
is a bijection from this sampling space to all words, so this is the actual
uniform word ensemble. Every step independently samples an operator and a
fresh operand. `averageFrom` evaluates the actual modular addition or XNOR
on full-width words, tracking the affine approximation in parallel. Its terminal
statistic is +1 for agreement of bit 1 and -1 for disagreement.

There are k operators and k + 1 operands. The source's N is therefore k + 1.
No absolute-correlation, planted-instance, search-complexity or hardness result
is asserted.

## Main definitions

* `step`, `word`: full-width modular addition/XNOR and the uniform word sampler.
* `averageFrom`, `averageCorrelation`: signed bit-1 agreement averaged over the chain ensemble.

## Main results

* `word_bijective`, `step_low`: faithful sampling and projection to the low two bits.
* `averageCorrelation_source`: the exact signed correlation in the paper's parameters.

## References

* [Wang et al., *Add/XNOR Chains*][WangLvShenZhang2027], Theorem 4, PDF p. 16.
-/

public section

open scoped BigOperators

namespace Cslib.Cryptanalysis.AddXNOR

variable {m h : ℕ}

/-- A modular addition (false) or bitwise XNOR (true). -/
@[expose] def step (b : Bool) (s a : BitVec m) : BitVec m :=
  if b then ~~~(s ^^^ a) else s + a

/-- The uniform word sampler, with h high bits and two low bits. -/
@[expose] def word (hi : Fin (2 ^ h)) (lo : Fin 4) : BitVec (h + 2) :=
  BitVec.ofNat (h + 2) (hi.val * 4 + lo.val)

/-- Exact range, so the word sampler never wraps. -/
theorem word_toNat (hi : Fin (2 ^ h)) (lo : Fin 4) :
    (word hi lo).toNat = hi.val * 4 + lo.val := by
  have hh := hi.isLt
  have hl := lo.isLt
  have hp : 2 ^ (h + 2) = 2 ^ h * 4 := by simp [pow_add]
  simp only [word, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  rw [hp]
  omega

/-- Every word has exactly one sampler preimage. This justifies uniformity. -/
theorem word_bijective (h : ℕ) : Function.Bijective
    (fun p : Fin (2 ^ h) × Fin 4 => word p.1 p.2) := by
  constructor
  · rintro ⟨hi, lo⟩ ⟨hi', lo'⟩ heq
    have he := congrArg BitVec.toNat heq
    rw [word_toNat, word_toNat] at he
    change hi.val * 4 + lo.val = hi'.val * 4 + lo'.val at he
    have hl := lo.isLt
    have hl' := lo'.isLt
    have heh : hi = hi' := Fin.ext (by omega)
    have hel : lo = lo' := Fin.ext (by omega)
    exact Prod.ext heh hel
  · intro w
    have hw := w.isLt
    have hp : 2 ^ (h + 2) = 2 ^ h * 4 := by simp [pow_add]
    rw [hp] at hw
    refine ⟨(⟨w.toNat / 4, by omega⟩, ⟨w.toNat % 4, by omega⟩), ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [word_toNat]
    simpa only [Nat.mul_comm] using Nat.div_add_mod w.toNat 4

/-- The sampled low two bits are exactly lo, regardless of all high bits. -/
theorem word_low (hi : Fin (2 ^ h)) (lo : Fin 4) :
    (word hi lo).setWidth 2 = BitVec.ofNat 2 lo.val := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, word_toNat]
  simp [Nat.add_mod, Nat.mod_eq_of_lt lo.isLt]

/-- Full-width operations commute with projection to the low two bits. -/
theorem step_low (b : Bool) (s a : BitVec (h + 2)) :
    (step b s a).setWidth 2 = step b (s.setWidth 2) (a.setWidth 2) := by
  cases b <;> simp [step, BitVec.setWidth_add, BitVec.setWidth_not, show 2 ≤ h + 2 by omega]

/-- Signed agreement statistic. -/
@[expose] def sign (b : Bool) : ℚ := if b then -1 else 1

/-- Exact expected signed agreement after k further actual word operations.
The affine bit is updated with operand bit 1 and the XNOR indicator. -/
@[expose] def averageFrom (h : ℕ) : ℕ → BitVec (h + 2) → Bool → ℚ
  | 0, s, ell => sign (s.getLsbD 1 ^^ ell)
  | k + 1, s, ell =>
    𝔼 hi : Fin (2 ^ h), 𝔼 lo : Fin 4,
      (averageFrom h k (step false s (word hi lo))
          (ell ^^ (word hi lo).getLsbD 1 ^^ false) +
       averageFrom h k (step true s (word hi lo))
          (ell ^^ (word hi lo).getLsbD 1 ^^ true)) / 2

/-- Average correlation of a chain with k operators (N=k + 1 operands). -/
@[expose] def averageCorrelation (h k : ℕ) : ℚ :=
  𝔼 hi : Fin (2 ^ h), 𝔼 lo : Fin 4,
    averageFrom h k (word hi lo) ((word hi lo).getLsbD 1)

private def closed (k : ℕ) (s : BitVec 2) (ell : Bool) : ℚ :=
  sign (s.getLsbD 1 ^^ ell) *
    (if s.getLsbD 0 then 1 else (k:ℚ) + 1) / 2 ^ k

private theorem closed_step (k : ℕ) : ∀ (s : BitVec 2) (ell : Bool),
    Finset.expect Finset.univ (fun lo : Fin 4 =>
      (closed k (step false s (BitVec.ofNat 2 lo.val))
          (ell ^^ (BitVec.ofNat 2 lo.val).getLsbD 1 ^^ false) +
       closed k (step true s (BitVec.ofNat 2 lo.val))
          (ell ^^ (BitVec.ofNat 2 lo.val).getLsbD 1 ^^ true)) / 2)
      = closed (k + 1) s ell := by
  intro s ell
  rcases s with ⟨s⟩
  fin_cases s <;> cases ell <;>
    norm_num [Finset.expect_eq_sum_div_card, Fin.sum_univ_succ, closed, step, sign, BitVec.getLsbD,
      BitVec.add_def, BitVec.not_def, Nat.testBit, pow_succ] <;> ring

private theorem bit1_low (s : BitVec (h + 2)) :
    (s.setWidth 2).getLsbD 1 = s.getLsbD 1 := by simp

private theorem averageFrom_closed (h k : ℕ) (s : BitVec (h + 2)) (ell : Bool) :
    averageFrom h k s ell = closed k (s.setWidth 2) ell := by
  induction k generalizing s ell with
  | zero => simp [averageFrom, closed]
  | succ k ih =>
    simp only [averageFrom, ih, step_low, word_low, ← bit1_low (word _ _), word_low]
    simp only [closed_step]
    exact Finset.expect_const Finset.univ_nonempty _

/-- Theorem 4: N=k + 1, m=h + 2. All full-width operations are evaluated before
projection. This holds even for k=0 (the source states N≥2). -/
theorem averageCorrelation_eq (h k : ℕ) :
    averageCorrelation h k = ((k:ℚ) + 2) / 2 ^ (k + 1) := by
  unfold averageCorrelation
  simp only [averageFrom_closed, word_low, ← bit1_low (word _ _), word_low]
  have hl : Finset.expect Finset.univ (fun lo : Fin 4 => closed k (BitVec.ofNat 2 lo.val)
      ((BitVec.ofNat 2 lo.val).getLsbD 1)) = ((k:ℚ) + 2) / 2 ^ (k + 1) := by
    norm_num [Finset.expect_eq_sum_div_card, Fin.sum_univ_succ, closed, sign, BitVec.getLsbD,
      Nat.testBit, pow_succ]
    ring
  simp only [hl]
  exact Finset.expect_const Finset.univ_nonempty _

/-- Source parameters N≥2 and m≥2. The sampled word width is
m-2 + 2=m, with N-1 independent uniformly sampled operators. -/
theorem averageCorrelation_source (N m : ℕ) (hN : 2 ≤ N) (_hm : 2 ≤ m) :
    averageCorrelation (m-2) (N-1) = ((N:ℚ) + 1) / 2 ^ N := by
  rw [averageCorrelation_eq]
  have hn : N-1 + 1 = N := by omega
  have hc : ((N-1:ℕ):ℚ) + 2 = (N:ℚ) + 1 := by
    have := congrArg (fun n : ℕ => (n:ℚ)) hn
    simp only [Nat.cast_add, Nat.cast_one] at this
    linear_combination this
  rw [hc, hn]

end Cslib.Cryptanalysis.AddXNOR
