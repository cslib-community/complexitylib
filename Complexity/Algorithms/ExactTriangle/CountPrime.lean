/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.Hashing
public import Complexity.Algorithms.MatrixMultiplication.Strassen.Correctness

/-!
# Modular triangle counts from the actual seven-product coefficient recursion

The coefficient arrays contain zero padding and one monomial for each real edge residue.
`CountPrime.count` applies the executable finite Strassen recursion and selects one product
coefficient for each original AB pair. It equals the existing `countZeroMod`, including
modular false positives. This is a mathematical specification and correctness bridge for
the native counter, not a native execution or running-time theorem.

The construction selectively adapts Spec/Sec3/Theorem17/Strassen.lean, the `matPList`,
`matQList`, `countBy` and `countOf_eq` sections, at revision
16a5ce41304fcdaea4e0be7c132e1c361dc26da5. Existing `matP`, `matQ`, cyclic coefficients and
modular triangle counts are reused; no parallel triangle problem or polynomial ring is added.
-/

public section

namespace Cslib.Algorithms.ExactTriangle.CountPrime

open Cslib.CyclicIntRing Cslib.Algorithms.MatrixMultiplication.Strassen

/-- Native P coefficient specification, including true zero padding outside the original side. -/
@[expose] def pCoefficients {n : ℕ} (p : ℕ) (wAC : Fin n → Fin n → ℤ) (i : ℕ) : ℤ :=
  if h : Nat.Morton.row (i / p) < n ∧ Nat.Morton.column (i / p) < n then
    if i % p = (wAC ⟨_, h.1⟩ ⟨_, h.2⟩ % (p : ℤ)).toNat then 1 else 0
  else 0

/-- Native Q coefficient specification; the original BC coordinates are transposed. -/
@[expose] def qCoefficients {n : ℕ} (p : ℕ) (wBC : Fin n → Fin n → ℤ) (i : ℕ) : ℤ :=
  if h : Nat.Morton.row (i / p) < n ∧ Nat.Morton.column (i / p) < n then
    if i % p = (wBC ⟨_, h.2⟩ ⟨_, h.1⟩ % (p : ℤ)).toNat then 1 else 0
  else 0

/-- Every actual monomial coefficient, including padding, has magnitude at most one. -/
theorem pCoefficients_natAbs_le_one {n : ℕ} (p : ℕ) (wAC : Fin n → Fin n → ℤ) (i : ℕ) :
    (pCoefficients p wAC i).natAbs ≤ 1 := by
  unfold pCoefficients
  split_ifs <;> decide

/-- The transposed monomial matrix has the same unit coefficient bound. -/
theorem qCoefficients_natAbs_le_one {n : ℕ} (p : ℕ) (wBC : Fin n → Fin n → ℤ) (i : ℕ) :
    (qCoefficients p wBC i).natAbs ≤ 1 := by
  unfold qCoefficients
  split_ifs <;> decide

private noncomputable def pad {n p : ℕ} (M : Matrix (Fin n) (Fin n) (CyclicIntRing p))
    (a b : ℕ) : CyclicIntRing p := if h : a < n ∧ b < n then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

private theorem pCoefficients_eq {n p : ℕ} (hp : p ≠ 0) (wAC : Fin n → Fin n → ℤ) :
    pCoefficients p wAC = coefficients hp (pad (matP wAC p)) := by
  funext i
  by_cases h : Nat.Morton.row (i / p) < n ∧ Nat.Morton.column (i / p) < n
  · simp only [pCoefficients, coefficients, pad, dite_eq_left h, matP, Matrix.of_apply,
      coeff_x_pow]
    rw [Nat.mod_eq_of_lt (show (wAC ⟨_, h.1⟩ ⟨_, h.2⟩ % (p : ℤ)).toNat < p from
      Int.natMod_lt hp)]
  · simp only [pCoefficients, coefficients, pad, dite_eq_right h, map_zero]

private theorem qCoefficients_eq {n p : ℕ} (hp : p ≠ 0) (wBC : Fin n → Fin n → ℤ) :
    qCoefficients p wBC = coefficients hp (pad (matQ wBC p)) := by
  funext i
  by_cases h : Nat.Morton.row (i / p) < n ∧ Nat.Morton.column (i / p) < n
  · simp only [qCoefficients, coefficients, pad, dite_eq_left h, matQ, Matrix.of_apply,
      coeff_x_pow]
    rw [Nat.mod_eq_of_lt (show (wBC ⟨_, h.2⟩ ⟨_, h.1⟩ % (p : ℤ)).toNat < p from
      Int.natMod_lt hp)]
  · simp only [qCoefficients, coefficients, pad, dite_eq_right h, map_zero]

private theorem sum_pad {n p N : ℕ} (hN : n ≤ N)
    (M K : Matrix (Fin n) (Fin n) (CyclicIntRing p)) (a b : Fin n) :
    ∑ c ∈ Finset.range N, pad M a c * pad K c b = (M * K) a b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have ht : ∑ c ∈ Finset.range k, pad M a (n + c) * pad K (n + c) b = 0 :=
    Finset.sum_eq_zero fun c _ => by simp [pad]
  rw [Finset.sum_range_add, ht, add_zero, Matrix.mul_apply, Finset.sum_range]
  exact Finset.sum_congr rfl fun c _ => by simp [pad]

/-- Every original pair and residue in the executable finite Strassen coefficient array
has exactly the existing cyclic matrix-product meaning, including power-of-two padding. -/
theorem multiply_entry_eq_coeff {n p k : ℕ} (hp : p ≠ 0) (hn : n ≤ 2 ^ k)
    (wBC wAC : Fin n → Fin n → ℤ) (a b : Fin n) (r : ℕ) (hr : r < p) :
    multiply p k (pCoefficients p wAC) (qCoefficients p wBC)
      (Nat.Morton.index a b * p + r) =
      CyclicIntRing.coeff hp r ((matP wAC p * matQ wBC p) a b) := by
  have hi := Nat.Morton.index_lt (a.isLt.trans_le hn) (b.isLt.trans_le hn)
  have hmul := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hmul
  have hidx : Nat.Morton.index a b * p + r < 4 ^ k * p := by omega
  rw [multiply_eq_coefficients hp k (pad (matP wAC p)) (pad (matQ wBC p))
    (pCoefficients p wAC) (qCoefficients p wBC)
    (fun i _ => congrFun (pCoefficients_eq hp wAC) i)
    (fun i _ => congrFun (qCoefficients_eq hp wBC) i) hidx,
    coefficients_at hp _ a b hr, sum_pad hn]

/-- The selected real product coefficient is a nonnegative count of at most n middle
vertices. Native signed-to-unsigned extraction uses this bound before every sum. -/
theorem multiply_entry_bounds {n p k : ℕ} (hp : p ≠ 0) (hn : n ≤ 2 ^ k)
    (wBC wAC : Fin n → Fin n → ℤ) (a b : Fin n) (r : ℕ) (hr : r < p) :
    0 ≤ multiply p k (pCoefficients p wAC) (qCoefficients p wBC)
        (Nat.Morton.index a b * p + r) ∧
      multiply p k (pCoefficients p wAC) (qCoefficients p wBC)
        (Nat.Morton.index a b * p + r) ≤ (n : ℤ) := by
  classical
  rw [multiply_entry_eq_coeff hp hn wBC wAC a b r hr,
    coeff_matP_mul_matQ wBC wAC hp a b r hr]
  have hc := Finset.card_le_card (Finset.filter_subset (s := Finset.univ)
    (p := fun c : Fin n => wAC a c + wBC b c ≡ (r : ℤ) [ZMOD (p : ℤ)]))
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  constructor
  · positivity
  · exact_mod_cast hc

/-- Select the (-AB)-residue coefficient for each original pair after the real seven-product
finite recursion. The depth controls zero padding; it is not a supplied multiplication. -/
@[expose] def count {n : ℕ} (p k : ℕ) (wAB wBC wAC : Fin n → Fin n → ℤ) : ℤ :=
  ∑ a : Fin n, ∑ b : Fin n,
    multiply p k (pCoefficients p wAC) (qCoefficients p wBC)
      (Nat.Morton.index a b * p + ((-wAB a b) % (p : ℤ)).toNat)

/-- The finite coefficient algorithm counts exactly the existing modular-zero predicate,
for every nonzero modulus and every power-of-two padding covering the input. -/
theorem count_eq {n p k : ℕ} (hp : p ≠ 0) (hn : n ≤ 2 ^ k)
    (wAB wBC wAC : Fin n → Fin n → ℤ) :
    count p k wAB wBC wAC = (countZeroMod wAB wBC wAC p : ℤ) := by
  have hc := falsePositiveCount_add_zeroCount_eq_sum_coeff wAB wBC wAC hp
  rw [← countZeroMod_eq] at hc
  rw [count, hc]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hr : ((-wAB a b) % (p : ℤ)).toNat < p := Int.natMod_lt hp
  exact multiply_entry_eq_coeff hp hn wBC wAC a b _ hr

end Cslib.Algorithms.ExactTriangle.CountPrime
