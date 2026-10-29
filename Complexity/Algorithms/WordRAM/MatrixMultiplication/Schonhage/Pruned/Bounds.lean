/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Values
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Weight
public import Complexity.Computability.GenericRAM.Signed.Fits
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory

/-!
# Input-derived bounds for native pruned evaluation

## Main definitions

* `PrunedQuery.nodeBudget`: a scalar address/counter budget, including remaining epochs.
* `PrunedQuery.magnitudeBound`: covers both operands and every partial sum.

## Main results

* `PrunedQuery.nodeBudget_input_le`: the concrete input-derived bound covers the root budget.
* `PrunedQuery.fits_partialValue`: the original magnitude bound derives partial accumulator fits.

The only fit assumptions are numerical inequalities on original parameters. No state-by-state
fit assertion or execution/time certificate is supplied.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- A node budget for ordinary pointers, powers, counters and all remaining fresh epochs. -/
def nodeBudget (L f a b E n : ℕ) : ℕ :=
  8 * f + 64 * (L + 1) * 10 ^ L + a + b + 2 * 10 ^ L + E + epochAllowance n + 128

/-- Root deduplication and reporting additionally use the original query/output pointers and
the full supplied query count, which may exceed the distinct-set capacity. -/
def evaluationBudget (L f a b q o Q E : ℕ) : ℕ :=
  nodeBudget L f a b (E + 1) L + 4 * (q + o + Q + 1)

/-- The callable kernel also computes its own powers and workspace pointers. Its numeric
admission includes those setup bounds and permits arbitrary separated input/output addresses. -/
def kernelBudget (L f a b q o Q E : ℕ) : ℕ :=
  addressBound L Q + evaluationBudget L f a b q o Q E

/-- The ordinary initialized layout covers evaluation, including repeated supplied queries. -/
theorem evaluationBudget_input_le (L Q : ℕ) :
    evaluationBudget L (scratchBase L Q) 3 (3 + 10 ^ L) (3 + 2 * 10 ^ L)
      (outputBase L Q) Q 0 ≤ addressBound L Q := by
  have he := epochAllowance_le L
  have hp : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  unfold evaluationBudget nodeBudget scratchBase outputBase addressBound
  nlinarith only [he, hp]

/-- The larger concrete standalone bound covers initialization and every root parameter. -/
theorem nodeBudget_input_le (L Q : ℕ) :
    nodeBudget L (scratchBase L Q) 3 (3 + 10 ^ L) 1 L ≤ addressBound L Q := by
  have he := epochAllowance_le L
  have hp : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  unfold nodeBudget scratchBase outputBase addressBound
  nlinarith only [he, hp]

/-- Epoch allocation to a child is paid for by the remaining parent allowance. -/
theorem nodeBudget_child_le {L f a b E E' n : ℕ}
    (hE : E' + epochAllowance n ≤ E + epochAllowance (n + 1)) :
    nodeBudget L f a b E' n ≤ nodeBudget L f a b E (n + 1) := by
  unfold nodeBudget
  omega

/-- A single original-parameter envelope covers the two inputs and all tensor partial sums. -/
def magnitudeBound (L A B : ℕ) : ℕ := A + B + 10 ^ L * (A * B)

/-- The positive-endpoint inequality makes the nonnegative envelope a signed fitting value. -/
theorem magnitudeBound_fits {w L A B : ℕ} (hw : 0 < w)
    (hfit : magnitudeBound L A B < 2 ^ (w - 1)) :
    GenericRAM.Signed.Fits w (magnitudeBound L A B : ℤ) := by
  refine ⟨hw, ?_, ?_⟩
  · have hp : (0 : ℤ) ≤ 2 ^ (w - 1) := by positivity
    have hm : (0 : ℤ) ≤ (magnitudeBound L A B : ℕ) := by positivity
    omega
  · exact_mod_cast hfit

/-- The original bound on one input entry derives its signed fit through the common envelope. -/
theorem fits_left {w L A B : ℕ} {z : ℤ}
    (hfit : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℤ)) (hz : |z| ≤ (A : ℤ)) :
    GenericRAM.Signed.Fits w z := by
  apply hfit.of_natAbs_le
  have hz' : z.natAbs ≤ A := by
    rw [← Int.natCast_natAbs] at hz
    exact_mod_cast hz
  exact hz'.trans (by unfold magnitudeBound; omega)

/-- The right operand uses the same envelope, including the zero-input boundary. -/
theorem fits_right {w L A B : ℕ} {z : ℤ}
    (hfit : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℤ)) (hz : |z| ≤ (B : ℤ)) :
    GenericRAM.Signed.Fits w z := by
  apply hfit.of_natAbs_le
  have hz' : z.natAbs ≤ B := by
    rw [← Int.natCast_natAbs] at hz
    exact_mod_cast hz
  exact hz'.trans (by unfold magnitudeBound; omega)

/-- The leaf product fits the same envelope, including when either input bound is zero. -/
theorem fits_product {w L A B : ℕ} {a b : ℤ}
    (hfit : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℤ))
    (ha : |a| ≤ (A : ℤ)) (hb : |b| ≤ (B : ℤ)) : GenericRAM.Signed.Fits w (a * b) := by
  apply hfit.of_natAbs_le
  have ha' : a.natAbs ≤ A := by
    rw [← Int.natCast_natAbs] at ha
    exact_mod_cast ha
  have hb' : b.natAbs ≤ B := by
    rw [← Int.natCast_natAbs] at hb
    exact_mod_cast hb
  rw [Int.natAbs_mul]
  have hp : A * B ≤ 10 ^ L * (A * B) :=
    Nat.le_mul_of_pos_left _ (by positivity : 0 < (10 : ℕ) ^ L)
  exact (Nat.mul_le_mul ha' hb').trans (hp.trans (by unfold magnitudeBound; omega))

/-- A partial sum at any remaining depth fits by the original global magnitude inequality. -/
theorem fits_partialValue {w L n A B : ℕ} (hn : n + 1 ≤ L)
    (hfit : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℤ))
    (a b : Leaf (n + 1) → ℤ) (ha : ∀ v, |a v| ≤ (A : ℤ))
    (hb : ∀ v, |b v| ≤ (B : ℤ)) (S : Finset (OutStr (n + 1)))
    (q : OutStr (n + 1)) (k : ℕ) : GenericRAM.Signed.Fits w (partialValue a b S q k) := by
  apply hfit.of_natAbs_le
  have h := abs_partialValue_le a b A B ha hb S q k
  have hnat : (partialValue a b S q k).natAbs ≤ 10 ^ (n + 1) * (A * B) := by
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (10 : ℕ)) hn
  have hm := Nat.mul_le_mul_right (A * B) hp
  exact hnat.trans (hm.trans (by unfold magnitudeBound; omega))

/-- Every returned child result fits, including an unselected or skipped zero value. -/
theorem fits_childResult {w L n A B : ℕ} (hn : n ≤ L)
    (hfit : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℤ))
    (a b : Leaf (n + 1) → ℤ) (ha : ∀ v, |a v| ≤ (A : ℤ))
    (hb : ∀ v, |b v| ≤ (B : ℤ)) (S : Finset (OutStr (n + 1)))
    (lam : Term) (q : OutStr n) : GenericRAM.Signed.Fits w (Pruned.childResult a b S lam q) := by
  apply hfit.of_natAbs_le
  have h := abs_childResult_le a b A B ha hb S lam q
  have hnat : (Pruned.childResult a b S lam q).natAbs ≤ 10 ^ n * (A * B) := by
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (10 : ℕ)) hn
  have hm := Nat.mul_le_mul_right (A * B) hp
  exact hnat.trans (hm.trans (by unfold magnitudeBound; omega))

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
