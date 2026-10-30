/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Exec

/-!
# Original-input admission for product-selected witness recovery

One positive width threshold covers the original producer/product admission, all real
descriptor/query/address arithmetic and both signed additions of original weights. It depends
on the original scalar headers and magnitude envelope, not on the physical width chosen by
the caller. The reserved product window is an address bound, not a charged clearing operation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Numerical envelope in original dimensions and weight magnitude; it covers all recovery
setup and calls after the genuine producer has established its own word/address bound. -/
@[expose] def envelope (n D g p A : ℕ) : ℕ :=
  64 * (PreparationInput.wordBound n D g p A + CallableProduct.windowSize n (n ^ 2) +
    n * D + n ^ 2 + n + g + D + A + 4096)

/-- Physical width for the same fixed native program at every larger admitted word size. -/
@[expose] def admissionWidth (n D g p A : ℕ) : ℕ :=
  max (RecordProduct.admissionWidth n D g p A) (Nat.clog 2 (envelope n D g p A)) + 3

/-- The initialized native threshold is positive for every original scalar tuple. -/
theorem admissionWidth_pos (n D g p A : ℕ) : 0 < admissionWidth n D g p A := by
  unfold admissionWidth
  omega

/-- The existing product's output slice precedes its admitted virtual-window boundary. -/
theorem outputBase_lt_window {m n Q : ℕ} (hN : D m ^ 18 ≤ n) :
    QueriedProduct.outputBase (19 * m) m n Q < CallableProduct.windowSize n Q := by
  have hout : QueriedProduct.outputBase (19 * m) m n Q ≤
      QueriedProduct.memoryEnd (19 * m) m n Q := by
    unfold QueriedProduct.memoryEnd QueriedProduct.stampBase QueriedProduct.scratchBase
    have hten := Nat.zero_le (10 ^ (19 * m))
    have hframes := Nat.zero_le (2 * (19 * m + 1) * 10 ^ (19 * m))
    omega
  have hword : QueriedProduct.memoryEnd (19 * m) m n Q ≤
      QueriedProduct.wordBudget (19 * m) m n Q := by
    unfold QueriedProduct.wordBudget
    omega
  exact (hout.trans hword).trans_lt (CallableProduct.source_admission hN).2.2

/-- Every pointer and temporary of the actual per-record caller fits from the original
producer word bound and the actual chunk count. No intermediate fit certificate is supplied. -/
theorem physical_fits {w m n g p A heap Q : ℕ}
    (hheap : heap ≤ PreparationInput.wordBound n (D m) g p A)
    (hQ : Q ≤ n ^ 2) (hN : D m ^ 18 ≤ n)
    (hW : admissionWidth n (D m) g p A ≤ w + 2) :
    Fits (w + 2) (4 * heap + 4 * CallableProduct.windowSize n Q +
      QueriedProduct.outputBase (19 * m) m n Q + 4 * Q + 4 * D m +
      2 * (n * D m) + 9 * (n * n) + 4 * n + g + 4096) := by
  have hwindow : CallableProduct.windowSize n Q ≤ CallableProduct.windowSize n (n ^ 2) := by
    unfold CallableProduct.windowSize CallableProduct.sourceWidth
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.mul_le_mul_left 128 (Nat.clog_mono_right 2 (by omega))
  have hout := (outputBase_lt_window (Q := Q) hN).le.trans hwindow
  have he : Fits (w + 2) (envelope n (D m) g p A) := by
    have hn := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (envelope n (D m) g p A)
    have hw : Nat.clog 2 (envelope n (D m) g p A) < w + 2 := by
      unfold admissionWidth at hW
      omega
    exact hn.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hw)
  apply he.of_le
  unfold envelope
  rw [pow_two] at hQ hwindow hout ⊢
  omega

/-- Two signed additions use the original envelope `2A`; the physical compiler extension
is included in the same original-input threshold. -/
theorem signed_fits {w n D g p A : ℕ} (hW : admissionWidth n D g p A ≤ w + 2) :
    GenericRAM.Signed.Fits w (2 * A : ℕ) := by
  have hw : Nat.clog 2 (envelope n D g p A) + 1 ≤ w := by
    unfold admissionWidth at hW
    omega
  have he : 2 * A < envelope n D g p A := by unfold envelope; omega
  have hp := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (envelope n D g p A)
  have ht : 2 * A < 2 ^ (w - 1) := he.trans_le
    (hp.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  refine ⟨by omega, ?_, by exact_mod_cast ht⟩
  have hz : (0 : ℤ) ≤ (2 * A : ℕ) := by exact_mod_cast Nat.zero_le (2 * A)
  have hp : (0 : ℤ) ≤ 2 ^ (w - 1) := by positivity
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
