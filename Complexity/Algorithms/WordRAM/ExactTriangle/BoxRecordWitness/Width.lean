/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.BoxRecordWitness.Exec
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Width
import Complexity.Computability.WordRAM.Admission

/-!
# Original-input admission for product-selected witness recovery

One positive width threshold covers the original producer/product admission, all real
descriptor/query/address arithmetic and both signed additions of original weights. It depends
on the original scalar headers and magnitude envelope, not on the physical width chosen by
the caller. The reserved product window is an address bound, not a charged clearing operation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.BoxRecordWitness

open Cslib.WordRAM RecordWitness
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- The existing product's output slice precedes its admitted virtual-window boundary. -/
theorem outputBase_lt_window {m n Q : ℕ} (hN : D m ^ 18 ≤ n) :
    QueriedProduct.outputBase (21 * m) m n Q < CallableProduct.windowSize n Q := by
  have hout : QueriedProduct.outputBase (21 * m) m n Q ≤
      QueriedProduct.memoryEnd (21 * m) m n Q := by
    unfold QueriedProduct.memoryEnd QueriedProduct.stampBase QueriedProduct.scratchBase
    have hten := Nat.zero_le (10 ^ (21 * m))
    have hframes := Nat.zero_le (2 * (21 * m + 1) * 10 ^ (21 * m))
    omega
  have hword : QueriedProduct.memoryEnd (21 * m) m n Q ≤
      QueriedProduct.wordBudget (21 * m) m n Q := by
    unfold QueriedProduct.wordBudget
    omega
  have hbox : QueriedProduct.wordBudget (21 * m) m n Q ≤
      BoxProduct.wordBudget (21 * m) m (m / 9) n Q := by
    unfold BoxProduct.wordBudget
    omega
  exact (hout.trans (hword.trans hbox)).trans_lt
    (CallableBoxProduct.source_admission (Nat.div_le_self m 9) hN).2.2

/-- Every pointer and temporary of the actual per-record caller fits from the original
producer word bound and the actual chunk count. No intermediate fit certificate is supplied. -/
theorem physical_fits {w m n g p A heap Q : ℕ}
    (hheap : heap ≤ PreparationInput.wordBound n (D m) g p A)
    (hQ : Q ≤ n ^ 2) (hN : D m ^ 18 ≤ n)
    (hW : admissionWidth n (D m) g p A ≤ w + 2) :
    Fits (w + 2) (4 * heap + 4 * CallableProduct.windowSize n Q +
      QueriedProduct.outputBase (21 * m) m n Q + 4 * Q + 4 * D m +
      2 * (n * D m) + 9 * (n * n) + 4 * n + g + 4096) := by
  have hwindow : CallableProduct.windowSize n Q ≤ CallableProduct.windowSize n (n ^ 2) :=
    CallableProduct.windowSize_mono_right n hQ
  have hout := (outputBase_lt_window (Q := Q) hN).le.trans hwindow
  have he : Fits (w + 2) (envelope n (D m) g p A) := by
    exact fits_of_clog_lt (by unfold admissionWidth at hW; omega)
  apply he.of_le
  unfold envelope
  rw [pow_two] at hQ hwindow hout ⊢
  omega


end Cslib.Algorithms.WordRAM.ExactTriangle.BoxRecordWitness
