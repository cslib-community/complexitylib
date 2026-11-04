/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Kernel
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Exec

/-!
# Complete native per-record product execution

Scalar preparation and the threshold-aware patch precede a native direct-to-snapshot gather.
Every returned word answers its original occurrence; the whole producer catalogue remains below
the owned
window and is preserved. These are internal readback composition rules; the producer client
discharges their descriptor and source-span assertions from its actual initialized execution.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

open Cslib.WordRAM
open RecordProduct
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- The retained per-record upper bound covers the improved actual gather implementation. -/
@[expose] def timeBound {m n : ℕ} (qs : List (Fin n × Fin n)) : ℕ :=
  CallableBoxProduct.timeBound m (m / 9) qs + 8 * m + 14 * (n * D m) + 14 * qs.length + 87

/-- Actual improved allowance: scalar preparation, four pointer deliveries, gather product,
and the returned physical pointer. The conservative public envelope remains `timeBound`. -/
@[expose] def gatherTimeBound {m n : ℕ} (qs : List (Fin n × Fin n)) : ℕ :=
  PointerBoxProduct.timeBound m (m / 9) qs + 8 * m + 69

/-- Exact identity of allowances. Three extra native pointer deliveries are charged alongside
all four gather copies; the two former staging allowances form the comparison pool. -/
theorem gatherTimeBound_ledger {m n : ℕ} (qs : List (Fin n × Fin n)) :
    timeBound (m := m) qs + PointerBoxProduct.gatherTime (n * D m) qs.length + 3 =
      gatherTimeBound (m := m) qs + (14 * (n * D m) + 14 * qs.length + 21) +
        3 * (7 * QueriedProduct.inputEnd m n qs.length + 10) := by
  have h := PointerBoxProduct.timeBound_ledger m (m / 9) qs
  unfold timeBound gatherTimeBound
  omega

/-- The actual gather allowance fits the previous advertised time envelope. This compares
proved upper bounds, and does not measure the difference of execution times. -/
theorem gatherTimeBound_le_timeBound {m n : ℕ} (qs : List (Fin n × Fin n)) :
    gatherTimeBound (m := m) qs ≤ timeBound (m := m) qs := by
  have h := gatherTimeBound_ledger (m := m) qs
  unfold PointerBoxProduct.gatherTime QueriedProduct.inputEnd at h
  omega

/-- Actual record-to-product execution, with only original input/readback premises and no
solver/run/time oracle. The final initialized client derives these premises from the producer. -/
theorem exec {W b m n i out rho piece s t q : ℕ}
    (X : Matrix (Fin n) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin n) ℤ)
    (qs : List (Fin n × Fin n)) (x : Data 320)
    (hD : x.mem 1 = D m) (hn : x.mem 3 = n)
    (hi : x.regs Reg.ordinal = i) (hout : x.regs 39 = out) (hb : x.regs 42 = b)
    (hrec : out + i * (6 + 2 * (n * D m)) + 6 ≤ b)
    (hrecord : (Block.mk (out + i * (6 + 2 * (n * D m))) 6).Realizes x.mem
      ![rho, piece, q, qs.length, s, t])
    (hsb : s + n * D m ≤ b) (htb : t + n * D m ≤ b)
    (hqb : q + 2 * qs.length ≤ b)
    (hleft : ∀ a < n * D m, x.mem (s + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem (5 + a))
    (hright : ∀ a < n * D m, x.mem (t + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem
        (5 + n * D m + a))
    (hqueries : ∀ a < 2 * qs.length, x.mem (q + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem
        (5 + 2 * (n * D m) + a))
    (hX : ∀ a k, 0 ≤ X a k ∧ X a k ≤ 1) (hY : ∀ k a, 0 ≤ Y k a ∧ Y k a ≤ 1)
    (hN : D m ^ 18 ≤ n)
    (hfit : Fits W (2 * b + 4 * CallableProduct.windowSize n qs.length + 1024)) :
    ∃ y, ExecWithin W program x y (timeBound (m := m) qs) ∧
      y.regs Reg.result = b + QueriedProduct.outputBase (21 * m) m n qs.length ∧
      (∀ j : Fin qs.length,
        y.mem (b + (QueriedProduct.outputBase (21 * m) m n qs.length + j.val)) =
          Signed.encode ((X * Y) (qs.get j).1 (qs.get j).2)) ∧
      (∀ a, a < b ∨ b + CallableProduct.windowSize n qs.length ≤ a → y.mem a = x.mem a) ∧
      ∀ j : Fin 320, j.val < 65 → y.regs j = x.regs j := by
  have hmargin := preparation_margin (Q := qs.length) hN
  obtain ⟨a, ha, ab, as, aright, aq, ahead, athreshold, af, ar⟩ := exec_prepare X Y qs x
    hD hn hi hout hb hrec hrecord (hfit.of_le (by omega))
  have hread (j : ℕ) (hj : j < b) : a.mem j = x.mem j := af j (Or.inl hj)
  have word (j : ℕ) (hj : 5 ≤ j) (hj' : j < QueriedProduct.inputEnd m n qs.length) :
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem j =
        (State.init (BoxProduct.input true (21 * m) (m / 9) X Y qs) : State 160).data.mem j :=
    (QueriedProduct.input_change_level true (19 * m) (21 * m) X Y qs j (by omega)).trans
      (BoxProduct.input_prefix true X Y qs j (by omega) hj').symm
  obtain ⟨y, hy, yr, yv, yf, yg⟩ := exec_invoke X Y qs a ab as aright aq ahead athreshold
    hsb htb hqb
    (by
      intro j hj
      rw [hread _ (by omega)]
      exact (hleft j hj).trans
        (word _ (by omega) (by unfold QueriedProduct.inputEnd; omega)))
    (by
      intro j hj
      rw [hread _ (by omega)]
      exact (hright j hj).trans
        (word _ (by omega) (by unfold QueriedProduct.inputEnd; omega)))
    (by
      intro j hj
      rw [hread _ (by omega)]
      exact (hqueries j hj).trans
        (word _ (by omega) (by unfold QueriedProduct.inputEnd; omega)))
    hX hY (Nat.div_le_self _ _) hN hfit
  have hI : 5 ≤ QueriedProduct.inputEnd m n qs.length := by
    unfold QueriedProduct.inputEnd; omega
  have hIwindow : QueriedProduct.inputEnd m n qs.length + 1 <
      CallableProduct.windowSize n qs.length := by
    unfold QueriedProduct.inputEnd
    omega
  refine ⟨y, (ha.seq hy).mono ?_, yr, yv, ?_, ?_⟩
  · exact (show 8 * m + 64 + (PointerBoxProduct.timeBound m (m / 9) qs + 5) ≤
        gatherTimeBound (m := m) qs by unfold gatherTimeBound; omega).trans
      (gatherTimeBound_le_timeBound qs)
  · intro j hj
    exact (yf j hj).trans (af j (by omega))
  · intro j hj
    have hne : j ≠ Reg.result := by intro h; subst j; simp [Reg.result] at hj
    exact (yg j (by omega) hne).trans (ar j hj)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct
