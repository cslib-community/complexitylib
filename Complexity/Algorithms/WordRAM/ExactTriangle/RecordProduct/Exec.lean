/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Prepare

/-!
# Complete native per-record product execution

The native preparation is followed by the complete existing callable product. Every returned
word answers its original occurrence; the whole producer catalogue remains below the owned
window and is preserved. These are internal readback composition rules; the producer client
discharges their descriptor and source-span assertions from its actual initialized execution.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- The complete per-record charge includes actual decoding, copying and callee invocation. -/
@[expose] def timeBound {m n : ℕ} (qs : List (Fin n × Fin n)) : ℕ :=
  CallableProduct.timeBound (m := m) qs + 8 * m + 14 * (n * D m) + 14 * qs.length + 71

/-- All preparation arithmetic and the original input lie below the already computed virtual
window. This follows from the existing actual product admission, rather than an input fit table. -/
theorem preparation_margin {m n Q : ℕ} (hN : D m ^ 18 ≤ n) :
    2 * (n * D m) + 2 * Q + 20 * m + D m + n + 256 < CallableProduct.windowSize n Q := by
  have hD : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hbudget := (CallableProduct.source_admission (Q := Q) hN).2.2
  change QueriedProduct.wordBudget (19 * m) m n Q < CallableProduct.windowSize n Q at hbudget
  unfold QueriedProduct.wordBudget QueriedProduct.inputEnd at hbudget
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
      y.regs Reg.result = b + QueriedProduct.outputBase (19 * m) m n qs.length ∧
      (∀ j : Fin qs.length,
        y.mem (b + (QueriedProduct.outputBase (19 * m) m n qs.length + j.val)) =
          Signed.encode ((X * Y) (qs.get j).1 (qs.get j).2)) ∧
      (∀ a, a < b ∨ b + CallableProduct.windowSize n qs.length ≤ a → y.mem a = x.mem a) ∧
      ∀ j : Fin 320, j.val < 65 → y.regs j = x.regs j := by
  have hmargin := preparation_margin (Q := qs.length) hN
  obtain ⟨a, ha, ab, ain, af, ar⟩ := exec_prepare X Y qs x hD hn hi hout hb hrec hrecord
    hsb htb hqb hleft hright hqueries (hfit.of_le (by omega))
  obtain ⟨y, hy, yr, yv, yi, yf, yg⟩ := exec_invoke X Y qs a ab ain hX hY hN
    (hfit.of_le (by omega))
  refine ⟨y, (ha.seq hy).mono (by unfold timeBound; omega), yr, yv, ?_, ?_⟩
  · intro j hj
    rw [yf j hj]
    apply af j
    unfold QueriedProduct.inputEnd
    omega
  · intro j hj
    have hne : j ≠ Reg.result := by intro h; subst j; simp [Reg.result] at hj
    exact (yg j (by omega) hne).trans (ar j hj)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
