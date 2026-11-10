/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Program
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.ThinWidth

/-!
# Actual translated box-product execution

The execution is derived from original zero/one matrices and request occurrences. The source
register bank and dirty source scratch are normalized by actual setup and translated loads.
No execution, routing, layout or cost certificate is a premise. These stage lemmas are internal
implementation APIs; exact physical answer/input words are normalized by the final spans.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBoxProduct

open Cslib.WordRAM
open CallableProduct
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Setup, all translated source instructions and the two real span-adjustment instructions. -/
@[expose] def coreTime (m t : ℕ) {N : ℕ} (qs : List (Fin N × Fin N)) : ℕ :=
  517 * Nat.clog 2 (N + qs.length + 3) + 184 +
    3 * BoxProduct.timeBound (21 * m) m t qs + 2

/-- Original dimensions and the threshold bound imply source admission; no fit oracle is used. -/
theorem source_admission {m t N Q : ℕ} (ht : t ≤ m) (hN : D m ^ 18 ≤ N) :
    0 < sourceWidth N Q - 2 ∧
      BoxProduct.magnitudeBound (21 * m) 1 < 2 ^ ((sourceWidth N Q - 2) - 1) ∧
      Fits (sourceWidth N Q) (BoxProduct.wordBudget (21 * m) m t N Q) :=
  BoxProduct.admission_bounds (BoxProduct.thin_admissionWidth_le m t N Q 1 ht hN)

/-- Original words initialize an actual callable native product prefix, even with arbitrary
dirty target memory in the reserved window. Answers here are clipped physical words; the
subsequent real normalization makes them exact. Original duplicate requests retain their order. -/
theorem exec_core {W b m t N : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 163) (hb : x.regs Reg.base = b)
    (hinput : ∀ a, a < QueriedProduct.inputEnd m N qs.length + 1 →
      x.mem (b + a) =
        (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem a)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (ht : t ≤ m) (hN : D m ^ 18 ≤ N) (hfit : Fits W (b + 4 * windowSize N qs.length + 1024)) :
    ∃ y, ExecWithin W core x y (coreTime m t qs) ∧
      y.regs Reg.base = b ∧ y.regs Reg.modulus = windowSize N qs.length ∧
      y.regs Reg.inputSize = QueriedProduct.inputEnd m N qs.length + 1 ∧
      y.regs Reg.queryCount = qs.length ∧
      y.regs Reg.output = QueriedProduct.outputBase (21 * m) m N qs.length ∧
      (∀ i : Fin qs.length,
        y.mem (b + (QueriedProduct.outputBase (21 * m) m N qs.length + i.val)) %
            windowSize N qs.length = Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < QueriedProduct.inputEnd m N qs.length + 1 →
        y.mem (b + a) % windowSize N qs.length = x.mem (b + a)) ∧
      (∀ a, a < b ∨ b + windowSize N qs.length ≤ a → y.mem a = x.mem a) := by
  have hXabs (i k) : |X i k| ≤ (1 : ℤ) := by rw [abs_of_nonneg (hX i k).1]; exact (hX i k).2
  have hYabs (k j) : |Y k j| ≤ (1 : ℤ) := by rw [abs_of_nonneg (hY k j).1]; exact (hY k j).2
  have hbits : true = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j) :=
    fun _ => ⟨fun i k => (hX i k).1, fun k j => (hY k j).1⟩
  obtain ⟨hw, hmag, hbudget⟩ := source_admission (Q := qs.length) ht hN
  have htwo : sourceWidth N qs.length - 2 + 2 = sourceWidth N qs.length := by omega
  have hbudget' : Fits (sourceWidth N qs.length - 2 + 2)
      (BoxProduct.wordBudget (21 * m) m t N qs.length) := by simpa only [htwo] using hbudget
  have hi := BoxProduct.input_fits hw (show m ≤ 21 * m by omega)
    true X Y qs hXabs hYabs hmag hbudget'
  have hi' : (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.Bounded
      (sourceWidth N qs.length) := by
    simpa only [htwo, State.init] using (Data.Bounded.init (r := 160) hi)
  have hrow : x.mem (b + 3) = N := by
    rw [hinput 3 (by unfold QueriedProduct.inputEnd; omega)]
    simp [State.init, Data.init, BoxProduct.input, QueriedProduct.input]
  have hcount : x.mem (b + 4) = qs.length := by
    rw [hinput 4 (by unfold QueriedProduct.inputEnd; omega)]
    simp [State.init, Data.init, BoxProduct.input, QueriedProduct.input]
  obtain ⟨s, hs, smem, smatch, sbound⟩ := exec_setup x hb hrow hcount hfit
  let v := MemoryWindow.view (sourceWidth N qs.length) b s
  have vinput (a : ℕ) (ha : a < QueriedProduct.inputEnd m N qs.length + 1) :
      v.mem a =
        (State.init (BoxProduct.input true (21 * m) t X Y qs) : State 160).data.mem a := by
    change s.mem (b + a) % 2 ^ sourceWidth N qs.length = _
    rw [smem, hinput a ha, Nat.mod_eq_of_lt (hi'.2 a)]
  obtain ⟨p, hp, pp, _, pv, pf⟩ := BoxProduct.exec hw (show m ≤ 21 * m by omega) ht
    true X Y qs v
    (fun a ha hb => (vinput a (by omega)).trans (BoxProduct.input_prefix true X Y qs a ha hb))
    ((vinput _ (by omega)).trans (BoxProduct.input_threshold true X Y qs))
    hXabs hYabs hbits hmag hbudget'
  have hp' : ExecWithin (sourceWidth N qs.length) (BoxProduct.program true) v p
      (BoxProduct.timeBound (21 * m) m t qs) := by
    simpa only [htwo] using hp
  have hwindow : Fits W (b + 2 ^ sourceWidth N qs.length) := hfit.of_le (by
    change b + windowSize N qs.length ≤ _
    omega)
  obtain ⟨y, hy, ymatch, yframe⟩ := MemoryWindow.execWithin hp'
    (BoxProduct.not_readsWidth true) sbound smatch (setup_fits hfit).1 hwindow
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have hI : Fits W (QueriedProduct.inputEnd m N qs.length + 1) := by
    have hlen := hi'.2 0
    change (Data.init (BoxProduct.input true (21 * m) t X Y qs) : Data 160).mem 0 < _ at hlen
    rw [Data.init_mem_zero, BoxProduct.input_length] at hlen
    exact hfit.of_le (by change _ ≤ b + 4 * (2 ^ sourceWidth N qs.length) + 1024; omega)
  let z := (y.set Reg.third 1).set Reg.inputSize (QueriedProduct.inputEnd m N qs.length + 1)
  have yI : y.regs Reg.inputSize = QueriedProduct.inputEnd m N qs.length :=
    (ymatch.regs _).trans pp.inputSize
  have hz : ExecWithin W includeThreshold y z 2 := by
    ram_eval [includeThreshold, z, yI, h1, hI, Reg.third, Reg.inputSize,
      QueriedProduct.Reg.inputSize, Fin.mk.injEq]
  have yb : y.regs Reg.base = b := ymatch.base_eq
  have yM : y.regs Reg.modulus = windowSize N qs.length := ymatch.modulus_eq
  refine ⟨z, (hs.seq (hy.seq hz)).mono (by unfold coreTime; omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa +decide [z, Reg.base, Reg.third, Reg.inputSize, QueriedProduct.Reg.inputSize,
      Function.update_apply] using yb
  · simpa +decide [z, Reg.modulus, Reg.third, Reg.inputSize, QueriedProduct.Reg.inputSize,
      Function.update_apply] using yM
  · simp [z]
  · simpa +decide [z, Reg.queryCount, Reg.third, Reg.inputSize, QueriedProduct.Reg.inputSize,
      QueriedProduct.Reg.queryCount, Function.update_apply] using
      (ymatch.regs QueriedProduct.Reg.queryCount).trans pp.queryCount
  · simpa +decide [z, Reg.output, Reg.third, Reg.inputSize, QueriedProduct.Reg.inputSize,
      QueriedProduct.Reg.output, Function.update_apply] using
      (ymatch.regs QueriedProduct.Reg.output).trans pp.output
  · intro i
    exact (ymatch.mem _).trans (pv i)
  · intro a ha
    change y.mem (b + a) % 2 ^ sourceWidth N qs.length = _
    rw [ymatch.mem, pf a (by omega)]
    change s.mem (b + a) % 2 ^ sourceWidth N qs.length = _
    rw [smem, hinput a ha, Nat.mod_eq_of_lt (hi'.2 a)]
  · intro a ha
    exact (yframe a ha).trans (congrFun smem a)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBoxProduct
