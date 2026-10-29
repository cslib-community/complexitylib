/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Program

/-!
# Relocated native copy and queried-product calls

All registers of each existing native program are renamed together. Memory relocation is
performed by the callable product's actual address compiler, not by register renaming.
These internal execution rules preserve the low producer bank and full outside-memory frame.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open Cslib.Algorithms.MatrixMultiplication.Schonhage

theorem copyBank_injective : Function.Injective copyBank := by
  intro i j h
  apply Fin.ext
  simpa only [copyBank, Nat.add_left_cancel_iff] using congrArg Fin.val h

theorem calleeBank_injective : Function.Injective calleeBank := by
  intro i j h
  apply Fin.ext
  simpa only [calleeBank, Nat.add_left_cancel_iff] using congrArg Fin.val h

/-- The real copy loop preserves all adapter metadata and the complete producer register bank. -/
theorem exec_copy {W s d n : ℕ} (x : Data 320)
    (hs : x.regs Reg.source = s) (hd : x.regs Reg.destination = d)
    (hn : x.regs Reg.length = n) (hsep : s + n ≤ d)
    (hfit : Fits W (s + d + n + 2)) :
    ∃ y, ExecWithin W copy x y (7 * n + 4) ∧
      y.mem = ArrayCopy.copyPrefix x.mem s d n ∧
      y.regs Reg.source = s ∧ y.regs Reg.destination = d ∧ y.regs Reg.length = n ∧
      ∀ i : Fin 320, i.val < 96 ∨ 103 ≤ i.val → y.regs i = x.regs i := by
  have hs' : (x.comap copyBank).regs ArrayCopy.src = s := hs
  have hd' : (x.comap copyBank).regs ArrayCopy.dst = d := hd
  have hn' : (x.comap copyBank).regs ArrayCopy.len = n := hn
  obtain ⟨a, ha, am, asrc, adst, alen⟩ := ArrayCopy.exec (x.comap copyBank)
    (hfit.of_le (by omega))
    (by rw [hs', hn']; exact hfit.of_le (by omega))
    (by rw [hd', hn']; exact hfit.of_le (by omega)) (by simpa only [hs', hd', hn'] using hsep)
  refine ⟨a.extend copyBank x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [copy, hn'] using ha.rename copyBank_injective
  · simpa only [Data.extend, Data.comap_mem, hs', hd', hn'] using am
  · exact (copyBank_injective.extend_apply _ _ ArrayCopy.src).trans (asrc.trans hs')
  · exact (copyBank_injective.extend_apply _ _ ArrayCopy.dst).trans (adst.trans hd')
  · exact (copyBank_injective.extend_apply _ _ ArrayCopy.len).trans (alen.trans hn')
  · intro i hi
    apply Function.extend_apply'
    rintro ⟨j, hj⟩
    have h := congrArg Fin.val hj
    change 96 + j.val = i.val at h
    omega

/-- The concrete original-input callee derives its execution from the matrices and coordinate
occurrences. No execution or time certificate is accepted by this invocation rule. -/
theorem exec_invoke {W b m N : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 320) (hb : x.regs Reg.base = b)
    (hinput : ∀ a, a < QueriedProduct.inputEnd m N qs.length →
      x.mem (b + a) =
        (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem a)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (hN : D m ^ 18 ≤ N) (hfit : Fits W (b + 4 * CallableProduct.windowSize N qs.length + 1024)) :
    ∃ y, ExecWithin W invoke x y (CallableProduct.timeBound (m := m) qs + 2) ∧
      y.regs Reg.result = b + QueriedProduct.outputBase (19 * m) m N qs.length ∧
      (∀ i : Fin qs.length,
        y.mem (b + (QueriedProduct.outputBase (19 * m) m N qs.length + i.val)) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < QueriedProduct.inputEnd m N qs.length → y.mem (b + a) = x.mem (b + a)) ∧
      (∀ a, a < b ∨ b + CallableProduct.windowSize N qs.length ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin 320, i.val < 128 → i ≠ Reg.result → y.regs i = x.regs i := by
  let z := x.set (calleeBank CallableProduct.Reg.base) b
  have hz : ExecWithin (B := .standard) W
      (.op (.copy (calleeBank CallableProduct.Reg.base) Reg.base)) x z 1 := by
    simpa only [z, hb] using
      (ExecWithin.copy (w := W) (x := x) (d := calleeBank CallableProduct.Reg.base)
        (s := Reg.base))
  have zb : (z.comap calleeBank).regs CallableProduct.Reg.base = b := by simp [z]
  obtain ⟨a, ha, ar, ab, aM, av, ai, af⟩ :=
    CallableProduct.exec X Y qs (z.comap calleeBank) zb hinput hX hY hN hfit
  let c := a.extend calleeBank z
  have hc : ExecWithin W (CallableProduct.program.rename calleeBank) z c
      (CallableProduct.timeBound (m := m) qs) := ha.rename calleeBank_injective
  have cr : c.regs (calleeBank CallableProduct.Reg.result) =
      b + QueriedProduct.outputBase (19 * m) m N qs.length :=
    (calleeBank_injective.extend_apply _ _ _).trans ar
  let y := c.set Reg.result (b + QueriedProduct.outputBase (19 * m) m N qs.length)
  have hy : ExecWithin (B := .standard) W
      (.op (.copy Reg.result (calleeBank CallableProduct.Reg.result))) c y 1 := by
    simpa only [y, cr] using (ExecWithin.copy (w := W) (x := c) (d := Reg.result)
      (s := calleeBank CallableProduct.Reg.result))
  refine ⟨y, ?_, by simp [y], av, ai, af, ?_⟩
  · exact (hz.seq (hc.seq hy)).mono (by omega)
  · intro i hi hne
    have hbank : ¬∃ j, calleeBank j = i := by
      rintro ⟨j, hj⟩
      have h := congrArg Fin.val hj
      change 128 + j.val = i.val at h
      omega
    have hiz : i ≠ calleeBank CallableProduct.Reg.base := by
      intro h
      exact hbank ⟨_, h.symm⟩
    simp only [y, Data.set_regs, Function.update_of_ne hne, c, Data.extend,
      Function.extend_apply' _ _ _ hbank, z, Function.update_of_ne hiz]

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
