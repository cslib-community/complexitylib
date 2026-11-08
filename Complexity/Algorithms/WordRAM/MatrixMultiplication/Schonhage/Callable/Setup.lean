/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import Complexity.Computability.WordRAM.Power.Rename
import Complexity.Computability.WordRAM.RegisterFrame
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Program
import Complexity.Tactic.Fits

/-!
# Computed virtual width and register normalization

Setup reads the actual original headers and executes the existing ceiling-logarithm and
natural-power programs. No logarithm, modulus, bounded initial scratch or source register
certificate is supplied in the input.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct

open Cslib.WordRAM

private theorem clogBank_injective : Function.Injective clogBank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 163 => k.val) h)

private theorem powerBank_injective : Function.Injective powerBank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 163 => k.val) h)

/-- The explicit physical numerical margin covers setup and the smaller native source width. -/
theorem setup_fits {W b N Q : ℕ} (hfit : Fits W (b + 4 * windowSize N Q + 1024)) :
    sourceWidth N Q ≤ W ∧ N + Q + 3 ≤ windowSize N Q ∧
      sourceWidth N Q < windowSize N Q := by
  have hlog : Nat.clog 2 (N + Q + 3) ≤ sourceWidth N Q := by unfold sourceWidth; omega
  have hp : N + Q + 3 ≤ windowSize N Q :=
    (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) hlog)
  have hwidth : sourceWidth N Q < windowSize N Q := Nat.lt_two_pow_self
  refine ⟨?_, hp, hwidth⟩
  by_contra h
  have hW : W ≤ sourceWidth N Q := by omega
  have he := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hW
  unfold Fits windowSize at hfit
  omega

/-- Actual setup computes the modulus, normalizes the fixed source register bank and preserves
every caller memory word. Its charge is logarithmic in original dimensions and query count. -/
theorem exec_setup {W b N Q : ℕ} (x : Data 163) (hb : x.regs Reg.base = b)
    (hN : x.mem (b + 3) = N) (hQ : x.mem (b + 4) = Q)
    (hfit : Fits W (b + 4 * windowSize N Q + 1024)) :
    ∃ y, ExecWithin W setup x y (517 * Nat.clog 2 (N + Q + 3) + 184) ∧
      y.mem = x.mem ∧
      MemoryWindow.Matches (sourceWidth N Q) b
        (MemoryWindow.view (sourceWidth N Q) b y) y ∧
      (MemoryWindow.view (sourceWidth N Q) b y).Bounded (sourceWidth N Q) := by
  change x.regs (160 : Fin 163) = b at hb
  obtain ⟨hw, hS, hwidth⟩ := setup_fits hfit
  have hc : Nat.clog 2 (N + Q + 3) ≤ sourceWidth N Q := by unfold sourceWidth; omega
  have h0 : Fits W 0 := fits_zero _
  have h2 : Fits W 2 := by fits
  have h3 : Fits W 3 := by fits
  have h4 : Fits W 4 := by fits
  have h128 : Fits W 128 := by fits
  have hb3 : Fits W (b + 3) := by fits
  have hb4 : Fits W (b + 4) := by fits
  have hsum : Fits W (N + Q) := by fits
  have hsize : Fits W (N + Q + 3) := by fits
  have hexp : Fits W (128 * Nat.clog 2 (N + Q + 3)) := by
    apply hfit.of_le
    change sourceWidth N Q ≤ _
    omega
  have hpfit : Fits W (2 ^ (128 * Nat.clog 2 (N + Q + 3)) +
      128 * Nat.clog 2 (N + Q + 3) + 2) := by
    apply hfit.of_le
    change windowSize N Q + sourceWidth N Q + 2 ≤ _
    omega
  obtain ⟨s, hs, ss, sm, sb⟩ :
      ∃ s, ExecWithin W readSize x s 9 ∧ s.regs Reg.result = N + Q + 3 ∧
        s.mem = x.mem ∧ s.regs Reg.base = b := by
    refine ⟨?s, ?run, ?result, ?memory, ?base⟩
    case run => ram_eval [readSize, hb, hN, hQ, h3, h4, hb3, hb4, hsum, hsize,
        Reg.result, Reg.second, Reg.base, Reg.address, Fin.mk.injEq]
    case result => simp +decide
    case memory => rfl
    case base => simpa +decide [Reg.base, Function.update_apply] using hb
  obtain ⟨l, hl, lr, lm, lo, lt⟩ := NatClog.exec_rename clogBank clogBank_injective s h2
    (by change Fits W (s.regs Reg.result + 1); rw [ss]; fits)
    (by change Fits W (Nat.clog 2 (s.regs Reg.result) + 1); rw [ss]; fits)
  have lc : l.regs Reg.second = Nat.clog 2 (N + Q + 3) := by
    change l.regs Reg.second = Nat.clog 2 (s.regs Reg.result) at lr
    simpa only [ss] using lr
  have lb : l.regs Reg.base = b := (hl.regs_eq
    (NatClog.program.preserves_rename_of_offset (offset := 0) clogBank
      (fun j => (Nat.zero_add j.val).symm) Reg.base (Or.inr (by decide)))).trans sb
  let p := ((l.set Reg.third 128).set Reg.fourth
    (Nat.clog 2 (N + Q + 3) * 128)).set Reg.third 2
  have hexp' : Fits W (Nat.clog 2 (N + Q + 3) * 128) := by
    simpa only [Nat.mul_comm] using hexp
  have hprep : ExecWithin W
      (ram[ Reg.third ← #128; Reg.fourth ← Reg.second * Reg.third; Reg.third ← #2 ]) l p 3 := by
    ram_eval [p, lc, h128, h2, hexp', Reg.third, Reg.fourth, Reg.second,
      Fin.mk.injEq]
  obtain ⟨z, hz, zv, _, _, am, _, _, hframe⟩ :=
    Power.exec_rename powerBank powerBank_injective (w := W) 2
      (128 * Nat.clog 2 (N + Q + 3)) (by decide) p
      (by simp [p, powerBank, Power.base, Reg.third, Reg.fourth])
      (by simp [p, powerBank, Power.exponent, Reg.third, Reg.fourth, Nat.mul_comm]) hpfit
  change z.regs Reg.result = windowSize N Q at zv
  have zb : z.regs Reg.base = b := by
    have hp : p.regs Reg.base = b := by
      simpa [p, Reg.base, Reg.third, Reg.fourth, Function.update_apply, Fin.mk.injEq] using lb
    refine (hframe _ ?_).trans hp
    intro i hi
    have hv := congrArg (fun k : Fin 163 => k.val) hi
    simp only [powerBank, Reg.base, Fin.val_castAdd] at hv
    omega
  let z' := z.set Reg.modulus (windowSize N Q)
  have hcopy : ExecWithin (B := .standard) W (.op (.copy Reg.modulus Reg.result)) z z' 1 := by
    simpa only [z', zv] using
      (ExecWithin.copy (B := .standard) (w := W) (x := z) (d := Reg.modulus) (s := Reg.result))
  have z'b : z'.regs Reg.base = b := by
    simpa [z', Reg.base, Reg.modulus,
      Function.update_apply, Fin.mk.injEq] using zb
  have z'm : z'.regs Reg.modulus = 2 ^ sourceWidth N Q := by simp [z', windowSize]
  obtain ⟨y, hy, ym, ymatch, ybound, yr⟩ := MemoryWindow.exec_normalizeRegisters
    z' z'b z'm hw
  refine ⟨y, ?_, ?_, ymatch, ybound⟩
  · apply (hs.seq (hl.seq (hprep.seq (hz.seq (hcopy.seq hy))))).mono
    change 9 + (5 * Nat.clog 2 (s.regs Reg.result) + 5 + _) ≤ _
    rw [ss]
    omega
  · exact ym.trans (am.trans (lm.trans sm))

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct
