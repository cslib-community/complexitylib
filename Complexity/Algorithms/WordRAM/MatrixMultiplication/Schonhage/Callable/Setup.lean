/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Program

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
  have h2 : Fits W 2 := hfit.of_le (by omega)
  have h3 : Fits W 3 := hfit.of_le (by omega)
  have h4 : Fits W 4 := hfit.of_le (by omega)
  have h128 : Fits W 128 := hfit.of_le (by omega)
  have hb3 : Fits W (b + 3) := hfit.of_le (by omega)
  have hb4 : Fits W (b + 4) := hfit.of_le (by omega)
  have hsum : Fits W (N + Q) := hfit.of_le (by omega)
  have hsize : Fits W (N + Q + 3) := hfit.of_le (by omega)
  have hs1 : Fits W (N + Q + 3 + 1) := hfit.of_le (by omega)
  have hc1 : Fits W (Nat.clog 2 (N + Q + 3) + 1) := hfit.of_le (by omega)
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
    (by change Fits W (s.regs Reg.result + 1); rw [ss]; exact hs1)
    (by change Fits W (Nat.clog 2 (s.regs Reg.result) + 1); rw [ss]; exact hc1)
  have lc : l.regs Reg.second = Nat.clog 2 (N + Q + 3) := by
    change l.regs Reg.second = Nat.clog 2 (s.regs Reg.result) at lr
    simpa only [ss] using lr
  have lb : l.regs Reg.base = b := (hl.regs_eq (by
    simp [NatClog.program, NatClog.body, Code.rename, Code.Preserves, Op.rename, Op.dest, Op.bin,
      clogBank, Reg.base, NatClog.result, NatClog.arg,
      NatClog.one, NatClog.two])).trans sb
  let p := ((l.set Reg.third 128).set Reg.fourth
    (Nat.clog 2 (N + Q + 3) * 128)).set Reg.third 2
  have hexp' : Fits W (Nat.clog 2 (N + Q + 3) * 128) := by
    simpa only [Nat.mul_comm] using hexp
  have hprep : ExecWithin W
      (ram[ Reg.third ← #128; Reg.fourth ← Reg.second * Reg.third; Reg.third ← #2 ]) l p 3 := by
    ram_eval [p, lc, h128, h2, hexp', Reg.third, Reg.fourth, Reg.second,
      Fin.mk.injEq]
  obtain ⟨a, ha, av, ac, ao, am, ab, ae⟩ := Power.exec (w := W) 2
    (128 * Nat.clog 2 (N + Q + 3)) (by decide) (p.comap powerBank)
    (by simp [p, powerBank, Power.base, Reg.third, Reg.fourth])
    (by simp [p, powerBank, Power.exponent, Reg.third, Reg.fourth, Nat.mul_comm]) hpfit
  let z := a.extend powerBank p
  have hz : ExecWithin W (Power.program.rename powerBank) p z
      (4 * (128 * Nat.clog 2 (N + Q + 3)) + 5) := ha.rename powerBank_injective
  have zv : z.regs Reg.result = windowSize N Q :=
    (powerBank_injective.extend_apply _ _ Power.value).trans av
  have zb : z.regs Reg.base = b := by
    have hnot : ¬∃ i, powerBank i = Reg.base := by
      rintro ⟨i, hi⟩
      have := congrArg (fun k : Fin 163 => k.val) hi
      simp only [powerBank, Reg.base, Fin.val_castAdd] at this
      omega
    change Function.extend powerBank a.regs p.regs Reg.base = b
    rw [Function.extend_apply' _ _ _ hnot]
    simpa [p, Reg.base, Reg.third, Reg.fourth,
      Function.update_apply, Fin.mk.injEq] using lb
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
