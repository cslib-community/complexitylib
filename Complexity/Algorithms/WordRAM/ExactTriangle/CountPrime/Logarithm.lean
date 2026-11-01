/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Program

/-!
# Computed native CountPrime depth

The actual runtime original side is copied into the existing native ceiling-logarithm
routine. Four constants, the call, and copying its result into the counter metadata are
charged. No depth/logarithm certificate or precomputed padding parameter is supplied.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- Compute the real ceiling binary logarithm and establish the four native constants.
All original counter argument registers and memory are preserved. -/
theorem exec_logarithm {w : ℕ} (x : Data 128)
    (hw : Fits w (x.regs Reg.side + Nat.clog 2 (x.regs Reg.side) + 8)) :
    ∃ y, ExecWithin w logarithm x y (5 * Nat.clog 2 (x.regs Reg.side) + 11) ∧
      y.regs Reg.depth = Nat.clog 2 (x.regs Reg.side) ∧
      y.regs Reg.zero = 0 ∧ y.regs Reg.one = 1 ∧ y.regs Reg.two = 2 ∧ y.regs Reg.four = 4 ∧
      y.mem = x.mem ∧
      ∀ i, 4 ≤ i.val → i ≠ Reg.depth → i ≠ Reg.zero → i ≠ Reg.one →
        i ≠ Reg.two → i ≠ Reg.four → y.regs i = x.regs i := by
  let K := Nat.clog 2 (x.regs Reg.side)
  let z := ((((x.set Reg.zero 0).set Reg.one 1).set Reg.two 2).set Reg.four 4).set
    Reg.low0 (x.regs Reg.side)
  have hargs : ExecWithin (B := .standard) w
      (ram[ Reg.zero ← #0; Reg.one ← #1; Reg.two ← #2; Reg.four ← #4;
        Reg.low0 ← Reg.side ]) x z 5 := by
    ram_eval [z, hw.of_le (show 0 ≤ _ by omega), hw.of_le (show 1 ≤ _ by omega),
      hw.of_le (show 2 ≤ _ by omega), hw.of_le (show 4 ≤ _ by omega),
      Reg.zero, Reg.one, Reg.two, Reg.four, Reg.low0, Reg.side]
  let f : Fin 4 → Fin 128 := Fin.castLE (by decide)
  have harg : (z.comap f).regs NatClog.arg = x.regs Reg.side := by
    simp [z, f, Data.comap, NatClog.arg, Reg.low0]
  obtain ⟨s, hs, result, memory, _, _⟩ := NatClog.exec (z.comap f)
    (hw.of_le (by omega))
    (by rw [harg]; exact hw.of_le (by omega))
    (by rw [harg]; exact hw.of_le (by omega))
  let t := s.extend f z
  have hcall : ExecWithin w (NatClog.program.rename f) z t (5 * K + 5) := by
    simpa only [harg] using hs.rename (Fin.castLE_injective _)
  have tresult : t.regs Reg.low1 = K := by
    change Function.extend f s.regs z.regs (f NatClog.result) = K
    rw [(Fin.castLE_injective _).extend_apply]
    simpa only [harg] using result
  have tm : t.mem = x.mem := memory
  have thigh (i : Fin 128) (hi : 4 ≤ i.val) : t.regs i = z.regs i := by
    apply Function.extend_apply'
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega
  let y := t.set Reg.depth K
  have hlast : ExecWithin (B := .standard) w (ram[ Reg.depth ← Reg.low1 ]) t y 1 := by
    simpa only [y, tresult] using (ExecWithin.copy (B := .standard) (w := w)
      (d := Reg.depth) (s := Reg.low1) (x := t))
  have he : ExecWithin w logarithm x y (5 * K + 11) := by
    obtain ⟨n, hn, argsRun⟩ := hargs
    obtain ⟨m, hm, restRun⟩ := hcall.seq hlast
    cases argsRun with
    | seq h₁ rest₁ => cases rest₁ with
      | seq h₂ rest₂ => cases rest₂ with
        | seq h₃ rest₃ => cases rest₃ with
          | seq h₄ h₅ =>
            exact ⟨_, by omega, .seq h₁ (.seq h₂ (.seq h₃ (.seq h₄ (.seq h₅ restRun))))⟩
  refine ⟨y, he, ?_, ?_, ?_, ?_, ?_, tm, ?_⟩
  · rfl
  · simp only [y, Data.set, Function.update_of_ne (show Reg.zero ≠ Reg.depth by decide),
      thigh Reg.zero (by decide)]
    simp +decide [z, Reg.zero, Reg.one, Reg.two, Reg.four, Reg.low0]
  · simp only [y, Data.set, Function.update_of_ne (show Reg.one ≠ Reg.depth by decide),
      thigh Reg.one (by decide)]
    simp +decide [z, Reg.zero, Reg.one, Reg.two, Reg.four, Reg.low0]
  · simp only [y, Data.set, Function.update_of_ne (show Reg.two ≠ Reg.depth by decide),
      thigh Reg.two (by decide)]
    simp +decide [z, Reg.zero, Reg.one, Reg.two, Reg.four, Reg.low0]
  · simp only [y, Data.set, Function.update_of_ne (show Reg.four ≠ Reg.depth by decide),
      thigh Reg.four (by decide)]
    simp +decide [z, Reg.zero, Reg.one, Reg.two, Reg.four, Reg.low0]
  · intro i hi hd h0 h1 h2 h4
    simp only [y, Data.set, Function.update_of_ne hd, thigh i hi, z,
      Function.update_of_ne (show i ≠ Reg.low0 by intro he; subst i; contradiction),
      Function.update_of_ne h0, Function.update_of_ne h1,
      Function.update_of_ne h2, Function.update_of_ne h4]

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
