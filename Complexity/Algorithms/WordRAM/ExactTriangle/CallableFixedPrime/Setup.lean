/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Properties

/-!
# Computed modulus and normalized source bank

The native setup executes the ceiling logarithm and power loops on the actual copied-word
sum. It normalizes only the fixed source register bank. Every memory word, original argument
and selector register is preserved; no clean window or precomputed modulus is supplied.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM

/-- The explicit physical margin covers the source width, scalar-size sum and power setup. -/
theorem setup_fits {W b n D g p total : ℕ}
    (hfit : Fits W (b + 4 * windowSize n D g p total + 1024)) :
    sourceWidth n D g p total ≤ W ∧
      n + D + g + p + total + 4 ≤ windowSize n D g p total ∧
      sourceWidth n D g p total < windowSize n D g p total ∧
      6166 ≤ windowSize n D g p total := by
  obtain ⟨hsize, hwidth, h6166⟩ := source_bounds n D g p total
  refine ⟨?_, hsize, hwidth, h6166⟩
  by_contra h
  have hW : W ≤ sourceWidth n D g p total := by omega
  have he := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hW
  unfold Fits windowSize at hfit
  omega

private theorem clogBank_injective : Function.Injective clogBank := by
  intro i j h
  have hv := congrArg Fin.val h
  exact Fin.ext (by simpa only [clogBank] using Nat.add_left_cancel hv)

private theorem powerBank_injective : Function.Injective powerBank := by
  intro i j h
  have hv := congrArg Fin.val h
  exact Fin.ext (by simpa only [powerBank] using Nat.add_left_cancel hv)

/-- Actual computed setup at every admitted physical width. Register normalization is charged
and source fits are postconditions of that code, not final caller assumptions. -/
theorem exec_setup {W : ℕ} (x : Data 640)
    (hfit : Fits W (x.regs Reg.base +
      4 * windowSize (x.regs Reg.n) (x.regs Reg.dimension) (x.regs Reg.groups)
        (x.regs Reg.prime) (x.regs Reg.total) + 1024)) :
    let n := x.regs Reg.n
    let D := x.regs Reg.dimension
    let g := x.regs Reg.groups
    let p := x.regs Reg.prime
    let total := x.regs Reg.total
    ∃ y, ExecWithin W setup x y
        (24669 * Nat.clog 2 (n + D + g + p + total + 4) + 439) ∧
      y.mem = x.mem ∧
      y.regs (sourceBank MemoryWindow.Reg.base) = x.regs Reg.base ∧
      y.regs (sourceBank MemoryWindow.Reg.modulus) = windowSize n D g p total ∧
      (∀ i : Fin 416, Fits (sourceWidth n D g p total) (y.regs (sourceReg i))) ∧
      ∀ j : Fin 640, j.val < 160 ∨ (600 ≤ j.val ∧ j.val < 608) → y.regs j = x.regs j := by
  let n := x.regs Reg.n
  let D := x.regs Reg.dimension
  let g := x.regs Reg.groups
  let p := x.regs Reg.prime
  let total := x.regs Reg.total
  let b := x.regs Reg.base
  let S := n + D + g + p + total + 4
  have fit : Fits W (b + 4 * windowSize n D g p total + 1024) := hfit
  obtain ⟨hw, hS, hwidth, h6166⟩ := setup_fits fit
  have h2 : Fits W 2 := fit.of_le (by omega)
  have h4 : Fits W 4 := fit.of_le (by omega)
  have hc : Fits W 6166 := fit.of_le (by omega)
  have hsize : Fits W S := fit.of_le (by omega)
  have hsize' : Fits W (S + 1) := fit.of_le (by omega)
  have hlog : Nat.clog 2 S ≤ sourceWidth n D g p total := by dsimp only [sourceWidth, S]; omega
  have hlog' : Fits W (Nat.clog 2 S + 1) := fit.of_le (by omega)
  have hexp : Fits W (Nat.clog 2 S * 6166) := fit.of_le (by
    have he : Nat.clog 2 S * 6166 = sourceWidth n D g p total := by
      dsimp only [sourceWidth, S]
      omega
    rw [he]
    omega)
  have hpfit : Fits W (2 ^ sourceWidth n D g p total + sourceWidth n D g p total + 2) :=
    fit.of_le (by change windowSize n D g p total + _ + 2 ≤ _; omega)
  have hND : Fits W (n + D) := hsize.of_le (by dsimp only [S]; omega)
  have hNDg : Fits W (n + D + g) := hsize.of_le (by dsimp only [S]; omega)
  have hNDgp : Fits W (n + D + g + p) := hsize.of_le (by dsimp only [S]; omega)
  have hNDgpt : Fits W (n + D + g + p + total) := hsize.of_le (by dsimp only [S]; omega)
  obtain ⟨s, hs, sval, smem, sbase⟩ :
      ∃ s, ExecWithin W sizeArgument x s 7 ∧ s.regs (clogBank 0) = S ∧
        s.mem = x.mem ∧ s.regs Reg.base = b := by
    refine ⟨?s, ?run, ?value, ?mem, ?base⟩
    case run => ram_eval [sizeArgument, clogBank, n, D, g, p, total, S, h4, hND, hNDg,
      hNDgp, hNDgpt, hsize, Reg.n, Reg.dimension, Reg.groups, Reg.prime, Reg.total,
      Fin.mk.injEq]
    case value => simp +decide [S, n, D, g, p, total, clogBank]
    case mem => rfl
    case base => simp +decide [b, Reg.base]
  obtain ⟨l, hl, lval, lmem, -, -⟩ := NatClog.exec_rename clogBank clogBank_injective s h2
    (by change Fits W (s.regs (clogBank 0) + 1); rw [sval]; exact hsize')
    (by change Fits W (Nat.clog 2 (s.regs (clogBank 0)) + 1); rw [sval]; exact hlog')
  have hl' : ExecWithin W (NatClog.program.rename clogBank) s l
      (5 * Nat.clog 2 S + 5) := by simpa only [sval] using hl
  have lc : l.regs (clogBank 1) = Nat.clog 2 S := by simpa only [sval] using lval
  have lb : l.regs Reg.base = b := (hl.regs_eq (by
    apply Code.preserves_rename_of_forall_ne
    intro i he
    have hv := congrArg Fin.val he
    change 620 + i.val = 607 at hv
    omega)).trans sbase
  let a := ((l.set (powerBank 2) 6166).set (powerBank 3)
    (Nat.clog 2 S * 6166)).set (powerBank 2) 2
  have ha : ExecWithin W powerArguments l a 3 := by
    let a₁ := l.set (powerBank 2) 6166
    have hconst : ExecWithin (B := .standard) W
        (.op (.const (powerBank 2) 6166)) l a₁ 1 := ExecWithin.const hc
    have hv₁ : a₁.regs (clogBank 1) = Nat.clog 2 S := by
      simpa [a₁, powerBank, clogBank] using lc
    have hc₁ : a₁.regs (powerBank 2) = 6166 :=
      Function.update_self (powerBank 2) 6166 l.regs
    have hmul : ExecWithin W
        (.op (.bin .mul (powerBank 3) (clogBank 1) (powerBank 2))) a₁
        (a₁.set (powerBank 3) (Nat.clog 2 S * 6166)) 1 := by
      simpa only [BinOp.eval, hv₁, hc₁] using
        (ExecWithin.bin (w := W) (f := .mul) (d := powerBank 3)
          (i := clogBank 1) (j := powerBank 2) (x := a₁)
          (by simpa only [BinOp.eval, hv₁, hc₁] using hexp))
    exact hconst.seq (hmul.seq (ExecWithin.const h2))
  have ab : a.regs Reg.base = b := by
    simpa [a, powerBank, Reg.base, Function.update_apply] using lb
  obtain ⟨v, hv, vv, -, -, vm, -, -⟩ := Power.exec (w := W) 2
    (sourceWidth n D g p total) (by decide) (a.comap powerBank)
    (by simp [a, powerBank, Power.base])
    (by simp [a, powerBank, Power.exponent, sourceWidth, S, Nat.mul_comm]) hpfit
  let z := v.extend powerBank a
  have hz : ExecWithin W (Power.program.rename powerBank) a z
      (4 * sourceWidth n D g p total + 5) := hv.rename powerBank_injective
  have zv : z.regs (powerBank 0) = windowSize n D g p total :=
    (powerBank_injective.extend_apply _ _ _).trans vv
  have zb : z.regs Reg.base = b := (hz.regs_eq (by
    apply Code.preserves_rename_of_forall_ne
    intro i he
    have hval := congrArg Fin.val he
    change 620 + i.val = 607 at hval
    omega)).trans ab
  let c := (z.set (sourceBank MemoryWindow.Reg.base) b).set
    (sourceBank MemoryWindow.Reg.modulus) (windowSize n D g p total)
  have hc' : ExecWithin W windowArguments z c 2 := by
    have hbase : ExecWithin (B := .standard) W
        (.op (.copy (sourceBank MemoryWindow.Reg.base) Reg.base)) z
        (z.set (sourceBank MemoryWindow.Reg.base) b) 1 := by
      simpa only [zb] using
        (ExecWithin.copy (B := .standard) (w := W) (x := z)
          (d := sourceBank MemoryWindow.Reg.base) (s := Reg.base))
    have hvalue : (z.set (sourceBank MemoryWindow.Reg.base) b).regs (powerBank 0) =
        windowSize n D g p total := by
      rw [Data.set_regs, Function.update_of_ne (by decide)]
      exact zv
    have hmodulus : ExecWithin (B := .standard) W
        (.op (.copy (sourceBank MemoryWindow.Reg.modulus) (powerBank 0)))
        (z.set (sourceBank MemoryWindow.Reg.base) b) c 1 := by
      simpa only [hvalue] using
        (ExecWithin.copy (B := .standard) (w := W)
          (x := z.set (sourceBank MemoryWindow.Reg.base) b)
          (d := sourceBank MemoryWindow.Reg.modulus) (s := powerBank 0))
    exact hbase.seq hmodulus
  have cb : c.regs (sourceBank MemoryWindow.Reg.base) = b := by
    simp +decide [c, sourceBank, MemoryWindow.Reg.base, MemoryWindow.Reg.modulus]
  have cM : c.regs (sourceBank MemoryWindow.Reg.modulus) = windowSize n D g p total := by
    simp [c]
  obtain ⟨v', hv', v'mem, v'match, v'bound, -⟩ := MemoryWindow.exec_normalizeRegisters
    (w := sourceWidth n D g p total) (W := W) (b := b) (c.comap sourceBank) cb cM hw
  let y := v'.extend sourceBank c
  have hy : ExecWithin W ((MemoryWindow.normalizeRegisters 416).rename sourceBank) c y 417 :=
    hv'.rename sourceBank_injective
  have he : ExecWithin W setup x y (24669 * Nat.clog 2 S + 439) := by
    apply (hs.seq (hl'.seq (ha.seq (hz.seq (hc'.seq hy))))).mono
    dsimp only [sourceWidth, S]
    exact le_of_eq (by ring)
  refine ⟨y, he, ?_, ?_, ?_, ?_, ?_⟩
  · exact v'mem.trans (vm.trans (lmem.trans smem))
  · exact (sourceBank_injective.extend_apply _ _ _).trans v'match.base_eq
  · exact (sourceBank_injective.extend_apply _ _ _).trans v'match.modulus_eq
  · intro i
    change Fits (sourceWidth n D g p total) (y.regs (sourceBank (i.castAdd 3)))
    rw [show y.regs (sourceBank (i.castAdd 3)) = v'.regs (i.castAdd 3) from
      sourceBank_injective.extend_apply _ _ _]
    exact v'bound.1 i
  · intro j hj
    obtain ⟨-, hj', -, -⟩ := program_preserves j hj
    exact he.regs_eq hj'

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
