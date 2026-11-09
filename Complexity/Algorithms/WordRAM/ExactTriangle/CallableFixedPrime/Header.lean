/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Program

/-!
# Real scalar-header stores for the caller adapter

The five stores create the existing preparation input convention in caller workspace. This
is only a fixed-size header, with no array/table initialization hidden in its specification.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM

/-- The memory after the five actual scalar-header stores. -/
@[expose] def headerMemory (mem : ℕ → ℕ) (base n D g p : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update mem
    base (n * n * 3 + 4)) (base + 1) D) (base + 2) g) (base + 3) n) (base + 4) p

/-- The unchanged original scalar registers supply every header store and length computation. -/
theorem exec_header {W : ℕ} (x : Data 640)
    (hfit : Fits W (x.regs Reg.base + 4 * (x.regs Reg.n * x.regs Reg.n) + 1024)) :
    ∃ y, ExecWithin W header x y 17 ∧
      y.regs Reg.area = x.regs Reg.n * x.regs Reg.n ∧ y.regs Reg.constant = 5 ∧
      y.mem = headerMemory x.mem (x.regs Reg.base) (x.regs Reg.n)
        (x.regs Reg.dimension) (x.regs Reg.groups) (x.regs Reg.prime) ∧
      ∀ j : Fin 640, j.val < 609 → y.regs j = x.regs j := by
  let n := x.regs Reg.n
  let b := x.regs Reg.base
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have h3 : Fits W 3 := hfit.of_le (by omega)
  have h4 : Fits W 4 := hfit.of_le (by omega)
  have h5 : Fits W 5 := hfit.of_le (by omega)
  have ha : Fits W (n * n) := hfit.of_le (by dsimp only [n]; omega)
  have hat : Fits W (n * n * 3) := hfit.of_le (by dsimp only [n]; omega)
  have hal : Fits W (n * n * 3 + 4) := hfit.of_le (by dsimp only [n]; omega)
  have hb1 : Fits W (b + 1) := hfit.of_le (by dsimp only [b]; omega)
  have hb2 : Fits W (b + 2) := hfit.of_le (by dsimp only [b]; omega)
  have hb3 : Fits W (b + 3) := hfit.of_le (by dsimp only [b]; omega)
  have hb4 : Fits W (b + 4) := hfit.of_le (by dsimp only [b]; omega)
  refine ⟨?y, ?run, ?area, ?constant, ?memory, ?regs⟩
  case run => ram_eval [header, n, b, h1, h3, h4, h5, ha, hat, hal, hb1, hb2, hb3, hb4,
    Reg.n, Reg.dimension, Reg.groups, Reg.prime, Reg.base, Reg.area, Reg.length,
    Reg.address, Reg.one, Reg.constant, Fin.mk.injEq]
  case area => simp +decide
  case constant => simp +decide
  case memory => rfl
  case regs =>
    intro j hj
    have hn (i : Fin 640) (hi : 609 ≤ i.val) : j ≠ i := by
      intro he
      have hv := congrArg Fin.val he
      omega
    simp only [Data.set_regs, Data.write_regs,
      Function.update_of_ne (hn Reg.area (by decide)),
      Function.update_of_ne (hn Reg.length (by decide)),
      Function.update_of_ne (hn Reg.address (by decide)),
      Function.update_of_ne (hn Reg.one (by decide)),
      Function.update_of_ne (hn Reg.constant (by decide))]

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
