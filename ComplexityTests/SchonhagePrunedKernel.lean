/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Kernel

/-! A callable signed native instance with a nonzero epoch and preserved outside memory. -/

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

namespace ComplexityTests.SchonhagePrunedKernel

private def caller : Data registers where
  regs i := match i.val with
    | 9 => 1 | 11 => 3 | 12 => 13 | 13 => 23 | 14 => 1 | 15 => 24 | 16 => 25 | 17 => 7
    | _ => 0
  mem c := if c = 1000 then 91 else if 3 ≤ c ∧ c < 13 then encode (-2) else
    if 13 ≤ c ∧ c < 23 then encode 3 else if c = 23 then 9 else 0

private def wildcard : Fin 1 → Cslib.Algorithms.MatrixMultiplication.Schonhage.OutStr 1 :=
  fun _ => ![.z0]

-- The kernel itself computes powers, layout, all ten contributing children and their stored
-- requests. The returned epoch/directory are ready for the next caller, without a dense clear.
example : ∃ y, ExecWithin 13 kernel caller y
      (4 + 29 + traceWeight (Finset.univ.image wildcard) + 41) ∧
    y.Bounded 13 ∧ y.mem 24 = encode (-60) ∧ y.mem 3 = encode (-2) ∧ y.mem 1000 = 91 ∧
    8 ≤ y.regs epoch ∧ y.regs epoch ≤ 26 ∧ ∀ q < 10, y.mem (73 + q) ≤ y.regs epoch := by
  have hbounded : caller.Bounded 13 := by
    constructor
    · intro i
      fin_cases i <;> decide
    · intro c
      dsimp only [caller]
      split_ifs <;> decide
  obtain ⟨y, hy, hv, hf, _, hel, heu, htable⟩ := exec_kernel (w := 11) (L := 1)
    (f := 25) (a0 := 3) (b0 := 13) (q0 := 23) (o0 := 24) (Q := 1) (E := 7)
    (A := 2) (B := 3) (fun _ => -2) (fun _ => 3)
    wildcard caller rfl rfl rfl rfl rfl rfl rfl rfl
    (by intro i; fin_cases i; decide +kernel)
    (by
      intro v
      have h := (Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding.leafIndex v).isLt
      dsimp only [caller]
      split_ifs <;> first | rfl | omega)
    (by
      intro v
      have h := (Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding.leafIndex v).isLt
      dsimp only [caller]
      split_ifs <;> first | rfl | omega)
    (by decide) (by decide) (by decide) (by decide)
    (by
      intro q hq
      dsimp only [caller]
      split_ifs <;> first | decide | omega)
    (by intro v; decide) (by intro v; decide) (by decide) (by decide) (by decide)
  refine ⟨y, hy, hy.bounded hbounded, ?_, ?_, ?_, hel, heu, htable⟩
  · have hr := hv (0 : Fin 1)
    have hm : Cslib.Algorithms.MatrixMultiplication.Schonhage.Pruned.result 1
        (fun _ => -2) (fun _ => 3)
        (Finset.univ.image wildcard) ![.z0] = -60 := by
      decide +kernel
    exact hr.trans (congrArg encode hm)
  · exact (hf 3 (by decide) (by decide)).trans rfl
  · exact (hf 1000 (by decide) (by decide)).trans rfl

end ComplexityTests.SchonhagePrunedKernel
