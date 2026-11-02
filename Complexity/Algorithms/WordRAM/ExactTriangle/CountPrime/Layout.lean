/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Program

/-!
# Actual native CountPrime workspace calculation

The existing native power routine computes the padded side from the computed depth.
Ordinary arithmetic instructions then calculate every matrix/residue/spread/workspace
pointer. The register assertions below describe the actual resulting state; no layout
object is supplied to the program. All intermediate fits follow from one original-parameter
numerical envelope. This module performs no allocation, clearing or memory copy.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- Original-parameter physical envelope for real layout arithmetic and power evaluation. -/
@[expose] def layoutWordBound (n p k scratch : ℕ) : ℕ :=
  scratch + 3 * (n * n) + 2 ^ k + 4 * (4 ^ k * p) + k + 2 * p + 16

/-- The actual metadata words computed by the native layout routine. This internal
postcondition contains no execution, time or multiplication contract. -/
structure LayoutRegisters (n p k scratch : ℕ) (x : Data 128) : Prop where
  /-- Original side survives the power call and all pointer arithmetic. -/
  side_eq : x.regs Reg.side = n
  /-- Original modulus survives. -/
  modulus_eq : x.regs Reg.modulus = p
  /-- Computed depth survives. -/
  depth_eq : x.regs Reg.depth = k
  /-- Original workspace base survives. -/
  scratch_eq : x.regs Reg.scratch = scratch
  /-- Actual native power result. -/
  paddedSide_eq : x.regs Reg.paddedSide = 2 ^ k
  /-- Original matrix length. -/
  cells_eq : x.regs Reg.cells = n * n
  /-- Padded cyclic-coefficient matrix length. -/
  area_eq : x.regs Reg.area = 4 ^ k * p
  /-- Padded scalar-matrix length. -/
  paddedCells_eq : x.regs Reg.paddedCells = 4 ^ k
  /-- Canonical signed positive modulus word. -/
  encodedModulus_eq : x.regs Reg.encodedModulus = 2 * p
  /-- First actual residue block. -/
  residueAB_eq : x.regs Reg.residueAB = scratch
  /-- Second actual residue block. -/
  residueBC_eq : x.regs Reg.residueBC = scratch + n * n
  /-- Third actual residue block. -/
  residueAC_eq : x.regs Reg.residueAC = scratch + 2 * (n * n)
  /-- Actual spread table. -/
  spread_eq : x.regs Reg.spread = scratch + 3 * (n * n)
  /-- Actual first coefficient matrix. -/
  matrixP_eq : x.regs Reg.matrixP = scratch + 3 * (n * n) + 2 ^ k
  /-- Actual second coefficient matrix. -/
  matrixQ_eq : x.regs Reg.matrixQ = scratch + 3 * (n * n) + 2 ^ k + 4 ^ k * p
  /-- Actual product coefficient matrix. -/
  matrixR_eq : x.regs Reg.matrixR = scratch + 3 * (n * n) + 2 ^ k + 2 * (4 ^ k * p)
  /-- Reusable native Strassen scratch begins after all three coefficient matrices. -/
  productScratch_eq : x.regs Reg.productScratch =
    scratch + 3 * (n * n) + 2 ^ k + 3 * (4 ^ k * p)

/-- Registers actually written by layout, including the complete low power bank. -/
@[expose] def LayoutLocal (i : Fin 128) : Prop := i.val < 5 ∨ i = Reg.paddedSide ∨
  i = Reg.cells ∨ i = Reg.paddedCells ∨ i = Reg.area ∨ i = Reg.encodedModulus ∨
  i = Reg.residueAB ∨ i = Reg.residueBC ∨ i = Reg.residueAC ∨ i = Reg.spread ∨
  i = Reg.matrixP ∨ i = Reg.matrixQ ∨ i = Reg.matrixR ∨ i = Reg.productScratch

instance (i : Fin 128) : Decidable (LayoutLocal i) :=
  inferInstanceAs (Decidable (i.val < 5 ∨ i = Reg.paddedSide ∨
    i = Reg.cells ∨ i = Reg.paddedCells ∨ i = Reg.area ∨ i = Reg.encodedModulus ∨
    i = Reg.residueAB ∨ i = Reg.residueBC ∨ i = Reg.residueAC ∨ i = Reg.spread ∨
    i = Reg.matrixP ∨ i = Reg.matrixQ ∨ i = Reg.matrixR ∨ i = Reg.productScratch))

/-- Compute every layout word through actual power/arithmetic instructions. All memory and
original argument registers survive; every intermediate fit follows from original n,p,k,scratch. -/
theorem exec_layout {w n p k scratch : ℕ} (x : Data 128)
    (hp : 0 < p) (hn : x.regs Reg.side = n) (hpr : x.regs Reg.modulus = p)
    (hk : x.regs Reg.depth = k) (hs : x.regs Reg.scratch = scratch)
    (h2 : x.regs Reg.two = 2) (hw : Fits w (layoutWordBound n p k scratch)) :
    ∃ y, ExecWithin w layout x y (4 * k + 20) ∧ LayoutRegisters n p k scratch y ∧
      y.mem = x.mem ∧ ∀ i, ¬LayoutLocal i → y.regs i = x.regs i := by
  let N := 2 ^ k
  let area := 4 ^ k * p
  let z := (x.set Reg.low2 2).set Reg.low3 k
  have hargs : ExecWithin (B := .standard) w
      (ram[ Reg.low2 ← Reg.two; Reg.low3 ← Reg.depth ]) x z 2 := by
    ram_eval [z, h2, hk, Reg.low2, Reg.low3, Reg.two, Reg.depth]
  let f : Fin 5 → Fin 128 := Fin.castLE (by decide)
  obtain ⟨s, he, value, _, _, memory, _, _⟩ := Power.exec 2 k (by decide) (z.comap f)
    (by simp +decide [z, f, Data.comap, Power.base, Reg.low2, Reg.low3])
    (by simp [z, f, Data.comap, Power.exponent, Reg.low3])
    (hw.of_le (by unfold layoutWordBound; omega))
  let t := s.extend f z
  have hcall : ExecWithin w (Power.program.rename f) z t (4 * k + 5) :=
    he.rename (Fin.castLE_injective _)
  have tvalue : t.regs Reg.low0 = N := by
    change Function.extend f s.regs z.regs (f Power.value) = N
    rw [(Fin.castLE_injective _).extend_apply]
    exact value
  have thigh (i : Fin 128) (hi : 5 ≤ i.val) : t.regs i = x.regs i := by
    have ht : t.regs i = z.regs i := by
      apply Function.extend_apply'
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      change j.val = i.val at hv
      omega
    simpa only [z, Data.set,
      Function.update_of_ne (show i ≠ Reg.low2 by intro he; subst i; contradiction),
      Function.update_of_ne (show i ≠ Reg.low3 by intro he; subst i; contradiction)] using ht
  have tn := (thigh Reg.side (by decide)).trans hn
  have tp := (thigh Reg.modulus (by decide)).trans hpr
  have ts := (thigh Reg.scratch (by decide)).trans hs
  have tt := (thigh Reg.two (by decide)).trans h2
  have hsquare : N * N = 4 ^ k := by dsimp only [N]; rw [← mul_pow]; rfl
  have harea : 4 ^ k ≤ area := by
    have hm := Nat.mul_le_mul_left (4 ^ k) (Nat.succ_le_of_lt hp)
    simpa only [Nat.mul_one] using hm
  have fit (v : ℕ) (hv : v ≤ layoutWordBound n p k scratch) : Fits w v := hw.of_le hv
  refine ⟨?y, ?run, ?fields, ?memory, ?regs⟩
  case run =>
    have tailRun : ExecWithin w (ram[
      Reg.paddedSide ← Reg.low0; Reg.cells ← Reg.side * Reg.side;
      Reg.paddedCells ← Reg.paddedSide * Reg.paddedSide;
      Reg.area ← Reg.paddedCells * Reg.modulus; Reg.encodedModulus ← Reg.modulus * Reg.two;
      Reg.residueAB ← Reg.scratch; Reg.residueBC ← Reg.residueAB + Reg.cells;
      Reg.residueAC ← Reg.residueBC + Reg.cells; Reg.spread ← Reg.residueAC + Reg.cells;
      Reg.matrixP ← Reg.spread + Reg.paddedSide; Reg.matrixQ ← Reg.matrixP + Reg.area;
      Reg.matrixR ← Reg.matrixQ + Reg.area;
      Reg.productScratch ← Reg.matrixR + Reg.area ]) t ?y 13 := by
      ram_eval [area, tvalue, tn, tp, ts, tt, hsquare,
        fit (n * n) (by unfold layoutWordBound; omega),
        fit (4 ^ k) (by unfold layoutWordBound; omega),
        fit area (by unfold layoutWordBound; dsimp [area]; omega),
        fit (p * 2) (by unfold layoutWordBound; omega),
        fit (scratch + n * n) (by unfold layoutWordBound; omega),
        fit (scratch + n * n + n * n) (by unfold layoutWordBound; omega),
        fit (scratch + n * n + n * n + n * n) (by unfold layoutWordBound; omega),
        fit (scratch + n * n + n * n + n * n + N) (by unfold layoutWordBound; omega),
        fit (scratch + n * n + n * n + n * n + N + area)
          (by unfold layoutWordBound; dsimp [area]; omega),
        fit (scratch + n * n + n * n + n * n + N + area + area)
          (by unfold layoutWordBound; dsimp [area]; omega),
        fit (scratch + n * n + n * n + n * n + N + area + area + area)
          (by unfold layoutWordBound; dsimp [area]; omega),
        Reg.paddedSide, Reg.low0, Reg.cells, Reg.side, Reg.paddedCells, Reg.area,
        Reg.modulus, Reg.encodedModulus, Reg.two, Reg.residueAB, Reg.scratch,
        Reg.residueBC, Reg.residueAC, Reg.spread, Reg.matrixP, Reg.matrixQ, Reg.matrixR,
        Reg.productScratch]
    obtain ⟨nSteps, hnSteps, argsRun⟩ := hargs
    obtain ⟨mSteps, hmSteps, restRun⟩ := hcall.seq tailRun
    cases argsRun with
    | seq h₁ h₂ => exact ⟨_, by omega, .seq h₁ (.seq h₂ restRun)⟩
  case fields =>
    constructor <;> simp +decide [Data.set, thigh, hn, hpr, hk, hs, N,
      Reg.side, Reg.modulus, Reg.depth, Reg.scratch, Reg.paddedSide, Reg.cells,
      Reg.paddedCells, Reg.area, Reg.encodedModulus, Reg.residueAB, Reg.residueBC,
      Reg.residueAC, Reg.spread, Reg.matrixP, Reg.matrixQ, Reg.matrixR, Reg.productScratch,
      Nat.add_assoc, Nat.mul_two, two_mul, show 3 * (n * n) = n * n + n * n + n * n by omega,
      show 3 * (4 ^ k * p) = 4 ^ k * p + 4 ^ k * p + 4 ^ k * p by omega]
  case memory => exact memory
  case regs =>
    intro i hi
    have hn (j : Fin 128) (hj : LayoutLocal j) : i ≠ j := by
      intro he
      subst i
      exact hi hj
    have hval : 5 ≤ i.val := by
      have hh : ¬i.val < 5 := fun h => hi (Or.inl h)
      omega
    simp only [Data.set,
      Function.update_of_ne (hn Reg.paddedSide (by decide)),
      Function.update_of_ne (hn Reg.cells (by decide)),
      Function.update_of_ne (hn Reg.paddedCells (by decide)),
      Function.update_of_ne (hn Reg.area (by decide)),
      Function.update_of_ne (hn Reg.encodedModulus (by decide)),
      Function.update_of_ne (hn Reg.residueAB (by decide)),
      Function.update_of_ne (hn Reg.residueBC (by decide)),
      Function.update_of_ne (hn Reg.residueAC (by decide)),
      Function.update_of_ne (hn Reg.spread (by decide)),
      Function.update_of_ne (hn Reg.matrixP (by decide)),
      Function.update_of_ne (hn Reg.matrixQ (by decide)),
      Function.update_of_ne (hn Reg.matrixR (by decide)),
      Function.update_of_ne (hn Reg.productScratch (by decide))]
    exact thigh i hval

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
