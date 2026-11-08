/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import Complexity.Computability.WordRAM.Power.Rename
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory
import Complexity.Tactic.Fits

/-!
# Charged initialization and encoding-array size

## Main results

* `PrunedQuery.exec_powers`: compute `10^L` by renaming `Power.program` after the five
  retained constant initializations, preserving all caller parameters and memory.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- The scalar registers initialized or advanced by the power routine. -/
def PowersLocal (i : Fin registers) : Prop :=
  i = nil ∨ i = one ∨ i = two ∨ i = ten ∨ i = nine ∨ i = frameWidth ∨ i = span ∨ i = index

instance (i : Fin registers) : Decidable (PowersLocal i) :=
  inferInstanceAs (Decidable
    (i = nil ∨ i = one ∨ i = two ∨ i = ten ∨ i = nine ∨ i = frameWidth ∨ i = span ∨ i = index))

/-- The five-register power assignment is injective. -/
theorem powerRegisters_injective : Function.Injective powerRegisters := by decide

private theorem powers_preserves (i : Fin registers) : ¬PowersLocal i → powers.Preserves i := by
  decide +kernel +revert

/-- The power routine charges its five constant initializations and the renamed `4*L+5`
`Power.program` execution. The only width premise is a bound on ordinary input-derived
natural numbers. -/
theorem exec_powers {w L Q : ℕ} (x : Data registers) (hL : x.regs inputDepth = L)
    (hbound : Fits w (addressBound L Q)) :
    ∃ y, ExecWithin w powers x y (4 * L + 10) ∧ y.mem = x.mem ∧
      y.regs inputDepth = L ∧ y.regs span = 10 ^ L ∧ y.regs index = L ∧
      y.regs nil = 0 ∧ y.regs one = 1 ∧ y.regs two = 2 ∧ y.regs ten = 10 ∧
      y.regs nine = 9 ∧ y.regs frameWidth = 4 ∧
      (∀ i, ¬PowersLocal i → y.regs i = x.regs i) := by
  have hspan : 1 ≤ (10 : ℕ) ^ L := by
    have hp : 0 < (10 : ℕ) ^ L := by positivity
    omega
  have hscalar : L + 128 + 128 * 10 ^ L ≤ addressBound L Q := by
    have hm := Nat.mul_le_mul_left L hspan
    unfold addressBound
    nlinarith
  have hbase := hbound.of_le hscalar
  have h0 : Fits w 0 := fits_zero w
  have h2 : Fits w 2 := by fits
  have h4 : Fits w 4 := by fits
  have h9 : Fits w 9 := by fits
  have h10 : Fits w 10 := by fits
  have hfit_pow : Fits w (10 ^ L + L + 2) := by fits
  let x0 := ((((x.set nil 0).set two 2).set ten 10).set nine 9).set frameWidth 4
  have hsetup : ExecWithin w powerSetup x x0 5 := by
    ram_eval [powerSetup, x0, h0, h2, h4, h9, h10]
  have hx0_ten : (x0.comap powerRegisters).regs Power.base = 10 := by
    simp +decide [x0, powerRegisters, Power.base, nil, two, ten, nine, frameWidth]
  have hx0_depth : (x0.comap powerRegisters).regs Power.exponent = L := by
    simpa +decide [x0, powerRegisters, Power.exponent, inputDepth, nil, two, ten, nine,
      frameWidth] using hL
  obtain ⟨y, hpow, hv, hc, ho, hm, hb', hd', -⟩ :=
    Power.exec_rename powerRegisters powerRegisters_injective 10 L (by decide) x0
      hx0_ten hx0_depth hfit_pow
  have he : ExecWithin w powers x y (4 * L + 10) :=
    (hsetup.seq hpow).mono (by omega)
  refine ⟨y, he, hm, hd', hv, hc, ?_, ho, ?_, hb', ?_, ?_,
    fun i hi => he.regs_eq (powers_preserves i hi)⟩
  · simpa +decide [x0, nil, two, ten, nine, frameWidth] using
      hpow.regs_eq (by decide : (Power.program.rename powerRegisters).Preserves nil)
  · simpa +decide [x0, nil, two, ten, nine, frameWidth] using
      hpow.regs_eq (by decide : (Power.program.rename powerRegisters).Preserves two)
  · simpa +decide [x0, nil, two, ten, nine, frameWidth] using
      hpow.regs_eq (by decide : (Power.program.rename powerRegisters).Preserves nine)
  · simpa +decide [x0, nil, two, ten, nine, frameWidth] using
      hpow.regs_eq (by decide : (Power.program.rename powerRegisters).Preserves frameWidth)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
