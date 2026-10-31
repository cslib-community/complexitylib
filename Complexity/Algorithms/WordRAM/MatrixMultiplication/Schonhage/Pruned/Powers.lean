/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory

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
  have h2 : Fits w 2 := hbase.of_le (by omega)
  have h4 : Fits w 4 := hbase.of_le (by omega)
  have h9 : Fits w 9 := hbase.of_le (by omega)
  have h10 : Fits w 10 := hbase.of_le (by omega)
  have hfit_pow : Fits w (10 ^ L + L + 2) := hbase.of_le (by omega)
  let x0 := ((((x.set nil 0).set two 2).set ten 10).set nine 9).set frameWidth 4
  have hsetup : ExecWithin w powerSetup x x0 5 := by
    ram_eval [powerSetup, x0, h0, h2, h4, h9, h10]
  have hx0_ten : (x0.comap powerRegisters).regs Power.base = 10 := by
    simp +decide [x0, powerRegisters, Power.base, nil, two, ten, nine, frameWidth]
  have hx0_depth : (x0.comap powerRegisters).regs Power.exponent = L := by
    simpa +decide [x0, powerRegisters, Power.exponent, inputDepth, nil, two, ten, nine,
      frameWidth] using hL
  obtain ⟨z, hz, hv, hc, ho, hm, hb', hd'⟩ :=
    Power.exec 10 L (by decide) (x0.comap powerRegisters) hx0_ten hx0_depth hfit_pow
  have hpow : ExecWithin w (Power.program.rename powerRegisters) x0
      (z.extend powerRegisters x0) (4 * L + 5) :=
    hz.rename powerRegisters_injective
  let y := z.extend powerRegisters x0
  have he : ExecWithin w powers x y (4 * L + 10) :=
    (hsetup.seq hpow).mono (by omega)
  have hce := Data.comap_extend powerRegisters_injective z x0
  refine ⟨y, he, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => he.regs_eq (powers_preserves i hi)⟩
  · have h := congrArg (fun d : Data 5 => d.regs Power.exponent) hce
    exact h.trans hd'
  · have h := congrArg (fun d : Data 5 => d.regs Power.value) hce
    exact h.trans hv
  · have h := congrArg (fun d : Data 5 => d.regs Power.counter) hce
    exact h.trans hc
  · simpa +decide [x0, nil, two, ten, nine, frameWidth] using
      hpow.regs_eq (by decide : (Power.program.rename powerRegisters).Preserves nil)
  · have h := congrArg (fun d : Data 5 => d.regs Power.one) hce
    exact h.trans ho
  · simpa +decide [x0, nil, two, ten, nine, frameWidth] using
      hpow.regs_eq (by decide : (Power.program.rename powerRegisters).Preserves two)
  · have h := congrArg (fun d : Data 5 => d.regs Power.base) hce
    exact h.trans hb'
  · simpa +decide [x0, nil, two, ten, nine, frameWidth] using
      hpow.regs_eq (by decide : (Power.program.rename powerRegisters).Preserves nine)
  · simpa +decide [x0, nil, two, ten, nine, frameWidth] using
      hpow.regs_eq (by decide : (Power.program.rename powerRegisters).Preserves frameWidth)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
