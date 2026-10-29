/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Registers
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Scalar

/-!
# Actual ordinary-host metadata controls

The controller copies the existing preprocessing registers, computes its polynomial reservation,
and retains its metadata while native callees execute in disjoint banks.

## Main definitions

* `Controls`: raw table/count/packed-length and caller-owned workspace register contents.

## Main results

* `exec_setup`: all ten metadata/constant instructions.

These metadata composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- The raw runtime controls for an entire catalogue traversal. -/
structure Controls {r : ℕ} (tab num N V : ℕ) (x : Data (registerCount r)) : Prop where
  table : x.regs (controllerRegisters r table) = tab
  count : x.regs (controllerRegisters r count) = num
  length : x.regs (controllerRegisters r length) = N
  envelope : x.regs (controllerRegisters r envelope) = V
  workspace : x.regs (controllerRegisters r workspace) = 2 * V
  one : x.regs (controllerRegisters r one) = 1

/-- Controls depend only on their six exact register values. -/
theorem Controls.congr {r tab num N V : ℕ} {x y : Data (registerCount r)}
    (h : Controls tab num N V x)
    (heq : ∀ i : Fin 16, i ≠ current → i ≠ answer → i ≠ address → i ≠ source →
      y.regs (controllerRegisters r i) = x.regs (controllerRegisters r i)) :
    Controls tab num N V y := by
  constructor
  all_goals first
    | exact (heq _ (by decide) (by decide) (by decide) (by decide)).trans h.table
    | exact (heq _ (by decide) (by decide) (by decide) (by decide)).trans h.count
    | exact (heq _ (by decide) (by decide) (by decide) (by decide)).trans h.length
    | exact (heq _ (by decide) (by decide) (by decide) (by decide)).trans h.envelope
    | exact (heq _ (by decide) (by decide) (by decide) (by decide)).trans h.workspace
    | exact (heq _ (by decide) (by decide) (by decide) (by decide)).trans h.one

/-- Copy the actual unsigned output ABI; no mathematical layout supplies runtime pointers. -/
theorem exec_setup {r κ n w tab num N : ℕ} (x : Data (registerCount r))
    (hn : x.regs (controllerRegisters r inputLength) = n)
    (ht : x.regs (preprocessingRegisters r ChanHe.Traversal.outputs) = tab)
    (hc : x.regs (preprocessingRegisters r ChanHe.Traversal.outputCount) = num)
    (hl : x.regs (preprocessingRegisters r ChanHe.Preprocessing.packedLength) = N)
    (hb : Fits w (n + 2)) (hE : Fits w (envelopeExponent κ)) :
    ∃ y, ExecWithin w (setup κ) x y 11 ∧
      y.regs (controllerRegisters r table) = tab ∧
      y.regs (controllerRegisters r count) = num ∧
      y.regs (controllerRegisters r length) = N ∧
      y.regs (controllerRegisters r scale) = n + 2 ∧
      y.regs (controllerRegisters r envelope) = 1 ∧
      y.regs (controllerRegisters r remaining) = envelopeExponent κ ∧
      y.regs (controllerRegisters r current) = 0 ∧
      y.regs (controllerRegisters r one) = 1 ∧
      y.regs (controllerRegisters r zero) = 0 ∧
      y.regs (controllerRegisters r answer) = x.regs (controllerRegisters r answer) ∧
      y.mem = x.mem := by
  let m := controllerRegisters r
  let y := x.set (m table) tab |>.set (m count) num |>.set (m length) N
    |>.set (m one) 1 |>.set (m two) 2 |>.set (m zero) 0
    |>.set (m scale) (n + 2) |>.set (m envelope) 1
    |>.set (m remaining) (envelopeExponent κ) |>.set (m current) 0
  have h1 : Fits w 1 := hb.of_le (by omega)
  have h2 : Fits w 2 := hb.of_le (by omega)
  have hne (i j : Fin 16) : m i = m j ↔ i = j := (controller_injective r).eq_iff
  have hp (i : Fin 128) (j : Fin 16) : preprocessingRegisters r i ≠ m j := by
    intro h
    have hv := congrArg Fin.val h
    have hi := i.isLt
    dsimp only [m, preprocessingRegisters, controllerRegisters] at hv
    omega
  have he : ExecWithin w (setup κ) x y 11 := by
    ram_eval [setup, y, m, hn, ht, hc, hl, hb, hE, h1, h2, hne,
      table, count, length, one, two, zero, scale, inputLength, envelope, remaining, current,
      hp, Fin.mk.injEq]
  refine ⟨y, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  all_goals simp +decide [y, m, hne, table, count, length, one, two, zero, scale,
    envelope, remaining, current, answer]

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
