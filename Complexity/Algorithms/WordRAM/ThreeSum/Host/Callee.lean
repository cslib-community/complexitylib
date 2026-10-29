/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Loop
public import Complexity.Computability.WordRAM.Width

/-!
# Concrete finite Exact Triangle callees for the native host

A callee is actual finite standard code, with raw unsigned protocol registers 0–5 and a raw
Boolean in register 6. Matrix cells use the existing signed encoding. The callee must preserve
the complete memory prefix below AB, including every remaining preprocessing instance.

The charged time and logarithmic width guarantee are proof obligations about that code, not
instructions or runtime oracles. No fast solver is assumed to have been constructed.

## Main definitions

* `Callee`: concrete code and its explicit width, frame, correctness and instruction contract.

This native calling convention and its composition interface are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Host

open Cslib.WordRAM

/-- A certified finite solver block. Unused registers and old workspace contents are arbitrary.
The caller delivers all six arguments; the solver establishes its own scratch initialization. -/
structure Callee (r : ℕ) where
  /-- The one fixed native code block, including its seven protocol registers. -/
  code : Code .standard (r + 7)
  /-- Charged instruction budget, independent of physical width, layout and matrix contents. -/
  time : ℕ → ℕ → ℕ
  /-- Multiplier for a logarithmic width guarantee, including addresses and scratch arithmetic. -/
  widthCoefficient : ℕ
  /-- The guarantee gives a positive width at every admitted call. -/
  coefficient_pos : 0 < widthCoefficient
  /-- Wider words do not change the mathematical execution. -/
  not_readsWidth : ¬code.ReadsWidth
  /-- Actual execution, exact verdict and caller-prefix preservation for arbitrary old memory. -/
  exec : ∀ (w t F ab bc ac free : ℕ) (x : Data (r + 7))
    (A B C : Fin t → Fin t → ℤ),
    0 < t → 0 < F →
    ab + t * t ≤ bc → bc + t * t ≤ ac → ac + t * t ≤ free →
    widthCoefficient * Nat.clog 2 (free + F + t + 2) ≤ w →
    x.regs (solverArg 0) = t → x.regs (solverArg 1) = F →
    x.regs (solverArg 2) = ab → x.regs (solverArg 3) = bc →
    x.regs (solverArg 4) = ac → x.regs (solverArg 5) = free →
    (∀ i j, x.mem (ab + i.val * t + j.val) = Signed.encode (A i j)) →
    (∀ i j, x.mem (bc + i.val * t + j.val) = Signed.encode (B i j)) →
    (∀ i j, x.mem (ac + i.val * t + j.val) = Signed.encode (C i j)) →
    (∀ i j, |A i j| ≤ F) → (∀ i j, |B i j| ≤ F) → (∀ i j, |C i j| ≤ F) →
    ∃ y, ExecWithin w code x y (time t F) ∧ y.regs (solverArg 6) ≤ 1 ∧
      (y.regs (solverArg 6) = 1 ↔ Cslib.Algorithms.ExactTriangle.HasZeroTriangle A B C) ∧
      ∀ a < ab, y.mem a = x.mem a

end Cslib.Algorithms.WordRAM.ThreeSum.Host
