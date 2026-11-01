/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Properties

/-!
# Actual raw verdict, witness and scan-counter return

Five real copies return the values from the complete translated solver bank. The Boolean and
original-coordinate meaning are supplied by its proved execution, not assumed by this stage.
No answer span needs copying or normalization: the returned source registers already agree
exactly with the compiled native computation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM

/-- Charge all actual return copies, including coordinates in unsuccessful calls. -/
theorem exec_receive {W : ℕ} (x : Data 640) :
    ∃ y, ExecWithin W receive x y 5 ∧ y.mem = x.mem ∧
      y.regs Reg.found = x.regs (sourceReg FixedPrime.Reg.found) ∧
      y.regs Reg.witnessA = x.regs (sourceReg (FixedPrime.recordBank RecordWitness.Reg.witnessA)) ∧
      y.regs Reg.witnessB = x.regs (sourceReg (FixedPrime.recordBank RecordWitness.Reg.witnessB)) ∧
      y.regs Reg.witnessC = x.regs (sourceReg (FixedPrime.recordBank RecordWitness.Reg.witnessC)) ∧
      y.regs Reg.scans = x.regs (sourceReg FixedPrime.Reg.scans) := by
  refine ⟨?y, ?run, ?mem, ?found, ?a, ?b, ?c, ?scans⟩
  case run => ram_eval [receive, sourceReg, sourceBank, FixedPrime.recordBank,
    FixedPrime.Reg.found, FixedPrime.Reg.scans, RecordWitness.Reg.witnessA,
    RecordWitness.Reg.witnessB, RecordWitness.Reg.witnessC,
    Reg.found, Reg.witnessA, Reg.witnessB, Reg.witnessC, Reg.scans, Fin.mk.injEq]
  case mem => rfl
  all_goals simp +decide [sourceReg, sourceBank, FixedPrime.recordBank,
    Reg.found, Reg.witnessA, Reg.witnessB, Reg.witnessC, Reg.scans,
    FixedPrime.Reg.found, FixedPrime.Reg.scans, RecordWitness.Reg.witnessA,
    RecordWitness.Reg.witnessB, RecordWitness.Reg.witnessC]

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
