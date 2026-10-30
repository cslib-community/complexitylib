/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Program

/-!
# Charged catalogue-controller setup and return

The occupied count is read from the real producer bank. The return code adds the actual
callee scan count, retains its actual unsigned flag, advances the visited prefix and closes
the loop only after success. These internal rules use concrete data instructions; neither
the scan count nor the verdict is supplied as an execution oracle.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM

-- These closed checks cover only the short controller and its finite register bank.
set_option maxRecDepth 4096 in
private theorem setup_preserves : ∀ i : Fin 416, i.val < 400 → setup.Preserves i := by
  decide

-- The return branch writes four controller registers and no part of the callee bank.
set_option maxRecDepth 4096 in
private theorem receive_preserves : ∀ i : Fin 416,
    i.val < 400 ∨ i = Reg.one → receive.Preserves i := by decide

/-- Read the actual occupied count, with all five initialization instructions charged. -/
theorem exec_setup {w : ℕ} (x : Data 416) (h1 : Fits w 1) :
    ∃ y, ExecWithin w setup x y 5 ∧ y.mem = x.mem ∧
      y.regs Reg.index = 0 ∧
      y.regs Reg.limit = x.regs (recordBank
        (RecordWitness.productBank (RecordProduct.producerBank Instances.produced))) ∧
      y.regs Reg.found = 0 ∧ y.regs Reg.scans = 0 ∧
      y.regs Reg.one = 1 ∧
      ∀ j : Fin 416, j.val < 400 → y.regs j = x.regs j := by
  let M := x.regs (recordBank
    (RecordWitness.productBank (RecordProduct.producerBank Instances.produced)))
  let y := x.set Reg.index 0 |>.set Reg.limit M |>.set Reg.found 0 |>.set Reg.scans 0
    |>.set Reg.one 1
  have he : ExecWithin w setup x y 5 := by
    ram_eval [setup, y, M, h1, Reg.index, Reg.limit, Reg.found, Reg.scans, Reg.one,
      recordBank, RecordWitness.productBank, RecordProduct.producerBank,
      Instances.produced, Fin.castLE]
  refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, ?_, fun j hj =>
    he.regs_eq (setup_preserves j hj)⟩
  all_goals simp +decide [y, M, Reg.index, Reg.limit, Reg.found, Reg.scans, Reg.one]

/-- The native return needs at most six instructions, including control. Its limit
is shortened exactly when the actual callee flag equals one. The complete callee bank survives. -/
theorem exec_receive {w i limit S performed flag : ℕ} (x : Data 416)
    (hi : x.regs Reg.index = i) (hl : x.regs Reg.limit = limit)
    (hs : x.regs Reg.scans = S)
    (hp : x.regs (recordBank RecordWitness.Reg.scans) = performed)
    (hf : x.regs (recordBank RecordWitness.Reg.found) = flag)
    (h1 : x.regs Reg.one = 1) (hS : Fits w (S + performed)) (hI : Fits w (i + 1)) :
    ∃ y, ExecWithin w receive x y 6 ∧ y.mem = x.mem ∧
      y.regs Reg.index = i + 1 ∧ y.regs Reg.limit = (if flag = 1 then i + 1 else limit) ∧
      y.regs Reg.scans = S + performed ∧ y.regs Reg.found = flag ∧
      ∀ j : Fin 416, j.val < 400 ∨ j = Reg.one →
        y.regs j = x.regs j := by
  dsimp only [Reg.index, Reg.limit, Reg.scans, Reg.one, recordBank,
    RecordWitness.Reg.found, RecordWitness.Reg.scans, Fin.castLE] at hi hl hs hp hf h1
  let y := x.set Reg.scans (S + performed) |>.set Reg.found flag |>.set Reg.index (i + 1)
    |>.set Reg.limit (if flag = 1 then i + 1 else limit)
  have he : ExecWithin w receive x y 6 := by
    by_cases hflag : flag = 1
    · ram_eval [receive, y, hi, hl, hs, hp, hf, h1, hS, hI, hflag,
        Reg.index, Reg.limit, Reg.found, Reg.scans, Reg.one, recordBank,
        RecordWitness.Reg.found, RecordWitness.Reg.scans, Fin.castLE]
    · ram_eval [receive, y, hi, hl, hs, hp, hf, h1, hS, hI, hflag,
        Reg.index, Reg.limit, Reg.found, Reg.scans, Reg.one, recordBank,
        RecordWitness.Reg.found, RecordWitness.Reg.scans, Fin.castLE]
  refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, fun j hj =>
    he.regs_eq (receive_preserves j hj)⟩
  all_goals simp +decide [y, Reg.index, Reg.limit, Reg.found, Reg.scans]

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
