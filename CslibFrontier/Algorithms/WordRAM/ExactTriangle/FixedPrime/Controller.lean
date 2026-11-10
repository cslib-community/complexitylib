/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.Program
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.BoxRecordWitness.Width

/-!
# Fixed-prime callee bank and early-stop return

The one-slot solver uses the complete 400-register box-product/witness callee and five disjoint
controller registers. The return accumulates actual scans, advances the visited prefix and
closes the loop exactly on success. These shared instructions contain no materialized solver.
The control adapts `Host.Loop` at
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`; native charges are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM

/-- The complete record-product/witness bank moves together, including both internal banks. -/
@[expose] def recordBank : Fin 400 → Fin 416 := Fin.castLE (by decide)

namespace Reg

/-- Number of actual occupied records visited. -/
abbrev index : Fin 416 := 400
/-- Logical record count, shortened to the visited prefix only after success. -/
abbrev limit : Fin 416 := 401
/-- Raw unsigned original-witness verdict. -/
abbrev found : Fin 416 := 402
/-- Total actual original-weight scans across all visited records. -/
abbrev scans : Fin 416 := 403
/-- Constant one outside the callee bank. -/
abbrev one : Fin 416 := 404
end Reg

/-- Actual product computation, descriptor reading and original signed-weight verification. -/
@[expose] def record : Code .standard 416 := BoxRecordWitness.program.rename recordBank

open Reg in
/-- Accumulate the actual scan counter and close the loop exactly on a successful return. -/
@[expose] def receive : Code .standard 416 :=
  let returned := recordBank RecordWitness.Reg.found
  let performed := recordBank RecordWitness.Reg.scans
  ram[ scans ← scans + performed; found ← returned; index ← index + one;
    if found = one then [ limit ← index ] else [ limit ← limit ] ]

-- The return branch writes four controller registers and no part of the callee bank.
set_option maxRecDepth 4096 in
private theorem receive_preserves : ∀ i : Fin 416,
    i.val < 400 ∨ i = Reg.one → receive.Preserves i := by decide

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
