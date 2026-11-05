/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.WordRAM.GhostLoop

/-!
# Variable native loop costs paid by a ghost potential

The actual counter increases from one to two before becoming zero. The proof therefore tracks
semantic phases, rather than assuming that the native counter decreases. The first branch costs
two instructions and the second costs four; the complete loop costs twelve, including control.
-/

namespace ComplexityTests.NativeGhostPotential

open Cslib.WordRAM

private inductive Phase where
  | first
  | second
  | done

private def counter : Phase → ℕ
  | .first => 1
  | .second => 2
  | .done => 0

private def potential : Phase → ℕ
  | .first => 10
  | .second => 6
  | .done => 0

private def body : Code .standard 4 :=
  .branch (.eq 0 1) (.op (.copy 0 2))
    (.seq (.op (.copy 0 3)) (.op (.copy 1 1)))

private def loop : Code .standard 4 := .loop (.lt 3 0) body

private def input : Data 4 := ⟨![1, 1, 2, 0], fun p => 99 + p⟩

private def invariant (s : Phase) (x : Data 4) : Prop :=
  x.regs 0 = counter s ∧ x.regs 1 = 1 ∧ x.regs 2 = 2 ∧ x.regs 3 = 0 ∧ x.mem = input.mem

-- This inhabited application uses different charged bounds for the two actual body paths.
-- The twelve-step budget is smaller than charging both bodies at their four-step maximum.
example : ∃ y, ExecWithin 2 loop input y 12 ∧
    y.regs 0 = 0 ∧ y.regs 2 = 2 ∧ y.mem = input.mem := by
  have step : ∀ s x, invariant s x → (Cond.lt 3 0).Holds x →
      ∃ s' y t, ExecWithin 2 body x y t ∧ invariant s' y ∧
        t + 2 + potential s' ≤ potential s := by
    intro s x hx hc
    rcases hx with ⟨hn, ho, ht, hz, hm⟩
    cases s with
    | first =>
      refine ⟨.second, x.set 0 (x.regs 2), 2, ?_, ?_, by decide⟩
      · exact (Exec.branch_pos (by
          change x.regs 0 = x.regs 1
          simpa [counter] using hn.trans ho.symm) Exec.copy).within
      · simp [invariant, counter, ho, ht, hz, hm]
    | second =>
      refine ⟨.done, (x.set 0 (x.regs 3)).set 1 (x.regs 1), 4, ?_, ?_, by decide⟩
      · exact (Exec.branch_neg (by
          change ¬x.regs 0 = x.regs 1
          simp_all [counter]) (Exec.copy.seq Exec.copy)).within
      · simp [invariant, counter, ho, ht, hz, hm]
    | done =>
      have hc' : x.regs 3 < x.regs 0 := hc
      simp only [counter] at hn
      omega
  obtain ⟨s, y, he, hy, hexit⟩ := ExecWithin.loop_potential_state invariant potential step
    (s := .first) (x := input) (by simp [invariant, input, counter])
  have hz : y.regs 3 = 0 := hy.2.2.2.1
  have hc : ¬y.regs 3 < y.regs 0 := hexit
  exact ⟨y, he, by omega, hy.2.2.1, hy.2.2.2.2⟩

-- The evaluator independently checks the exact clock, increasing counter path and untouched
-- dirty memory. No memory word is read, so unused cells need not fit the physical width.
/-- info: true -/
#guard_msgs in
#eval decide ((Code.eval 2 3 loop input).map (fun (y, t) =>
  [t, y.regs 0, y.regs 1, y.regs 2, y.regs 3, y.mem 0, y.mem 7]) =
    some [12, 0, 1, 2, 0, 99, 106])

private def initialized : Code .standard 4 :=
  .seq (.op (.const 0 1)) (.seq (.op (.const 1 1))
    (.seq (.op (.const 2 2)) (.seq (.op (.const 3 0)) loop)))

-- Two bits admit the actual initializer; one bit rejects its constant two.
/-- info: true -/
#guard_msgs in
#eval decide ((Code.eval 2 3 initialized (Data.init [])).map (fun (y, t) =>
  [t, y.regs 0, y.regs 2]) = some [16, 0, 2])

/-- info: true -/
#guard_msgs in
#eval (Code.eval 1 3 initialized (Data.init [])).isNone

end ComplexityTests.NativeGhostPotential
