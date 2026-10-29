/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Execute

/-!
# Complete initialized native ordinary 3SUM host

One finite program per fixed input-magnitude exponent and concrete certified finite Exact
Triangle block starts at actual `State.init`. It computes preprocessing, reads all actual packed
pointers and calls the caller-safe Convolution host. Its final raw Boolean is equivalent to the
existing integer 3SUM predicate with distinct positions and repeated values permitted.

The result is conditional on the supplied *actual finite code* and its explicit callee contract.
The slow exhaustive certified block provides a live instance; this theorem does not construct a
fast backend or claim the final subquadratic endpoint.

## Main results

* `exec_input`: complete actual structured execution, global logarithmic width and verdict.
* `runs_input`: actual halting flat execution and its actual pre-halt state witness.
* `not_readsWidth`: the complete ordinary host never reads physical width.

The composition and resource bookkeeping are original and reuse the existing finite reductions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum (HasSolution)

/-- The complete charged budget always includes the seven small-branch instructions. -/
theorem seven_le_cost {r : ℕ} (κ : ℕ) (c : Host.Callee r) (n : ℕ) : 7 ≤ cost κ c n := by
  dsimp only [cost]
  omega

/-- The fixed ordinary host is independent of physical word width. -/
theorem not_readsWidth {r : ℕ} (κ : ℕ) (c : Host.Callee r) : ¬(program κ c).ReadsWidth := by
  have hr : ¬readLength.ReadsWidth := by decide
  have hp : ¬power.ReadsWidth := by decide
  have hw : ¬reserve.ReadsWidth := by decide
  have hl : ¬loadSource.ReadsWidth := by decide
  have hs : ¬(setup (r := r) κ).ReadsWidth := by
    simp only [setup, Code.ReadsWidth, Op.bin, Op.ReadsWidth, reduceCtorEq,
      or_self, not_false_eq_true]
  have hc : ¬(callSetup (r := r)).ReadsWidth := by
    simp only [callSetup, Code.ReadsWidth, Op.ReadsWidth, or_self, not_false_eq_true]
  have hf : ¬(finish (r := r)).ReadsWidth := by
    simp only [finish, Code.ReadsWidth, Op.bin, Op.ReadsWidth, reduceCtorEq,
      or_self, not_false_eq_true]
  simp only [program, large, calls, body, Code.ReadsWidth, Code.readsWidth_rename,
    Op.ReadsWidth, hr, hp, hw, hl, hs, hc, hf, ChanHe.Preprocessing.not_readsWidth κ,
    c.not_readsWidth_bodyAt, or_false, not_false_eq_true]

/-- Actual execution from initialized signed input, uniformly over all admitted wider words. -/
theorem exec_input {κ w r : ℕ} (input : List ℤ) (c : Host.Callee r)
    (hw : width κ c.widthCoefficient input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    ∃ y, ExecWithin w (program κ c) (Data.init (input.map Signed.encode)) y
        (cost κ c input.length - 1) ∧
      y.regs (controllerRegisters r answer) ≤ 1 ∧
      (y.regs (controllerRegisters r answer) = 1 ↔
        HasSolution (fun i : Fin input.length => input[i])) := by
  have hcost := seven_le_cost κ c input.length
  have h3 : Fits w 3 := (reservation_fits hw).2.2.2
  by_cases hn : input.length < 3
  · obtain ⟨y, hy, ha, hno⟩ := exec_small (κ := κ) input c hn h3
    refine ⟨y, hy.mono (by omega), by omega, ?_⟩
    simp only [ha, reduceCtorEq, false_iff]
    exact hno
  let x : Data (registerCount r) := Data.init (input.map Signed.encode)
  let a := (x.comap (controllerRegisters r)).set address 0
    |>.set inputLength input.length |>.set three 3 |>.set answer 0
  let q := a.extend (controllerRegisters r) x
  have hread : ExecWithin w (readLength.rename (controllerRegisters r)) x q 4 := by
    apply ExecWithin.rename (controller_injective r)
    simpa only [Data.comap_mem, x, Data.init_mem_zero, List.length_map] using
      exec_readLength (x.comap (controllerRegisters r)) h3
  have hqa : q.regs (controllerRegisters r answer) = 0 := by
    rw [extend_controller]
    simp +decide [a, answer, three, inputLength, address]
  have hqn : q.regs (controllerRegisters r inputLength) = input.length := by
    rw [extend_controller]
    simp +decide [a, answer, three, inputLength, address]
  have hq3 : q.regs (controllerRegisters r three) = 3 := by
    rw [extend_controller]
    simp +decide [a, answer, three]
  have hqpp : q.comap (preprocessingRegisters r) = Data.init (input.map Signed.encode) := by
    ext i
    · exact (extend_controller_preprocessing _ _ i).trans rfl
    · rfl
  obtain ⟨y, hy, hb, hans⟩ := exec_large input c q hw (by omega) hvalues hqpp hqn hqa
  refine ⟨y, ?_, hb, hans⟩
  unfold program
  exact (hread.seq (hy.branch_neg (show
      ¬(Cond.lt (controllerRegisters r inputLength) (controllerRegisters r three)).Holds q by
    simpa only [Cond.holds_lt, hqn, hq3] using hn))).mono (by omega)

/-- Complete actual flat execution and actual pre-halt output-state witness.
The output is raw `0` or `1`; the input and every generated matrix cell use signed encoding. -/
theorem runs_input {κ w r : ℕ} (input : List ℤ) (c : Host.Callee r)
    (hw : width κ c.widthCoefficient input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    ∃ (y : Data (registerCount r)) (steps : ℕ),
      Executes w (flatProgram κ c) (State.init (input.map Signed.encode))
        (y.regs (controllerRegisters r answer)) steps ∧
      Runs w (flatProgram κ c) (State.init (input.map Signed.encode))
        ⟨(program κ c).size, y⟩ (steps - 1) ∧ steps ≤ cost κ c input.length ∧
      y.regs (controllerRegisters r answer) ≤ 1 ∧
      (y.regs (controllerRegisters r answer) = 1 ↔
        HasSolution (fun i : Fin input.length => input[i])) ∧ y.Bounded w := by
  obtain ⟨y, ⟨t, ht, he⟩, hb, hans⟩ := exec_input input c hw hvalues
  have hcost := seven_le_cost κ c input.length
  refine ⟨y, t + 1, ?_, ?_, by omega, hb, hans, ?_⟩
  · simpa only [flatProgram, State.init] using he.executes (controllerRegisters r answer)
  · simpa only [flatProgram, State.init, Nat.zero_add, Nat.add_sub_cancel] using
      he.runs (pc := 0) (p := flatProgram κ c) (Program.Contains.self _).append_left
  · exact he.bounded (Data.Bounded.init (ChanHe.Preprocessing.input_fits input
      ((preprocessing_width_le κ c.widthCoefficient input.length).trans hw) hvalues))

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
