/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Execute

/-!
# Initialized ordinary 3SUM through the native Chan–He visitor

One finite program per fixed magnitude exponent and certified finite Exact Triangle block starts
from signed-encoded `State.init`. It computes the frontend and consumes every actual packed node
during traversal through the caller-safe Convolution host. Calls retain the exact finite preorder,
including multiplicity, and continue after a positive result. The final raw Boolean decides a
zero-sum triple of distinct positions, allowing repeated input values.

The initialized endpoint retains its existing magnitude and physical-width hypotheses, charged
cost and same-state prehalt/halt witness. The lower-level `exec_large` helper additionally needs a
fully bounded register file; the actual initialized prefix derives this premise here. The ordinary
decision path publishes no packed-pointer table. Each call preserves its lower live prefix at the
complete current-node endpoint, then one native copy releases the dead packed/residue/histogram
tail. Persistent heavy-buffer capacities and count cells remain allocated, with a monotone
committed frontier and the old table gap reserved. The unchanged polynomial support envelope does
not assert a tighter total-space or callee high-water bound.

The generic result consumes actual finite callee code with its explicit protocol. The certified
exhaustive block inhabits that protocol; the concrete fast endpoint is supplied in `One9992`.

## Main results

* `exec_input`: actual initialized structured execution at every admitted wider width.
* `runs_input`: the charged flat halt and its actual prehalt state witness.
* `not_readsWidth`: the complete ordinary visitor never reads physical width.

The native composition and resource bookkeeping are original and reuse the finite reductions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum (HasSolution)

/-- The complete charged budget always includes the seven small-branch instructions. -/
theorem seven_le_cost {r : ℕ} (κ : ℕ) (c : Host.Callee r) (n : ℕ) : 7 ≤ cost κ c n := by
  dsimp only [cost]
  omega

open Visitor in
/-- The fixed ordinary host is independent of physical word width. -/
theorem not_readsWidth {r : ℕ} (κ : ℕ) (c : Host.Callee r) :
    ¬(program κ c.code).ReadsWidth := by
  have hr : ¬readLength.ReadsWidth := by decide
  have hp : ¬power.ReadsWidth := by decide
  have hd : ¬ChanHe.Traversal.localVisit.ReadsWidth := by decide
  have hc : ¬ChanHe.Traversal.pushChildren.ReadsWidth := by decide
  have hpop : ¬ChanHe.Traversal.popFrame.ReadsWidth := by decide
  have hpush : ¬ChanHe.Traversal.pushFrame.ReadsWidth := by decide
  have hs : ¬ChanHe.Preprocessing.snapshot.ReadsWidth := by decide
  have hpr : ¬ChanHe.Preprocessing.preparePrimes.ReadsWidth := by decide
  have hprime : ¬PrimeTable.program.ReadsWidth := by decide
  have hst : ¬ChanHe.Preprocessing.setupTraversal.ReadsWidth := by decide
  have hre : ¬ChanHe.Preprocessing.reserve.ReadsWidth := by decide
  have hfi : ¬ChanHe.Preprocessing.finishLayout.ReadsWidth := by decide
  have hload : ¬ChanHe.Preprocessing.loadRoot.ReadsWidth := by decide
  simp only [program, large, forest, oneRoot, body, visit, consume, releasePacked, prepareHost,
    receive,
    prepareEnvelope, prepareTraversal, Code.ReadsWidth, Code.readsWidth_rename,
    Op.bin, Op.ReadsWidth,
    reduceCtorEq, hr, hp, hd, hc, hpop, hpush, hs, hpr, hprime, hst, hre, hfi, hload,
    Frontend.not_readsWidth κ, c.not_readsWidth_bodyAt, or_self,
    not_false_eq_true]

/-- Actual execution from initialized signed input, uniformly over all admitted wider words. -/
theorem exec_input {κ w r : ℕ} (input : List ℤ) (c : Host.Callee r)
    (hw : width κ c.widthCoefficient input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    ∃ y, ExecWithin w (program κ c.code) (Data.init (input.map Signed.encode)) y
        (cost κ c input.length - 1) ∧
      y.regs (controllerRegisters r answer) ≤ 1 ∧
      (y.regs (controllerRegisters r answer) = 1 ↔
        HasSolution (fun i : Fin input.length => input[i])) := by
  have hcost := seven_le_cost κ c input.length
  have h3 : Fits w 3 := (envelope_fits hw).2.2.2
  by_cases hn : input.length < 3
  · obtain ⟨y, hy, ha, hno⟩ := exec_small (κ := κ) input c hn h3
    refine ⟨y, hy.mono (by omega), by omega, ?_⟩
    simp only [ha, reduceCtorEq, false_iff]
    exact hno
  obtain ⟨q, hread, hqa, hqn, hq3, hqpp⟩ := exec_readLength_init (r := r) input h3
  have hqb := hread.bounded (Data.Bounded.init (ChanHe.Preprocessing.input_fits input
    ((preprocessing_width_le κ c.widthCoefficient input.length).trans hw) hvalues))
  obtain ⟨y, hy, hb, hans⟩ := exec_large input c q hw hqb (by omega) hvalues hqpp hqn hqa
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
      Executes w (flatProgram κ c.code) (State.init (input.map Signed.encode))
        (y.regs (controllerRegisters r answer)) steps ∧
      Runs w (flatProgram κ c.code) (State.init (input.map Signed.encode))
        ⟨(program κ c.code).size, y⟩ (steps - 1) ∧ steps ≤ cost κ c input.length ∧
      y.regs (controllerRegisters r answer) ≤ 1 ∧
      (y.regs (controllerRegisters r answer) = 1 ↔
        HasSolution (fun i : Fin input.length => input[i])) ∧ y.Bounded w := by
  obtain ⟨y, ⟨t, ht, he⟩, hb, hans⟩ := exec_input input c hw hvalues
  have hcost := seven_le_cost κ c input.length
  refine ⟨y, t + 1, ?_, ?_, by omega, hb, hans, ?_⟩
  · simpa only [flatProgram, State.init] using he.executes (controllerRegisters r answer)
  · simpa only [flatProgram, State.init, Nat.zero_add, Nat.add_sub_cancel] using
      he.runs (pc := 0) (p := flatProgram κ c.code) (Program.Contains.self _).append_left
  · exact he.bounded (Data.Bounded.init (ChanHe.Preprocessing.input_fits input
      ((preprocessing_width_le κ c.widthCoefficient input.length).trans hw) hvalues))

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
