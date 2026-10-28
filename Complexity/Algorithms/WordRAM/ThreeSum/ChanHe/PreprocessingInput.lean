/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingExecute

/-!
# Complete native Chan–He preprocessing from initialized input

Every parameter, sorted multiplicity table, frontend descriptor, prime bit, heavy list and packed
output is computed by one finite native program for the fixed magnitude exponent. The output
list is exactly the existing finite instances, including negative and small-input cases.

## Main definitions

* `cost`: charged complete-program bound, including the final halt.

## Main results

* `exec_input`: complete actual native execution and exact finite packed output.
* `runs_input`: native halting execution and the same actual pre-halt memory witness.

These initialized-input composition proofs are original; existing finite reduction mathematics,
native kernels and native compilation APIs are reused without an algorithm or operation oracle.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- All actual native instructions, including the complete initialized frontend and final halt. -/
def cost (κ n : ℕ) : ℕ :=
  let U := (n + 2) ^ κ
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  Frontend.cost κ n + (m + 1) * (7 * m + 15) + 8 + 4 * F + 45 +
    (Frontend.layout κ n).count * (Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17)

/-- Complete actual native preprocessing, uniformly over every admitted sufficiently wide input. -/
theorem exec_input {κ w : ℕ} (input : List ℤ) (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    let n := input.length
    let U := (n + 2) ^ κ
    let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
    ∃ (out : List (ℕ × Node)) (y : Data 128),
      ExecWithin w (program κ) (Data.init (input.map Signed.encode)) y (cost κ n - 1) ∧
      out.map (fun p => p.2.oneArray (2 * U)) =
        Cslib.Algorithms.ThreeSum.ChanHe.instances n U (fun i : Fin n => input[i]) ∧
      Traversal.StoredNodes (2 * U) (2 * m ^ 2) (arena κ n y.mem).table out y.mem ∧
      y.regs Traversal.outputCount = out.length ∧
      y.regs Traversal.outputs = (arena κ n y.mem).table ∧
      y.regs packedLength = 8 * m ^ 2 := by
  obtain ⟨x, rs, hf, ho, hbase, hcount, hend, hnd, _, hkeys, hcounts, _, _, hp, _⟩ :=
    Frontend.exec_input input ((frontend_width_le κ input.length).trans hw) hvalues
  have hcard : rs.length ≤ input.length := by
    have ht := hnd.length_le_of_subset (fun k hk => (hkeys k).mp hk)
    simpa only [List.length_map] using ht
  have hb : x.Bounded w := hf.bounded (Data.Bounded.init (input_fits input hw hvalues))
  have hw2 : w - 2 + 2 = w := by have := (three_le_width κ input.length).trans hw; omega
  obtain ⟨out, y, hs, hout, hstored, hlen, htable, hpacked⟩ :=
    afterFrontend_exec (w := w - 2) input rs x (by simpa only [hw2] using hw)
      (by simpa only [hw2] using hb) hvalues ho hp hbase hcount hend hkeys hnd hcard
  rw [hw2] at hs
  have hnodes := entries_output hkeys (fun p hp => (hcounts p hp).2) hvalues
  have heq : out.map Prod.snd = Cslib.Algorithms.ThreeSum.ChanHe.allNodes input.length
      ((input.length + 2) ^ κ) (fun i : Fin input.length => input[i]) := hout.trans hnodes
  refine ⟨out, y, (hf.seq hs).mono ?_, ?_, hstored, hlen, htable, hpacked⟩
  · have hpos : 0 < Frontend.cost κ input.length := by dsimp only [Frontend.cost]; omega
    dsimp only [cost]
    omega
  · rw [Cslib.Algorithms.ThreeSum.ChanHe.instances, ← heq, List.map_map]
    rfl

/-- The native flat program halts, and its actual pre-halt state retains the exact output. -/
theorem runs_input {κ w : ℕ} (input : List ℤ) (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    let n := input.length
    let U := (n + 2) ^ κ
    let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
    ∃ (out : List (ℕ × Node)) (y : Data 128) (steps : ℕ),
      Executes w (flatProgram κ) (State.init (input.map Signed.encode)) out.length steps ∧
      Runs w (flatProgram κ) (State.init (input.map Signed.encode))
        ⟨(program κ).size, y⟩ (steps - 1) ∧ steps ≤ cost κ n ∧
      out.map (fun p => p.2.oneArray (2 * U)) =
        Cslib.Algorithms.ThreeSum.ChanHe.instances n U (fun i : Fin n => input[i]) ∧
      Traversal.StoredNodes (2 * U) (2 * m ^ 2) (arena κ n y.mem).table out y.mem ∧
      y.regs Traversal.outputCount = out.length ∧
      y.regs Traversal.outputs = (arena κ n y.mem).table ∧
      y.regs packedLength = 8 * m ^ 2 ∧ y.Bounded w := by
  obtain ⟨out, y, ⟨t, ht, he⟩, hout, hstored, hlen, htable, hpacked⟩ :=
    exec_input input hw hvalues
  have hpos : 0 < cost κ input.length := by dsimp only [cost]; omega
  refine ⟨out, y, t + 1, ?_, ?_, by omega, hout, hstored, hlen, htable, hpacked, ?_⟩
  · simpa only [flatProgram, hlen, State.init] using he.executes Traversal.outputCount
  · simpa only [flatProgram, State.init, Nat.zero_add, Nat.add_sub_cancel] using
      he.runs (pc := 0) (p := flatProgram κ) (Program.Contains.self _).append_left
  · exact he.bounded (Data.Bounded.init (input_fits input hw hvalues))

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
