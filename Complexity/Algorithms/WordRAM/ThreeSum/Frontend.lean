/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Input
public import Complexity.Computability.WordRAM.Width
public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Time

/-!
# Complete native distinct-position 3SUM frontend

One finite 128-register program per fixed exponent starts from ordinary native initialized
signed input. It computes `(n+2)^κ`, sorts with an explicit magnitude-derived bit count,
retains full multiplicities, and writes six-word descriptors of compact injective arrays.
Reading the descriptors gives exactly the existing `ThreeSum.inputs`, in its existing order,
including empty arrays and the two multiplicity triples at lengths zero, one and two.

The mathematical definitions are reused from the frontend adaptation of
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`,
`PaperStatements.lean` lines 1358–1376. In particular `twiceSet` contains positive `2*a`.
Native programs, layout and charged proofs here are original; no source machine is imported.
This is the frontend component, not complete Chan–He preprocessing or a subquadratic solver.

## Main definitions

* `program`: native code depending only on the fixed polynomial exponent.
* `layout`: six-word descriptors followed by disjoint capacity-`n+1` payload blocks.
* `width`, `cost`: derived positive logarithmic width and all charged instructions.

## Main results

* `exec_input`: initialized-input execution, exact slots/frame and full multiplicities.
* `runs_input`: exact existing-root readback and complete native halting execution.
* `cost_bound`: explicit uniform logarithmic-square instruction bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend

open Cslib.WordRAM

/-- Physical word width is never read, so it never determines the radix iteration count. -/
theorem not_readsWidth (κ : ℕ) : ¬(program κ).ReadsWidth := by
  have hp := (Code.readsWidth_rename parameterRegisters (ChanHe.Parameters.program κ)).not.mpr
    (ChanHe.Parameters.not_readsWidth κ)
  exact not_or.mpr ⟨hp, by decide⟩

/-- Code size depends only on the fixed exponent; the assembled final halt adds one. -/
theorem size_program (κ : ℕ) : (program κ).size = κ + 71 + construct.size := by
  simp only [program, Code.size, Code.size_rename, ChanHe.Parameters.size_program]

/-- The complete finite program halts with its descriptor count, and following its descriptors
gives exactly the existing frontend list. The memory witness is the actual native state just
before the final halt. No slot, bit budget, sorting result or fit is advice. -/
theorem runs_input {κ w : ℕ} (input : List ℤ) (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    ∃ (y : Data 128) (steps : ℕ),
      Executes w ((program κ).program descriptorCount) (State.init (input.map Signed.encode))
        (layout κ input.length).count steps ∧
      Runs w ((program κ).program descriptorCount) (State.init (input.map Signed.encode))
        ⟨(program κ).size, y⟩ (steps - 1) ∧ steps ≤ cost κ input.length ∧
      readRoots (layout κ input.length) y.mem =
        Cslib.Algorithms.ThreeSum.inputs ((input.length + 2) ^ κ)
          (fun i : Fin input.length => input[i]) ∧
      y.regs descriptorBase = (layout κ input.length).descriptors ∧
      y.regs descriptorCount = (layout κ input.length).count ∧
      y.regs heapEnd = (layout κ input.length).endpoint ∧ y.Bounded w := by
  obtain ⟨y, rs, he, ho, hbase, hcount, hend, _, _, hkeys, hcounts, _, _, _, _⟩ :=
    exec_input input hw hvalues
  obtain ⟨steps, hsteps, hexec⟩ := he
  have hpos : 0 < cost κ input.length := by dsimp only [cost]; omega
  refine ⟨y, steps + 1, ?_, ?_, by omega, ?_, hbase, hcount, hend, ?_⟩
  · simpa only [hcount, State.init] using hexec.executes descriptorCount
  · simpa only [State.init, Nat.zero_add, Nat.add_sub_cancel] using
      hexec.runs (pc := 0) (p := (program κ).program descriptorCount)
        (Program.Contains.self _).append_left
  · exact ho.readback hkeys (fun p hp => (hcounts p hp).2) hvalues
  · exact hexec.bounded (Data.Bounded.init (input_fits input hw hvalues))

/-- Every run prefix at every admitted width uses polynomially bounded words. This includes
all memory words and registers, rather than merely the final output or a pair-count metric. -/
theorem intermediates_polynomial {κ w : ℕ} (input : List ℤ)
    (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ))
    {s : State 128} {steps : ℕ}
    (hr : Runs w ((program κ).program descriptorCount)
      (State.init (input.map Signed.encode)) s steps) :
    (∀ i, s.data.regs i < (input.length + 2) ^ (160 * κ + 968)) ∧
      ∀ a, s.data.mem a < (input.length + 2) ^ (160 * κ + 968) := by
  obtain ⟨_, _, he, _, _, _, _, _, _, _⟩ := runs_input input le_rfl hvalues
  have hsmall := Runs.prefix_at_smaller_width
    (Code.not_readsWidth_program (not_readsWidth κ) descriptorCount) hw hr he
  have hb := hsmall.bounded_init (input_fits input le_rfl hvalues)
  have hpoly := two_pow_width_le κ input.length
  exact ⟨fun i => (hb.1 i).trans_le hpoly, fun a => (hb.2 a).trans_le hpoly⟩

end Cslib.Algorithms.WordRAM.ThreeSum.Frontend
