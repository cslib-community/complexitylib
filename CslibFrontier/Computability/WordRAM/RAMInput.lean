/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.RAM
public import CslibFrontier.Computability.RAM.Input

/-!
# Word-RAM simulation with charged input preparation

The fixed compiler is preceded by `Cslib.RAM.Input.prepare`, which moves the input length and
words to the compiler's memory region and clears its workspace. Every relocation, clearing,
compiler-initialization, simulation and output instruction is charged.

The external input convention still supplies five zero scratch registers followed by the length
header and input words. Installing this fixed convention is uncharged, as for the underlying RAM;
this is not a certified encoding reduction from an arbitrary bare list. The simulation is forward
and restricted to successful bounded-word executions in the additive-memory fragment.

The source word RAM adapts [MIT–ULB CompGeom Group][Tromino2025]. The target is the library's
natural-number adaptation of [Cook and Reckhow][CookReckhow1973], with logarithmic cost. This
does not establish equivalence with the original integer/I/O model or with Turing machines.

## Main definitions

* `Cslib.WordRAM.ToRAM.preparedProgram`, `Cslib.WordRAM.ToRAM.preparedProgramAdditive`: input
  preparation followed by the fixed compiler.

## Main results

* `Cslib.WordRAM.ToRAM.haltsWithResultInTime_prepared_of_bitLength_le`,
  `Cslib.WordRAM.ToRAM.haltsWithResultInTime_prepared_of_bitLength_le_additive`: the sum of
  preparation and simulation costs, keeping the input bit bound separate from the source word width.
* `Cslib.WordRAM.ToRAM.haltsWithResultInTime_prepared`,
  `Cslib.WordRAM.ToRAM.haltsWithResultInTime_prepared_additive`: logarithmic cost at most
  `C_r (t + input.length + 1) (w + 1)`, for an explicit constant depending only on `r`.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]
-/

@[expose] public section

namespace Cslib.WordRAM.ToRAM

variable {r : ℕ}

/-- A fixed target program that prepares the length-bearing input and then simulates `p`.
Its external input convention is `RAM.Input.encode 5`; the installed scratch prefix is
independent of the source program, register count, input and word width. -/
def preparedProgram (p : Program .standard r) : RAM.Program :=
  let pre := RAM.Input.prepare (memoryBase r)
  (pre ++ prologue r) ++ compile (pre.length + 2) p

/-- The charged preparation and simulation bound with a separate input bit-length bound.
The fixed external layout is supplied; all subsequent target instructions are charged. -/
theorem haltsWithResultInTime_prepared_of_bitLength_le {p : Program .standard r} (hp : p.IsAdditive)
    {input : List ℕ} {w v n b : ℕ} (hi : InputFits w input)
    (h : Executes w p (State.init input) v n)
    (hlen : RAM.bitLength input.length ≤ b)
    (hinput : ∀ x ∈ input, RAM.bitLength x ≤ b) :
    let R := memoryBase r
    RAM.HaltsWithResultInTime RAM.logCost (preparedProgram p) (RAM.Input.encode 5 input) v
      ((24 + R) * (RAM.bitLength (R + 5) + 2) * (input.length + 1) * b +
        8 * (RAM.bitLength R + 1) * (n + 1) * (w + 1)) := by
  let pre := RAM.Input.prepare (memoryBase r)
  let tail := prologue r ++ compile (pre.length + 2) p
  have hR : 5 ≤ memoryBase r := by simp [memoryBase]
  have hrun := RAM.Input.run_prepare_append hR tail input
  have hcost := RAM.Input.time_prepare_append_le hR tail input hlen hinput
  obtain ⟨k, hk, hv, ht⟩ := executes_compile_from_paddedInput hp pre hi h
  have hprogram : pre ++ tail = preparedProgram p := List.append_assoc .. |>.symm
  change RAM.run (pre ++ tail) _ _ = _ at hrun
  change RAM.time RAM.logCost (pre ++ tail) _ _ ≤ _ at hcost
  rw [hprogram] at hrun hcost
  change (RAM.run (preparedProgram p) k _).isHalted _ at hk
  change (RAM.run (preparedProgram p) k _).regs.output = v at hv
  change RAM.time RAM.logCost (preparedProgram p) k _ ≤ _ at ht
  refine ⟨RAM.Input.prepareSteps (memoryBase r) input + k, ?_, ?_, ?_⟩
  · rwa [RAM.run_add, hrun]
  · rwa [RAM.run_add, hrun]
  · rw [RAM.time_add, hrun]
    exact Nat.add_le_add hcost ht

/-- Every successful fitting source run has logarithmic target cost
`C_r (t + input.length + 1) (w + 1)`, including input relocation and workspace clearing.
The displayed constant depends only on the fixed source register count. The supplied external
input is five zero words followed by its length header and words; installing it is uncharged. -/
theorem haltsWithResultInTime_prepared {p : Program .standard r} (hp : p.IsAdditive)
    {input : List ℕ} {w v n : ℕ} (hi : InputFits w input)
    (h : Executes w p (State.init input) v n) :
    let R := memoryBase r
    RAM.HaltsWithResultInTime RAM.logCost (preparedProgram p) (RAM.Input.encode 5 input) v
      (((24 + R) * (RAM.bitLength (R + 5) + 2) + 8 * (RAM.bitLength R + 1)) *
        (n + input.length + 1) * (w + 1)) := by
  have hcost := haltsWithResultInTime_prepared_of_bitLength_le hp hi h
    hi.1.bitLength_le (fun x hx => (hi.2 x hx).bitLength_le)
  refine hcost.mono ?_
  calc
    _ ≤ (24 + memoryBase r) * (RAM.bitLength (memoryBase r + 5) + 2) *
          (n + input.length + 1) * (w + 1) +
        8 * (RAM.bitLength (memoryBase r) + 1) * (n + input.length + 1) * (w + 1) := by
      gcongr <;> lia
    _ = _ := by ring

/-- A fixed target program that prepares the length-bearing input and then simulates a
source program over `Basis.additive`. -/
def preparedProgramAdditive (p : Program .additive r) : RAM.Program :=
  preparedProgram (p.mapOp Basis.additiveHomStandard)

/-- Charged preparation and simulation bound for a program over `Basis.additive`, with a
separate input bit-length bound. -/
theorem haltsWithResultInTime_prepared_of_bitLength_le_additive {p : Program .additive r}
    {input : List ℕ} {w v n b : ℕ} (hi : InputFits w input)
    (h : Executes w p (State.init input) v n)
    (hlen : RAM.bitLength input.length ≤ b)
    (hinput : ∀ x ∈ input, RAM.bitLength x ≤ b) :
    let R := memoryBase r
    RAM.HaltsWithResultInTime RAM.logCost (preparedProgramAdditive p)
      (RAM.Input.encode 5 input) v
      ((24 + R) * (RAM.bitLength (R + 5) + 2) * (input.length + 1) * b +
        8 * (RAM.bitLength R + 1) * (n + 1) * (w + 1)) :=
  haltsWithResultInTime_prepared_of_bitLength_le p.mapOp_additiveHomStandard_isAdditive hi
    ((executes_mapOp_iff Basis.additiveHomStandard).mpr h) hlen hinput

/-- Charged preparation and simulation bound for a program over `Basis.additive`. -/
theorem haltsWithResultInTime_prepared_additive {p : Program .additive r}
    {input : List ℕ} {w v n : ℕ} (hi : InputFits w input)
    (h : Executes w p (State.init input) v n) :
    let R := memoryBase r
    RAM.HaltsWithResultInTime RAM.logCost (preparedProgramAdditive p)
      (RAM.Input.encode 5 input) v
      (((24 + R) * (RAM.bitLength (R + 5) + 2) + 8 * (RAM.bitLength R + 1)) *
        (n + input.length + 1) * (w + 1)) :=
  haltsWithResultInTime_prepared p.mapOp_additiveHomStandard_isAdditive hi
    ((executes_mapOp_iff Basis.additiveHomStandard).mpr h)

end Cslib.WordRAM.ToRAM

end
