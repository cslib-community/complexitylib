/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ElementDistinctness
public import Complexity.Computability.WordRAM.RAMInput

/-!
# Element distinctness on a logarithmic-cost RAM

The bounded-universe direct-addressing algorithm
[Cormen et al., Section 11.1][CLRS2009] uses only the additive-memory fragment of the word RAM.
Compiling its fixed twelve-register program with `Cslib.WordRAM.ToRAM.paddedProgram` gives a
natural-number RAM decider with logarithmic cost `O((n + 1) (log(n + 1) + 1))`.

The prepared program starts from five supplied zero scratch words, a length header and the input.
It charges every relocation, clearing, compiler-initialization, simulation and output instruction.
Installing this external convention remains uncharged. A second theorem starts directly from the
larger padded workspace. The entries must be below the input length; unrestricted element
distinctness is outside the statements. The target is the library's
natural-number adaptation of [Cook and Reckhow][CookReckhow1973], not a Turing-machine theorem.
The source word RAM adapts [MIT–ULB CompGeom Group][Tromino2025].

## Main definitions

* `Cslib.Algorithms.WordRAM.ElementDistinctness.paddedRamProgram`: the fixed compiled decider.
* `Cslib.Algorithms.WordRAM.ElementDistinctness.ramProgram`: the fixed compiled decider with
  charged input preparation.

## Main results

* `Cslib.Algorithms.WordRAM.ElementDistinctness.program_isAdditive`: the concrete source
  program belongs to the compiler's supported fragment.
* `Cslib.Algorithms.WordRAM.ElementDistinctness.haltsWithResultInTime_nodup_padded`: the
  compiled decider answers within `2448 (n + 1) (Nat.log 2 (n + 1) + 1)` logarithmic cost.
* `Cslib.Algorithms.WordRAM.ElementDistinctness.haltsWithResultInTime_nodup`: including
  preparation, the bound is `2735 (n + 1) (Nat.log 2 (n + 1) + 1)`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ElementDistinctness

open Cslib.WordRAM

/-- Every instruction of the compiled source decider is in the additive-memory fragment,
because `decider` is the image of `deciderAdditive` under `Basis.additiveHomStandard`. -/
theorem program_isAdditive : (decider.program Reg.ans).IsAdditive := by
  rw [← deciderAdditive_mapOp]
  exact deciderAdditive.program_mapOp_additiveHomStandard_isAdditive Reg.ans

/-- The fixed twelve-register source decider compiled to the natural-number RAM. Its input
convention is `ToRAM.paddedInput 12`, whose supplied zero prefix has length seventeen. -/
def paddedRamProgram : RAM.Program :=
  ToRAM.paddedProgramAdditive (deciderAdditive.program Reg.ans)

/-- `paddedRamProgram` equals `ToRAM.paddedProgram` applied to `decider.program Reg.ans`. -/
@[simp]
theorem paddedRamProgram_eq :
    paddedRamProgram = ToRAM.paddedProgram (decider.program Reg.ans) := by
  simp [paddedRamProgram, ToRAM.paddedProgramAdditive, ← Code.program_mapOp]

/-- The fixed compiled decider preceded by charged input relocation and workspace clearing.
Its external input convention is `RAM.Input.encode 5`. -/
def ramProgram : RAM.Program :=
  ToRAM.preparedProgramAdditive (deciderAdditive.program Reg.ans)

/-- `ramProgram` equals `ToRAM.preparedProgram` applied to `decider.program Reg.ans`. -/
@[simp]
theorem ramProgram_eq :
    ramProgram = ToRAM.preparedProgram (decider.program Reg.ans) := by
  simp [ramProgram, ToRAM.preparedProgramAdditive, ← Code.program_mapOp]

private theorem exists_nodup_execution (a : Input) :
    ∃ t, Executes (logWidth 2 a.1.length) (deciderAdditive.program Reg.ans) (State.init a.1)
      (if a.1.Nodup then 1 else 0) t ∧ t ≤ 16 * (a.1.length + 1) := by
  obtain ⟨v, t, he, ht, hv, hnodup⟩ :=
    decidesInTime_nodup_additive a (logWidth 2 a.1.length) le_rfl (inputFits a le_rfl)
  have hvalue : v = if a.1.Nodup then 1 else 0 := by
    change v = 1 ↔ a.1.Nodup at hnodup
    by_cases ha : a.1.Nodup
    · simp [ha, hnodup.mpr ha]
    · simp only [ite_eq_right ha]
      have : v ≠ 1 := fun h => ha (hnodup.mp h)
      lia
  exact ⟨t, hvalue ▸ he, ht⟩

private theorem compiled_cost_le {n t : ℕ} (ht : t ≤ 16 * (n + 1)) :
    48 * (t + 1) * (logWidth 2 n + 1) ≤ 2448 * (n + 1) * (Nat.log 2 (n + 1) + 1) := by
  have ht' : t + 1 ≤ 17 * (n + 1) := by lia
  have hw : logWidth 2 n + 1 ≤ 3 * (Nat.log 2 (n + 1) + 1) := by
    have := Nat.log_mono_right (b := 2) (Nat.le_succ n)
    dsimp [logWidth]
    lia
  calc
    _ ≤ 48 * (17 * (n + 1)) * (3 * (Nat.log 2 (n + 1) + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 48 ht') hw
    _ = _ := by ring

/-- Bounded-universe element distinctness has logarithmic RAM cost
`2448 (n + 1) (log₂(n + 1) + 1)` from the supplied padded-input convention. The constant is
not optimized. All source and compiler instructions are charged, but constructing the
initial padded list is not included. -/
theorem haltsWithResultInTime_nodup_padded (a : Input) :
    RAM.HaltsWithResultInTime RAM.logCost paddedRamProgram (ToRAM.paddedInput 12 a.1)
      (if a.1.Nodup then 1 else 0)
      (2448 * (a.1.length + 1) * (Nat.log 2 (a.1.length + 1) + 1)) := by
  obtain ⟨t, he, ht⟩ := exists_nodup_execution a
  exact (ToRAM.haltsWithResultInTime_padded_additive (inputFits a le_rfl) he).mono
    (compiled_cost_le ht)

/-- Bounded-universe element distinctness has logarithmic RAM cost
`2735 (n + 1) (log₂(n + 1) + 1)` including input relocation and workspace clearing. The same
fixed program handles every input, whose entries must be below its length. Installing the
external five-zero prefix, length header and words is uncharged; all instructions are charged. -/
theorem haltsWithResultInTime_nodup (a : Input) :
    RAM.HaltsWithResultInTime RAM.logCost ramProgram (RAM.Input.encode 5 a.1)
      (if a.1.Nodup then 1 else 0)
      (2735 * (a.1.length + 1) * (Nat.log 2 (a.1.length + 1) + 1)) := by
  obtain ⟨t, he, ht⟩ := exists_nodup_execution a
  have hlen : RAM.bitLength a.1.length ≤ Nat.log 2 (a.1.length + 1) + 1 :=
    RAM.bitLength_mono (Nat.le_succ a.1.length)
  have hinput (x : ℕ) (hx : x ∈ a.1) : RAM.bitLength x ≤ Nat.log 2 (a.1.length + 1) + 1 :=
    (RAM.bitLength_mono (a.2 x hx).le).trans hlen
  have h := ToRAM.haltsWithResultInTime_prepared_of_bitLength_le_additive
    (inputFits a le_rfl) he hlen hinput
  refine h.mono ?_
  change 287 * (a.1.length + 1) * (Nat.log 2 (a.1.length + 1) + 1) +
    48 * (t + 1) * (logWidth 2 a.1.length + 1) ≤ _
  calc
    _ ≤ 287 * (a.1.length + 1) * (Nat.log 2 (a.1.length + 1) + 1) +
        2448 * (a.1.length + 1) * (Nat.log 2 (a.1.length + 1) + 1) :=
      Nat.add_le_add_left (compiled_cost_le ht) _
    _ = _ := by ring

end Cslib.Algorithms.WordRAM.ElementDistinctness

end
