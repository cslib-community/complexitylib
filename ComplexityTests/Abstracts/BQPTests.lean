/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.BQPAbstract
import ComplexityTests.BQP

/-! # Concrete clients of the public `BQP ⊆ PP` abstract

The explicit gate formulas act as expected on small registers: Toffoli flips its target exactly
when both controls are one, and one Hadamard gate on qubit `0` accepts with probability `1/2`. The
first-bit language, decided exactly by a family without gates, is in the public `BQP`, so the
headline places it in the public `PP`.
-/

namespace ComplexityTests.Abstracts.BQPTests

open ComplexityAbstracts ComplexityAbstracts.BQPAbstract

/-! ### The explicit gates -/

-- Toffoli with controls `0, 1` and target `2` maps `110` to `111` and fixes `100`.
example : flip 2 [0, 1] (![true, true, false] : Fin 3 → Bool) = ![true, true, true] := by decide
example : flip 2 [0, 1] (![true, false, false] : Fin 3 → Bool) = ![true, false, false] := by
  decide

-- NOT on qubit `1`, and CNOT from qubit `0` to qubit `1`.
example : flip 1 [] (![false, false] : Fin 2 → Bool) = ![false, true] := by decide
example : flip 1 [0] (![true, true] : Fin 2 → Bool) = ![true, false] := by decide

-- Well-formedness: a Toffoli gate needs three distinct qubits in range; Hadamard has no controls.
example : WellFormed 3 (false, 2, [0, 1]) := ⟨by decide, by decide, by decide⟩
example : ¬WellFormed 3 (false, 1, [1]) := fun h => absurd h.2.1 (by decide)
example : ¬WellFormed 2 (true, 0, [1]) := fun h => absurd h.2 (by decide)

/-- A single Hadamard gate on qubit `0` accepts with probability `1/2`, on every input. -/
theorem acceptProb_hadamard (x : List Bool) :
    acceptProb (x.length + 1) [(true, 0, [])] x = 1 / 2 := by
  have hwf : ∀ g ∈ [((true, 0, []) : GateCode)],
      Cslib.Quantum.GateCode.WellFormed (x.length + 1) g := by
    intro g hg
    rw [List.mem_singleton.mp hg]
    exact ⟨Nat.succ_pos _, rfl⟩
  exact (BQPBridge.acceptProb_eq hwf x).trans (ComplexityTests.BQP.acceptProb_hadamardOnce x)

/-! ### Membership and the headline -/

/-- The library's `BQP` is contained in the public one. -/
theorem mem_BQP_of_mem {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ Cslib.Complexity.BQP enc) : A ∈ BQP enc := by
  obtain ⟨width, gates, ⟨hwidth, hgates, hn⟩, hdec⟩ := BQPBridge.mem_BQP_iff.mpr hA
  have hwf (m : ℕ) (g : GateCode) (h : Cslib.Quantum.GateCode.WellFormed m g) :
      WellFormed m g := by
    obtain ⟨_ | _, t, cs⟩ := g <;> exact h
  exact ⟨width, gates, ⟨hwidth, hgates, fun n => ⟨(hn n).1, (hn n).2.1,
    fun g hg => hwf _ g ((hn n).2.2 g hg)⟩⟩, hdec⟩

/-- Words whose first bit is one are in the public `BQP`. -/
theorem firstBit_mem_BQP :
    ComplexityTests.BQP.FirstBit ∈ BQP ComplexityTests.Abstracts.Encoding.encBits :=
  mem_BQP_of_mem ComplexityTests.BQP.firstBit_mem_BQP

/-- The headline then places them in the public `PP`. -/
example : ComplexityTests.BQP.FirstBit ∈ PP ComplexityTests.Abstracts.Encoding.encBits :=
  BQP_subset_PP _ firstBit_mem_BQP

end ComplexityTests.Abstracts.BQPTests
