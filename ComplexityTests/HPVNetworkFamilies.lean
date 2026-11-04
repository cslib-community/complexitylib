/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.BlockNetworks

/-! The block-counting network families of #1833: the networks of a concrete machine at a small
clock, their counting identity and admissibility, and the class containments conditional only
on a contraction algorithm. -/

namespace ComplexityTests.HPVNetworkFamilies

open Turing MultiTapeMachine MultiTapeTM Cslib.Complexity Cslib.Complexity.CountingSimulation
  Cslib.Circuits.Frontier

/-- Emit the first coin and halt. No work tapes; the input head stays. -/
private def emitCoin : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

-- At the clock `t = 2`: blocks of `⌈log₂ 4⌉ = 2` steps, one interval, three schedule numbers.
example : blockLength 2 = 2 ∧ numBlocks 2 = 1 ∧ scheduleCount 1 2 = 3 ∧ paddedTime 2 = 2 := by
  decide

-- The networks of the three schedule numbers count the two accepting choice strings of two bits.
example : ∑ σ ∈ Finset.range (scheduleCount 1 2),
    (blockNetworkOf emitCoin (Equiv.ofUnique Unit (Fin 1)) ([], 2, σ)).2.contraction = 2 := by
  rw [sum_contraction_blockNetworkOf _ _ _ le_rfl, show paddedTime 2 = 2 by decide]
  decide

-- Each network is admissible at size `2` with constant `6 * 1 * 5 = 30`; it has the two old
-- vertices of its one interval as rows.
example (σ : ℕ) : ExplicitAdmissible 30 2
    (blockNetworkOf emitCoin (Equiv.ofUnique Unit (Fin 1)) ([], 2, σ)) ∧
    (blockNetworkOf emitCoin (Equiv.ofUnique Unit (Fin 1)) ([], 2, σ)).1 = 2 :=
  ⟨explicitAdmissible_blockNetworkOf _ _ _ σ le_rfl,
    show numBlocks 2 * (3 * 0 + 2) = 2 by decide⟩

-- The family of `emitCoin` blocks one head, the input head.
example : (blockNetworkFamily emitCoin (Equiv.ofUnique Unit (Fin 1))).heads = 1 := rfl

-- The class containments assume only a contraction algorithm.
example {α : Type} {enc : α ↪ List Bool} {T : ℕ → ℕ}
    (A : ContractionAlgorithm (encPair encNat ExplicitTensorNetwork.encExplicitNetwork)
      (fun G => G.2.contraction) ExplicitAdmissible)
    (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    NTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  NTIME_subset_iUnion_DTIME_of_contractionAlgorithm A hT hTn

end ComplexityTests.HPVNetworkFamilies
