/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.BlockNetwork

/-! Block-counting networks of concrete fair-coin machines: summed over schedules, their
contractions are accepting counts computed directly. -/

namespace ComplexityTests.HPVBlockNetwork

open Turing MultiTapeMachine

/-- Emit the first coin and halt. No work tapes; the input head stays. -/
private def emitCoin : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

-- One interval of two bits: the strings starting with `true` accept.
example : ∑ σ : MultiTapePTM.Schedule 0 1, (emitCoin.blockNetwork [] 2 σ).contraction = 2 := by
  rw [MultiTapePTM.sum_contraction_blockNetwork _ _ _ one_pos,
    show emitCoin.acceptCount [] (1 * 2) = 2 by decide]

/-- On one work tape, write every coin and move right. The first step emits its coin; then the
machine keeps walking without output. -/
private def walk : MultiTapePTM 1 Bool Bool where
  initial := false
  tr state _ _ _ bit := .step
    { inputTape := 1,
      workTapes := fun _ => (some (some bit), 1),
      output := if state then none else some bit, state := some true }
    Empty.elim Empty.elim

-- Two intervals of two bits, with windows on the work tape: half of the `16` strings accept.
example :
    ∑ σ : MultiTapePTM.Schedule 1 2, (walk.blockNetwork [true] 2 σ).contraction = 8 := by
  rw [MultiTapePTM.sum_contraction_blockNetwork _ _ _ two_pos,
    show walk.acceptCount [true] (2 * 2) = 8 by decide]

-- Each network has `2 * (3 + 1) = 8` edges and `2 * (3 + 2) = 10` vertices, degree at most `8`,
-- no loops, and entries at most `2 ^ 2`.
example (σ : MultiTapePTM.Schedule 1 2) :
    Fintype.card (MultiTapePTM.BlockEdge 1 2) = 8 ∧
      Fintype.card (Fin 2 ⊕ MultiTapePTM.BlockEdge 1 2) = 10 ∧
      (walk.blockNetwork [true] 2 σ).MaxDegreeLE 8 ∧ (walk.blockNetwork [true] 2 σ).Loopless ∧
      ∀ v x, (walk.blockNetwork [true] 2 σ).tensor v x ≤ 4 :=
  ⟨MultiTapePTM.card_blockEdge, MultiTapePTM.card_blockVertex,
    walk.maxDegreeLE_blockNetwork _ _ σ, walk.loopless_blockNetwork _ _ σ,
    walk.tensor_blockNetwork_le _ _ σ⟩

end ComplexityTests.HPVBlockNetwork
