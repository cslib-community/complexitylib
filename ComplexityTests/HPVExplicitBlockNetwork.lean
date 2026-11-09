/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork
import Complexity.Foundations.Data.Nat.Log

/-! Explicit block-counting networks of concrete fair-coin machines: the letter numbering on
concrete letters, the counting identity, and the size, degree and bipartition of the networks. -/

namespace ComplexityTests.HPVExplicitBlockNetwork

open Turing MultiTapeMachine MultiTapePTM Cslib.Circuits.Frontier

/-- Emit the first coin and halt. No work tapes; the input head stays. -/
private def emitCoin : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

/-- On one work tape, write every coin and move right. The first step emits its coin; then the
machine keeps walking without output. -/
private def walk : MultiTapePTM 1 Bool Bool where
  initial := false
  tr state _ _ _ bit := .step
    { inputTape := 1,
      workTapes := fun _ => (some (some bit), 1),
      output := if state then none else some bit, state := some true }
    Empty.elim Empty.elim

/-! ### The letter numbering -/

/-- With two states, one work tape and blocks of two cells, there are
`3 * (2 ^ 2 * 3) = 36` control records, numbered first. The block holding `true` twice is
contents number `2 + 2 * 3 = 8`, so letter number `44`. -/
example : (letterEquiv (k := 1) (b := 2) finTwoEquiv.symm (.inr fun _ => some true) : ℕ) = 44 :=
  by decide

/-- The record of state `true` with both offsets `1` and output track `accept`: state digit `2`,
offset digits `1 + 1 * 2 = 3`, track digit `1`, so number `2 * 12 + (3 * 3 + 1) = 34`. -/
example : (letterEquiv (k := 1) (b := 2) finTwoEquiv.symm
    (.inl (some true, fun _ => 1, .accept)) : ℕ) = 34 := by decide

/-- The code of letter `44 = 0b101100` in `(2 + 1 + 4) * 2 = 14` bits, least significant first. -/
example : List.ofFn (letterCode (k := 1) (b := 2) finTwoEquiv.symm (.inr fun _ => some true)) =
    [false, false, true, true, false, true, false, false, false, false, false, false, false,
      false] := by decide

/-! ### The counting identity -/

-- One interval of two bits: the strings starting with `true` accept.
example : ∑ σ : Schedule 0 1,
    (emitCoin.explicitBlockNetwork [] 2 σ (Equiv.ofUnique Unit (Fin 1))).contraction = 2 := by
  rw [sum_contraction_explicitBlockNetwork _ _ _ _ one_pos,
    show emitCoin.acceptCount [] (1 * 2) = 2 by decide]

-- Two intervals of two bits, with windows on the work tape: half of the `16` strings accept.
example : ∑ σ : Schedule 1 2,
    (walk.explicitBlockNetwork [true] 2 σ finTwoEquiv.symm).contraction = 8 := by
  rw [sum_contraction_explicitBlockNetwork _ _ _ _ two_pos,
    show walk.acceptCount [true] (2 * 2) = 8 by decide]

/-! ### Size, degree and bipartition -/

-- Letters of `14` bits; `2 * (2 * 4 * 14) = 224` edges; `10` old vertices and `112` subdivision
-- vertices; degree at most `2 * 4 * 14 = 112`; the `10` old vertices are the rows; every table has
-- an entry for each list of bits on its ports, and every entry is at most `2 ^ 2`.
example (σ : Schedule 1 2) :
    letterBits 1 2 2 = 14 ∧
      (walk.explicitBlockNetwork [true] 2 σ finTwoEquiv.symm).numEdges = 224 ∧
      (walk.explicitBlockNetwork [true] 2 σ finTwoEquiv.symm).vertices.length = 122 ∧
      (walk.explicitBlockNetwork [true] 2 σ finTwoEquiv.symm).maxDegree ≤ 112 ∧
      (walk.explicitBlockNetwork [true] 2 σ finTwoEquiv.symm).IsRowsFirstBipartite 10 ∧
      ∀ p ∈ (walk.explicitBlockNetwork [true] 2 σ finTwoEquiv.symm).vertices,
        p.2.length = 2 ^ p.1.length ∧ ∀ a ∈ p.2, a ≤ 4 :=
  ⟨rfl, numEdges_explicitBlockNetwork .., length_vertices_explicitBlockNetwork ..,
    maxDegree_explicitBlockNetwork_le .., isRowsFirstBipartite_explicitBlockNetwork ..,
    fun _ hp => ⟨length_table_explicitBlockNetwork _ _ _ _ _ hp,
      fun _ ha => entry_le_explicitBlockNetwork _ _ _ _ _ hp ha⟩⟩

-- At the clock `t = 2`, blocks of `⌈log₂ 4⌉ = 2` steps and one interval: the network of
-- `emitCoin` is rows-first bipartite with at most `6 * 1 * 5 * 2 = 60` edges (it has
-- `2 * (1 * 1 * 10) = 20`) and degree at most `6 * 1 * 5 * ⌊log₂ 2⌋ = 30`.
example (σ : Schedule 0 1) :
    (emitCoin.explicitBlockNetwork [] 2 σ (Equiv.ofUnique Unit (Fin 1))).IsRowsFirstBipartite 2 ∧
      (emitCoin.explicitBlockNetwork [] 2 σ (Equiv.ofUnique Unit (Fin 1))).numEdges ≤ 60 ∧
      (emitCoin.explicitBlockNetwork [] 2 σ (Equiv.ofUnique Unit (Fin 1))).maxDegree ≤ 30 := by
  have hb : 2 ≤ 3 * Nat.log 2 2 := by
    simpa [show Nat.clog 2 (2 + 2) = 2 by decide] using
      Nat.clog_two_add_two_le_three_mul_log_two (le_refl 2)
  have h := emitCoin.admissible_explicitBlockNetwork [] 2 σ (Equiv.ofUnique Unit (Fin 1)) hb
    (by norm_num)
  rw [show Nat.log 2 2 = 1 by decide] at h
  simpa using h

end ComplexityTests.HPVExplicitBlockNetwork
