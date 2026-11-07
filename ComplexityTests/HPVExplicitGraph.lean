/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.GraphPolyTime

/-! The graph of the explicit block-counting networks on numbers: schedule numbers, edge targets
and ports for concrete machines, compared with the explicit networks, and the polynomial-time
certificate. -/

namespace ComplexityTests.HPVExplicitGraph

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

/-! ### Schedule numbers -/

-- With one work tape and two intervals, the digits of `σ = 2 + 1 * 3 + 0 * 9 + 2 * 27 = 59` are
-- `2, 1` for interval `0` (input head up, work head stays) and `0, 2` for interval `1`.
example : scheduleOfNat 1 2 59 0 none = 1 ∧ scheduleOfNat 1 2 59 0 (some 0) = 0 ∧
    scheduleOfNat 1 2 59 1 none = -1 ∧ scheduleOfNat 1 2 59 1 (some 0) = 1 := by decide

-- So at the start of interval `2` the input head is back in block `0` and the work head in
-- block `1`, counted by its digits `2` and `0`.
example : scheduleBlock (scheduleOfNat 1 2 59) 2 none = 0 ∧
    scheduleBlock (scheduleOfNat 1 2 59) 2 (some 0) = 1 := by
  rw [scheduleBlock_scheduleOfNat 59 le_rfl, scheduleBlock_scheduleOfNat 59 le_rfl]
  decide

-- Summing over the `3` schedule numbers of one interval without work tapes is summing over the
-- schedules: the strings of two bits starting with `true` accept.
example : ∑ σ ∈ Finset.range (3 ^ ((0 + 1) * 1)),
    (emitCoin.explicitBlockNetwork [] 2 (scheduleOfNat 0 1 σ)
      (Equiv.ofUnique Unit (Fin 1))).contraction = 2 := by
  rw [sum_range_scheduleOfNat (fun σ => (emitCoin.explicitBlockNetwork [] 2 σ
      (Equiv.ofUnique Unit (Fin 1))).contraction),
    sum_contraction_explicitBlockNetwork _ _ _ _ one_pos,
    show emitCoin.acceptCount [] (1 * 2) = 2 by decide]

/-! ### Edge targets and ports -/

-- `emitCoin` with one interval of two steps: letters of `(1 + 0 + 4) * 2 = 10` bits. The control
-- edge `0` ends at its sink, vertex `1`. The interval has the `10` source halves as ports, the
-- sink the `10` target halves, and subdivision vertex `2 + r` the two halves of copy `r`.
example : (emitCoin.explicitBlockNetwork [] 2 (scheduleOfNat 0 1 0)
    (Equiv.ofUnique Unit (Fin 1))).vertices.map Prod.fst =
      List.range 10 :: (List.range 10).map (· + 10) ::
        (List.range 10).map fun r => [r, r + 10] := by
  rw [map_fst_vertices_explicitBlockNetwork]
  decide

-- `walk` with two intervals, every head staying except the work head, which moves right in
-- interval `0`: digits `1, 2, 1, 1`, so `σ = 1 + 2 * 3 + 9 + 27 = 43`. The block edge `(0, 0, 2)`,
-- number `2 + 2 = 4`, carries block `1`, which is in the window of interval `1`. The block edge
-- `(0, 0, 0)`, number `2`, carries block `-1`, which is not: it ends at its sink `2 + 2`.
example : edgeTargetNum 1 2 43 4 = 1 ∧ edgeTargetNum 1 2 43 2 = 4 := by decide

-- With every head staying (all digits `1`, `σ = 40`), all three block edges of interval `0` end at
-- interval `1`, and the control edge of interval `1` ends at its sink `2 + 1`.
example : edgeTargetNum 1 2 40 2 = 1 ∧ edgeTargetNum 1 2 40 3 = 1 ∧ edgeTargetNum 1 2 40 4 = 1 ∧
    edgeTargetNum 1 2 40 1 = 3 := by decide

-- So in the network of `σ = 43`, with letters of `(2 + 1 + 4) * 2 = 14` bits, interval `1` has
-- the `4 * 14` source halves of its edges and the target halves of the control edge `0` and of
-- the block edges `3` and `4`: `56 + 42 = 98` ports.
example : ((walk.explicitBlockNetwork [true] 2 (scheduleOfNat 1 2 43)
    finTwoEquiv.symm).vertices.map Prod.fst)[1]!.length = 98 := by
  rw [map_fst_vertices_explicitBlockNetwork]
  decide

/-! ### Polynomial time -/

-- The ports are polynomial-time in the schedule number (binary) and the vertex (unary).
example : MultiTapeTM.ComputableInPolyTime (fun p : ℕ × ℕ => explicitPortsNum 1 2 14 p.1 p.2)
    (MultiTapeTM.encPair MultiTapeTM.encNat MultiTapeTM.encUnary)
    (MultiTapeTM.encList MultiTapeTM.encNat) :=
  computableInPolyTime_explicitPortsNum (.const _) (.const _)
    (MultiTapeTM.ComputableInPolyTime.fst _ _) (MultiTapeTM.ComputableInPolyTime.snd _ _)

end ComplexityTests.HPVExplicitGraph
