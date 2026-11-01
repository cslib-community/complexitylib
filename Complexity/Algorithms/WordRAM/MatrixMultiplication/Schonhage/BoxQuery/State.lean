/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Memory
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Frontier
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.CompleteLeaf
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Decode

/-!
# Actual query-loop state and original-input resource bounds

The invariant connects real registers and stack words to finite frontier conservation.
It contains no assumed execution, time, intermediate fit or solver. The complete native
program establishes it from the original arrays and its actual constructed table.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- One original depth/span bound reserves enough task words without clearing them. -/
@[expose] def stackCapacity (L : ℕ) : ℕ := (L + 1) * 10 ^ L + 10

/-- Uniform scalar/address envelope of the reusable query, derived from its original arguments. -/
@[expose] def queryAddressBound (L t AA BB D V K : ℕ) : ℕ :=
  100 * (AA + BB + D + V + K + (L + 1) * 10 ^ L + t + 64)

/-- Pure readback and conservation data for the actual native frontier. -/
structure Ready {L : ℕ} (η : OutStr L) (m t AA BB D V K F : ℕ) (a b : Leaf L → ℤ)
    (finished : List (Leaf L)) (tasks : List (List Term)) (x : Data registers) : Prop where
  /-- Original scalar arguments and initialized constants. -/
  parameters : Parameters L t (PrunedQuery.queryIndex η).val AA BB D V K F x
  /-- Finite occurrences, values and remaining work agree with the original query. -/
  frontier : FrontierInvariant η t (leafQueryValue m t η a b) finished tasks
  /-- The actual occupied-record count. -/
  top : x.regs Reg.top = tasks.length
  /-- Every actual pending task word. -/
  stack : StackMemory η F tasks x.mem
  /-- The actual canonical signed accumulator. -/
  answer : x.regs Reg.answer = Signed.encode ((finished.map (leafQueryValue m t η a b)).sum)
  /-- Protected original arrays and actual constructed-table words. -/
  table : Readback m t D V AA BB a b x.mem

/-- The pending actual stack count follows from the original finite query cardinality. -/
theorem Ready.pending_le {L m t AA BB D V K F : ℕ} {η : OutStr L} {a b : Leaf L → ℤ}
    {finished : List (Leaf L)} {tasks : List (List Term)} {x : Data registers}
    (h : Ready η m t AA BB D V K F a b finished tasks x)
    (hη : (innerSetO η).card = m) : tasks.length ≤ (L + 1) * 10 ^ L := by
  have hc : (possibleLeaves η t []).card ≤ 10 ^ L := by
    rw [possibleLeaves_root_eq_queryLeaves η hη]
    exact card_queryLeaves_le_span t η hη
  exact h.frontier.pending_length_le.trans (Nat.mul_le_mul_left _ hc)

/-- The actual signed accumulator needs no supplied intermediate-fit certificate. -/
theorem Ready.answer_natAbs_le {L m t AA BB D V K F A B : ℕ} {η : OutStr L}
    {a b : Leaf L → ℤ} {finished : List (Leaf L)} {tasks : List (List Term)}
    {x : Data registers} (h : Ready η m t AA BB D V K F a b finished tasks x)
    (hη : (innerSetO η).card = m)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B) :
    ((finished.map (leafQueryValue m t η a b)).sum).natAbs ≤ magnitudeBound L A B := by
  have hc : (possibleLeaves η t []).card ≤ 10 ^ L := by
    rw [possibleLeaves_root_eq_queryLeaves η hη]
    exact card_queryLeaves_le_span t η hη
  have hfinished := h.frontier.finished_length_le.trans hc
  have hm := natAbs_sum_take_leafQueryValue_le m t η a b ha hb finished hfinished finished.length
  have hs : ((finished.map (leafQueryValue m t η a b)).sum).natAbs ≤
      10 ^ (2 * L) * (A * B) := by
    simpa only [← List.length_map (f := leafQueryValue m t η a b), List.take_length] using hm
  exact hs.trans (by unfold magnitudeBound; omega)

/-- The proof-only native-memory measure agrees with the invariant's finite frontier work. -/
theorem Ready.work_eq {L m t AA BB D V K F : ℕ} {η : OutStr L} {a b : Leaf L → ℤ}
    {finished : List (Leaf L)} {tasks : List (List Term)} {x : Data registers}
    (h : Ready η m t AA BB D V K F a b finished tasks x) :
    workMeasure η t F x = frontierWork η t tasks := workMeasure_eq h.stack h.top

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
