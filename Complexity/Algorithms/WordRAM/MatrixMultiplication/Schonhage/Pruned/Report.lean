/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory
public import Complexity.Computability.WordRAM.Heap

/-!
# Returning queried values in the actual input order

## Main results

* `PrunedQuery.exec_report`: the native reporting loop preserves duplicate requests and writes
  their corresponding values in order, charging every load, address, store and loop test.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Registers used while reporting the explicitly supplied query list. -/
def ReportLocal (i : Fin registers) : Prop :=
  i = index ∨ i = address ∨ i = query ∨ i = temporary

instance (i : Fin registers) : Decidable (ReportLocal i) :=
  inferInstanceAs (Decidable (i = index ∨ i = address ∨ i = query ∨ i = temporary))

private theorem reportStep_preserves (i : Fin registers) :
    ¬ReportLocal i → reportStep.Preserves i := by decide +kernel +revert

private theorem report_preserves (i : Fin registers) :
    ¬ReportLocal i → report.Preserves i := by decide +kernel +revert

/-- The finite native loop reads the original requests, including duplicates. Its only writes
are the `N` output cells; the value directory and original requests remain unchanged. -/
theorem exec_report {w N capacity : ℕ} (x : Data registers) (codes : ℕ → ℕ)
    (hN : x.regs queryCount = N)
    (hinput : ∀ i < N, x.mem (x.regs queries + i) = codes i)
    (hcodes : ∀ i < N, codes i < capacity)
    (hsrc : x.regs queries + N ≤ x.regs output ∨
      x.regs output + N ≤ x.regs queries)
    (hvals : x.regs values + capacity ≤ x.regs output ∨
      x.regs output + N ≤ x.regs values)
    (h1 : x.regs one = 1)
    (hw : Fits w (x.regs queries + N + x.regs values + capacity +
      x.regs output + N + N + 12)) :
    ∃ y, ExecWithin w report x y (9 * N + 3) ∧ y.regs index = N ∧
      (∀ i < N, y.mem (x.regs output + i) = x.mem (x.regs values + codes i)) ∧
      Modifies (Block.mk (x.regs output) N).footprint x.mem y.mem ∧
      (∀ i, ¬ReportLocal i → y.regs i = x.regs i) := by
  let u := x.set index 0
  have hsetup : ExecWithin w (ram[ index ← #0 ] : Code .standard registers) x u 1 := by
    ram_eval [u]
  let I (y : Data registers) : Prop :=
    y.regs index ≤ N ∧
    (∀ i < y.regs index, y.mem (x.regs output + i) = x.mem (x.regs values + codes i)) ∧
    (∀ i < N, y.mem (x.regs queries + i) = codes i) ∧
    (∀ q < capacity, y.mem (x.regs values + q) = x.mem (x.regs values + q)) ∧
    Modifies (Block.mk (x.regs output) N).footprint x.mem y.mem ∧
    (∀ i, ¬ReportLocal i → y.regs i = x.regs i)
  have hinit : I u := by
    refine ⟨by simp [u], ?_, hinput, fun _ _ => rfl, Modifies.refl _ _, ?_⟩
    · simp only [u, Data.set_regs, Function.update_self, not_lt_zero, false_implies,
        implies_true]
    · intro i hi
      exact Function.update_of_ne (by intro he; exact hi (Or.inl he)) _ _
  have hstep (y : Data registers) (hy : I y)
      (hc : (Cond.lt index queryCount).Holds y) :
      ∃ z, ExecWithin w reportStep y z 7 ∧ I z ∧ N - z.regs index < N - y.regs index := by
    obtain ⟨hle, hdone, hread, hvalue, hframe, hfrozen⟩ := hy
    have hq := hfrozen queries (by decide)
    have hv := hfrozen values (by decide)
    have ho := hfrozen output (by decide)
    have hn := (hfrozen queryCount (by decide)).trans hN
    have h1' := (hfrozen one (by decide)).trans h1
    have hk : y.regs index < N := by simpa only [Cond.holds_lt, hn] using hc
    let k := y.regs index
    let value := x.mem (x.regs values + codes k)
    let z := (((((((y.set address (y.regs queries + k)).set query (codes k)).set
      address (y.regs values + codes k)).set temporary value).set
      address (y.regs output + k)).write (y.regs output + k) value).set index (k + 1))
    have hread' : y.mem (y.regs queries + k) = codes k := by rw [hq]; exact hread k hk
    have hval' : y.mem (y.regs values + codes k) = value := by
      rw [hv]
      exact hvalue (codes k) (hcodes k hk)
    have hqa : Fits w (y.regs queries + k) := hw.of_le (by rw [hq]; dsimp [k]; omega)
    have hva : Fits w (y.regs values + codes k) :=
      hw.of_le (by rw [hv]; have := hcodes k hk; omega)
    have hoa : Fits w (y.regs output + k) := hw.of_le (by rw [ho]; dsimp [k]; omega)
    have hki : Fits w (k + 1) := hw.of_le (by dsimp [k]; omega)
    have hz : ExecWithin w reportStep y z 7 := by
      ram_eval [reportStep, z, k, value, hread', hval', h1', hqa, hva, hoa, hki,
        index, address, query, temporary, queries, values, output, one, Fin.mk.injEq]
    have hmem : z.mem = Function.update y.mem (x.regs output + k) value := by
      simp only [z, Data.set_mem, Data.write_mem, ho]
    have hidx : z.regs index = k + 1 := by simp [z]
    have hawaySrc (i : ℕ) (hi : i < N) : x.regs queries + i ≠ x.regs output + k := by
      rcases hsrc with h | h <;> dsimp [k] <;> omega
    have hawayVal (q : ℕ) (hq' : q < capacity) :
        x.regs values + q ≠ x.regs output + k := by
      rcases hvals with h | h <;> dsimp [k] <;> omega
    refine ⟨z, hz, ?_, by dsimp [k] at hidx; omega⟩
    refine ⟨by dsimp [k] at hidx; omega, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [hidx] at hi
      by_cases he : i = k
      · subst i
        simp only [hmem, Function.update_self, value]
      · rw [hmem, Function.update_of_ne (by omega : x.regs output + i ≠ x.regs output + k)]
        exact hdone i (by dsimp [k] at hi; omega)
    · intro i hi
      rw [hmem, Function.update_of_ne (hawaySrc i hi)]
      exact hread i hi
    · intro q hq'
      rw [hmem, Function.update_of_ne (hawayVal q hq')]
      exact hvalue q hq'
    · intro a ha
      have hnot : a ≠ x.regs output + k := by
        intro he
        apply ha
        rw [Block.mem_footprint]
        change x.regs output ≤ a ∧ a < x.regs output + N
        dsimp [k] at he
        omega
      rw [hmem, Function.update_of_ne hnot]
      exact hframe a ha
    · exact fun i hi => (hz.regs_eq (reportStep_preserves i hi)).trans (hfrozen i hi)
  obtain ⟨y, hy, hIy, hstop⟩ := ExecWithin.loop_invariant I (fun y => N - y.regs index)
    hstep hinit
  obtain ⟨hle, hdone, _, _, hframe, hfrozen⟩ := hIy
  have hn := (hfrozen queryCount (by decide)).trans hN
  have hidx : y.regs index = N := by
    simp only [Cond.holds_lt, hn, not_lt] at hstop
    omega
  have hloop : ExecWithin w (.loop (.lt index queryCount) reportStep) u y (9 * N + 2) := by
    simpa only [u, Data.set_regs, Function.update_self, Nat.sub_zero, Nat.mul_comm] using hy
  have he : ExecWithin w report x y (9 * N + 3) := (hsetup.seq hloop).mono (by omega)
  exact ⟨y, he, hidx, by simpa only [hidx] using hdone, hframe,
    fun i hi => he.regs_eq (report_preserves i hi)⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
