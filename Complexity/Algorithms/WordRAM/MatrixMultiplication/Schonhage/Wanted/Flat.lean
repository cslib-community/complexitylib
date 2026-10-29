/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Input

/-!
# Initialized flat runs of native wanted-query grouping

## Main results

* `Wanted.runs`: one actual initialized native run returns grouped query codes, their
  original-position permutation and exact tile spans; halt is charged on that same run.
* `Wanted.bounded_reachable`: every initialized reachable prefix has fitting data words.

The returned unsigned pointer names the code array. Other addresses are explicit functions of
the original headers, and the complete original input and outside memory are preserved.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual initialized standard WordRAM runs, with the same final memory carrying all
answers, a charged halt, and the readonly-input/outside frame. -/
theorem runs {w L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N))
    (hfit : Fits w (wordBudget L m N qs.length)) :
    InputFits w (input L m qs) ∧
    ∃ y n, n ≤ timeBound L m N qs.length ∧
      Runs w (program.program codes) (State.init (input L m qs)) ⟨program.size, y⟩ n ∧
      Executes w (program.program codes) (State.init (input L m qs))
        (codeAddress L m N qs.length) (n + 1) ∧ y.Bounded w ∧
      (∀ i : Fin qs.length,
        y.mem (codeAddress L m N qs.length +
            CountingSort.position (tileKey L m N ∘ inputPairs qs) qs.length i.val) =
            (PrunedQuery.queryIndex
              (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val ∧
          y.mem (originalAddress L m N qs.length +
            CountingSort.position (tileKey L m N ∘ inputPairs qs) qs.length i.val) = i.val) ∧
      (∀ t ≤ numBands L m N ^ 2, y.mem (offsetAddress L m N qs.length + t) =
        Nat.count (fun k => (tileKey L m N ∘ inputPairs qs) k < t) qs.length) ∧
      y.mem (offsetAddress L m N qs.length + numBands L m N ^ 2) = qs.length ∧
      (∀ a, a < inputLimit qs.length ∨ memoryLimit L m N qs.length ≤ a →
        y.mem a = (State.init (input L m qs) : State 96).data.mem a) := by
  obtain ⟨hi, y, ⟨n, hn, he⟩, hp, hb, hv, ho, ht, hf⟩ := exec_input hm qs hfit
  refine ⟨hi, y, n, hn, ?_, ?_, hb, hv, ho, ht, hf⟩
  · simpa only [Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := program.program codes) (Program.Contains.self _).append_left
  · simpa only [hp.codes, State.init] using he.executes codes

/-- Ordinary initialized native safety holds at every reachable prefix, including the
parameter, table, count and scatter stages, from the same original-input fit guarantee. -/
theorem bounded_reachable {w L m N n : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N))
    (hfit : Fits w (wordBudget L m N qs.length)) {y : State 96}
    (hy : Runs w (program.program codes) (State.init (input L m qs)) y n) :
    y.data.Bounded w := hy.bounded_init (input_fits hm qs hfit)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
