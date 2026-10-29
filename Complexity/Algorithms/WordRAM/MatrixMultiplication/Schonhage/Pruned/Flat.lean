/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Input

/-!
# Flat initialized executions of native pruned queries

## Main results

* `PrunedQuery.runs`: prefix `Runs` and charged halting `Executes` from actual `State.init`,
  connected to the same final memory, existing finite pruned values and outside frame.
* `PrunedQuery.bounded_reachable`: every reachable prefix has target-sized data words.

The single fixed program returns the unsigned pointer to its encoded answer list. Queries may
repeat and their order is preserved. Its 96 registers and code-size bound are independent of
depth, query count, input values and physical word width.
These initialized-run theorems, `runs_wide` in `Pruned.Width` and `exec_kernel` in
`Pruned.Kernel` are the client interfaces. Stage `exec_*` lemmas in their dependencies are
internal implementation APIs exported for proof composition.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual initialized flat executions. The prefix witness holding all answers is precisely
the state at the final halt, and the halt is charged as one further target instruction. -/
theorem runs {w L A B : ℕ} (hw : 0 < w) (a b : Fin (10 ^ L) → ℤ)
    (qs : List (Fin (10 ^ L))) (ha : ∀ v, |a v| ≤ (A : ℤ)) (hb : ∀ v, |b v| ≤ (B : ℤ))
    (hmag : magnitudeBound L A B < 2 ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L qs.length)) :
    InputFits (w + 2) (input L a b qs) ∧
    ∃ y n, n ≤ timeBound qs ∧
      Runs (w + 2) (program.program output) (State.init (input L a b qs))
        ⟨program.size, y⟩ n ∧
      Executes (w + 2) (program.program output) (State.init (input L a b qs))
        (outputBase L qs.length) (n + 1) ∧ y.Bounded (w + 2) ∧
      (∀ i : Fin qs.length, y.mem (outputBase L qs.length + i.val) = encode
        (Pruned.result L (fun v => a (Encoding.leafIndex v))
          (fun v => b (Encoding.leafIndex v)) (requested qs) (queryAt (qs.get i)))) ∧
      (∀ c, ¬(outputBase L qs.length ≤ c ∧ c < memoryEnd L qs.length) →
        y.mem c = (State.init (input L a b qs) : State registers).data.mem c) := by
  obtain ⟨hi, y, ⟨n, hn, he⟩, hb, hv, hf, ho⟩ := exec_input hw a b qs ha hb hmag haddr
  refine ⟨hi, y, n, hn, ?_, ?_, hb, hv, hf⟩
  · simpa only [Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := program.program output) (Program.Contains.self _).append_left
  · simpa only [ho, State.init] using he.executes output

/-- Ordinary native safety applies to every initialized reachable prefix, not merely the
returned witness. The admission hypotheses are the same numerical original-input bounds. -/
theorem bounded_reachable {w L A B n : ℕ} (hw : 0 < w) (a b : Fin (10 ^ L) → ℤ)
    (qs : List (Fin (10 ^ L))) (ha : ∀ v, |a v| ≤ (A : ℤ)) (hb : ∀ v, |b v| ≤ (B : ℤ))
    (hmag : magnitudeBound L A B < 2 ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L qs.length)) {y : State registers}
    (hy : Runs (w + 2) (program.program output) (State.init (input L a b qs)) y n) :
    y.data.Bounded (w + 2) :=
  hy.bounded_init (input_fits hw a b qs ha hb hmag haddr)

/-- An encoder producer's existing leaf-value contract gives the original bilinear product at
every supplied query. This is the same actual initialized program and charged run as `runs`;
the mathematical specialization adds no machine operation or assumed producer execution. -/
theorem runs_bilinear {w L A B : ℕ} (hw : 0 < w) (left right : Fin (10 ^ L) → ℤ)
    (qs : List (Fin (10 ^ L))) (a : LeftStr L → ℤ) (b : RightStr L → ℤ)
    (hleft : ∀ v, left (Encoding.leafIndex v) = encodingL a v)
    (hright : ∀ v, right (Encoding.leafIndex v) = encodingR b v)
    (ha : ∀ v, |left v| ≤ (A : ℤ)) (hb : ∀ v, |right v| ≤ (B : ℤ))
    (hmag : magnitudeBound L A B < 2 ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L qs.length)) :
    InputFits (w + 2) (input L left right qs) ∧
    ∃ y n, n ≤ timeBound qs ∧
      Runs (w + 2) (program.program output) (State.init (input L left right qs))
        ⟨program.size, y⟩ n ∧
      Executes (w + 2) (program.program output) (State.init (input L left right qs))
        (outputBase L qs.length) (n + 1) ∧ y.Bounded (w + 2) ∧
      (∀ i : Fin qs.length, y.mem (outputBase L qs.length + i.val) =
        encode (bilinearProduct a b (queryAt (qs.get i)))) ∧
      (∀ c, ¬(outputBase L qs.length ≤ c ∧ c < memoryEnd L qs.length) →
        y.mem c = (State.init (input L left right qs) : State registers).data.mem c) := by
  obtain ⟨hi, y, n, hn, hr, he, hy, hv, hf⟩ := runs hw left right qs ha hb hmag haddr
  refine ⟨hi, y, n, hn, hr, he, hy, ?_, hf⟩
  intro i
  have hvalue := hv i
  rw [show (fun v => left (Encoding.leafIndex v)) = encodingL a from funext hleft,
    show (fun v => right (Encoding.leafIndex v)) = encodingR b from funext hright,
    Pruned.result_eq_piecewise_bilinearProduct,
    Finset.piecewise_eq_of_mem _ _ _ (queryAt_mem_requested (List.get_mem qs i))] at hvalue
  exact hvalue

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
