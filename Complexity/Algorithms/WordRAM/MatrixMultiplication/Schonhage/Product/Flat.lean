/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Exec

/-!
# Initialized flat native queried products

## Main results

* `QueriedProduct.runs`: actual `State.init` executions, exact original-order product values,
  guaranteed input fit, complete frame and a charged halt tied to the same final memory.
* `QueriedProduct.bounded_reachable`: every initialized reachable prefix has fitting data words.
* `QueriedProduct.program_length_le`: one fixed finite 160-register program for each input mode.

The code is independent of all dimensions, entry magnitudes, query counts and word widths.
These results are component results; they do not instantiate a complete Exact Triangle solver
or the ordinary-3SUM endpoint under #1394.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

set_option maxRecDepth 8192 in
-- This closed structural check traverses the two fixed native program trees and signed kernels.
/-- The full flattened instruction list, including halt, is fixed independently of the input. -/
public theorem program_length_le (bits : Bool) :
    (program bits |>.program output).length ≤ 32768 := by
  cases bits <;> decide +kernel

set_option maxRecDepth 8192 in
-- This is a finite syntactic check of the actual code, including each renamed producer/kernel.
/-- Neither mode reads the physical width; the same fixed code runs at every admitted width. -/
public theorem not_readsWidth (bits : Bool) : ¬(program bits).ReadsWidth := by
  cases bits <;> decide +kernel

/-- Original matrices and coordinates initialize the real native run. The charged prefix
reaches the same memory that contains all product values, and its next instruction halts. -/
public theorem runs {w L m N A : ℕ} (hw : 0 < w) (hm : m ≤ L) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hX : ∀ i k, |X i k| ≤ (A : ℤ))
    (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hbits : bits = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j))
    (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N qs.length)) :
    InputFits (w + 2) (input bits L X Y qs) ∧
    ∃ y n, n ≤ timeBound hm qs ∧
      Runs (w + 2) ((program bits).program output) (State.init (input bits L X Y qs))
        ⟨(program bits).size, y⟩ n ∧
      Executes (w + 2) ((program bits).program output) (State.init (input bits L X Y qs))
        (outputBase L m N qs.length) (n + 1) ∧ y.Bounded (w + 2) ∧
      (∀ i : Fin qs.length, y.mem (outputBase L m N qs.length + i.val) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, ¬(inputEnd m N qs.length ≤ a ∧ a < memoryEnd L m N qs.length) →
        y.mem a = (State.init (input bits L X Y qs) : State 160).data.mem a) := by
  have hi := input_fits hw hm bits X Y qs hX hY hmag hfit
  obtain ⟨y, he, hp, hv, hf⟩ := exec hw hm bits X Y qs
    (State.init (input bits L X Y qs)).data (by intro _ _ _; rfl) hX hY hbits hmag hfit
  have hy := he.bounded (Data.Bounded.init hi)
  obtain ⟨n, hn, he⟩ := he
  refine ⟨hi, y, n, hn, ?_, ?_, hy, hv, hf⟩
  · simpa only [Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := (program bits).program output) (Program.Contains.self _).append_left
  · simpa only [hp.output, State.init] using he.executes output

/-- Every reachable initialized prefix is bounded at the same physical width. -/
public theorem bounded_reachable {w L m N A n : ℕ} (hw : 0 < w) (hm : m ≤ L) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hX : ∀ i k, |X i k| ≤ (A : ℤ))
    (hY : ∀ k j, |Y k j| ≤ (A : ℤ)) (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N qs.length)) {y : State 160}
    (hy : Runs (w + 2) ((program bits).program output) (State.init (input bits L X Y qs)) y n) :
    y.data.Bounded (w + 2) := hy.bounded_init (input_fits hw hm bits X Y qs hX hY hmag hfit)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
