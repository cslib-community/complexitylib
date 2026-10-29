/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Flat
public import Mathlib.Data.Nat.Log

/-!
# Sufficient physical width for native wanted-query grouping

## Main definitions

* `Wanted.admissionWidth`: a positive ceiling-logarithmic threshold from original parameters.

## Main results

* `Wanted.runs_wide`: input fit and actual initialized runs at every admitted physical width.
* `Wanted.program_length_le`: a fixed finite code-size bound independent of the input.

Coordinates and query codes are unsigned. No signed-kernel width adjustment is needed for
this routing component. Relating its parameters to a whole 3SUM input remains composition work.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Positive sufficient physical width, logarithmic in the explicit original-parameter budget.
The program does not read the width or this threshold. -/
def admissionWidth (L m N Q : ℕ) : ℕ := Nat.clog 2 (wordBudget L m N Q + 1) + 1

/-- The width condition admits positive widths even for zero dimension and empty queries. -/
theorem admissionWidth_pos (L m N Q : ℕ) : 0 < admissionWidth L m N Q := by
  unfold admissionWidth
  omega

/-- A sufficiently large physical width guarantees the actual numerical fit premise. -/
theorem admission_fit {W L m N Q : ℕ} (hW : admissionWidth L m N Q ≤ W) :
    Fits W (wordBudget L m N Q) := by
  have hc := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (wordBudget L m N Q + 1)
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
    (by unfold admissionWidth at hW; omega : Nat.clog 2 (wordBudget L m N Q + 1) ≤ W)
  change wordBudget L m N Q < 2 ^ W
  omega

/-- Actual initialized runs at every sufficiently wide physical width. The same returned
memory holds the original-index permutation, query codes, exact spans and readonly frame. -/
theorem runs_wide {W L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N))
    (hW : admissionWidth L m N qs.length ≤ W) :
    InputFits W (input L m qs) ∧
    ∃ y n, n ≤ timeBound L m N qs.length ∧
      Runs W (program.program codes) (State.init (input L m qs)) ⟨program.size, y⟩ n ∧
      Executes W (program.program codes) (State.init (input L m qs))
        (codeAddress L m N qs.length) (n + 1) ∧ y.Bounded W ∧
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
        y.mem a = (State.init (input L m qs) : State 96).data.mem a) :=
  runs hm qs (admission_fit hW)

/-- The code is one finite 96-register program; all data-dependent repetition is in loops. -/
theorem program_length_le : (program.program codes).length ≤ 4096 := by decide +kernel

/-- The native program is uniform across admitted widths. -/
theorem not_readsWidth : ¬program.ReadsWidth := by decide +kernel

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
