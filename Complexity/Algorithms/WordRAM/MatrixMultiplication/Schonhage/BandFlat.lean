/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandInput

/-!
# Flat native preparation of every public band encoding

## Main results

* `BandPreparation.runs`: actual flat `State.init` run, all public left/right encodings for
  the computed deterministic layout, retained computed tables, input/outside frame and charged halt.
* `BandPreparation.program_length_le`: one fixed finite program, independent of every parameter.

This is a bounded preparation component under the ordinary native 3SUM objective, not a
whole 3SUM algorithm or a pruned-query evaluation theorem.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The left catalogue retains the original mathematical band and leaf interfaces. -/
theorem catalogueValue_left {L m N : ℕ} (hm : m ≤ L)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (matrix : ℕ → ℕ → ℤ)
    (hX : ∀ i k, matrix i.val k.val = X i k) (β : ℕ) (τ : Leaf L) :
    catalogueValue L m N false matrix β (Encoding.leafIndex τ).val =
      encodingL (bandArrayL (MaskTable.layout hm) X β) τ := by
  apply Encoding.value_final_left
  intro u
  simpa only [Equiv.symm_apply_apply] using
    (bandValue_left hm X matrix hX β (finFunctionFinEquiv u))

/-- The right catalogue uses the same original flat leaf order. -/
theorem catalogueValue_right {L m N : ℕ} (hm : m ≤ L)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (matrix : ℕ → ℕ → ℤ)
    (hY : ∀ k i, matrix i.val k.val = Y k i) (β : ℕ) (τ : Leaf L) :
    catalogueValue L m N true matrix β (Encoding.leafIndex τ).val =
      encodingR (bandArrayR (MaskTable.layout hm) Y β) τ := by
  apply Encoding.value_final_right
  intro u
  simpa only [Equiv.symm_apply_apply] using
    (bandValue_right hm Y matrix (fun i k => hY k i) β (finFunctionFinEquiv u))

set_option maxRecDepth 4096 in
-- Static size arithmetic traverses the new finite blocks, reusing both encoder size bounds.
/-- One finite code-size bound for the 96-register program and its final halt. -/
theorem program_length_le : (program.program catalogue).length ≤ 16384 := by
  have hl := Encoding.program_length_le false
  have hr := Encoding.program_length_le true
  simp only [Code.program, List.length_append, Code.length_assemble,
    List.length_cons, List.length_nil] at hl hr ⊢
  simp only [program, header, headerLoads, headerPowers, headerLayout, powerCode,
    saveInput, countCode, countMasks, countBody, populationCode, rootCode, rootBody,
    bandCount, tablesCode, tableBody, tableWrite, encodeBands, bandBody, prepareBand,
    prepareHead, prepareBody, splitCode, splitHead, splitBody, readCell, collectBand,
    collectHead, restoreInput, Code.size, Code.size_rename, Power.program, Power.body,
    ArrayCopy.program, ArrayCopy.body, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd]
  omega

set_option maxRecDepth 4096 in
-- This finite structural check covers the same fixed instruction list, not an execution.
/-- The uniform program does not inspect its target word width. -/
theorem not_readsWidth : ¬program.ReadsWidth := by decide

/-- Every row and column band is encoded exactly once into its shared flat block. The
actual input contains only the three scalar parameters and signed matrices. `w` is the signed
source magnitude width and `w+2` is the target width used by the existing native kernels.
The prefix run exposes the actual final memory; its next instruction is the charged halt.
No unrelated caller memory or header is required to be zero in the general `exec` theorem. -/
theorem runs {w L m N : ℕ} (hw : 0 < w) (hm : m ≤ L)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (A : ℤ) (hA : 0 ≤ A) (hX : ∀ i k, |X i k| ≤ A) (hY : ∀ k j, |Y k j| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N)) :
    InputFits (w + 2) (input L m N X Y) ∧
    ∃ y n, n ≤ timeBound L m N ∧
      Runs (w + 2) (program.program catalogue) (State.init (input L m N X Y))
        ⟨program.size, y⟩ n ∧
      Executes (w + 2) (program.program catalogue) (State.init (input L m N X Y))
        (catalogueBase L m N) (n + 1) ∧
      y.Bounded (w + 2) ∧
      (∀ β < numBands L m N, ∀ τ,
        y.mem (catalogueAddress L m N false β (Encoding.leafIndex τ).val) =
          encode (encodingL (bandArrayL (MaskTable.layout hm) X β) τ)) ∧
      (∀ β < numBands L m N, ∀ τ,
        y.mem (catalogueAddress L m N true β (Encoding.leafIndex τ).val) =
          encode (encodingR (bandArrayR (MaskTable.layout hm) Y β) τ)) ∧
      (∀ a < 2 ^ L, y.mem (inverseBase L m N + a) = MaskTable.lookup L m a) ∧
      (∀ gh : Fin (K0 L m) × Fin (K0 L m),
        y.mem (tableBase L m N + (MaskTable.pairRank gh).val) =
          (MaskTable.selectedMask gh).val) ∧
      (∀ b, ¬(inputEnd m N ≤ b ∧ b < memoryEnd L m N) →
        y.mem b = (State.init (input L m N X Y) : State 96).data.mem b) := by
  obtain ⟨hi, y, he, hb, hp, hv, ht, hf, hframe⟩ :=
    exec_input hw hm X Y A hA hX hY hmag hfit
  obtain ⟨n, hn, he⟩ := he
  refine ⟨hi, y, n, hn, ?_, ?_, hb, ?_, ?_, ht, hf, hframe⟩
  · simpa only [Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := program.program catalogue) (Program.Contains.self _).append_left
  · simpa only [hp.catalogue, State.init] using he.executes catalogue
  · intro β hβ τ
    rw [hv false β hβ _ (Encoding.leafIndex τ).isLt,
      catalogueValue_left hm X _ (by intro i k; simp [matrixValues])]
  · intro β hβ τ
    rw [hv true β hβ _ (Encoding.leafIndex τ).isLt,
      catalogueValue_right hm Y _ (by intro k i; simp [matrixValues])]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
