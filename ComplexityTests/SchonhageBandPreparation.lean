/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandThin
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandCatalogue
import Complexity.Algorithms.MatrixMultiplication.Schonhage.MaskTable

-- These regressions evaluate actual native code; general execution proofs are checked separately.
set_option linter.hashCommand false

namespace ComplexityTests.SchonhageBandPreparation

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open BandPreparation

private def leafAt {L : ℕ} (i : Fin (10 ^ L)) : Leaf L :=
  fun ℓ => Encoding.termAt (finFunctionFinEquiv.symm i ℓ)

private def expected {L m N : ℕ} (hm : m ≤ L)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) : List ℤ :=
  ((List.range (numBands L m N)).flatMap fun β =>
    List.ofFn fun i => encodingL (bandArrayL (MaskTable.layout hm) X β) (leafAt i)) ++
  ((List.range (numBands L m N)).flatMap fun β =>
    List.ofFn fun i => encodingR (bandArrayR (MaskTable.layout hm) Y β) (leafAt i))

private def observe (w L m N : ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) :
    Option ((List ℤ × Bool) × List ℕ) :=
  let initial := ((State.init (input L m N X Y) : State 96).data.write
    (memoryEnd L m N) 91)
  (program.eval w 1024 initial).map fun (y, _) =>
    (((List.range (2 * numBands L m N * 10 ^ L)).map fun i =>
        decode (y.mem (catalogueBase L m N + i)),
      decide ((∀ a < inputEnd m N, y.mem a = initial.mem a) ∧
        y.mem (memoryEnd L m N) = 91)),
      (List.range (2 ^ L)).map fun i => y.mem (inverseBase L m N + i))

-- Distinct tiles share the existing row/column band blocks, with no per-tile duplication.
#guard tileInputBases 1 0 4 (0, 1) == (57, 87)
#guard tileInputBases 1 0 4 (1, 1) == (67, 87)

-- A zero-dimensional matrix computes its tables and has no bands. Its input is restored.
#guard observe 8 0 0 0 (fun _ _ => 0) (fun _ _ => 0) == some (([], true), [1])

-- A genuine signed zero-depth band on each side calls both actual encoder programs.
#guard observe 8 0 0 1 (fun _ _ => -3) (fun _ _ => 2) == some (([-3, 2], true), [1])

-- All leaves of four distinct shared bands agree with the unchanged mathematical arrays.
#guard (observe 12 1 1 2 (fun i k => (i.val : ℤ) - k.val)
    (fun k j => (k.val : ℤ) - 2 * j.val)).map (fun z => z.1) ==
  some (expected (N := 2) (by decide : 1 ≤ 1) (fun i k => (i.val : ℤ) - k.val)
    (fun k j => (k.val : ℤ) - 2 * j.val), true)

-- Two row and column bands with padding: the last band has only one real row/column.
#guard (observe 12 1 0 4 (fun i _ => (i.val : ℤ) - 2)
    (fun _ j => 1 - (j.val : ℤ))).map (fun z => z.1) ==
  some (expected (N := 4) (by decide : 0 ≤ 1) (fun i _ => (i.val : ℤ) - 2)
    (fun _ j => 1 - (j.val : ℤ)), true)

-- The second size-one mask is unselected when K0² = 1; the first is mask one.
#guard (observe 12 2 1 1 (fun _ _ => -1) (fun _ _ => 1)).map Prod.snd ==
  some [0, 1, 0, 0]

private def asymmetricRead (side : Bool) (a : ℕ) : Code .standard 96 :=
  .seq header (.seq saveInput (.seq countCode (.seq tablesCode
    (.seq (.op (.const band 0)) (.seq (.op (.const index a))
      (.seq splitCode (readCell side)))))))

private def observeAsymmetricRead (side : Bool) (a : ℕ) :
    Option (ℕ × ℕ × ℕ × ℕ × ℤ) :=
  let data : Data 96 := (State.init (input 4 1 29
    (fun i k => ((100 * i.val + k.val : ℕ) : ℤ) - 1000)
    (fun k j => -((1000 * k.val + j.val + 7 : ℕ) : ℤ)))).data
  ((asymmetricRead side a).eval 24 256 data).map fun (y, _) =>
    (y.regs root, y.regs maskAcc, y.regs block, y.regs row, decode (y.regs value))

-- At L=4,m=1, the computed root is 2. Masks 2 and 4 have ranks 1 and 2, so division
-- and remainder select different blocks. Both guarded rows (1 and 28) are real at N=29.
-- These runs compute headers/tables/snapshot and decode/load only, without an encoder run.
#guard observeAsymmetricRead false 36 == some (2, 2, 0, 1, -898)
#guard observeAsymmetricRead true 36 == some (2, 2, 1, 28, -2035)
#guard observeAsymmetricRead false 246 == some (2, 4, 1, 28, 1802)
#guard observeAsymmetricRead true 246 == some (2, 4, 0, 1, -2008)

-- Address-width boundary for a padded, two-band call. The nonzero sentinel also survives.
#guard observe 6 1 0 4 (fun _ _ => 0) (fun _ _ => 0) == none
#guard (observe 7 1 0 4 (fun _ _ => 0) (fun _ _ => 0)).map (fun z => z.1.2) == some true

/-- The original numerical width premise has a checked strict boundary. -/
example : ¬Fits 13 (wordBudget 1 0 4) ∧ Fits 14 (wordBudget 1 0 4) := by decide +kernel

/-- A negative zero-depth initialized client. The actual final memory belongs to the
charged prefix run, which is followed by its charged halt. -/
example : ∃ y : Data 96, ∃ n, n ≤ timeBound 0 0 1 ∧
    Runs 11 (program.program catalogue)
      (State.init (input 0 0 1 (fun _ _ => -3) (fun _ _ => 2))) ⟨program.size, y⟩ n ∧
    Executes 11 (program.program catalogue)
      (State.init (input 0 0 1 (fun _ _ => -3) (fun _ _ => 2)))
      (catalogueBase 0 0 1) (n + 1) ∧
    y.mem (catalogueAddress 0 0 1 false 0 0) = 7 ∧
    y.mem (catalogueAddress 0 0 1 true 0 0) = 4 := by
  obtain ⟨_, y, n, hn, hr, he, _, hl, hright, _⟩ := runs (w := 9) (N := 1) (by decide)
    (by decide : 0 ≤ 0) (fun _ _ => -3) (fun _ _ => 2) 3 (by decide)
    (by intro i k; decide) (by intro k j; decide) (by decide) (by decide +kernel)
  refine ⟨y, n, hn, hr, he, ?_, ?_⟩
  · have h := hl 0 (by decide +kernel) (Fin.elim0 : Leaf 0)
    have hi : (Encoding.leafIndex (Fin.elim0 : Leaf 0)).val = 0 := by
      have := (Encoding.leafIndex (Fin.elim0 : Leaf 0)).isLt
      norm_num at this ⊢
    have hv : encodingL (bandArrayL (N := 1) (MaskTable.layout (by decide : 0 ≤ 0))
        (fun _ _ => -3) 0) Fin.elim0 = -3 := by decide +kernel
    simpa only [hi, hv, show encode (-3) = 7 from rfl] using h
  · have h := hright 0 (by decide +kernel) (Fin.elim0 : Leaf 0)
    have hi : (Encoding.leafIndex (Fin.elim0 : Leaf 0)).val = 0 := by
      have := (Encoding.leafIndex (Fin.elim0 : Leaf 0)).isLt
      norm_num at this ⊢
    have hv : encodingR (bandArrayR (N := 1) (MaskTable.layout (by decide : 0 ≤ 0))
        (fun _ _ => 2) 0) Fin.elim0 = 2 := by decide +kernel
    simpa only [hi, hv, show encode 2 = 4 from rfl] using h

/-- A positive-depth, signed padded multi-band client of the general kernel-checked run.
The prefix is tied to its actual final memory, including restored input and outside frame. -/
example : ∃ y : Data 96, ∃ n, n ≤ timeBound 1 0 4 ∧
    Runs 14 (program.program catalogue)
      (State.init (input 1 0 4 (fun i _ => (i.val : ℤ) - 2)
        (fun _ j => 1 - (j.val : ℤ)))) ⟨program.size, y⟩ n ∧
    Executes 14 (program.program catalogue)
      (State.init (input 1 0 4 (fun i _ => (i.val : ℤ) - 2)
        (fun _ j => 1 - (j.val : ℤ)))) (catalogueBase 1 0 4) (n + 1) ∧
    y.mem (catalogueAddress 1 0 4 false 0
      (Encoding.leafIndex (fun _ : Fin 1 => Term.P 0 0)).val) = encode (-2) ∧
    (∀ b, ¬(inputEnd 0 4 ≤ b ∧ b < memoryEnd 1 0 4) →
      y.mem b = (State.init (input 1 0 4 (fun i _ => (i.val : ℤ) - 2)
        (fun _ j => 1 - (j.val : ℤ))) : State 96).data.mem b) := by
  obtain ⟨_, y, n, hn, hr, he, _, hl, _, _, _, hf⟩ := runs (w := 12) (N := 4) (by decide)
    (by decide : 0 ≤ 1) (fun i _ => (i.val : ℤ) - 2) (fun _ j => 1 - (j.val : ℤ))
    2 (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)
  refine ⟨y, n, hn, hr, he, ?_, hf⟩
  have hv : encodingL (bandArrayL (N := 4) (MaskTable.layout (by decide : 0 ≤ 1))
      (fun i _ => (i.val : ℤ) - 2) 0) (fun _ : Fin 1 => Term.P 0 0) = -2 := by decide +kernel
  simpa only [hv] using hl 0 (by decide +kernel) (fun _ : Fin 1 => Term.P 0 0)

private def framedEmpty : Data 96 :=
  ((State.init (input 0 0 0 (fun _ _ => 0) (fun _ _ => 0)) : State 96).data.write
    0 77).write (memoryEnd 0 0 0) 91

/-- General-call framing allows an unrelated native header zero and a nonzero adjacent
query/scratch sentinel. The full original prefix, including header zero, is restored. -/
example : ∃ y : Data 96, ∃ n, n ≤ timeBound 0 0 0 ∧
    Runs 10 (program.program catalogue) ⟨0, framedEmpty⟩ ⟨program.size, y⟩ n ∧
    y.mem 0 = 77 ∧ y.mem (memoryEnd 0 0 0) = 91 := by
  obtain ⟨y, ⟨n, hn, he⟩, _, _, _, _, hf⟩ := exec (w := 8) (L := 0) (m := 0)
    (N := 0) (by decide) (by decide) framedEmpty (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (fun _ _ _ => 0)
    (by intro side r hr; omega) 0 (by decide) (by intro side r hr; omega)
    (by decide) (by decide +kernel)
  refine ⟨y, n, hn, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add] using he.runs (pc := 0)
      (p := program.program catalogue) (Program.Contains.self _).append_left
  · rw [hf 0 (by decide +kernel)]
    decide +kernel
  · rw [hf (memoryEnd 0 0 0) (by omega)]
    rfl

/-- Symbolic positive-depth thin parameters and nonzero signed matrices simultaneously
satisfy all width premises and the genuine charged native saving, without enumerating them. -/
example (m : ℕ) : let M := m + 1
    ∃ w n, 0 < w ∧ 0 < M ∧ Fits (w + 2) (wordBudget (19 * M) M (D M ^ 18)) ∧
      (7 ^ (19 * M) : ℕ) * (1 : ℤ) < (2 : ℤ) ^ (w - 1) ∧
      Executes (w + 2) (program.program catalogue)
        (State.init (input (19 * M) M (D M ^ 18) (fun _ _ => 1) (fun _ _ => -1)))
        (catalogueBase (19 * M) M (D M ^ 18)) n ∧
      (n : ℝ) ≤ 81920 * ((19 * M + 1 : ℕ) : ℝ) * (D M ^ 18 : ℕ) ^ (2 : ℕ) /
        (D M : ℝ) ^ (1 / 18 : ℝ) := by
  dsimp only
  obtain ⟨w, hw, hmag, hfit⟩ := width_exists (19 * (m + 1)) (m + 1)
    (D (m + 1) ^ 18) 1 (by decide)
  obtain ⟨n, he, ht⟩ := runs_thin (m := m + 1) (N := D (m + 1) ^ 18) hw (Nat.le_refl _)
    (fun _ _ => 1) (fun _ _ => -1) 1 (by decide)
    (by intro i k; decide) (by intro k j; decide) hmag hfit
  exact ⟨w, n, hw, Nat.succ_pos _, hfit, hmag, he, ht⟩

end ComplexityTests.SchonhageBandPreparation
