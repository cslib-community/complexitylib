/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Init
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.GroupedRuns
import Complexity.Algorithms.MatrixMultiplication.Schonhage.MaskTable

set_option linter.hashCommand false

open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
open Cslib.Algorithms

private def expectedCode {L m : ℕ} (hm : m ≤ L) (I J : ℕ) : ℕ :=
  (PrunedQuery.queryIndex (outStrOfPos (MaskTable.layout hm) I J)).val

-- Distinct row/column block indices use rank 1 and rank 2, not their transposes.
#guard expectedCode (by decide : 1 ≤ 4) 2 28 == 97
#guard expectedCode (by decide : 1 ≤ 4) 28 2 == 905
example : QueryDigits.pack 4 2 2 1 ≠ QueryDigits.pack 4 4 1 2 := by decide +kernel

private def packedInput : Data 16 where
  regs i := if i = depth then 4 else if i = mask then 2 else
    if i = row then 2 else if i = col then 1 else 81
  mem a := if a = 23 then 91 else 0

-- The arbitrary nonzero scratch bank is initialized by real code; the same returned state
-- carries the packed word and the unchanged memory assertion.
example : ∃ y, ExecWithin 19 packCode packedInput y 70 ∧
    y.regs code = 97 ∧ y.mem 23 = 91 := by
  obtain ⟨y, he, hv, _, hf⟩ := exec_pack (w := 19) 4 2 2 1 packedInput
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨y, he, hv, congrFun hf 23⟩

private def routingInput (L m N : ℕ) (qs : List (ℕ × ℕ)) : List ℕ :=
  [L, m, N, qs.length] ++ qs.flatMap (fun q => [q.1, q.2])

private def observe (L m N : ℕ) (qs : List (ℕ × ℕ)) :
    Option (List ℕ × List ℕ × List ℕ × Bool) :=
  let initial := (State.init (routingInput L m N qs) : State 96).data.write 100000 91
  (program.eval 25 1024 initial).map fun (y, _) =>
    ((List.range qs.length).map fun i => y.mem (y.regs codes + i),
      (List.range qs.length).map fun i => y.mem (y.regs originals + i),
      (List.range (y.regs tileCount + 1)).map fun i => y.mem (y.regs offsets + i),
      decide ((∀ a < 5 + 2 * qs.length, y.mem a = initial.mem a) ∧ y.mem 100000 = 91))

-- Actual initialized empty and zero-depth runs, including the computed tables and prefix pass.
#guard observe 0 0 0 [] == some ([], [], [0], true)
#guard observe 0 0 2 [(1, 0), (0, 1), (1, 0)] ==
  some ([0, 0, 0], [1, 0, 2], [0, 0, 1, 3, 3], true)

-- K0=2, three bands, asymmetric row/column digits and an original repeated query.
-- This exercises only routing; it never materializes a 10^4-leaf encoded array.
#guard observe 4 1 110 [(2, 28), (28, 2), (55, 109), (2, 28), (109, 55)] ==
  some ([97, 905, 97, 49, 49], [0, 1, 3, 2, 4], [0, 3, 3, 3, 3, 3, 4, 4, 5, 5], true)

private def repeatedQueries : List (Fin 2 × Fin 2) :=
  [(1, 0), (0, 1), (1, 0)]

-- The kernel-checked initialized run and its halt use the same memory witness. Both
-- equal coordinate pairs survive as separate occurrences in the original-index array.
example : InputFits 32 (input 0 0 repeatedQueries) ∧
    ∃ y n, n ≤ timeBound 0 0 2 3 ∧
      Runs 32 (program.program codes) (State.init (input 0 0 repeatedQueries))
        ⟨program.size, y⟩ n ∧
      Executes 32 (program.program codes) (State.init (input 0 0 repeatedQueries))
        (codeAddress 0 0 2 3) (n + 1) ∧
      y.mem (codeAddress 0 0 2 3 + 1) = 0 ∧
      y.mem (originalAddress 0 0 2 3 + 1) = 0 ∧
      y.mem (originalAddress 0 0 2 3 + 2) = 2 ∧
      y.mem 1 = 0 := by
  obtain ⟨hi, y, n, hn, hr, he, _, hv, _, _, hf⟩ :=
    runs (w := 32) (by decide : 0 ≤ 0) repeatedQueries (by decide +kernel)
  have h0 := hv ⟨0, by decide⟩
  have h2 := hv ⟨2, by decide⟩
  have hp0 : CountingSort.position (tileKey 0 0 2 ∘ inputPairs repeatedQueries) 3 0 = 1 := by
    decide +kernel
  have hp2 : CountingSort.position (tileKey 0 0 2 ∘ inputPairs repeatedQueries) 3 2 = 2 := by
    decide +kernel
  have hz : (PrunedQuery.queryIndex
      (outStrOfPos (MaskTable.layout (by decide : 0 ≤ 0))
        (repeatedQueries.get ⟨0, by decide⟩).1
        (repeatedQueries.get ⟨0, by decide⟩).2)).val = 0 := by
    have hlt := (PrunedQuery.queryIndex
      (outStrOfPos (MaskTable.layout (by decide : 0 ≤ 0))
        (repeatedQueries.get ⟨0, by decide⟩).1 (repeatedQueries.get ⟨0, by decide⟩).2)).isLt
    change _ < 1 at hlt
    omega
  simp only [show repeatedQueries.length = 3 from rfl, hp0] at h0
  simp only [show repeatedQueries.length = 3 from rfl, hp2] at h2
  refine ⟨hi, y, n, hn, hr, he, h0.1.trans hz, h0.2, h2.2, ?_⟩
  exact hf 1 (Or.inl (by decide))

-- The entirely empty input is admitted too; the terminal offset is written by real code.
example : ∃ y n, Runs 32 (program.program codes) (State.init (input 0 0
      ([] : List (Fin 0 × Fin 0)))) ⟨program.size, y⟩ n ∧
    Executes 32 (program.program codes) (State.init (input 0 0
      ([] : List (Fin 0 × Fin 0)))) (codeAddress 0 0 0 0) (n + 1) ∧
    y.mem (offsetAddress 0 0 0 0) = 0 := by
  obtain ⟨_, y, n, _, hr, he, _, _, _, ht, _⟩ :=
    runs (w := 32) (by decide : 0 ≤ 0) ([] : List (Fin 0 × Fin 0)) (by decide +kernel)
  exact ⟨y, n, hr, he, ht⟩

-- A physical width can fail the numerical admission premise, even for zero depth.
example : ¬Fits 1 (wordBudget 0 0 0 0) := by decide +kernel
example : Fits 32 (wordBudget 0 0 0 0) := by decide +kernel
example : (program.program codes).length ≤ 4096 := program_length_le
example : ¬program.ReadsWidth := not_readsWidth

private def asymmetricQueries : List (Fin 110 × Fin 110) :=
  [(2, 28), (28, 2), (55, 109), (2, 28), (109, 55)]

-- All admission premises are discharged on the asymmetric positive-inner-depth family.
-- The code-set assertion uses the same y as the actual initialized Runs and charged halt.
example : InputFits 64 (input 4 1 asymmetricQueries) ∧
    ∃ y n, Runs 64 (program.program codes) (State.init (input 4 1 asymmetricQueries))
        ⟨program.size, y⟩ n ∧
      Executes 64 (program.program codes) (State.init (input 4 1 asymmetricQueries))
        (codeAddress 4 1 110 5) (n + 1) ∧
      n + 1 ≤ 128 * 5 * (5 + 3 ^ 2 + 2 ^ 4 + 1) ∧
      (Finset.Ico (y.mem (offsetAddress 4 1 110 5))
        (y.mem (offsetAddress 4 1 110 5 + 1))).image
          (fun j => y.mem (codeAddress 4 1 110 5 + j)) =
        (wantedStrings (MaskTable.layout (by decide : 1 ≤ 4))
          asymmetricQueries.toFinset 0 0).image (fun w => (PrunedQuery.queryIndex w).val) ∧
      Function.Injective (fun j : Fin 5 => y.mem (originalAddress 4 1 110 5 + j.val)) := by
  obtain ⟨hi, y, n, hn, hr, he, _, _, hg, _, _, _, hj, _, _, _⟩ :=
    runs_grouped (W := 64) (by decide : 1 ≤ 4) asymmetricQueries (by decide +kernel)
  have hg0 := hg (0, 0) (by decide +kernel)
  have hbands : numBands 4 1 110 = 3 := by decide +kernel
  simp only [show asymmetricQueries.length = 5 from rfl, hbands] at hn
  simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero] at hg0
  exact ⟨hi, y, n, hr, he, hn, hg0, hj⟩
