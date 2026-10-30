/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.QueryValues
import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationInput

/-!
# Original pairs from an actual producer query block

The small concrete producer instance tests the readback API independently of thin-product
geometry. The kernel client starts with the original scalar headers and twelve zero weights;
neither a prepared query list nor a layout certificate is supplied as input.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMExactTriangleQueryValues

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle

private def values : List ℤ := List.replicate 12 0
private def zeroAB : Fin 2 → Fin 2 → ℤ := fun _ _ => 0

-- The actual producer writes all four original coordinate pairs in row-major rank order.
#guard (Instances.program.eval 256 64 (Data.init (PreparationInput.input 2 1 1 2 values))).map
    (fun (y, _) => (List.range 8).map (fun j => y.mem (31 + j))) ==
  some [0, 0, 0, 1, 1, 0, 1, 1]

/-- Fully admitted initialized producer execution, connected to the new query-value API.
The original pairs occur once each and their order is the existing finite class rank. -/
example : ∃ T : ℕ, ∃ y : Data 64,
    ExecWithin 256 Instances.program (Data.init (PreparationInput.input 2 1 1 2 values)) y T ∧
    let qs := RecordProduct.decodedQueries (by decide : 0 < 2) y.mem 31 4
    qs.Nodup ∧ qs.toFinset = Finset.univ ∧
      ∀ i : Fin qs.length, rankIn (Finset.univ : Finset (Fin 2 × Fin 2)) (qs.get i) = i.val := by
  obtain ⟨y, he, hout, -, -⟩ := PreparationInput.exec_input
    (n := 2) (D := 1) (g := 1) (p := 2) (A := 0) (W := 256) values
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro z hz; exact le_of_eq (congrArg Int.natAbs (List.eq_of_mem_replicate hz)))
    (by decide)
  have hAB : ∀ a b, values.getD (pairIndex (a, b)) 0 = zeroAB a b := by
    intro a b
    change (List.replicate 12 (0 : ℤ))[pairIndex (a, b)]?.getD 0 = 0
    exact List.getElem?_getD_replicate_default_eq _ _ _
  have hcap : queryCap 2 1 = 4 := by
    have hl : 4 ≤ Nat.sqrt 16 := Nat.le_sqrt.mpr (by decide)
    have hu : Nat.sqrt 16 < 5 := Nat.sqrt_lt.mpr (by decide)
    change Nat.sqrt 16 = 4
    omega
  have hclass : residueClass zeroAB 2 0 = Finset.univ := by decide
  have hk : 0 < numChunks (residueClass zeroAB 2 0) (queryCap 2 1) := by
    rw [hcap, hclass]
    decide
  obtain ⟨hget, hnodup, hset⟩ := RecordProduct.decodedQueries_chunkOf
    (fun q => values.getD q 0) zeroAB (by decide) (by decide) hAB
    (by decide) (by decide) hout 0 0 hk
  have hchunk : chunkOf zeroAB 1 2 0 0 = Finset.univ := by
    rw [chunkOf, chunk, hclass, hcap]
    ext pair
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, rankIn_univ]
    apply iff_true_intro
    apply Nat.div_eq_of_lt
    have ha := pair.1.isLt
    have hb := pair.2.isLt
    dsimp only [pairIndex]
    omega
  simp_rw [hcap, hclass] at hget
  simp only [hcap, hclass] at hnodup hset
  simp only [Nat.reduceAdd, Nat.reduceMul, Fin.val_zero, zero_mul, Nat.add_zero,
    Nat.sub_zero, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    min_self] at hget hnodup hset
  refine ⟨_, y, he, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hnodup
  · exact hset.trans hchunk
  · intro i
    simpa [hcap, hclass] using (hget ⟨i.val, by
      simpa [RecordProduct.decodedQueries_length, hcap, hclass] using i.isLt⟩).2

end ComplexityTests.WordRAMExactTriangleQueryValues
