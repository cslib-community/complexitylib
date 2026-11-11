/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Boolean.GF2Rank
import CslibFrontier.Computability.Circuit.Boolean.Synthesis
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tests for the `ZMod 2` rank circuits

Two instances of the rank threshold:
- The `2 × 2` matrix whose entries are the four input bits. Its rank test costs at most
  `14 · 3 · 3 · 5 = 630` gates, and on the all-zero input the matrix has rank `0`.
- The `1 × 1` matrix holding the exclusive or of two inputs, whose entry is itself synthesised.
  This is how the zero-sum matrices of the rank property get their entries.
-/

public section

namespace CslibFrontierTests.Computability.Circuit.Boolean.GF2Rank

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.BitString Matrix Matrix.GaussJordan

/-- The `2 × 2` matrix over `ZMod 2` whose entries are the four input bits. -/
def inputMatrix (x : BitString 4) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun i l => bitEquiv.symm (x (finProdFinEquiv (i, l)))

theorem entryBits_inputMatrix_subset : entryBits inputMatrix ⊆ inputs 4 := by
  intro f hf
  obtain ⟨i, l, rfl⟩ := mem_entryBits.mp hf
  exact ⟨finProdFinEquiv (i, l), funext fun x => by simp [inputMatrix]⟩

/-- The rank test on four input bits costs at most `630` gates. -/
example : complexity interpretation (single fun x => decide (1 ≤ (inputMatrix x).rank)) ≤ 630 :=
  (synthesis_le_rank inputMatrix entryBits_inputMatrix_subset (by omega)).complexity_le

/-- On the all-zero input the matrix has rank `0`, so the test rejects. -/
example : (inputMatrix fun _ => false).rank = 0 := by
  rw [rank_eq_card_reduce_ne_zero]
  decide +kernel

/-- The `1 × 1` matrix holding the exclusive or of two inputs. -/
def xorMatrix (x : BitString 2) : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  Matrix.of fun _ _ => bitEquiv.symm (x 0 ^^ x 1)

/-- Its entry costs four gates over the inputs, so the rank test costs at most
`4 + 14 · 2 · 2 · 3 = 172` gates. -/
example : complexity interpretation (single fun x => decide (1 ≤ (xorMatrix x).rank)) ≤ 172 := by
  have hentry : Synthesis interpretation (inputs 2) (entryBits xorMatrix) 4 := by
    have h := (Synthesis.of_mem (I := interpretation) (s := inputs 2) (f := fun x => x 0)
      ⟨0, rfl⟩).xor (Synthesis.of_mem (f := fun x => x 1) ⟨1, rfl⟩)
    refine h.mono Set.Subset.rfl ?_ le_rfl
    intro f hf
    obtain ⟨i, l, rfl⟩ := mem_entryBits.mp hf
    simp [xorMatrix]
  exact (synthesis_le_rank_of_synthesis xorMatrix hentry (by omega)).complexity_le

end CslibFrontierTests.Computability.Circuit.Boolean.GF2Rank
