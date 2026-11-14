/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Foundations.Data.Code.RegularSyndrome

/-! Checked clients for binary regular syndrome decoding. -/

public section

namespace RegularSyndromeTests

open Cslib.Code Matrix

def positions : Fin 2 → Fin 3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2

def H : Matrix (Fin 2) (Fin 2 × Fin 3) Bool :=
  fun i p => decide (p.1 = i)

def y : Fin 2 → Bool := fun _ => true

-- There is one selected position in each length-three chunk.
example : IsRegularWord (regularWord positions) := by
  exact isRegular_regularWord positions

example : hammingNorm (regularWord positions) = 2 := by
  exact hammingNorm_regularWord positions

-- Each parity-check row sums the corresponding chunk, so the regular witness has syndrome `11`.
example : IsRegularSyndromeSolution H y (regularWord positions) := by
  constructor
  · exact isRegular_regularWord positions
  · simp only [syndrome_eq]
    decide +kernel

def invalid : Fin 2 × Fin 3 → Bool := fun _ => false

-- The zero word has the wrong per-chunk weight and the wrong syndrome.
private theorem invalid_not_regular : ¬IsRegularWord invalid := by decide +kernel

example : ¬IsRegularWord invalid :=
  invalid_not_regular

example : ¬IsRegularSyndromeSolution H y invalid := by
  intro h
  exact invalid_not_regular h.1

end RegularSyndromeTests
