/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Fusion.Graph.Random

/-!
# Clients of finite cover descriptions and random graph hardness

Zero-pair descriptions distinguish the two constants. A concrete nontrivial graph has a row
cover and remains exactly decodable after padding. The probability theorem gives a numerical
failure bound at its smallest permitted vertex count.
-/

namespace ComplexityTests.FusionRandom

open Cslib.Circuits.Fusion

private def emptyCode : CoverCode 0 0 := fun _ => ⟨false, Fin.elim0, Fin.elim0⟩
private def fullCode : CoverCode 0 0 := fun _ => ⟨true, Fin.elim0, Fin.elim0⟩

example {U : Type*} : emptyCode.decode (Fin.elim0 : Fin 0 → Set U) = ∅ := by
  ext x
  simp [CoverCode.decode, CoverCode.read, emptyCode]

example {U : Type*} : fullCode.decode (Fin.elim0 : Fin 0 → Set U) = Set.univ := by
  ext x
  simp [CoverCode.decode, CoverCode.read, fullCode]

example : Fintype.card (CoverCode 0 0) = 2 := by simp

private def diagonal : Set (Fin 2 × Fin 2) := {x | x.1 = x.2}

example : (0, 0) ∈ diagonal := rfl
example : (0, 1) ∉ diagonal := by simp [diagonal]

example : (Graph.rowCover diagonal).pairs.length = 2 := by simp

example : ∃ code : CoverCode 4 5, code.decode (Graph.sources (V := Fin 2)) = diagonal := by
  exact (Graph.rowCover diagonal).exists_code_of_length_le (by simp)

example : Graph.smallCoverProbability 16 1 ≤ (1 / 65536 : ℝ) := by
  have h := Graph.smallCoverProbability_le_half_pow (N := 16) (by decide)
  norm_num at h ⊢
  exact h

end ComplexityTests.FusionRandom
