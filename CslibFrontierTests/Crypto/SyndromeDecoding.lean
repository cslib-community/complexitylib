/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Foundations.Data.Code.RegularSyndrome.Reduction

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

namespace SDToRSDCoreTests

open Cslib.Code Matrix

abbrev Coord := Fin 2 × Fin 3

def targetPositions : Fin 2 → Fin 3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2

def target : Coord → Bool :=
  regularWord targetPositions

def retainedRows : Fin 4 ↪ Fin 5 :=
  Fin.castLEEmb (by norm_num)

/-- The first two retained rows encode the selected coordinate of chunk zero and the next two
encode the selected coordinate of chunk one. The fifth row is the source wrapper's full-instance
validation row. -/
def uniqueH : Matrix (Fin 5) Coord Bool := fun i p =>
  match i.val, p.1.val, p.2.val with
  | 0, 0, 1 => true
  | 1, 0, 2 => true
  | 2, 1, 1 => true
  | 3, 1, 2 => true
  | 4, 0, 0 => true
  | _, _, _ => false

def uniqueY : Fin 5 → Bool :=
  syndrome uniqueH target

def targetSolver (_ : Matrix (Fin 4) Coord Bool) (_ : Fin 4 → Bool) : Option (Coord → Bool) :=
  some target

private theorem targetSolvesRetained :
    IsRegularSyndromeSolution
      (restrictedPermutedMatrix retainedRows (Equiv.refl Coord) uniqueH)
      (restrictSyndrome retainedRows uniqueY) target := by
  decide +kernel

-- The four retained rows distinguish all `3 * 3` regular supports.
private theorem targetIsUnique :
    ∀ z, IsRegularSyndromeSolution
      (restrictedPermutedMatrix retainedRows (Equiv.refl Coord) uniqueH)
      (restrictSyndrome retainedRows uniqueY) z → z = target := by
  decide +kernel

-- The exact unique-solution theorem makes the successful retained solver pass the full check.
example :
    sdToRsdPermutationCore retainedRows (Equiv.refl Coord) targetSolver uniqueH uniqueY =
      some target := by
  apply sdToRsdPermutationCore_eq_some_of_unique retainedRows (Equiv.refl Coord) targetSolver
    uniqueH uniqueY target target
  · rfl
  · simpa [target] using isRegular_regularWord targetPositions
  · rfl
  · exact targetSolvesRetained
  · exact ⟨target, targetSolvesRetained, targetIsUnique⟩

def wrongPositions : Fin 2 → Fin 3
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2

def wrong : Coord → Bool :=
  regularWord wrongPositions

/-- The retained rows are zero, so the truncated instance is nonunique; the fifth row
distinguishes `target` from `wrong`. -/
def ambiguousH : Matrix (Fin 5) Coord Bool := fun i p =>
  decide (i.val = 4 ∧ p.1.val = 0 ∧ p.2.val = 1)

def ambiguousY : Fin 5 → Bool :=
  syndrome ambiguousH target

def wrongSolver (_ : Matrix (Fin 4) Coord Bool) (_ : Fin 4 → Bool) : Option (Coord → Bool) :=
  some wrong

-- The solver's wrong word is nevertheless a valid solution of the nonunique retained instance.
example :
    IsRegularSyndromeSolution
      (restrictedPermutedMatrix retainedRows (Equiv.refl Coord) ambiguousH)
      (restrictSyndrome retainedRows ambiguousY) wrong := by
  decide +kernel

-- Full-instance validation rejects that wrong extension.
example :
    sdToRsdPermutationCore retainedRows (Equiv.refl Coord) wrongSolver ambiguousH ambiguousY =
      none := by
  decide +kernel

-- A uniform permutation regularizes a fixed weight-two support with probability `3^2 / 6.choose 2`.
example :
    Finset.dens {sigma : Equiv.Perm Coord | IsRegularWord (permuteWord sigma target)} =
      (3 : ℚ≥0) / 5 := by
  rw [dens_permuteWord_isRegular target (hammingNorm_regularWord targetPositions)]
  norm_num [Nat.choose]

-- Table 3's three binary parameter sets have the source-required equal-size regular chunks.
example : 10360 = 56 * 185 := by norm_num
example : 18396 = 73 * 252 := by norm_num
example : 19864 = 104 * 191 := by norm_num

end SDToRSDCoreTests
