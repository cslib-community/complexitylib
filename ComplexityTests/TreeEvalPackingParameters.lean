/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Complexity.Computability.TreeEval.Ary.PackingParameters

/-!
# Packed field-parameter regressions

With fan-in two and five-bit values, four-bit chunks leave three padding bits. The modulus is
prime, contains every four-bit chunk, and satisfies the strict degree threshold. Actual framed
residue lists test both zero entries and larger residues; a full register table is checked too.
-/

public section

namespace ComplexityTests.TreeEvalPackingParameters

open Cslib.TreeEval.Ary.Packed Turing.MultiTapeTM

example : chunkWidth 2 5 = 4 := by decide
example : chunkCount 2 5 = 2 := by decide
example : chunkCount 2 5 * chunkWidth 2 5 - 5 = 3 := by decide
example : gateDegree 2 5 = 60 := by decide

example : 62 ≤ fieldModulus 2 5 ∧ fieldModulus 2 5 ≤ 122 :=
  ⟨gateDegree_add_two_le 2 5, fieldModulus_le 2 5⟩

example : (fieldModulus 2 5).Prime := fieldModulus_prime 2 5
example : 60 < fieldModulus 2 5 - 1 := gateDegree_lt 2 5
example : (fieldModulus 2 5).size ≤ 10 := fieldModulus_size_le (by decide) (by decide)

/-- The alphabet contains values beyond Boolean coordinates. -/
theorem distinct_nonbinary_chunks :
    alphabetEmbedding (d := 2) (b := 5) (by decide) (by decide) 7 ≠
      alphabetEmbedding (d := 2) (b := 5) (by decide) (by decide) 15 :=
  (alphabetEmbedding (d := 2) (b := 5) (by decide) (by decide)).injective.ne (by decide)

example : (encList encNat [0, 1, 7, 15, 31, 61]).length = 44 := by decide
example : (encList encNat (List.replicate 6 0)).length = 6 := by decide

/-- The smallest nonempty case also has a field meeting the strict degree condition. -/
example : chunkWidth 1 1 = 1 ∧ chunkCount 1 1 = 1 ∧ gateDegree 1 1 = 1 := by decide

example : 1 < fieldModulus 1 1 - 1 := gateDegree_lt 1 1

/-- Positivity of fan-in is needed for coverage: the chosen width is zero at fan-in zero. -/
example : ¬5 ≤ chunkCount 0 5 * chunkWidth 0 5 := by decide

example : (encList encNat [0, 1, 7, 15, 31, 61]).length ≤ 243 := by
  apply length_encList_residues_le (d := 2) (b := 5) (by decide) (by decide)
    _ (by decide)
  intro v hv
  have hp : 62 ≤ fieldModulus 2 5 := gateDegree_add_two_le 2 5
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

instance : Fact (fieldModulus 2 5).Prime := ⟨fieldModulus_prime 2 5⟩

/-- Every full three-register, two-coordinate table fits the concrete bound, with all entries
charged through their canonical unsigned residues and list framing. -/
theorem full_register_storage (S : Fin 3 → Fin 2 → ZMod (fieldModulus 2 5)) :
    (encList encNat (List.ofFn fun i : Fin 6 =>
      (S ((finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).symm i).1
        ((finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).symm i).2).val)).length ≤ 243 := by
  apply length_encList_residues_le (d := 2) (b := 5) (by decide) (by decide)
    _ (by rw [List.length_ofFn]; decide)
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact ZMod.val_lt _

end ComplexityTests.TreeEvalPackingParameters
