/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Tally

/-!
# Tally problems

Tally and non-tally languages; residues and fingerprints on concrete words; a separating
fingerprint for a word outside a one-word problem, from
`Cslib.Complexity.Tally.exists_fingerprint_notMem`; and conjunctive reductions of a finite
problem to a tally problem, of unions and intersections of problems in `P`, of a finite union of
problems in `P`, and of asking a computed list of queries.
-/

namespace ComplexityTests.Tally

open Cslib.Complexity Turing.MultiTapeTM

/-! ### Tally languages -/

example : encUnary '' {0, 3} ∈ TALLY ∧ encUnary '' {0, 3} ∈ SPARSE encBits :=
  ⟨image_encUnary_mem_TALLY _, TALLY_subset_SPARSE (image_encUnary_mem_TALLY _)⟩

/-- A word with a `false` letter is not tally. -/
example : ({[true, false]} : Set (List Bool)) ∉ TALLY := fun h => by
  simpa using h [true, false] rfl false (by simp)

/-! ### Fingerprints -/

/-- `101` is `5` in binary, which is `2` modulo `3` and `1` modulo `4`. -/
example : Tally.residue 2 [true, false, true] = 2 ∧ Tally.residue 3 [true, false, true] = 1 ∧
    Tally.residue 2 [true, false, true] = Cslib.BitString.binaryValue [true, false, true] % 3 := by
  decide

/-- `10` and `11` agree modulo `1` but not modulo `2`. -/
example : Tally.fingerprint [true, false] 0 = Tally.fingerprint [true, true] 0 ∧
    Tally.fingerprint [true, false] 1 ≠ Tally.fingerprint [true, true] 1 := by
  decide

/-- With one member of length `2`, nine moduli separate `10` from the problem `{11}`. -/
example : ∃ m < 9, Tally.fingerprint [true, false] m ∉ Tally.fingerprints {[true, true]} :=
  Tally.exists_fingerprint_notMem (s := 1)
    (fun T hT => Finset.card_le_one.2 fun a ha b hb => by
      rw [(hT a ha).1, (hT b hb).1])
    (by decide) (by simp)

/-! ### Conjunctive reductions to tally problems -/

/-- A finite problem is sparse, so it reduces conjunctively to a tally problem. -/
example : ∃ T ∈ TALLY,
    PolyTimeCTTReducible encBits encBits ({[true, false], [false]} : Set (List Bool)) T :=
  exists_mem_TALLY_polyTimeCTTReducible_of_mem_SPARSE (Set.toFinite _).mem_SPARSE

/-- Problems in `P` reduce conjunctively to tally problems, and so do their unions and
intersections. -/
example {L₁ L₂ : Set (List Bool)} (h₁ : L₁ ∈ P encBits) (h₂ : L₂ ∈ P encBits) :
    (∃ A : Set ℕ, PolyTimeCTTReducible encBits encUnary (L₁ ∪ L₂) A) ∧
      ∃ A : Set ℕ, PolyTimeCTTReducible encBits encUnary (L₁ ∩ L₂) A := by
  obtain ⟨A₁, hA₁⟩ := exists_polyTimeCTTReducible_encUnary_of_mem_P h₁
  obtain ⟨A₂, hA₂⟩ := exists_polyTimeCTTReducible_encUnary_of_mem_P h₂
  exact ⟨hA₁.exists_encUnary_union hA₂, hA₁.exists_encUnary_inter hA₂⟩

/-- A union of problems in `P` indexed by a list reduces conjunctively to a tally problem. -/
example {L : ℕ → Set (List Bool)} (h : ∀ i, L i ∈ P encBits) :
    ∃ A : Set ℕ, PolyTimeCTTReducible encBits encUnary (⋃ i ∈ [0, 1, 2], L i) A :=
  PolyTimeCTTReducible.exists_encUnary_biUnion _ fun i _ =>
    exists_polyTimeCTTReducible_encUnary_of_mem_P (h i)

/-- Asking whether all positions of a word lie in a set `A` of natural numbers reduces it
conjunctively to `A`. -/
example (A : Set ℕ) :
    PolyTimeCTTReducible encBits encUnary {w : List Bool | ∀ n ∈ List.range w.length, n ∈ A} A :=
  (PolyTimeCTTReducible.refl encUnary A).forall_mem (by fun_prop)

end ComplexityTests.Tally
