/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Parameterized.Distillation

/-!
# Tests: OR-distillation and `NP/poly`

The halving cover on a concrete map, where one value covers everything; `NP ⊆ NP/poly`; and the
hypotheses of the Fortnow–Santhanam theorem satisfied by concrete maps. "Some entry is `true`" is an
OR-distillation of the problem `{true}` with output length `1`, which places `{false}` in
`NP/poly`. Equality of lengths is a polynomial equivalence relation on bit strings with `n + 1`
classes up to length `n`, and testing whether some entry of a list of bit strings has a `true` bit
satisfies the class-wise hypotheses with `t n = 2`, placing the all-`false` strings in `NP/poly`.
-/

namespace ComplexityTests.Distillation

open Cslib Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime Finset

/-! ### The halving cover -/

/-- Pairs from `Fin 4` mapped to the parity of their sum: fewer than `2 ^ 2` values, so
`⌊log₂ 4⌋ + 1 = 3` values cover `Fin 4`; in fact `0` alone does, through the pairs `(a, a)`. -/
example :
    (∃ S ⊆ ({0, 1} : Finset ℕ), #S ≤ 3 ∧ ∀ a ∈ (univ : Finset (Fin 4)),
      ∃ g : Fin 2 → Fin 4, (∀ i, g i ∈ univ) ∧ a ∈ Set.range g ∧
        (g 0 + g 1 : ℕ) % 2 ∈ S) ∧
    ∀ a : Fin 4, ((fun _ => a : Fin 2 → Fin 4) 0 + (fun _ => a : Fin 2 → Fin 4) 1 : ℕ) % 2 = 0 := by
  refine ⟨?_, fun a => show ((a : ℕ) + a) % 2 = 0 by omega⟩
  have := exists_tupleCover (t := 2) (fun g : Fin 2 → Fin 4 => (g 0 + g 1 : ℕ) % 2) {0, 1}
    (by decide) univ fun g _ => by
      rcases Nat.mod_two_eq_zero_or_one (g 0 + g 1 : ℕ) with h | h <;> simp [h]
  have h4 : Nat.log 2 4 = 2 := by simpa using Nat.log_pow Nat.one_lt_two 2
  simpa [h4] using this

/-! ### `NP/poly` -/

/-- `NP ⊆ NP/poly`, and the duality between `coNP ⊆ NP/poly` and `NP ⊆ coNP/poly`, on `SAT`. -/
example : SAT ∈ NPPoly encCNF ∧ SATᶜ ∈ coNPPoly encCNF ∧
    (coNP encCNF ⊆ NPPoly encCNF ↔ NP encCNF ⊆ coNPPoly encCNF) :=
  ⟨NP_subset_NPPoly CookLevin.SAT_npComplete.1,
    by simpa [mem_coNPPoly] using NP_subset_NPPoly CookLevin.SAT_npComplete.1,
    coNP_subset_NPPoly_iff⟩

/-! ### An OR-distillation -/

/-- "Some entry is `true`" is an OR-distillation of `{true}` into `{true}` with size bound `1`. -/
theorem isORDistillation_any :
    IsORDistillation encBool encBool {true} {true} (fun l => l.any id) fun _ => 1 := by
  refine ⟨?_, fun l _ => ?_, fun _ l _ _ => by simp⟩
  · exact anyWithInput (id' (encIn := encList encBool))
      (snd _ _)
  · simp

/-- The OR-distillation theorem applies to it: `{false}` is in `NP/poly`. -/
example : ({false} : Set Bool) ∈ NPPoly encBool := by
  have := isORDistillation_any.compl_mem_NPPoly Decoder.bool (.const 1)
  have hcompl : ({true} : Set Bool)ᶜ = {false} := by
    ext b
    cases b <;> simp
  rwa [hcompl] at this

/-! ### A polynomial equivalence relation with many classes -/

/-- Bit strings of equal length. -/
private def sameLength (p : List Bool × List Bool) : Bool := decide (p.1.length = p.2.length)

/-- Equal length is a polynomial equivalence relation on bit strings, with the `n + 1` classes of
the strings `false ^ m` for `m ≤ n` up to length `n`. -/
theorem isPolyEquivalence_sameLength : IsPolyEquivalence encBits sameLength := by
  refine ⟨⟨fun _ => by simp [sameLength], fun h => by simp_all [sameLength],
    fun h h' => by simp_all [sameLength]⟩, ?_, fun n => n + 1, by fun_prop, fun n => ?_⟩
  · exact decide_eq'
      (length_bits.comp (fst _ _))
      (length_bits.comp (snd _ _))
  · refine ⟨(range (n + 1)).image fun m => List.replicate m false, card_image_le.trans
      (by simp), fun a ha => ⟨List.replicate a.length false, ?_, by simp [sameLength]⟩⟩
    exact mem_image.2 ⟨a.length, mem_range.2 (by simpa using Nat.lt_succ_of_le ha), rfl⟩

/-- Testing whether some entry of a list of bit strings has a `true` bit compresses lists of
strings of equal length to one bit, so the class-wise theorem places the all-`false` strings in
`NP/poly`. -/
example : {w : List Bool | ∀ b ∈ w, b = false} ∈ NPPoly encBits := by
  have h := compl_mem_NPPoly_of_orCompression (A := {w : List Bool | true ∈ w})
    (B := {true}) Decoder.bits isPolyEquivalence_sameLength
    (f := fun l => l.any fun w => decide (true ∈ w))
    (anyWithInput (id' (encIn := encList encBits))
      (decide_mem ((bits_encList_polyTime encBool).1.comp (snd _ _)) (const true)))
    (fun l _ _ => by simp) (t := fun _ => 2) (.const 2) fun _ _ _ _ _ => by simp
  have hcompl : {w : List Bool | true ∈ w}ᶜ = {w : List Bool | ∀ b ∈ w, b = false} := by
    ext w
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · intro h b hb
      cases b
      · rfl
      · exact absurd hb h
    · intro h ht
      exact Bool.noConfusion (h true ht)
  rwa [hcompl] at h

end ComplexityTests.Distillation
