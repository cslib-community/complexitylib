/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Word

/-!
# Rewiring words over the De Morgan basis

Shifts, truncations, zero extensions, and one-bit words only rewire bits. If a word's bits are
available, then so are the bits of these derived words, once the `false` constant is available.
No gates are needed. Masking a word by one available bit costs one conjunction per bit.

## Main results

* `Cslib.Circuits.Boolean.wordWires_subset_iff`: available words in the bitwise form used by
  `Synthesis.word_add`.
* `Cslib.Circuits.Boolean.wordWires_subset_of_forall`: a word whose bits are `false` or bits of an
  available word is available.
* `Cslib.Circuits.Boolean.wordWires_ushiftRight_subset`,
  `Cslib.Circuits.Boolean.wordWires_shiftLeft_subset`, `Cslib.Circuits.Boolean.wordWires_ofBool`:
  shifts and one-bit words.
* `Cslib.Circuits.Synthesis.word_mask`: masking by an available bit, one gate per bit.
-/

public section

namespace Cslib.Circuits

namespace Boolean

variable {n v w : ℕ} {s : Set (BooleanFunction n)}

/-- A word is available exactly when each of its bits is. -/
theorem wordWires_subset_iff {a : BitString n → BitVec w} :
    wordWires a ⊆ s ↔ ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s := by
  simp [wordWires, Set.range_subset_iff]

/-- A word each of whose bits is constantly `false` or a fixed bit of an available word is
available, provided `false` is. -/
theorem wordWires_subset_of_forall {f : BitString n → BitVec v} {g : BitString n → BitVec w}
    (hg : wordWires g ⊆ s) (hz : (fun _ => false) ∈ s)
    (h : ∀ i : Fin v, (∀ x, (f x).getLsbD i = false) ∨
      ∃ j : Fin w, ∀ x, (f x).getLsbD i = (g x).getLsbD j) :
    wordWires f ⊆ s := by
  rintro _ ⟨i, rfl⟩
  rcases h i with h | ⟨j, hj⟩
  · simpa only [h] using hz
  · simpa only [hj] using hg ⟨j, rfl⟩

/-- A logical right shift only rewires bits. -/
theorem wordWires_ushiftRight_subset {k : ℕ} {g : BitString n → BitVec w}
    (hg : wordWires g ⊆ s) (hz : (fun _ => false) ∈ s) :
    wordWires (fun x => g x >>> k) ⊆ s := by
  refine wordWires_subset_of_forall hg hz fun i => ?_
  by_cases h : k + i.val < w
  · exact Or.inr ⟨⟨k + i.val, h⟩, fun x => by rw [BitVec.getLsbD_ushiftRight]⟩
  · exact Or.inl fun x => by
      rw [BitVec.getLsbD_ushiftRight]
      exact BitVec.getLsbD_of_ge _ _ (by omega)

/-- A left shift only rewires bits. -/
theorem wordWires_shiftLeft_subset {k : ℕ} {g : BitString n → BitVec w}
    (hg : wordWires g ⊆ s) (hz : (fun _ => false) ∈ s) :
    wordWires (fun x => g x <<< k) ⊆ s := by
  refine wordWires_subset_of_forall hg hz fun i => ?_
  by_cases h : k ≤ i.val
  · exact Or.inr ⟨⟨i.val - k, by omega⟩, fun x => by
      simp only [BitVec.getLsbD_shiftLeft, i.isLt, decide_true, Bool.true_and,
        show ¬ i.val < k by omega, decide_false, Bool.not_false]⟩
  · exact Or.inl fun x => by simp [show i.val < k by omega]

/-- An available bit is an available one-bit word. -/
theorem wordWires_ofBool {f : BooleanFunction n} (hf : f ∈ s) :
    wordWires (fun x => BitVec.ofBool (f x)) ⊆ s := by
  rintro _ ⟨i, rfl⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simpa using hf

end Boolean

namespace Synthesis

open Boolean

variable {n w : ℕ} {s : Set (BooleanFunction n)}

/-- Masking a word by an available bit costs one conjunction per bit. -/
theorem word_mask {f : BooleanFunction n} {b : BitString n → BitVec w} (hf : f ∈ s)
    (hb : wordWires b ⊆ s) :
    Synthesis interpretation s (wordWires fun x => if f x then b x else 0) w := by
  have h := family (I := interpretation) (s := s)
    (fun i : Fin w => fun x => f x && (b x).getLsbD i.val) (fun _ => 1)
    fun i => by simpa using (of_mem hf).and (of_mem (hb ⟨i, rfl⟩))
  have heq : (fun i : Fin w => fun x => (if f x then b x else 0).getLsbD i.val) =
      fun i : Fin w => fun x => f x && (b x).getLsbD i.val := by
    funext i x
    cases f x <;> simp
  rw [wordWires, heq]
  simpa using h

end Synthesis

end Cslib.Circuits
