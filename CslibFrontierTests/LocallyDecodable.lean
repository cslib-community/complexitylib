/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.LocallyDecodable.Hadamard
import CslibFrontier.Computability.LocallyDecodable.OneQuery
import Mathlib.Tactic.NormNum

/-!
# Tests: locally decodable codes

The Hadamard code of three bits is a `(2, 1/8, 1/4)` locally decodable code and a `(2, 2, 1/2)`
smooth code, and the Katz–Trevisan smoothing of its decoder is a `(2, 16, 1/4)` smooth decoder. The
repetition code of one bit, read at a uniform position, is a `(1, 1, 1/2)` smooth code; it attains
the one-query bound `4 |ι| ε² ≤ c² (|Γ| - 1)` with equality. No binary code of two message bits is
a `(1, 1, 1/2)` smooth code, and no binary code of a hundred message bits is a `(1, 1/4, 1/4)`
locally decodable code, whatever its length.
-/

namespace CslibFrontierTests.LocallyDecodable

open Cslib Cslib.Code Cslib.BitString Probability

/-! ### The Hadamard code -/

/-- The Hadamard decoder recovers each of three bits with probability `3/4` from a word that
differs from the codeword on an eighth of the positions. -/
private theorem isLocalDecoder_hadamard :
    IsLocalDecoder hadamardCode 2 (1 / 8) (1 / 4) (hadamardDecoder (ι := Fin 3)) := by
  have h := isLocalDecoder_hadamardDecoder (ι := Fin 3) (1 / 8)
  have hε : (1 / 2 - 2 * (1 / 8) : ℝ) = 1 / 4 := by norm_num
  rw [hε] at h
  exact h

example : IsLocallyDecodable (hadamardCode (ι := Fin 3)) 2 (1 / 8) (1 / 4) :=
  isLocalDecoder_hadamard.isLocallyDecodable

example : IsSmoothCode (hadamardCode (ι := Fin 3)) 2 2 (1 / 2) :=
  isSmoothDecoder_hadamardDecoder.isSmoothCode

/-- Katz–Trevisan smoothing turns the `(2, 1/8, 1/4)` Hadamard decoder into a `(2, 16, 1/4)`
smooth decoder. -/
example : IsSmoothCode (hadamardCode (ι := Fin 3)) 2 16 (1 / 4) := by
  have h := isLocalDecoder_hadamard.isSmoothCode hasObliviousReads_hadamardDecoder
    (by norm_num : (0 : ℝ) < 1 / 8)
  have h16 : ((2 : ℕ) : ℝ) / (1 / 8) = 16 := by norm_num
  rw [h16] at h
  exact h

/-! ### The repetition code -/

/-- The repetition code of one bit, of length three. -/
private def repetition : (Unit → Bool) → Fin 3 → Bool := fun x _ => x ()

/-- Read a uniform position and output it. -/
private noncomputable def repetitionDecoder : LocalDecoder Unit (Fin 3) Bool := fun _ =>
  nonadaptive (ProbComp.uniform (Fin 3)) (fun r => ![r]) (fun _ a => a 0)

/-- The repetition code of one bit is a `(1, 1, 1/2)` smooth code. -/
private theorem isSmoothDecoder_repetitionDecoder :
    IsSmoothDecoder repetition 1 1 (1 / 2) repetitionDecoder := by
  have h := isSmoothDecoder_nonadaptive_of_uniform (C := repetition) (ε := 1 / 2)
    (fun _ => ProbComp.uniform (Fin 3)) (fun _ r => ![r]) (fun _ _ a => a 0)
    (fun _ k => by
      rw [ProbComp.eval_uniform]
      fin_cases k
      exact PMF.map_id _)
    (fun x _ => by
      rw [decodeLaw_nonadaptive, ProbComp.eval_uniform]
      have hconst : (fun r : Fin 3 => (fun (_ : Fin 3) (a : Fin 1 → Bool) => a 0) r
          (repetition x ∘ ![r])) = Function.const _ (x ()) := rfl
      rw [hconst, PMF.map_const, PMF.pure_apply_self, ENNReal.toReal_one]
      norm_num)
  rw [Nat.cast_one] at h
  exact h

/-- The repetition code attains the one-query bound with equality. -/
example : 4 * Fintype.card Unit * (1 / 2 : ℝ) ^ 2 ≤ 1 ^ 2 * (Fintype.card Bool - 1) :=
  isSmoothDecoder_repetitionDecoder.four_mul_card_mul_sq_le (by norm_num)

example : 4 * Fintype.card Unit * (1 / 2 : ℝ) ^ 2 = 1 ^ 2 * (Fintype.card Bool - 1) := by
  norm_num

/-- The repetition code of one bit, of length three, is a `(1, 1/3, 1/6)` locally decodable code:
a word with at most one corrupted position agrees with the codeword on at least two of the three
positions, so a uniform read recovers the bit with probability at least `2/3`. -/
private theorem isLocalDecoder_repetitionDecoder :
    IsLocalDecoder repetition 1 (1 / 3) (1 / 6) repetitionDecoder where
  isQueryBounded _ := isQueryBounded_nonadaptive _ _ _
  correct x y i hy := by
    have h3 : (1 / 3 : ℝ) * Fintype.card (Fin 3) = 1 := by norm_num
    rw [h3] at hy
    have hd : hammingDist y (repetition x) ≤ 1 := by exact_mod_cast hy
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 3))) (fun r => y r = x i)
    have hdist : (Finset.univ.filter fun r : Fin 3 => ¬ y r = x i).card =
        hammingDist y (repetition x) := rfl
    rw [Finset.card_univ, Fintype.card_fin, hdist] at hsplit
    have hgood : (2 : ℝ) ≤ (Finset.univ.filter fun r : Fin 3 => y r = x i).card := by
      exact_mod_cast (by omega : 2 ≤ (Finset.univ.filter fun r : Fin 3 => y r = x i).card)
    rw [repetitionDecoder, decodeLaw_nonadaptive, ProbComp.eval_uniform,
      PMF.toReal_uniformOfFintype_map_apply, Finset.nnratCast_dens, Fintype.card_fin]
    change 1 / 2 + 1 / 6 ≤ ((Finset.univ.filter fun r : Fin 3 => y r = x i).card : ℝ) / (3 : ℕ)
    rw [Nat.cast_ofNat, le_div_iff₀ (by norm_num)]
    linarith

example : IsLocallyDecodable repetition 1 (1 / 3) (1 / 6) :=
  isLocalDecoder_repetitionDecoder.isLocallyDecodable

/-- Katz–Trevisan smoothing of a concrete one-query code: the `(1, 1/3, 1/6)` repetition code is a
`(1, 3, 1/6)` smooth code. -/
example : IsSmoothCode repetition 1 3 (1 / 6) := by
  have h := isLocalDecoder_repetitionDecoder.isSmoothCode_of_one (by norm_num)
  have h3 : (1 : ℝ) / (1 / 3) = 3 := by norm_num
  rw [h3] at h
  exact h

/-! ### Codes that are not one-query decodable -/

/-- No binary code of two message bits is a `(1, 1, 1/2)` smooth code. -/
example {P : Type} [Fintype P] [DecidableEq P] (C : (Fin 2 → Bool) → P → Bool) :
    ¬ IsSmoothCode C 1 1 (1 / 2) := by
  intro hC
  obtain ⟨A, hA⟩ := isSmoothCode_iff.mp hC
  have h := hA.four_mul_card_mul_sq_le (by norm_num)
  norm_num at h

/-- No binary code of a hundred message bits is a `(1, 1/4, 1/4)` locally decodable code, whatever
its length. -/
example {P : Type} [Fintype P] (C : (Fin 100 → Bool) → P → Bool) :
    ¬ IsLocallyDecodable C 1 (1 / 4) (1 / 4) := by
  intro hC
  obtain ⟨A, hA⟩ := isLocallyDecodable_iff.mp hC
  have h := hA.four_mul_sq_mul_card_mul_sq_le (by norm_num) (by norm_num)
  norm_num at h

end CslibFrontierTests.LocallyDecodable
