/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.BitString.Weight
import CslibFrontier.Foundations.Data.Code.BerlekampWelch
import CslibFrontier.Foundations.Data.Code.Justesen
import CslibFrontier.Foundations.Data.Code.LocalDecoding
import CslibFrontier.Foundations.Data.Code.Sudan
import CslibFrontier.Foundations.FieldTheory.Finite.Subfield
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.ComputeDegree

/-!
# Tests: decoding algebraic codes, and Justesen codes

The Berlekamp–Welch decoder over `ZMod 7` reports failure on a received word of length three that
no constant is within distance one of, although `2 * 1 + 1 ≤ 3`; without its checks the decoder
returned a quotient here. Sudan's decoder lists exactly the two lines `X` and `2 * X` for a word
over `ZMod 7` that agrees with each of them at four of the seven points: three errors, beyond the
two that unique decoding corrects at dimension two. The line decoder of the Reed–Muller code of
degree two in two variables over `ZMod 5` reads a value along a line, and corrects one error from
more than half of the directions. A binary Hamming ball, and Justesen codes over the Galois fields
with `2 ^ (16 * s)` elements, which satisfy the hypotheses of the asymptotic statement.
-/

namespace CslibFrontierTests.Code.M3

open Cslib Cslib.Code Finset Polynomial

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ### Failure detection of the Berlekamp–Welch decoder -/

/-- Three points of `ZMod 7`. -/
private def points3 : Fin 3 → ZMod 7 := fun i => (i : ℕ)

private theorem points3_injective : Function.Injective points3 := by decide

/-- A received word with three distinct values: every constant differs from it twice. -/
private def received3 : Fin 3 → ZMod 7 := ![1, 2, 4]

private theorem lt_hammingDist_received3 (p : (ZMod 7)[X]) (hp : p.degree < 1) :
    1 < hammingDist (fun i => p.eval (points3 i)) received3 := by
  rw [eq_C_of_degree_le_zero (Order.le_of_lt_succ hp)]
  simp only [eval_C]
  generalize p.coeff 0 = a
  revert a
  decide

/-- No constant is within distance one of the received word, so the decoder fails. -/
example : berlekampWelch points3 1 1 received3 = none :=
  berlekampWelch_eq_none_of_forall_lt_hammingDist lt_hammingDist_received3

/-- The decoder for one error and dimension one returns nothing on the received word, since
`2 * 1 + 1 ≤ 3`: it fails exactly when no constant is within distance one. -/
example : ¬∃ p, berlekampWelch points3 1 1 received3 = some p := by
  rintro ⟨p, hp⟩
  have := (berlekampWelch_eq_some_iff points3_injective (by simp)).1 hp
  exact absurd this.2 (not_le.2 (lt_hammingDist_received3 p this.1))

/-! ### Sudan's list decoder over `ZMod 7` -/

/-- The seven points of `ZMod 7`. -/
private def points7 : Fin 7 → ZMod 7 := fun i => (i : ℕ)

private theorem points7_injective : Function.Injective points7 := by decide

/-- The values of `X` at the points `0, 1, 2, 3` and of `2 * X` at the points `0, 4, 5, 6`. -/
private def received7 : Fin 7 → ZMod 7 := ![0, 1, 2, 3, 1, 3, 5]

/-- The lines that agree with the received word at more than three points: `X` and `2 * X`. -/
private theorem agree_iff (a b : ZMod 7) :
    3 < #{i | b * points7 i + a = received7 i} ↔ a = 0 ∧ b = 1 ∨ a = 0 ∧ b = 2 := by
  revert a b
  decide

/-- **Sudan's decoder lists exactly the two close lines.** At dimension two and weighted degree
three, `2 * 1 * 7 < 4 * 5`, so the decoder lists the lines agreeing with the word at four or more
points. -/
example : sudan points7 received7 2 3 = {X, C 2 * X} := by
  ext P
  rw [mem_sudan_iff_of_lt points7_injective le_rfl (by norm_num)]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨hP, hagree⟩
    rw [eq_X_add_C_of_degree_le_one (Order.le_of_lt_succ hP)] at hagree ⊢
    simp only [eval_add, eval_mul, eval_C, eval_X] at hagree
    rcases (agree_iff _ _).1 hagree with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · left
      rw [h0, h1, C_0, add_zero, C_1, one_mul]
    · right
      rw [h0, h1, C_0, add_zero]
  · rintro (rfl | rfl)
    · refine ⟨by compute_degree!, ?_⟩
      simpa using (agree_iff 0 1).2 (Or.inl ⟨rfl, rfl⟩)
    · refine ⟨by compute_degree!, ?_⟩
      simpa using (agree_iff 0 2).2 (Or.inr ⟨rfl, rfl⟩)

/-- The list of Sudan's decoder at dimension two and weighted degree three has at most three
entries. -/
example (w : Fin 7 → ZMod 7) : #(sudan points7 w 2 3) ≤ 3 := by
  simpa using card_sudan_mul_le (α := points7) (w := w) (k := 2) (D := 3)

/-! ### Local decoding of a Reed–Muller code over `ZMod 5` -/

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The evaluation table of `X 0 * X 1`, of total degree two. -/
private def table : (Fin 2 → ZMod 5) → ZMod 5 := fun x => x 0 * x 1

private theorem table_mem : table ∈ reedMuller (ZMod 5) 2 2 := by
  refine mem_reedMuller.2 ⟨MvPolynomial.X 0 * MvPolynomial.X 1, ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp [MvPolynomial.totalDegree_X]
  · funext x
    simp [table]

/-- Along the direction `(1, 1)`, the line decoder reads `table (1, 2) = 2` from the values
`table (1 + c, 2 + c)` for `c ≠ 0`. -/
example : lineDecode table ![1, 2] ![1, 1] = 2 := by decide

/-- The line decoder is exact on the codeword. -/
example (x v : Fin 2 → ZMod 5) : lineDecode table x v = table x :=
  lineDecode_eq_of_mem_reedMuller (by simp) table_mem x v

/-- With one corrupted value, more than half of the `24` nonzero directions recover each value:
`2 * (1 * 4) < 24`. -/
example (y x : Fin 2 → ZMod 5) (a : ZMod 5) :
    24 < 2 * #{v ∈ univ.erase 0 | lineDecode (Function.update table y a) x v = table x} := by
  have hdist : hammingDist (Function.update table y a) table ≤ 1 := by
    by_cases h : table y = a
    · rw [← h, Function.update_eq_self, hammingDist_self]
      exact zero_le_one
    · rw [hammingDist_comm, hammingDist_update_of_ne h]
  have := lt_two_mul_card_filter_lineDecode_eq (by simp) table_mem (w := Function.update table y a)
    (by simp only [ZMod.card]; omega) x
  simpa using this

/-! ### Justesen codes -/

/-- There are `1 + 4 = 5` binary words of length four and weight at most one. -/
example : #{x : Fin 4 → Bool | hammingNorm x ≤ 1} = 5 := by
  simp only [← BitString.weight_eq_hammingNorm, BitString.card_filter_weight_le]
  decide

/-- **Justesen codes are asymptotically good, non-vacuously.** For every `s`, the Galois field
with `2 ^ (16 * (s + 1))` elements is written as `16 * (s + 1)` bits, and the resulting family of
Justesen codes of outer dimension `2 ^ (16 * (s + 1) - 1)` is asymptotically good. -/
example :
    ∃ (_ : ∀ s, Fintype (GaloisField 2 (16 * (s + 1))))
      (_ : ∀ s, DecidableEq (GaloisField 2 (16 * (s + 1))))
      (φ : ∀ s, GaloisField 2 (16 * (s + 1)) ≃+ BitString (16 * (s + 1))),
      IsAsymptoticallyGood fun s => justesenCode (φ s) (2 ^ (16 * (s + 1) - 1)) := by
  classical
  let _ (s : ℕ) : Fintype (GaloisField 2 (16 * (s + 1))) := Fintype.ofFinite _
  have hcard (s : ℕ) : Fintype.card (GaloisField 2 (16 * (s + 1))) = 2 ^ (16 * (s + 1)) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 _ (by omega)]
  exact ⟨inferInstance, inferInstance, fun s => (nonempty_addEquiv_bitString (hcard s)).some,
    isAsymptoticallyGood_justesenCode _⟩

/-- **The full code family is not asymptotically good.** Although `Set.univ` has rate `1` and its
block lengths `s + 2` grow without bound, its minimum distance is `1`, so its relative distance
`1 / (s + 2)` tends to `0`. -/
example : ¬ IsAsymptoticallyGood (fun s : ℕ => (Set.univ : Set (Fin (s + 2) → Bool))) := by
  intro h
  obtain ⟨Δ, -, hΔ⟩ := h.exists_minDist
  let x : Fin (Δ + 2) → Bool := fun _ => false
  let y : Fin (Δ + 2) → Bool := Function.update x 0 true
  have hxy : x ≠ y := fun h => by simpa [x, y] using congrFun h 0
  have hdist : hammingDist x y = 1 := hammingDist_update_of_ne (by decide : x 0 ≠ true)
  have hmin : minDist (Set.univ : Set (Fin (Δ + 2) → Bool)) ≤ 1 := by
    have := minDist_le_hammingDist (Set.mem_univ x) (Set.mem_univ y) hxy
    rwa [hdist, Nat.cast_one] at this
  have hle := (hΔ Δ).trans (mul_le_mul_right hmin (Δ : ℕ∞))
  rw [Fintype.card_fin, mul_one, Nat.cast_le] at hle
  omega

end CslibFrontierTests.Code.M3
