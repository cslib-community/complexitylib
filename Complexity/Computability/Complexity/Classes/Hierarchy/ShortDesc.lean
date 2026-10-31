/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bound
import Mathlib.Data.Nat.Size

/-!
# Short descriptions

The time and space hierarchy theorems diagonalize only over inputs whose framed description is
*short*: `2 ^ |unframe x| ≤ |x|` (`Cslib.Complexity.Diagonal.shortDesc`). Decoding a description
of `L` bits then takes time polynomial in `L`, of a degree fixed by the decoder, hence `O(2 ^ L)`,
which is `O(|x|)`. Padded descriptions are short.

## Main definitions

* `Cslib.Complexity.Diagonal.shortDesc`: whether the framed description at the start of a word is
  short.

## Main results

* `Cslib.Complexity.Diagonal.shortDesc_eq_decide`: shortness compares the length of the
  description with the number of binary digits of the length of the word.
* `Cslib.Complexity.Diagonal.computableInO_shortDesc`: shortness is decided within linear time
  and space, by halving the length of the word once per bit of the description.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorems 9.3 and 9.10][Sipser2013]:
  the padded descriptions in the proofs of the hierarchy theorems.
-/

@[expose] public section

namespace Cslib.Complexity.Diagonal

open Turing Turing.MultiTapeTM

/-- The description framed at the start of `x` is *short*: `2 ^ |unframe x| ≤ |x|`. -/
def shortDesc (x : List Bool) : Bool := decide (2 ^ (unframe x).length ≤ x.length)

/-- Shortness compares the length of the description with the number of binary digits of the
length of the word. -/
theorem shortDesc_eq_decide (x : List Bool) :
    shortDesc x = decide ((unframe x).length + 1 ≤ (encNat x.length).length) := by
  rw [shortDesc, encNat_apply, Nat.size_eq_bits_len]
  exact decide_eq_decide.mpr (Nat.lt_size.symm.trans Nat.lt_iff_add_one_le)

/-! ### Shortness in linear time -/

/-- The transducer halving a unary number: it keeps every second bit. -/
private def halveT : Transducer Bool Bool where
  q₀ := false
  step q _ := (!q, if q then [true] else [])
  final _ := []
  length_step_le q _ := by cases q <;> simp
  length_final_le _ := by simp

private lemma run_halveT (q : Bool) (k : ℕ) :
    halveT.run q (List.replicate k true) = List.replicate ((k + q.toNat) / 2) true := by
  induction k generalizing q with
  | zero => cases q <;> rfl
  | succ k ih =>
    rw [List.replicate_succ, Transducer.run_cons, ih]
    cases q
    · simp only [halveT, Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.nil_append,
        Bool.toNat_true, Bool.toNat_false]
    · have e : (k + 1 + Bool.toNat true) / 2 = (k + Bool.toNat false) / 2 + 1 := by
        simp only [Bool.toNat_true, Bool.toNat_false]
        omega
      rw [e, List.replicate_succ]
      rfl

/-- The transducer emitting nothing. -/
private def silentT : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private lemma run_silentT (w : List Bool) : silentT.run () w = [] := by
  induction w with
  | nil => rfl
  | cons b w ih => exact ih

/-- The transducer reporting whether a unary number is positive. -/
private def posT : Transducer Bool Bool where
  q₀ := false
  step _ _ := (true, [])
  final q := [q]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private lemma run_posT (q : Bool) (k : ℕ) :
    posT.run q (List.replicate k true) = [q || decide (0 < k)] := by
  induction k generalizing q with
  | zero => simp [posT]
  | succ k ih =>
    rw [List.replicate_succ, Transducer.run_cons, ih]
    simp [posT]

private lemma iterate_div_two (n i : ℕ) : (· / 2)^[i] n = n / 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ, Nat.div_div_eq_div_mul]

private lemma sum_div_two_pow_le (n L : ℕ) : ∑ i ∈ Finset.range L, n / 2 ^ i ≤ 2 * n := by
  induction L generalizing n with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ']
    have h (i : ℕ) : n / 2 ^ (i + 1) = n / 2 / 2 ^ i := by
      rw [pow_succ', Nat.div_div_eq_div_mul]
    simp only [h, pow_zero, Nat.div_one]
    have := ih (n / 2)
    omega

/-- Comparing `2 ^ L` with `n`, both in unary, in linear time: `n` is halved `L` times, which costs
`n + n / 2 + ⋯`, and the result is tested for positivity. -/
private theorem computableTidilyInO_two_pow_le :
    ComputableTidilyInO (fun p : ℕ × ℕ => decide (2 ^ p.2 ≤ p.1)) (encPair encUnary encUnary)
      encBool (fun p => (encPair encUnary encUnary p).length)
      fun p => (encPair encUnary encUnary p).length := by
  have hN : ComputableTidilyInTimeAndSpace (· / 2) encUnary encUnary
      (fun k => 4 * (encUnary k).length + 8) fun _ => 0 :=
    halveT.computableTidilyInTimeAndSpace fun k => by
      rw [encUnary_apply, encUnary_apply, run_halveT]
      rfl
  have hE : ComputableTidilyInTimeAndSpace (fun _ : ℕ => ([] : List Bool)) encUnary encBits
      (fun k => 4 * (encUnary k).length + 8) fun _ => 0 :=
    silentT.computableTidilyInTimeAndSpace fun k => (run_silentT _).symm
  have hF : ComputableTidilyInTimeAndSpace (fun k : ℕ => [decide (0 < k)]) encUnary encBits
      (fun k => 4 * (encUnary k).length + 8) fun _ => 0 :=
    posT.computableTidilyInTimeAndSpace fun k => by
      rw [encUnary_apply, run_posT]
      rfl
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.iterate_unary_stream_sum hN hE hF
    (R := fun x i => 17 * (x.1 / 2 ^ i) + 17) (Q := fun _ => 0) (B := fun x => x.1)
    (fun x i _ => by
      simp only [encUnary_apply, List.length_replicate, iterate_div_two]
      have : x.1 / 2 ^ (i + 1) ≤ x.1 / 2 ^ i :=
        Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ i)) (by positivity)
      omega)
    (fun _ _ _ => le_rfl)
    (fun x i _ => by
      simp only [encUnary_apply, List.length_replicate, iterate_div_two]
      exact Nat.div_le_self _ _)
  refine ComputableTidilyInO.of_bounds (h.of_enc_eq fun p => ?_) (100 * c + 100)
    (fun p => ?_) (fun p => ?_) fun p => ?_
  · simp only [encBool_apply, encBits_apply, iterate_div_two, List.map_const',
      List.flatten_replicate_nil, List.nil_append, List.cons.injEq, and_true]
    exact decide_eq_decide.mpr (Nat.div_pos_iff.trans (and_iff_right (by positivity))).symm
  · have hs := sum_div_two_pow_le p.1 p.2
    have hq : p.1 / 2 ^ p.2 ≤ p.1 := Nat.div_le_self _ _
    simp only [encUnary_apply, List.length_replicate, iterate_div_two, length_encPair,
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      smul_eq_mul]
    nlinarith
  · simp only [length_encPair, encUnary_apply, List.length_replicate]
    nlinarith
  · simp only [encBool_apply, List.length_singleton]
    nlinarith

/-- **Shortness is decided within linear time and space.** The length of the word and of the
framed description are written in unary, and the first is halved once per bit of the second. -/
theorem computableInO_shortDesc :
    ComputableInO shortDesc encBits encBool (fun x => x.length) fun x => x.length := by
  have hu : ComputableTidilyInO unframe encBits encBits (fun x => x.length) fun x => x.length :=
    ComputableTidilyInO.of_linear (.of_unframe fun _ => rfl)
  have hl := ComputableInO.lengthUnary.tidy
  have h := computableTidilyInO_two_pow_le.comp (hl.prod (hl.comp hu))
  refine (h.mono 8 (fun x => ?_) fun x => ?_).computableInO
  all_goals
    have h₁ := length_unframe_le x
    simp only [Function.comp_apply, length_encPair, encUnary_apply, List.length_replicate] at h₁ ⊢
    omega

end Cslib.Complexity.Diagonal
