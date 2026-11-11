/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bound
import Mathlib.Data.Nat.Size

/-!
# Short descriptions

The time hierarchy theorems diagonalize only over inputs whose framed description is
*short*: `2 ^ |unframe x| ≤ |x|` (`Cslib.Complexity.Diagonal.shortDesc`). Decoding a description
of `L` bits then takes time polynomial in `L`, of a degree fixed by the decoder, hence `O(2 ^ L)`,
which is `O(|x|)`. Padded descriptions are short. The space hierarchy theorem asks for tiny
descriptions instead (`CslibFrontier.Computability.Complexity.Classes.Hierarchy.TinyDesc`), so that
decoding takes logarithmic space.

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

/-- Comparing `2 ^ L` with `n`, both in unary, in linear time: `n` is halved `L` times by
`Turing.MultiTapeTM.ComputableInO.unary_halvings`, which costs `n + n / 2 + ⋯`, and the result is
tested for positivity. -/
private theorem computableInO_two_pow_le :
    ComputableInO (fun p : ℕ × ℕ => decide (2 ^ p.2 ≤ p.1)) (encPair encUnary encUnary)
      encBool (fun p => p.1 + p.2) fun p => p.1 + p.2 := by
  have hlen (n : ℕ) : (encUnary n).length = n := by simp [encUnary_apply]
  have hT : ComputableTidilyInTimeAndSpace (fun k : ℕ => [decide (0 < k)]) encUnary encBits
      (fun k => 4 * (encUnary k).length + 8) fun _ => 0 :=
    posT.computableTidilyInTimeAndSpace fun k => by
      rw [encUnary_apply, run_posT]
      rfl
  have hpos : ComputableInO (fun k : ℕ => [decide (0 < k)]) encUnary encBits (fun v => v)
      fun v => v :=
    .of_bounds hT.computableInTimeAndSpace 12 (fun n => by rw [hlen]; omega)
      (fun _ => Nat.zero_le _) fun _ => by simp only [encBits_apply, List.length_singleton]; omega
  have hnil : ComputableInO (fun _ : ℕ => ([] : List Bool)) encUnary encBits (fun v => v)
      fun v => v :=
    (ComputableInO.constZero _).mono 1 (fun n => by rw [hlen]; omega) fun _ => Nat.zero_le _
  refine (ComputableInO.unary_halvings hnil hpos).of_enc_eq fun p => ?_
  simp only [encBool_apply, encBits_apply, List.map_const', List.flatten_replicate_nil,
    List.nil_append, List.cons.injEq, and_true]
  exact decide_eq_decide.mpr (Nat.div_pos_iff.trans (and_iff_right (by positivity))).symm

/-- **Shortness is decided within linear time and space.** The length of the word and of the
framed description are written in unary, and the first is halved once per bit of the second. -/
theorem computableInO_shortDesc :
    ComputableInO shortDesc encBits encBool (fun x => x.length) fun x => x.length := by
  have hu : ComputableInO unframe encBits encBits (fun x => x.length) fun x => x.length :=
    (ComputableTidilyInO.of_linear (.of_unframe fun _ => rfl)).computableInO
  have hl := ComputableInO.lengthUnary
  have h := computableInO_two_pow_le.comp (hl.prod (hl.comp hu))
  refine h.mono 8 (fun x => ?_) fun x => ?_
  all_goals
    have h₁ := length_unframe_le x
    simp only [Function.comp_apply] at h₁ ⊢
    omega

end Cslib.Complexity.Diagonal
