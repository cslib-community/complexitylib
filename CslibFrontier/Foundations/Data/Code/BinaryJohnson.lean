/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Foundations.Analysis.InnerProductSpace.NearlyOrthogonal
import CslibFrontier.Foundations.Data.BitString.Sign.BigOperators
import CslibFrontier.Foundations.Data.BitString.SignWord
import CslibFrontier.Foundations.Data.Code.HammingBound
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The binary Johnson bound in correlation form

Read binary words `X → Bool` as `±1` vectors, so that the inner product of two words is their sign
correlation `∑ x, signVal (f x) * signVal (g x)` (`Cslib.BitString.inner_signWord`). If words
`c i`, `i ∈ s`, each have correlation at least `α |X|` with a fixed word `w`, where `α ≥ 0`, and
pairwise correlation at most `β |X|`, then the Cauchy–Schwarz inequality for `w` and `∑ i, c i`
gives `#s (α ^ 2 - β) ≤ 1 - β` for nonempty `s`
(`Cslib.Code.card_mul_sq_sub_le_of_le_sum_signVal_mul_signVal`). Only an upper bound on the
pairwise correlations is needed: pairs of nearly complementary words are allowed.

A word agrees with `w` on at least a `1 / 2 + ε` fraction of the positions exactly when their
correlation is at least `2 ε |X|` (`Cslib.BitString.sum_signVal_mul_signVal_eq_two_mul_card_sub`).
With `α = 2 ε` and `β = 2 ε ^ 2` this is the **binary Johnson bound**: fewer than `1 / (2 ε ^ 2)`
words with pairwise correlation at most `2 ε ^ 2 |X|` agree with `w` on a `1 / 2 + ε` fraction of
the positions (`Cslib.Code.card_mul_two_mul_sq_lt_one`). In terms of distances: a binary code of
relative minimum distance at least `1 / 2 - ε ^ 2` has fewer than `1 / (2 ε ^ 2)` codewords within
relative distance `1 / 2 - ε` of any word
(`Cslib.Code.card_filter_hammingDist_le_mul_two_mul_sq_lt_one`). This is the binary Johnson bound
as stated in [Arora and Barak, Chapter 19][AroraBarak09] for distance `1 / 2 - ε ^ 2` and radius
`1 / 2 - ε`, with a strict inequality. The alphabet-free and `q`-ary bounds of
`Cslib.Code.card_filter_hammingDist_le_le` and `Cslib.Code.card_filter_hammingDist_le_le_of_mul_le`
reach comparable radii but bound the list by the length of the code.

For an encoding of messages that are not themselves separated, the list is first covered by
the Hamming balls of radius `r` around a subset of messages pairwise farther than `r` apart
(`Cslib.Code.exists_subset_pairwise_lt_hammingDist_forall_exists_le`). If the encodings of
messages farther than `r` apart have correlation at most `2 ε ^ 2 |X|`, the Johnson bound applies
to that subset, so at most `V / (2 ε ^ 2)` messages have encodings agreeing with `w` on a
`1 / 2 + ε` fraction of the positions, where `V` bounds the size of a ball of radius `r`
(`Cslib.Code.card_filter_mul_two_mul_sq_le`).

## Main results

* `Cslib.Code.card_mul_sq_sub_le_of_le_sum_signVal_mul_signVal`: the Johnson bound for words with
  correlations at least `α |X|` to a fixed word and at most `β |X|` to each other.
* `Cslib.Code.card_mul_two_mul_sq_lt_one`: the binary Johnson bound in agreement form.
* `Cslib.Code.card_filter_hammingDist_le_mul_two_mul_sq_lt_one`: the binary Johnson bound for a code
  of relative distance `1 / 2 - ε ^ 2` at radius `1 / 2 - ε`.
* `Cslib.Code.card_filter_mul_two_mul_sq_le`: the list size of an encoding whose distant messages
  have nearly uncorrelated encodings.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
* [S. M. Johnson, *A new upper bound for error-correcting codes*][Johnson1962]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019],
  Section 7.3
-/

public section

namespace Cslib.Code

open Finset BitString
open scoped RealInnerProductSpace

variable {X : Type*} [Fintype X]

/-- **The Johnson bound in correlation form**: if the words `c i`, `i ∈ s`, of a nonempty family
each have sign correlation at least `α |X|` with `w`, where `α ≥ 0`, and pairwise sign correlation
at most `β |X|`, then `#s (α ^ 2 - β) ≤ 1 - β`. -/
theorem card_mul_sq_sub_le_of_le_sum_signVal_mul_signVal [Nonempty X] {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) (c : ι → X → Bool) (w : X → Bool) {α β : ℝ} (hα : 0 ≤ α)
    (hβ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∑ x, signVal (c i x) * signVal (c j x) ≤ β * Fintype.card X)
    (hw : ∀ i ∈ s, α * Fintype.card X ≤ ∑ x, signVal (c i x) * signVal (w x)) :
    (#s : ℝ) * (α ^ 2 - β) ≤ 1 - β := by
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have h := card_mul_sq_le_of_inner_ge hs (fun i => signWord (c i)) (signWord w) hX hα
    (norm_signWord_sq w).le (fun i _ => (norm_signWord_sq _).le)
    (fun i hi j hj hij => by rw [inner_signWord]; exact hβ i hi j hj hij)
    (fun i hi => by rw [real_inner_comm, inner_signWord]; exact hw i hi)
  linarith

/-- **The binary Johnson bound** in agreement form: if the words `c i`, `i ∈ s`, have pairwise sign
correlation at most `2 ε ^ 2 |X|` and each agrees with `w` on at least a `1 / 2 + ε` fraction of
the positions, where `ε ≥ 0`, then `#s * (2 ε ^ 2) < 1`: there are fewer than `1 / (2 ε ^ 2)` of
them. -/
theorem card_mul_two_mul_sq_lt_one [Nonempty X] {ι : Type*} {s : Finset ι}
    (c : ι → X → Bool) (w : X → Bool) {ε : ℝ} (hε : 0 ≤ ε)
    (hβ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∑ x, signVal (c i x) * signVal (c j x) ≤ 2 * ε ^ 2 * Fintype.card X)
    (hagree : ∀ i ∈ s, (1 / 2 + ε) * Fintype.card X ≤ #{x | c i x = w x}) :
    (#s : ℝ) * (2 * ε ^ 2) < 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  rcases hε.eq_or_lt with rfl | hε0
  · simp
  have h := card_mul_sq_sub_le_of_le_sum_signVal_mul_signVal hs c w (by positivity : 0 ≤ 2 * ε)
    hβ fun i hi => by
      rw [sum_signVal_mul_signVal_eq_two_mul_card_sub]
      linarith [hagree i hi]
  nlinarith [sq_nonneg ε, mul_pos hε0 hε0]

/-- **The binary Johnson bound** for codes [Arora and Barak, Chapter 19][AroraBarak09]: if any two
distinct words of a binary code `C` differ on at least a `1 / 2 - ε ^ 2` fraction of the positions,
where `ε ≥ 0`, then fewer than `1 / (2 ε ^ 2)` codewords lie within distance `(1 / 2 - ε) |X|` of
any word `w`. -/
theorem card_filter_hammingDist_le_mul_two_mul_sq_lt_one [Nonempty X]
    {C : Finset (X → Bool)} {ε : ℝ} (hε : 0 ≤ ε)
    (hC : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → (1 / 2 - ε ^ 2) * Fintype.card X ≤ hammingDist c c')
    (w : X → Bool) :
    (#{c ∈ C | (hammingDist c w : ℝ) ≤ (1 / 2 - ε) * Fintype.card X} : ℝ) * (2 * ε ^ 2) < 1 := by
  refine card_mul_two_mul_sq_lt_one (fun c => c) w hε (fun c hc c' hc' hcc' => ?_)
    (fun c hc => ?_)
  · rw [sum_signVal_mul_signVal_eq_card_sub]
    linarith [hC c (mem_filter.1 hc).1 c' (mem_filter.1 hc').1 hcc']
  · have hsum : (#{x | c x = w x} : ℝ) + hammingDist c w = Fintype.card X := by
      exact_mod_cast card_filter_eq_add_hammingDist c w
    linarith [(mem_filter.1 hc).2]

/-- **List size by covering**: let `E` encode messages `m : ι → A` as binary words on `X`. Suppose
the encodings of messages farther than `r` apart have sign correlation at most `2 ε ^ 2 |X|`, where
`ε ≥ 0`, and every Hamming ball of radius `r` holds at most `V ≥ 0` messages. Then the messages
whose encodings agree with `w` on at least a `1 / 2 + ε` fraction of the positions number at most
`V / (2 ε ^ 2)`. -/
theorem card_filter_mul_two_mul_sq_le [Nonempty X] {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] (E : (ι → A) → X → Bool) (w : X → Bool) {ε V : ℝ} (hε : 0 ≤ ε)
    (hV : 0 ≤ V) (r : ℕ)
    (hfar : ∀ m m' : ι → A, r < hammingDist m m' →
      ∑ x, signVal (E m x) * signVal (E m' x) ≤ 2 * ε ^ 2 * Fintype.card X)
    (hball : ∀ m : ι → A, (#{m' | hammingDist m m' ≤ r} : ℝ) ≤ V) :
    (#{m | (1 / 2 + ε) * Fintype.card X ≤ #{x | E m x = w x}} : ℝ) * (2 * ε ^ 2) ≤ V := by
  set L := ({m | (1 / 2 + ε) * Fintype.card X ≤ #{x | E m x = w x}} : Finset (ι → A))
  -- cover the list by balls of radius `r` around messages pairwise farther than `r` apart
  obtain ⟨C, hCL, hCr, hcov⟩ := exists_subset_pairwise_lt_hammingDist_forall_exists_le L r
  have hLC : (#L : ℝ) ≤ #C * V := by
    have hsub : L ⊆ C.biUnion fun m => {m' | hammingDist m m' ≤ r} := fun m' hm' => by
      obtain ⟨m, hm, hmm'⟩ := hcov m' hm'
      exact mem_biUnion.2 ⟨m, hm, mem_filter.2 ⟨mem_univ _, hmm'⟩⟩
    calc (#L : ℝ) ≤ #(C.biUnion fun m => {m' | hammingDist m m' ≤ r}) := by
          exact_mod_cast card_le_card hsub
      _ ≤ ∑ m ∈ C, (#{m' | hammingDist m m' ≤ r} : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ _m ∈ C, V := sum_le_sum fun m _ => hball m
      _ = #C * V := by rw [sum_const, nsmul_eq_mul]
  -- the Johnson bound on the separated messages
  have hC : (#C : ℝ) * (2 * ε ^ 2) < 1 :=
    card_mul_two_mul_sq_lt_one E w hε (fun m hm m' hm' hmm' => hfar m m' (hCr hm hm' hmm'))
      fun m hm => (mem_filter.1 (hCL hm)).2
  calc (#L : ℝ) * (2 * ε ^ 2) ≤ #C * V * (2 * ε ^ 2) :=
        mul_le_mul_of_nonneg_right hLC (by positivity)
    _ = V * (#C * (2 * ε ^ 2)) := by ring
    _ ≤ V * 1 := mul_le_mul_of_nonneg_left hC.le hV
    _ = V := mul_one V

end Cslib.Code
