/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.UniformLearning.CIKK.Learner
import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.DirectProduct.Complexity

/-!
# The size of the CIKK learner's hypotheses

The hypotheses of the CIKK learner (`Cslib.MachineLearning.UniformLearning.cikkLearner`) are
small circuits relative to the test. Every output of the learner is the output of one of its runs.
That run's hypothesis is the direct-product decoder over the Goldreich–Levin candidate over the
Nisan–Wigderson hypothesis, so its size bound composes three bounds:

1. the Nisan–Wigderson hypothesis
   (`Cslib.MachineLearning.UniformLearning.complexity_eval_nwLearner_le`) of the negated test,
   which costs one gate more than the test (`Cslib.Circuits.Boolean.complexity_not_le`);
2. each output bit of the Goldreich–Levin candidate
   (`Cslib.Circuits.Boolean.complexity_glAmpCandidate_apply_le`);
3. the direct-product decoder
   (`Cslib.Circuits.Boolean.DirectProduct.complexity_dpDecode_le`).

The bound `Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_le` is affine in the
circuit complexity of the test, with `T (F + 1) (2 ^ K - 1)` copies of it for `T = cikkTrials e g`
trials, `F = cikkFixed e g` fixed positions and `K = cikkMasks e g` masks. If the gates of the
test cost one each, it is the size that the corresponding oracle circuit would have, as in
[Carmosino, Impagliazzo, Kabanets and Kolokolova, Theorem 5.1, p. 10:19]
[CarmosinoImpagliazzoKabanetsKolokolova2016]; that oracle circuit is not built. The closed form
`Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_le_two_pow` uses this library's
constants and is not tight. The bounds concern size only: depth and running time are not
certified.

## Main results

* `Cslib.MachineLearning.UniformLearning.complexity_eval_ampLearner_le`: the hypothesis of the
  reconstruction of the amplification, from a bound on the hypothesis it decodes.
* `Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_le`,
  `Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_le_two_pow`: the hypothesis of
  the CIKK learner, in full and in closed form.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets and A. Kolokolova,
  *Learning Algorithms from Natural Proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.MachineLearning.UniformLearning

open Finset Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.DirectProduct
  Cslib.Crypto.PRG Cslib.Crypto.PRG.NisanWigderson

/-- **Size of the reconstructed hypothesis.** If the hypothesis of `A` on `glAmp f k` has circuit
complexity at most `c`, the hypothesis of `ampLearner A s m K` on `f` has circuit complexity at most
`m (s + 1) ((2 ^ K - 1) (c + 1) + 8 + 2 (2 ^ K - 1) (2 ^ K + 1)) + 3 m + 1`: the direct-product
decoder over `m` trials and `s` fixed positions, over the output bits of the Goldreich–Levin
candidate. -/
theorem complexity_eval_ampLearner_le {k n : ℕ} {Ω : Type*}
    (A : QueryLearner (Fin (k * n + k)) Ω) (s m K : ℕ) (f : BooleanFunction n) (ω : Ω)
    (a : AmpSeed n k s m K) {c : ℕ}
    (hA : complexity interpretation (single ((A ω).eval (glAmp f k))) ≤ c) :
    complexity interpretation (single ((ampLearner A s m K (ω, a)).eval f)) ≤
      m * (s + 1) * ((2 ^ K - 1) * (c + 1) + (8 + 2 * (2 ^ K - 1) * (2 ^ K + 1))) +
        3 * m + 1 := by
  obtain ⟨⟨masks, guess⟩, P, b₀, v⟩ := a
  rw [eval_ampLearner]
  have hP : #(P : Finset (Fin k)) = s := (mem_powersetCard.1 P.2).2
  refine (complexity_dpDecode_le _ false P b₀ v
    (complexity_glAmpCandidate_apply_le hA masks guess)).trans_eq ?_
  rw [hP]
  ring

/-- **Size of the CIKK learner's hypotheses.** On any target and seed, the hypothesis of
`cikkLearner n ℓ e g h test` has circuit complexity at most
`T (F + 1) ((2 ^ K - 1) (c + N + 3) + 8 + 2 (2 ^ K - 1) (2 ^ K + 1)) + 3 T + 1`, where `c` is the
circuit complexity of the test, `N = 2 ^ ℓ (2 ^ (ℓ - 1) (2 (ℓ - 1) + 3) + 1)` is the cost of the
Nisan–Wigderson reconstruction around it, `T = cikkTrials e g`, `F = cikkFixed e g` and
`K = cikkMasks e g`.

The bound is affine in `c`, with `T (F + 1) (2 ^ K - 1)` copies of the test. If the gates of the
test cost one each, it is the size of the corresponding oracle circuit of
[Carmosino, Impagliazzo, Kabanets and Kolokolova, Theorem 5.1, p. 10:19]; that oracle circuit is
not built. -/
theorem complexity_eval_cikkLearner_le (n ℓ e g h : ℕ) (test : BitString (2 ^ ℓ) → Bool)
    (f : BooleanFunction n) (ω) :
    complexity interpretation (single ((cikkLearner n ℓ e g h test ω).eval f)) ≤
      cikkTrials e g * (cikkFixed e g + 1) *
          ((2 ^ cikkMasks e g - 1) * (complexity interpretation (single test) +
              2 ^ ℓ * (2 ^ (ℓ - 1) * (2 * (ℓ - 1) + 3) + 1) + 3) +
            (8 + 2 * (2 ^ cikkMasks e g - 1) * (2 ^ cikkMasks e g + 1))) +
        3 * cikkTrials e g + 1 := by
  rw [cikkLearner_def]
  obtain ⟨ω, x⟩ := ω
  refine (QueryLearner.le_sup_eval_bestOf _ _ _ f ω x
    fun h => complexity interpretation (single h)).trans (Finset.sup_le fun j _ => ?_)
  refine complexity_eval_ampLearner_le _ _ _ _ f (ω j).1 (ω j).2 ?_
  refine (complexity_eval_nwLearner_le _ _ _ _).trans ?_
  have := complexity_not_le test
  omega

/-- The Nisan–Wigderson term of `complexity_eval_cikkLearner_le` is at most `2 ^ (3 ℓ + 3)`. -/
private theorem nwTerm_le (ℓ : ℕ) :
    2 ^ ℓ * (2 ^ (ℓ - 1) * (2 * (ℓ - 1) + 3) + 1) ≤ 2 ^ (3 * ℓ + 3) := by
  have hu : 2 ^ ℓ ≤ 2 * 2 ^ (ℓ - 1) := by
    rcases ℓ with _ | ℓ
    · norm_num
    · rw [pow_succ, Nat.add_sub_cancel]
      omega
  have ha : ℓ - 1 < 2 ^ (ℓ - 1) := Nat.lt_two_pow_self
  calc 2 ^ ℓ * (2 ^ (ℓ - 1) * (2 * (ℓ - 1) + 3) + 1)
      ≤ (2 * 2 ^ (ℓ - 1)) * (2 ^ (ℓ - 1) * (3 * 2 ^ (ℓ - 1)) + 2 ^ (ℓ - 1) * 2 ^ (ℓ - 1)) := by
        gcongr
        · omega
        · exact Nat.one_le_iff_ne_zero.2 (by positivity)
    _ = 8 * (2 ^ (ℓ - 1)) ^ 3 := by ring
    _ ≤ 8 * (2 ^ ℓ) ^ 3 := by gcongr; exact Nat.sub_le _ _
    _ = 2 ^ (3 * ℓ + 3) := by ring

/-- The arithmetic of `complexity_eval_cikkLearner_le_two_pow`, from the closed forms of the
parameters. -/
private theorem size_le_two_pow (c ℓ e g T F K : ℕ) (hT : T ≤ 2 ^ (4 * g + 2 * e + 24) * (e + 4))
    (hF : F ≤ 2 ^ (e + 7) * (8 * g + 5 * e + 50)) (hK : K ≤ 3 * g + 2 * e + 17) :
    T * (F + 1) * ((2 ^ K - 1) * (c + 2 ^ ℓ * (2 ^ (ℓ - 1) * (2 * (ℓ - 1) + 3) + 1) + 3) +
        (8 + 2 * (2 ^ K - 1) * (2 ^ K + 1))) + 3 * T + 1 ≤
      2 ^ (11 * g + 9 * e + 3 * ℓ + 80) * (c + 1) := by
  have hN := nwTerm_le ℓ
  have hP8 : 8 ≤ 2 ^ (3 * ℓ + 3) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 * ℓ + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set N := 2 ^ ℓ * (2 ^ (ℓ - 1) * (2 * (ℓ - 1) + 3) + 1)
  set P := 2 ^ (3 * ℓ + 3) with hP
  set B := 2 ^ K with hB
  have hB1 : 1 ≤ B := Nat.one_le_two_pow
  -- the argument of each Goldreich–Levin candidate
  have hX : 5 * (c + N + 3) ≤ 8 * P * (c + 1) := by
    have : c ≤ c * P := Nat.le_mul_of_pos_right c (by omega)
    have h8 : 8 * P * (c + 1) = 8 * (c * P) + 8 * P := by ring
    omega
  -- each output bit of the candidate
  have hInner : (B - 1) * (c + N + 3) + (8 + 2 * (B - 1) * (B + 1)) ≤
      5 * B ^ 2 * (c + N + 3) := by
    have h1 : (B - 1) * (c + N + 3) ≤ B ^ 2 * (c + N + 3) := by
      gcongr
      calc B - 1 ≤ B := Nat.sub_le _ _
        _ ≤ B ^ 2 := Nat.le_self_pow (by norm_num) B
    have h2 : 2 * (B - 1) * (B + 1) ≤ 4 * B ^ 2 :=
      calc 2 * (B - 1) * (B + 1) ≤ 2 * B * (B + B) := by gcongr; omega
        _ = 4 * B ^ 2 := by ring
    have h3 : 12 * B ^ 2 ≤ 4 * B ^ 2 * (c + N + 3) :=
      calc 12 * B ^ 2 = 4 * B ^ 2 * 3 := by ring
        _ ≤ 4 * B ^ 2 * (c + N + 3) := by gcongr; omega
    have h4 : 8 ≤ 8 * B ^ 2 := Nat.le_mul_of_pos_right 8 (by positivity)
    have h5 : 5 * B ^ 2 * (c + N + 3) = B ^ 2 * (c + N + 3) + 4 * B ^ 2 * (c + N + 3) := by ring
    omega
  have hInner' : (B - 1) * (c + N + 3) + (8 + 2 * (B - 1) * (B + 1)) ≤
      2 ^ (6 * g + 4 * e + 3 * ℓ + 40) * (c + 1) := by
    have hB2 : B ^ 2 ≤ 2 ^ (6 * g + 4 * e + 34) := by
      rw [hB, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    calc (B - 1) * (c + N + 3) + (8 + 2 * (B - 1) * (B + 1))
        ≤ 5 * B ^ 2 * (c + N + 3) := hInner
      _ = B ^ 2 * (5 * (c + N + 3)) := by ring
      _ ≤ 2 ^ (6 * g + 4 * e + 34) * (8 * P * (c + 1)) := Nat.mul_le_mul hB2 hX
      _ = 2 ^ (6 * g + 4 * e + 3 * ℓ + 40) * (c + 1) := by rw [hP]; ring
  -- the trials and fixed positions
  have hTb : T ≤ 2 ^ (4 * g + 3 * e + 26) := by
    have he : e < 2 ^ e := Nat.lt_two_pow_self
    calc T ≤ 2 ^ (4 * g + 2 * e + 24) * (e + 4) := hT
      _ ≤ 2 ^ (4 * g + 2 * e + 24) * (4 * 2 ^ e) := by gcongr; omega
      _ = 2 ^ (4 * g + 3 * e + 26) := by ring
  have hFb : F + 1 ≤ 2 ^ (g + 2 * e + 13) := by
    have hge : g + e < 2 ^ (g + e) := Nat.lt_two_pow_self
    have h7 : 1 ≤ 2 ^ (e + 7) := Nat.one_le_two_pow
    calc F + 1 ≤ 2 ^ (e + 7) * (8 * g + 5 * e + 50) + 2 ^ (e + 7) := by omega
      _ = 2 ^ (e + 7) * (8 * g + 5 * e + 51) := by ring
      _ ≤ 2 ^ (e + 7) * (64 * 2 ^ (g + e)) := by gcongr; omega
      _ = 2 ^ (g + 2 * e + 13) := by ring
  have hTF : T * (F + 1) ≤ 2 ^ (5 * g + 5 * e + 39) :=
    calc T * (F + 1) ≤ 2 ^ (4 * g + 3 * e + 26) * 2 ^ (g + 2 * e + 13) := Nat.mul_le_mul hTb hFb
      _ = 2 ^ (5 * g + 5 * e + 39) := by ring
  -- the decoder's trials make up half of the bound, and the rest is small
  have hmain := Nat.mul_le_mul hTF hInner'
  have hsmall : 4 * 2 ^ (4 * g + 3 * e + 26) ≤ 2 ^ (11 * g + 9 * e + 3 * ℓ + 79) * (c + 1) :=
    calc 4 * 2 ^ (4 * g + 3 * e + 26) = 2 ^ (4 * g + 3 * e + 28) := by ring
      _ ≤ 2 ^ (11 * g + 9 * e + 3 * ℓ + 79) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ (11 * g + 9 * e + 3 * ℓ + 79) * (c + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hsum : 2 ^ (5 * g + 5 * e + 39) * (2 ^ (6 * g + 4 * e + 3 * ℓ + 40) * (c + 1)) =
      2 ^ (11 * g + 9 * e + 3 * ℓ + 79) * (c + 1) := by ring
  have htot : 2 ^ (11 * g + 9 * e + 3 * ℓ + 80) * (c + 1) =
      2 * (2 ^ (11 * g + 9 * e + 3 * ℓ + 79) * (c + 1)) := by
    ring
  have ht1 : 1 ≤ 2 ^ (4 * g + 3 * e + 26) := Nat.one_le_two_pow
  omega

/-- **Closed form of the hypothesis size**: at most `2 ^ (11 g + 9 e + 3 ℓ + 80) (c + 1)`, where `c`
is the circuit complexity of the test. The constant is this library's and is not tight. -/
theorem complexity_eval_cikkLearner_le_two_pow (n ℓ e g h : ℕ) (test : BitString (2 ^ ℓ) → Bool)
    (f : BooleanFunction n) (ω) :
    complexity interpretation (single ((cikkLearner n ℓ e g h test ω).eval f)) ≤
      2 ^ (11 * g + 9 * e + 3 * ℓ + 80) * (complexity interpretation (single test) + 1) :=
  (complexity_eval_cikkLearner_le n ℓ e g h test f ω).trans
    (size_le_two_pow _ ℓ e g _ _ _ (cikkTrials_le e g) (cikkFixed_le e g) (cikkMasks_le e g))

end Cslib.MachineLearning.UniformLearning
