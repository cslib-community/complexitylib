/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Razborov.LearningParams
public import CslibFrontier.MachineLearning.UniformLearning.CIKK.Learner
import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.AmpGeneratorCircuit
import CslibFrontier.MachineLearning.UniformLearning.CIKK.Complexity

/-!
# Learning AC⁰[2] with the rank property

Carmosino, Impagliazzo, Kabanets and Kolokolova learn every class against which a natural property
is useful [Carmosino et al., Theorem 5.1, p. 10:19]
[CarmosinoImpagliazzoKabanetsKolokolova2016], and conclude that AC⁰[p] is learnable in
quasi-polynomial time with membership queries under the uniform distribution
[Carmosino et al., Corollary 5.4, p. 10:20][CarmosinoImpagliazzoKabanetsKolokolova2016]. This file
proves the `p = 2` case for a fixed depth `d` and size `s`, with the GF(2) rank property as the
test. It certifies the number of queries and the De Morgan circuit size of the hypotheses, not the
running time.

The CIKK learner (`Cslib.MachineLearning.UniformLearning.learns_cikkLearner`) needs a test that is
dense and rejects every output `g_z` of the black-box generator on the amplified target. Take the
test that accepts the truth tables of the rank property at the input length
`ℓ = cikkAC0Len d e n s g` and the advantage exponent `g = cikkAC0Gap d e n s`
(`CslibFrontier.Computability.Circuit.Boolean.Razborov.LearningParams`). It accepts at least half of
the truth tables, which covers the density hypothesis by the fixed point `ℓ + 2 ≤ g`. Each `g_z`
is computed by a circuit with `MOD_2` gates of depth at most `d + 7` and size at most
`S(g) = k s + 6 (k n + k)² + 3` (`Cslib.Crypto.PRG.NisanWigderson.exists_circuit_generator_glAmp`),
so the rank test rejects it.

The learner then makes at most `(h + 1) 2 ^ (12 g + 6 e + 59)` queries, and
`g ≤ 2^{2D(5D+25)} B^{2D}` with `D = d + 7` and `B` the bit length of
`M² (s + 6 (n + 1)² + 3)`, `M = 2^{e+10} (3e + 42)`. For fixed `d`, `B = O(e + log (n s))`, so the
number of queries is `2 ^ O((e + log (n s)) ^ (2 d + 14))` times `h + 1`: quasi-polynomial in `n`,
`s` and the inverse error `2 ^ e`.

The rank test is decided from the truth table by a De Morgan circuit with at most `173 · 8 ^ ℓ`
gates (`Cslib.Circuits.Boolean.Razborov.complexity_truthTableTest_rankTest_le`). Composed with the
bound of the learner's hypotheses, affine in the test's circuit size
(`Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_le_two_pow`), and with
`ℓ + 2 ≤ g`, every hypothesis has a De Morgan circuit with at most `2 ^ (17 g + 9 e + 76)` gates,
again quasi-polynomial for fixed `d`. Since the test is itself a small circuit, this bounds the
circuit complexity of the hypotheses themselves, not the size of an oracle circuit.

Labels:
* **Rank property.** The test is this library's variant of the rank property (one square matrix,
  threshold `C(n, a) / 2`, level `sliceLevel`; see
  `Cslib.Circuits.Boolean.Razborov.RankProperty`), with density `1 / 2` where Theorem 5.1 assumes
  largeness `1 / 5`. Its constructivity enters only through the size of its truth-table circuit,
  which bounds the hypotheses' size; the source's constructivity is NC² rather than size.
* **`p = 2` only.** Corollary 5.4 states every prime.
* **Queries, not time.** Corollary 5.4 bounds the running time; this file certifies the number of
  queries. The learner's running time is not certified.
* **Hypothesis size.** The hypotheses' bound is De Morgan circuit size with this library's
  constants; their depth is not certified, so they are not shown to lie in AC⁰[2]. Corollary 5.4's
  hypotheses are general circuits as well, so neither learner is shown to be proper.
* **Nonuniform target class.** The class is fixed by `d` and `s`, with the input length `n`. The
  parameters `g` and `ℓ` are explicit closed forms rather than the source's choice of `L` with
  `log L > u⁻¹(poly)` [Carmosino et al., proof of Theorem 5.1, p. 10:19]
  [CarmosinoImpagliazzoKabanetsKolokolova2016]; the depth overhead `7` is that of the library's
  generator circuits, and all constants are this library's.

The deviations of `learns_cikkLearner` (a single outer best-of selection, powers of two) carry
over.

## Main results

* `Cslib.MachineLearning.UniformLearning.learns_cikkLearner_rankTest`: the CIKK learner with the
  rank test learns the functions computed by depth-`d`, size-`s` circuits with `MOD_2` gates, with
  error `2^{-e}` and confidence `1 - 2^{-h}`.
* `Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner_rankTest`: it makes at most
  `(h + 1) 2 ^ (12 g + 6 e + 59)` queries.
* `Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner_rankTest_le`: the same bound in
  closed form in `d`, `e`, `h`, `n` and `s`.
* `Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_rankTest_le_two_pow`: every
  hypothesis has a De Morgan circuit with at most `2 ^ (17 g + 9 e + 76)` gates.
* `Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_rankTest_le`: the same bound in
  closed form in `d`, `e`, `n` and `s`.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*, Theorem 5.1 (p. 10:19) and Corollary 5.4 (p. 10:20)]
  [CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.MachineLearning.UniformLearning

open Finset Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Razborov
  Cslib.Crypto.PRG Cslib.Crypto.PRG.NisanWigderson

/-- **Learning AC⁰[2] with the rank property** [Carmosino et al., Theorem 5.1, p. 10:19, and
Corollary 5.4, p. 10:20][CarmosinoImpagliazzoKabanetsKolokolova2016], for `p = 2`: with
`g = cikkAC0Gap d e n s` and `ℓ = cikkAC0Len d e n s g`, the CIKK learner whose test accepts the
truth tables of the rank property at `ℓ` learns every function on `n` bits computed by a circuit
with `MOD_2` gates of depth at most `d` and size at most `s`, with error `2^{-e}` and confidence
`1 - 2^{-h}`. The class is the circuit model of `Cslib.Circuits.Boolean.AC0Mod 2` at length `n`,
with explicit depth bound `d` and size bound `s`: a language in `AC0Mod 2` has, at length `n`, a
circuit of this kind with `d` its depth bound and `s` its size bound at `n`. The labels are in the
module docstring. -/
theorem learns_cikkLearner_rankTest (d e h n s : ℕ) :
    (cikkLearner n (cikkAC0Len d e n s (cikkAC0Gap d e n s)) e (cikkAC0Gap d e n s) h
        (truthTableTest (rankProperty sliceLevel (cikkAC0Len d e n s (cikkAC0Gap d e n s))))).Learns
      (cikkSeed n (cikkAC0Len d e n s (cikkAC0Gap d e n s)) e (cikkAC0Gap d e n s) h)
      {f | ∃ C : Circuit Unbounded.extSignature n 1,
        C.Computes (Unbounded.extInterpretation (modGate 2)) (single f) ∧ C.depth ≤ d ∧
          C.size ≤ s}
      (1 / 2 ^ e) (1 / 2 ^ h) := by
  set g := cikkAC0Gap d e n s
  set ℓ := cikkAC0Len d e n s g
  refine learns_cikkLearner e g h ?_ ?_
  · -- the rank test accepts half of the truth tables, and `ℓ + 2 ≤ g`
    have hfix : ℓ + 2 ≤ g := cikkAC0Len_add_two_le_cikkAC0Gap d e n s
    have hhalf : 2 ^ 2 ^ ℓ ≤ 2 * #{T | truthTableTest (rankProperty sliceLevel ℓ) T = true} := by
      rw [card_filter_truthTableTest, rankProperty_apply]
      exact two_pow_two_pow_le_two_mul_ncard_rankTest ℓ (sliceLevel ℓ)
    calc 2 ^ 2 ^ ℓ * 2 ^ (ℓ + 1)
        ≤ 2 * #{T | truthTableTest (rankProperty sliceLevel ℓ) T = true} * 2 ^ (ℓ + 1) :=
          Nat.mul_le_mul_right _ hhalf
      _ = 2 ^ (ℓ + 2) * #{T | truthTableTest (rankProperty sliceLevel ℓ) T = true} := by ring
      _ ≤ 2 ^ g * #{T | truthTableTest (rankProperty sliceLevel ℓ) T = true} :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hfix)
  · -- every generator output has a small circuit, which the rank test rejects
    rintro f ⟨C, hC, hCd, hCs⟩ z
    obtain ⟨G, hG, hGs, hGd⟩ :=
      exists_circuit_generator_glAmp (Signature.Hom.id _) hC (cikkK e g) ℓ z
    have hrej := notMem_rankProperty_cikkAC0Len_of_computes (hGd.trans (by omega))
      (hGs.trans (by gcongr)) hG
    rw [Bool.eq_false_iff, ne_eq, truthTableTest_eq_true_iff]
    exact hrej

/-- **Queries of the AC⁰[2] learner**: with `g = cikkAC0Gap d e n s`, the learner of
`learns_cikkLearner_rankTest` makes at most `(h + 1) 2 ^ (12 g + 6 e + 59)` queries. -/
theorem queriesAtMost_cikkLearner_rankTest (d e h n s : ℕ) :
    (cikkLearner n (cikkAC0Len d e n s (cikkAC0Gap d e n s)) e (cikkAC0Gap d e n s) h
        (truthTableTest (rankProperty sliceLevel
          (cikkAC0Len d e n s (cikkAC0Gap d e n s))))).QueriesAtMost
      ((h + 1) * 2 ^ (12 * cikkAC0Gap d e n s + 6 * e + 59)) := by
  have hfix := cikkAC0Len_add_two_le_cikkAC0Gap d e n s
  exact fun ω => (queriesAtMost_cikkLearner_two_pow _ _ _ _ _ _ ω).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- **Quasi-polynomially many queries** [Carmosino et al., Corollary 5.4, p. 10:20]
[CarmosinoImpagliazzoKabanetsKolokolova2016], for `p = 2` and counting queries: with `D = d + 7`,
`M = 2^{e+10} (3e + 42)` and `B = ⌊log₂ (M² (s + 6 (n + 1)² + 3))⌋ + 1`, the learner of
`learns_cikkLearner_rankTest` makes at most `(h + 1) 2 ^ (12 · 2^{2D(5D+25)} B^{2D} + 6 e + 59)`
queries. For fixed `d`, `B = O(e + log (n s))`, so this is quasi-polynomial in `n`, `s` and
`2 ^ e`. -/
theorem queriesAtMost_cikkLearner_rankTest_le (d e h n s : ℕ) :
    (cikkLearner n (cikkAC0Len d e n s (cikkAC0Gap d e n s)) e (cikkAC0Gap d e n s) h
        (truthTableTest (rankProperty sliceLevel
          (cikkAC0Len d e n s (cikkAC0Gap d e n s))))).QueriesAtMost
      ((h + 1) * 2 ^ (12 * (2 ^ (2 * (d + 7) * (5 * (d + 7) + 25)) *
        (Nat.log 2 ((2 ^ (e + 10) * (3 * e + 42)) ^ 2 * (s + 6 * (n + 1) ^ 2 + 3)) + 1) ^
          (2 * (d + 7))) + 6 * e + 59)) := by
  have hg := cikkAC0Gap_le d e n s
  exact fun ω => (queriesAtMost_cikkLearner_rankTest d e h n s ω).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- The hypothesis bound at any input length `ℓ` and advantage exponent `g` with `ℓ + 2 ≤ g`: the
test has at most `173 · 8 ^ ℓ < 2 ^ (3 ℓ + 8)` gates. -/
private theorem complexity_eval_cikkLearner_rankTest_le_of_add_two_le {n ℓ g : ℕ} (e h : ℕ)
    (hfix : ℓ + 2 ≤ g) (f : BooleanFunction n) (ω) :
    complexity interpretation (single
        ((cikkLearner n ℓ e g h (truthTableTest (rankProperty sliceLevel ℓ)) ω).eval f)) ≤
      2 ^ (17 * g + 9 * e + 76) := by
  have htest : complexity interpretation (single (truthTableTest (rankProperty sliceLevel ℓ))) + 1 ≤
      2 ^ (3 * ℓ + 8) := by
    rw [rankProperty_apply]
    have h8 : (8 : ℕ) ^ ℓ = 2 ^ (3 * ℓ) := by rw [pow_mul]; norm_num
    have := complexity_truthTableTest_rankTest_le ℓ (sliceLevel ℓ)
    rw [pow_add, ← h8]
    have : 1 ≤ 8 ^ ℓ := Nat.one_le_pow _ _ (by norm_num)
    omega
  calc _ ≤ 2 ^ (11 * g + 9 * e + 3 * ℓ + 80) *
          (complexity interpretation (single (truthTableTest (rankProperty sliceLevel ℓ))) + 1) :=
        complexity_eval_cikkLearner_le_two_pow n ℓ e g h _ f ω
    _ ≤ 2 ^ (11 * g + 9 * e + 3 * ℓ + 80) * 2 ^ (3 * ℓ + 8) := Nat.mul_le_mul_left _ htest
    _ = 2 ^ (11 * g + 9 * e + 6 * ℓ + 88) := by ring
    _ ≤ 2 ^ (17 * g + 9 * e + 76) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Size of the AC⁰[2] learner's hypotheses** [Carmosino et al., Theorem 5.1, p. 10:19, and
Corollary 5.4, p. 10:20][CarmosinoImpagliazzoKabanetsKolokolova2016], for `p = 2`: with
`g = cikkAC0Gap d e n s`, on every target `f` and seed, the hypothesis of the learner of
`learns_cikkLearner_rankTest` has a De Morgan circuit with at most `2 ^ (17 g + 9 e + 76)` gates.
This bounds size only, with this library's constants: depth is not certified, so the hypotheses are
not shown to lie in AC⁰[2]. -/
theorem complexity_eval_cikkLearner_rankTest_le_two_pow (d e h n s : ℕ) (f : BooleanFunction n)
    (ω) :
    complexity interpretation (single
        ((cikkLearner n (cikkAC0Len d e n s (cikkAC0Gap d e n s)) e (cikkAC0Gap d e n s) h
          (truthTableTest (rankProperty sliceLevel
            (cikkAC0Len d e n s (cikkAC0Gap d e n s)))) ω).eval f)) ≤
      2 ^ (17 * cikkAC0Gap d e n s + 9 * e + 76) :=
  complexity_eval_cikkLearner_rankTest_le_of_add_two_le e h
    (cikkAC0Len_add_two_le_cikkAC0Gap d e n s) f ω

/-- **Quasi-polynomial hypothesis size** [Carmosino et al., Corollary 5.4, p. 10:20]
[CarmosinoImpagliazzoKabanetsKolokolova2016], for `p = 2`: with `D = d + 7`,
`M = 2^{e+10} (3e + 42)` and `B = ⌊log₂ (M² (s + 6 (n + 1)² + 3))⌋ + 1`, the hypothesis of the
learner of `learns_cikkLearner_rankTest` has a De Morgan circuit with at most
`2 ^ (17 · 2^{2D(5D+25)} B^{2D} + 9 e + 76)` gates. For fixed `d`, `B = O(e + log (n s))`, so this
is quasi-polynomial in `n`, `s` and `2 ^ e`. Depth is not certified. -/
theorem complexity_eval_cikkLearner_rankTest_le (d e h n s : ℕ) (f : BooleanFunction n) (ω) :
    complexity interpretation (single
        ((cikkLearner n (cikkAC0Len d e n s (cikkAC0Gap d e n s)) e (cikkAC0Gap d e n s) h
          (truthTableTest (rankProperty sliceLevel
            (cikkAC0Len d e n s (cikkAC0Gap d e n s)))) ω).eval f)) ≤
      2 ^ (17 * (2 ^ (2 * (d + 7) * (5 * (d + 7) + 25)) *
        (Nat.log 2 ((2 ^ (e + 10) * (3 * e + 42)) ^ 2 * (s + 6 * (n + 1) ^ 2 + 3)) + 1) ^
          (2 * (d + 7))) + 9 * e + 76) := by
  have hg := cikkAC0Gap_le d e n s
  exact (complexity_eval_cikkLearner_rankTest_le_two_pow d e h n s f ω).trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))

end Cslib.MachineLearning.UniformLearning
