/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.Circuit
public import CslibFrontier.Computability.Circuit.Boolean.NaturalProof
import CslibFrontier.Computability.Circuit.Boolean.AtLeast
import CslibFrontier.Computability.Circuit.Boolean.Synthesis
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.PMF.Uniform
public import Cslib.Probability.PMF

/-!
# Learners yield natural properties

A membership-query learner for a class `C` of Boolean functions, with uniform seeds from a finite
set, separates `C` from most functions. On a member of `C`, its hypothesis agrees with the target at
a uniform point with probability at least `θ = (1 - δ) (1 - ε)`, averaged over the seeds. On a
uniformly random function it agrees with probability at most `p = 1 / 2 + q / 2 ^ (N + 1)`, because
a point it did not query is a fair coin (`QueryLearner.expect_dens_agrees_le`). So the functions
on which the averaged agreement is below `θ` (`QueryLearner.lowAgreement`) form a property that
* contains no member of `C` (`QueryLearner.notMem_lowAgreement`),
* holds for at least a `θ - p` fraction of all functions (`QueryLearner.sub_le_dens_lowAgreement`),
* is decided from truth tables by a threshold of the `M = |Ω| 2 ^ n` tests that run the learner and
  compare its hypothesis with the table, with `M t + O(M ^ 2)` gates when each test has `t` gates
  (`QueryLearner.complexity_truthTableTest_lowAgreement_le`).

Asymptotically, learners for `SIZE s` with circuit tests and seed sets of size `2 ^ O(n)`, and an
accuracy gap `θ - p ≥ 2 ^ (-O(n))`, yield a `P/poly`-natural property useful against `SIZE s`
(`UniformLearning.isNatural_PPoly_and_isUseful_SIZE`). This is the learning-to-natural-property
direction of [OliveiraSanthanam2017, Theorem 8, (1) ⇒ (5)]; with the converse of
[CarmosinoImpagliazzoKabanetsKolokolova2016] (`CslibFrontier.MachineLearning.UniformLearning.CIKK`)
it closes the loop between learning and natural properties.

The model differs from the source as follows.
* **Accurate learners.** The theorem needs `(1 - δ) (1 - ε)` to exceed `1 / 2 + q / 2 ^ (n + 1)`, so
  it covers strong or confidence-amplified learners. The non-trivial learners of
  [OliveiraSanthanam2017, Theorem 8, item (1)], with error `1 / 2 - 1 / n ^ k` and confidence
  `1 - 1 / n`, have `(1 - δ) (1 - ε) = (1 - 1 / n) (1 / 2 + 1 / n ^ k)`, which is below `1 / 2` for
  `k ≥ 2` and `n ≥ 3`; those learners are not covered as stated.
* **Uniform seeds from a small set.** The learner's seeds are uniform on a set of size `2 ^ O(n)`,
  so the property averages exactly over all seeds and points instead of sampling them; arbitrary
  seed distributions are not handled.
* **Fair-coin bound.** The bound on random functions is the fair-coin argument, not the bound
  [OliveiraSanthanam2017, Lemma 4] on hypotheses of small description.
* **Nonuniform constructivity.** Constructivity is `P/poly`, by circuit size; running time is not
  modelled, so this is not the `P`- or `BPP`-natural form.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.QueryLearner.lowAgreement`: the functions on which the
  learner's averaged agreement is below a threshold.

## Main results

* `Cslib.MachineLearning.UniformLearning.QueryLearner.notMem_lowAgreement`: usefulness.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.sub_le_dens_lowAgreement`: largeness.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.complexity_truthTableTest_lowAgreement_le`:
  constructivity, for one input length.
* `Cslib.MachineLearning.UniformLearning.isUseful_lowAgreement`,
  `Cslib.MachineLearning.UniformLearning.isNatural_PPoly_lowAgreement`,
  `Cslib.MachineLearning.UniformLearning.isNatural_PPoly_and_isUseful_SIZE`: **learners yield
  natural properties**.

## References

* [I. C. Oliveira, R. Santhanam, *Conspiracies between learning algorithms, circuit lower bounds,
  and pseudorandomness*][OliveiraSanthanam2017]
* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.MachineLearning.UniformLearning.QueryLearner

open Finset
open scoped BigOperators

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [Nonempty Ω]

/-- The functions on which the learner `A`, averaged over its seeds, agrees with the function at a
uniform point with probability less than `θ`. -/
def lowAgreement (A : QueryLearner ι Ω) (θ : ℝ) : Set ((ι → Bool) → Bool) :=
  {g | 𝔼 ω, (dens {z | A.agrees ω z g = true} : ℝ) < θ}

/-- **The property contains no member of the class.** If `A` learns `C` with uniform seeds, error
`ε ≤ 1` and confidence `1 - δ ≤ 1`, then no member of `C` lies in
`A.lowAgreement ((1 - δ) (1 - ε))`. -/
theorem notMem_lowAgreement {A : QueryLearner ι Ω}
    {C : PACLearning.ConceptClass (ι → Bool) Bool} {ε δ : ℝ}
    (hA : A.Learns (Cslib.Probability.PMF.uniformOfFintype Ω) C ε δ) (hε : ε ≤ 1) (hδ : 0 ≤ δ)
    {f : (ι → Bool) → Bool} (hf : f ∈ C) : f ∉ A.lowAgreement ((1 - δ) * (1 - ε)) := by
  classical
  have hbad := ENNReal.toReal_le_of_le_ofReal hδ (learns_iff.1 hA f hf)
  rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal] at hbad
  have hδ' : (dens {ω | ε < uniformError f ((A ω).eval f)} : ℝ) ≤ δ := by
    rw [Finset.nnratCast_dens]
    exact hbad
  have := le_expect_dens_eq (fun _ : Ω => f) (fun ω => (A ω).eval f) hε hδ'
  simp only [lowAgreement, Set.mem_ofPred_eq, not_lt]
  refine this.trans_eq (expect_congr rfl fun ω _ => ?_)
  simp only [agrees_eq_true_iff]

/-- **The property is large.** If `A` makes at most `q` queries, then for `θ ≤ 1` at least a
`θ - p` fraction of all functions lie in `A.lowAgreement θ`, where `p = 1 / 2 + q / 2 ^ (N + 1)`
bounds the averaged agreement on a uniformly random function (`expect_dens_agrees_le`). -/
theorem sub_le_dens_lowAgreement {A : QueryLearner ι Ω} {q : ℕ} (hA : A.QueriesAtMost q)
    {θ : ℝ} (hθ : θ ≤ 1) [DecidablePred (· ∈ A.lowAgreement θ)] :
    θ - (1 / 2 + q / 2 ^ (Fintype.card ι + 1)) ≤ (dens {g | g ∈ A.lowAgreement θ} : ℝ) := by
  set X : ((ι → Bool) → Bool) → ℝ := fun g => 𝔼 ω, (dens {z | A.agrees ω z g = true} : ℝ)
  -- the average of the agreement over all functions is at most `p`
  have hmean : 𝔼 g, X g ≤ 1 / 2 + q / 2 ^ (Fintype.card ι + 1) := by
    have h : 𝔼 g, X g = 𝔼 ω, 𝔼 z, (dens {g | A.agrees ω z g = true} : ℝ) := by
      simp only [X, ← Fintype.expect_boole]
      rw [expect_comm]
      refine expect_congr rfl fun ω _ => ?_
      rw [expect_comm]
    rw [h]
    exact expect_le univ_nonempty fun ω _ => expect_dens_agrees_le hA ω
  -- pointwise, `θ` is at most the agreement plus the indicator of the property
  have hpt (g : (ι → Bool) → Bool) : θ ≤ X g + if g ∈ A.lowAgreement θ then 1 else 0 := by
    have hX : 0 ≤ X g := expect_nonneg fun ω _ => by positivity
    have hX1 : X g ≤ 1 := expect_le univ_nonempty fun ω _ => by exact_mod_cast dens_le_one
    split_ifs with hg
    · linarith
    · simp only [lowAgreement, Set.mem_ofPred_eq, not_lt] at hg
      linarith
  have hsum : θ ≤ 𝔼 g, X g + (dens {g | g ∈ A.lowAgreement θ} : ℝ) := by
    rw [← Fintype.expect_boole, ← expect_add_distrib]
    exact le_expect univ_nonempty fun g _ => hpt g
  linarith

end Cslib.MachineLearning.UniformLearning.QueryLearner

namespace Cslib.MachineLearning.UniformLearning.QueryLearner

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.MCSP Cslib.Crypto.PRG Finset
open scoped BigOperators

variable {n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The truth-table test of `A.lowAgreement θ` is a negated threshold of the `M = |Ω| 2 ^ n`
tests `A.agrees ω z`; if each has at most `t` gates, it has at most
`M t + 2 + M (2 (M + 2)) + 1` gates. -/
theorem complexity_truthTableTest_lowAgreement_le {A : QueryLearner (Fin n) Ω} {t : ℕ}
    (hA : ∀ ω z, IsCircuitTest t fun T : BitString (2 ^ n) =>
      PMF.pure (A.agrees ω z ((truthTable n).symm T))) (θ : ℝ) :
    complexity interpretation (single (truthTableTest (A.lowAgreement θ))) ≤
      Fintype.card Ω * 2 ^ n * t +
        (2 + Fintype.card Ω * 2 ^ n * (2 * (Fintype.card Ω * 2 ^ n + 2))) + 1 := by
  classical
  choose tst htst heq using hA
  set M := Fintype.card Ω * 2 ^ n with hM
  have hcard : Fintype.card (Ω × BitString n) = M := by
    simp [hM, Fintype.card_prod, Fintype.card_bool]
  let e : Ω × BitString n ≃ Fin M := Fintype.equivFinOfCardEq hcard
  let f : Fin M → BooleanFunction (2 ^ n) := fun i => tst (e.symm i).1 (e.symm i).2
  have hf (i : Fin M) (T : BitString (2 ^ n)) :
      f i T = A.agrees (e.symm i).1 (e.symm i).2 ((truthTable n).symm T) := by
    have h := congrArg PMF.support (congrFun (heq (e.symm i).1 (e.symm i).2) T)
    simp only [PMF.support_pure, Set.singleton_eq_singleton_iff] at h
    exact h.symm
  -- the averaged agreement is the fraction of agreeing pairs
  have hX (g : BooleanFunction n) :
      𝔼 ω, (dens {z | A.agrees ω z g = true} : ℝ) =
        (#{p : Ω × BitString n | A.agrees p.1 p.2 g = true} : ℝ) / M := by
    simp only [← Fintype.expect_boole]
    rw [← Fintype.expect_prod_type
      (fun p : Ω × BitString n => if A.agrees p.1 p.2 g = true then (1 : ℝ) else 0),
      Fintype.expect_boole, Finset.nnratCast_dens, hcard]
  -- the threshold counts the agreeing pairs
  have hw (T : BitString (2 ^ n)) : BitString.weight (fun i => f i T) =
      #{p : Ω × BitString n | A.agrees p.1 p.2 ((truthTable n).symm T) = true} := by
    rw [BitString.weight]
    refine Finset.card_bij' (fun i _ => e.symm i) (fun p _ => e p) ?_ ?_ ?_ ?_ <;> simp [hf]
  have hMpos : (0 : ℝ) < M := by
    rw [hM]
    exact_mod_cast Nat.mul_pos Fintype.card_pos (Nat.two_pow_pos n)
  have htest : truthTableTest (A.lowAgreement θ) =
      fun T => !threshold M ⌈θ * M⌉₊ fun i => f i T := by
    funext T
    rw [Bool.eq_iff_iff, truthTableTest_eq_true_iff, Bool.not_eq_true', ← Bool.not_eq_true,
      threshold_eq_true_iff, hw, not_le, Nat.lt_ceil]
    simp only [lowAgreement, Set.mem_ofPred_eq, hX]
    rw [div_lt_iff₀ hMpos]
  rw [htest]
  exact (complexity_not_le _).trans (Nat.add_le_add_right
    (complexity_threshold_pi_le_of_le f fun i => htst _ _) 1)

end Cslib.MachineLearning.UniformLearning.QueryLearner

namespace Cslib.MachineLearning.UniformLearning

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.NaturalProof Filter Finset
open QueryLearner

universe u

variable {Ω : ℕ → Type u} [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]

/-- **Learners yield useful properties.** If, for all large `n`, the learner `A n` with uniform
seeds learns `C n` with error `ε n ≤ 1` and confidence `1 - δ n ≤ 1`, then the low-agreement
property is useful against every class `Λ` whose languages eventually have their slices in `C`. -/
theorem isUseful_lowAgreement {A : ∀ n, QueryLearner (Fin n) (Ω n)}
    {C : ∀ n, PACLearning.ConceptClass (BitString n) Bool} {ε δ : ℕ → ℝ}
    (hA : ∀ᶠ n in atTop, (A n).Learns (Cslib.Probability.PMF.uniformOfFintype (Ω n)) (C n) (ε n)
      (δ n))
    (hε : ∀ n, ε n ≤ 1) (hδ : ∀ n, 0 ≤ δ n) {Λ : Set (Language Bool)}
    (hΛ : ∀ L ∈ Λ, ∀ᶠ n in atTop, L.slice n ∈ C n) :
    IsUseful Λ fun n => (A n).lowAgreement ((1 - δ n) * (1 - ε n)) := fun L hL => by
  filter_upwards [hA, hΛ L hL] with n hn hLn
  exact notMem_lowAgreement hn (hε n) (hδ n) hLn

/-- Learners for `C` with circuit tests of size `2 ^ O(n)`, seed sets of size `2 ^ O(n)` and an
accuracy gap of `2 ^ (-O(n))` above `1 / 2 + q / 2 ^ (n + 1)` make the low-agreement property
`P/poly`-natural. -/
theorem isNatural_PPoly_lowAgreement {A : ∀ n, QueryLearner (Fin n) (Ω n)} {q t : ℕ → ℕ}
    {ε δ : ℕ → ℝ} {c : ℕ} (hΩ : ∀ n, Fintype.card (Ω n) ≤ 2 ^ (c * (n + 1)))
    (ht : ∀ n, t n ≤ 2 ^ (c * (n + 1))) (hA : ∀ n, (A n).HasCircuitTests (q n) (t n))
    (hε : ∀ n, 0 ≤ ε n ∧ ε n ≤ 1) (hδ : ∀ n, 0 ≤ δ n)
    (hgap : ∀ᶠ n in atTop,
      ((2 : ℝ) ^ (c * n))⁻¹ ≤ (1 - δ n) * (1 - ε n) - (1 / 2 + q n / 2 ^ (n + 1))) :
    IsNatural PPoly fun n => (A n).lowAgreement ((1 - δ n) * (1 - ε n)) := by
  classical
  refine ⟨_, fun n => le_rfl, ⟨c, ?_⟩, ?_⟩
  · -- largeness
    filter_upwards [hgap] with n hn
    have hθ : (1 - δ n) * (1 - ε n) ≤ 1 := by
      nlinarith [hε n, hδ n]
    obtain ⟨B, hBq, hB⟩ := (hA n).exists_queriesAtMost
    have hagr (ω : Ω n) (z : BitString n) (g : BooleanFunction n) :
        B.agrees ω z g = (A n).agrees ω z g := by
      rw [Bool.eq_iff_iff, agrees_eq_true_iff, agrees_eq_true_iff, hB]
    have hAB : (A n).lowAgreement ((1 - δ n) * (1 - ε n)) =
        B.lowAgreement ((1 - δ n) * (1 - ε n)) := by
      simp only [lowAgreement, hagr]
    have hd := sub_le_dens_lowAgreement hBq hθ
    rw [← hAB, Fintype.card_fin] at hd
    have hset : (A n).lowAgreement ((1 - δ n) * (1 - ε n)) =
        ↑({g | g ∈ (A n).lowAgreement ((1 - δ n) * (1 - ε n))} : Finset (BooleanFunction n)) := by
      ext g
      simp
    rw [hset, Set.ncard_coe_finset]
    rw [Finset.nnratCast_dens, Fintype.card_fun, Fintype.card_bool, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool] at hd
    have h3 : (0 : ℝ) < 2 ^ (c * n) := by positivity
    have key := hn.trans hd
    rw [inv_le_iff_one_le_mul₀ h3, div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul]
      at key
    rw [mul_comm]
    exact_mod_cast key
  · -- constructivity: the tests have `2 ^ O(n)` gates
    refine truthTableLanguage_mem_PPoly_of_complexity_le _
      (cost := fun N => 2 ^ c * N ^ (c + 1) * (2 ^ c * N ^ c) +
        (2 + 2 ^ c * N ^ (c + 1) * (2 * (2 ^ c * N ^ (c + 1) + 2))) + 1)
      (by fun_prop) fun n => ?_
    have he : 2 ^ (c * (n + 1)) = 2 ^ c * (2 ^ n) ^ c := by
      rw [mul_add, mul_one, pow_add, mul_comm (2 ^ (c * n)), mul_comm c n, pow_mul]
    have hM : Fintype.card (Ω n) * 2 ^ n ≤ 2 ^ c * (2 ^ n) ^ (c + 1) := by
      rw [pow_succ, ← mul_assoc, ← he]
      exact Nat.mul_le_mul_right _ (hΩ n)
    have ht' : t n ≤ 2 ^ c * (2 ^ n) ^ c := he ▸ ht n
    refine (complexity_truthTableTest_lowAgreement_le (hA n).isCircuitTest _).trans ?_
    gcongr

/-- **Learners yield natural properties** [OliveiraSanthanam2017, Theorem 8]. Let `A n` have
circuit tests of size `t n ≤ 2 ^ (c (n + 1))` with `q n` queries and uniform seeds from a set of
size at most `2 ^ (c (n + 1))`. Suppose that for all large `n` it learns the functions with
circuits of at most `s n` gates with error `ε n ∈ [0, 1]` and confidence `1 - δ n ≤ 1`, with
accuracy `(1 - δ n) (1 - ε n)` at least `2 ^ (-c n)` above `1 / 2 + q n / 2 ^ (n + 1)`. Then the
low-agreement property is `P/poly`-natural and useful against `SIZE s`. -/
theorem isNatural_PPoly_and_isUseful_SIZE {A : ∀ n, QueryLearner (Fin n) (Ω n)} {q t s : ℕ → ℕ}
    {ε δ : ℕ → ℝ} {c : ℕ} (hΩ : ∀ n, Fintype.card (Ω n) ≤ 2 ^ (c * (n + 1)))
    (ht : ∀ n, t n ≤ 2 ^ (c * (n + 1))) (hA : ∀ n, (A n).HasCircuitTests (q n) (t n))
    (hL : ∀ᶠ n in atTop, (A n).Learns (Cslib.Probability.PMF.uniformOfFintype (Ω n))
      {f | complexity interpretation (single f) ≤ s n} (ε n) (δ n))
    (hε : ∀ n, 0 ≤ ε n ∧ ε n ≤ 1) (hδ : ∀ n, 0 ≤ δ n)
    (hgap : ∀ᶠ n in atTop,
      ((2 : ℝ) ^ (c * n))⁻¹ ≤ (1 - δ n) * (1 - ε n) - (1 / 2 + q n / 2 ^ (n + 1))) :
    IsNatural PPoly (fun n => (A n).lowAgreement ((1 - δ n) * (1 - ε n))) ∧
      IsUseful (SIZE s) fun n => (A n).lowAgreement ((1 - δ n) * (1 - ε n)) :=
  ⟨isNatural_PPoly_lowAgreement hΩ ht hA hε hδ hgap,
    isUseful_lowAgreement hL (fun n => (hε n).2) hδ fun _ hL' => Eventually.of_forall hL'⟩

end Cslib.MachineLearning.UniformLearning
