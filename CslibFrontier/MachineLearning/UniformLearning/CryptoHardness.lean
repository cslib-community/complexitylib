/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.UniformLearning.MembershipQuery
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.Minimax
import CslibFrontier.Probability.PMF.Uniform

/-!
# Learners distinguish pseudorandom functions from random functions

A membership-query learner for a class that contains every member of a keyed family `F` of Boolean
functions is a distinguisher for `F`: run the learner on the unknown function and compare its
hypothesis with the function at a fresh uniform point [Valiant1984], [GGM1986] (locators
unverified). On a member of the family, the learner is accurate with error `ε` except with
probability `δ`, so the comparison succeeds with probability at least `(1 - δ) (1 - ε)`. On a
uniformly random function, the value at a point the learner did not query is a fair coin
independent of everything the learner saw, so the comparison succeeds with probability at most
`1 / 2 + q / 2 ^ (N + 1)` for a learner making at most `q` queries on a cube of `N` coordinates.
This is the converse of learning from natural proofs: efficient learners for a class rule out
pseudorandom functions in it.

The statements fix the learner's seed `ω` and the comparison point `z`, which turns the test into a
deterministic function of the oracle (`UniformLearning.QueryLearner.agrees A ω z`). The theorem
`UniformLearning.QueryLearner.exists_dens_agrees_sub_dens_agrees` finds `ω` and `z` for which the
fraction of keys on which the test accepts exceeds the fraction of all functions on which it accepts
by at least `(1 - δ) (1 - ε) - 1 / 2 - q / 2 ^ (N + 1)`. Fixing them is the averaging step that
makes the test a small circuit when the learner is one
(`CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.Circuit`); the instance for the GGM
functions is `CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.GGM`. The statements
apply to adaptive learners. The randomized test that draws `ω` and `z` is not formalized.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.QueryLearner.agrees`: the test that runs the learner with
  a fixed seed and compares its hypothesis with the oracle at a fixed point.

## Main results

* `Cslib.MachineLearning.UniformLearning.QueryLearner.expect_dens_agrees_le`: **an unqueried point
  is a fair coin**. Against a uniformly random function and a uniform point, the learner with any
  seed agrees with the function with probability at most `1 / 2 + q / 2 ^ (N + 1)`.
* `Cslib.MachineLearning.UniformLearning.le_expect_dens_eq`: hypotheses with error at most `ε`
  except on a `δ` fraction of the indices agree with their targets with probability at least
  `(1 - δ) (1 - ε)`.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.exists_le_expect_dens_agrees`: some seed
  makes the test accept the members of the family with probability at least `(1 - δ) (1 - ε)`.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.exists_dens_agrees_sub_dens_agrees`:
  **learners distinguish pseudorandom functions**, with advantage at least
  `(1 - δ) (1 - ε) - 1 / 2 - q / 2 ^ (N + 1)`.

## References

* [L. G. Valiant, *A theory of the learnable*][Valiant1984]
* [O. Goldreich, S. Goldwasser, S. Micali, *How to construct random functions*][GGM1986]
-/

public section

namespace Cslib.MachineLearning.UniformLearning.QueryLearner

open Finset
open scoped BigOperators

variable {ι Ω : Type*}

/-- The test built from the learner `A` with the seed `ω` and the point `z`: run `A` on the oracle
`g`, and accept when its hypothesis agrees with `g` at `z`. -/
def agrees (A : QueryLearner ι Ω) (ω : Ω) (z : ι → Bool) (g : (ι → Bool) → Bool) : Bool :=
  decide ((A ω).eval g z = g z)

@[simp] theorem agrees_eq_true_iff {A : QueryLearner ι Ω} {ω : Ω} {z : ι → Bool}
    {g : (ι → Bool) → Bool} : A.agrees ω z g = true ↔ (A ω).eval g z = g z :=
  decide_eq_true_iff

variable [Fintype ι] [DecidableEq ι]

/-- The oracle `g` with its value at `z` flipped. -/
private def flipAt (z : ι → Bool) (g : (ι → Bool) → Bool) : (ι → Bool) → Bool :=
  Function.update g z (!g z)

omit [DecidableEq ι] in
private theorem flipAt_involutive (z : ι → Bool) : Function.Involutive (flipAt z) := fun g => by
  funext x
  by_cases hx : x = z
  · subst hx
    simp [flipAt]
  · simp [flipAt, hx]

/-- **An unqueried point is a fair coin.** Let `A` make at most `q` queries. For every seed, the
hypothesis of `A` on a uniformly random function agrees with the function at a uniform point with
probability at most `1 / 2 + q / 2 ^ (N + 1)`, where `N` is the number of coordinates. Flipping the
value of the function at a point `z` that `A` did not query leaves the hypothesis unchanged and
negates the value at `z`, so exactly one of the two functions is accepted. -/
theorem expect_dens_agrees_le {A : QueryLearner ι Ω} {q : ℕ} (hA : A.QueriesAtMost q) (ω : Ω) :
    𝔼 z, (dens {g | A.agrees ω z g = true} : ℝ) ≤ 1 / 2 + q / 2 ^ (Fintype.card ι + 1) := by
  -- the indicator of acceptance, and that of `z` being queried
  let acc : (ι → Bool) → ((ι → Bool) → Bool) → ℝ := fun z g =>
    if (A ω).eval g z = g z then 1 else 0
  let hit : (ι → Bool) → ((ι → Bool) → Bool) → ℝ := fun z g =>
    if z ∈ (A ω).queries g then 1 else 0
  -- flipping the value at `z` preserves the uniform average
  have hflip (z : ι → Bool) : 𝔼 g, acc z g = 𝔼 g, acc z (flipAt z g) :=
    Fintype.expect_equiv (Function.Involutive.toPerm _ (flipAt_involutive z)) _ _
      fun g => by
        simp only [Function.Involutive.coe_toPerm]
        rw [flipAt_involutive z g]
  -- pointwise, the two acceptances sum to at most `1` plus the indicator of a query at `z`
  have hpair (z : ι → Bool) (g : (ι → Bool) → Bool) :
      acc z g + acc z (flipAt z g) ≤ 1 + hit z g := by
    by_cases hz : z ∈ (A ω).queries g
    · simp only [acc, hit, hz, ↓reduceIte]
      split_ifs <;> norm_num
    · have heval : (A ω).eval (flipAt z g) = (A ω).eval g :=
        (A ω).eval_eq_of_forall_mem_queries fun x hx => by
          have hxz : x ≠ z := fun h => hz (h ▸ hx)
          simp [flipAt, hxz]
      have hval : flipAt z g z = !g z := by simp [flipAt]
      simp only [acc, hit, hz, ↓reduceIte, heval, hval]
      cases (A ω).eval g z <;> cases g z <;> norm_num
  have hz (z : ι → Bool) : 𝔼 g, acc z g ≤ 1 / 2 + (𝔼 g, hit z g) / 2 := by
    have h2 : 2 * 𝔼 g, acc z g ≤ 1 + 𝔼 g, hit z g := by
      calc 2 * 𝔼 g, acc z g = 𝔼 g, (acc z g + acc z (flipAt z g)) := by
            rw [expect_add_distrib, ← hflip, two_mul]
        _ ≤ 𝔼 g, (1 + hit z g) := expect_le_expect fun g _ => hpair z g
        _ = 1 + 𝔼 g, hit z g := by rw [expect_add_distrib, Fintype.expect_const]
    linarith
  -- a query hits a uniform point with probability at most `q / 2 ^ N`
  have hhit : 𝔼 z, 𝔼 g, hit z g ≤ q / 2 ^ Fintype.card ι := by
    rw [expect_comm]
    refine expect_le (univ_nonempty) fun g _ => ?_
    rw [Fintype.expect_boole_mem]
    rw [Finset.dens, Fintype.card_fun, Fintype.card_bool]
    push_cast
    gcongr
    exact_mod_cast ((A ω).card_queries_le_depth g).trans (hA ω)
  calc 𝔼 z, (dens {g | A.agrees ω z g = true} : ℝ) = 𝔼 z, 𝔼 g, acc z g := by
        refine expect_congr rfl fun z _ => ?_
        rw [← Fintype.expect_boole]
        simp only [agrees_eq_true_iff, acc]
    _ ≤ 𝔼 z, (1 / 2 + (𝔼 g, hit z g) / 2) := expect_le_expect fun z _ => hz z
    _ = 1 / 2 + (𝔼 z, 𝔼 g, hit z g) / 2 := by
        rw [expect_add_distrib, Fintype.expect_const, ← expect_div]
    _ ≤ 1 / 2 + (q / 2 ^ Fintype.card ι) / 2 := by gcongr
    _ = 1 / 2 + q / 2 ^ (Fintype.card ι + 1) := by rw [pow_succ]; ring

/-- **Accurate hypotheses agree on average.** Let `K` be a finite index set, and for each `k` let
`h k` be a hypothesis for the target `F k`. If at most a `δ` fraction of the indices have error
above `ε ≤ 1`, then `h k` and `F k` agree at a uniform point with probability at least
`(1 - δ) (1 - ε)`, over a uniform index and point: an accurate hypothesis agrees on at least a
`1 - ε` fraction of the points. -/
theorem _root_.Cslib.MachineLearning.UniformLearning.le_expect_dens_eq {K : Type*} [Fintype K]
    [Nonempty K] (F h : K → (ι → Bool) → Bool) {ε δ : ℝ} (hε : ε ≤ 1)
    (hbad : (dens {k | ε < uniformError (F k) (h k)} : ℝ) ≤ δ) :
    (1 - δ) * (1 - ε) ≤ 𝔼 k, (dens {z | h k z = F k z} : ℝ) := by
  -- the agreement of an index is one minus the error of its hypothesis
  have hk (k : K) : (1 - ε) * (1 - if ε < uniformError (F k) (h k) then 1 else 0) ≤
      (dens {z | h k z = F k z} : ℝ) := by
    have herr := uniformError_eq_one_sub_dens (F k) (h k)
    split_ifs with hlt
    · rw [sub_self, mul_zero]
      positivity
    · rw [sub_zero, mul_one]
      linarith [not_lt.1 hlt]
  calc (1 - δ) * (1 - ε)
      ≤ (1 - ε) * (1 - dens {k | ε < uniformError (F k) (h k)}) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hε) (sub_nonneg.2 hbad)]
    _ = 𝔼 k, (1 - ε) * (1 - if ε < uniformError (F k) (h k) then 1 else 0) := by
        rw [← mul_expect, expect_sub_distrib, Fintype.expect_const, Fintype.expect_boole]
    _ ≤ 𝔼 k, (dens {z | h k z = F k z} : ℝ) := expect_le_expect fun k _ => hk k

variable {Key : Type*} [Fintype Key] [Nonempty Key]

/-- **The learner is accurate on the family.** Let `A` learn, with error `ε` and confidence
`1 - δ`, a class containing every member of the keyed family `F`. Then some seed makes `A` agree
with a member of the family at a uniform point with probability at least `(1 - δ) (1 - ε)`, over a
uniform key and point. -/
theorem exists_le_expect_dens_agrees {A : QueryLearner ι Ω} {μ : PMF Ω}
    {C : PACLearning.ConceptClass (ι → Bool) Bool} {ε δ : ℝ} (hA : A.Learns μ C ε δ)
    {F : Key → (ι → Bool) → Bool} (hF : ∀ key, F key ∈ C) (hε : ε ≤ 1) (hδ : 0 ≤ δ) :
    ∃ ω ∈ μ.support, (1 - δ) * (1 - ε) ≤ 𝔼 z, (dens {key | A.agrees ω z (F key) = true} : ℝ) := by
  -- some seed fails on at most a `δ` fraction of the keys
  obtain ⟨ω, hω, hbad⟩ := Cslib.Probability.PMF.exists_mem_support_toOuterMeasure_le μ
    (Cslib.Probability.PMF.uniformOfFintype Key)
    (fun ω key => ε < uniformError (F key) ((A ω).eval (F key))) (ε := δ) fun key _ => by
      refine ENNReal.toReal_le_of_le_ofReal hδ ?_
      exact learns_iff.1 hA (F key) (hF key)
  refine ⟨ω, hω, ?_⟩
  rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal] at hbad
  have hbad' : (dens {key | ε < uniformError (F key) ((A ω).eval (F key))} : ℝ) ≤ δ := by
    rw [Finset.nnratCast_dens]
    exact hbad
  refine (le_expect_dens_eq F (fun key => (A ω).eval (F key)) hε hbad').trans_eq ?_
  -- exchange the averages over keys and points
  simp only [← Fintype.expect_boole]
  rw [expect_comm]
  simp only [agrees_eq_true_iff]

/-- **Learners distinguish pseudorandom functions from random functions** [Valiant1984].
Let `A` make at most `q` queries and learn, with error `ε ≤ 1` and confidence `1 - δ`, a class
containing every member of the keyed family `F` of Boolean functions on `N` coordinates. Then for
some seed `ω` and point `z`, the test `A.agrees ω z` accepts the member of a uniformly random key
more often than a uniformly random function by at least
`(1 - δ) (1 - ε) - 1 / 2 - q / 2 ^ (N + 1)`. -/
theorem exists_dens_agrees_sub_dens_agrees {A : QueryLearner ι Ω} {μ : PMF Ω}
    {C : PACLearning.ConceptClass (ι → Bool) Bool} {ε δ : ℝ} {q : ℕ} (hA : A.Learns μ C ε δ)
    (hq : A.QueriesAtMost q) {F : Key → (ι → Bool) → Bool} (hF : ∀ key, F key ∈ C) (hε : ε ≤ 1)
    (hδ : 0 ≤ δ) :
    ∃ ω ∈ μ.support, ∃ z, (1 - δ) * (1 - ε) - 1 / 2 - q / 2 ^ (Fintype.card ι + 1) ≤
      (dens {key | A.agrees ω z (F key) = true} : ℝ) - dens {g | A.agrees ω z g = true} := by
  obtain ⟨ω, hω, hreal⟩ := exists_le_expect_dens_agrees hA hF hε hδ
  have hideal := expect_dens_agrees_le hq ω
  obtain ⟨z, -, hz⟩ := exists_le_of_le_expect (s := univ) univ_nonempty
    (f := fun z => (dens {key | A.agrees ω z (F key) = true} : ℝ) -
      dens {g | A.agrees ω z g = true})
    (a := (1 - δ) * (1 - ε) - 1 / 2 - q / 2 ^ (Fintype.card ι + 1)) (by
      rw [expect_sub_distrib]
      linarith)
  exact ⟨ω, hω, z, hz⟩

end Cslib.MachineLearning.UniformLearning.QueryLearner
