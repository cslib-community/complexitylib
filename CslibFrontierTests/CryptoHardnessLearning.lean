/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.GGM
import CslibFrontier.Computability.Circuit.Boolean.Substitution

/-!
# Tests: learners distinguish pseudorandom functions

A toy learner on `n + 1` bits that makes no queries and outputs the dictator `x ↦ x 0`. It learns
the class `{x ↦ x 0}` exactly, with one seed. Its test therefore distinguishes the family whose
only member is the dictator from a uniformly random function with advantage at least `1 / 2`, and
the family is not `1 / 4`-secure against circuits with seven gates: the reduction has teeth.

An adaptive learner on `n + 1` bits asks `0` first and then the point all of whose bits are the
first answer, and outputs the constant of the second answer. Its queries are substitutions of two
gates each and its hypothesis a projection, so it has adaptive circuits of four gates and circuit
tests through the truth-table reading of its answers.

The asymptotic theorem is instantiated at error and failure probability `1 / 10`, for adaptive and
for non-adaptive learners; its hypotheses, a subexponentially secure generator, are cryptographic
assumptions and stay hypotheses.
-/

namespace CslibFrontierTests.CryptoHardnessLearning

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto Cslib.Crypto.PRG
  Cslib.MachineLearning.UniformLearning Filter

variable {n : ℕ}

/-- The dictator on the first bit. -/
private def dictator : BooleanFunction (n + 1) := fun x => x 0

/-- Make no queries and output the dictator. -/
private noncomputable def dictatorLearner : QueryLearner (Fin (n + 1)) Unit :=
  QueryLearner.ofNonadaptive (fun _ => []) fun _ _ => dictator

private theorem eval_dictatorLearner (f : BooleanFunction (n + 1)) :
    (dictatorLearner ()).eval f = dictator :=
  QueryLearner.eval_ofNonadaptive (fun _ _ _ _ => rfl) f ()

private theorem queriesAtMost_dictatorLearner : (dictatorLearner (n := n)).QueriesAtMost 0 :=
  fun ω => QueryLearner.depth_ofNonadaptive_le _ _ ω

/-- The toy learner has no queries and a circuit with no gates: a projection. -/
private theorem hasCircuit_dictatorLearner : (dictatorLearner (n := n)).HasCircuit 0 0 :=
  QueryLearner.hasCircuit_ofNonadaptive (fun _ _ _ _ => rfl)
    fun _ => ⟨Fin.elim0, fun z => z (Fin.natAdd 0 0),
      le_of_eq (complexity_wiring (I := interpretation) fun _ => Fin.natAdd 0 0),
      fun _ x => (Fin.append_right _ x 0).symm⟩

/-- The toy learner learns the dictator exactly, with probability one. -/
private theorem learns_dictatorLearner :
    (dictatorLearner (n := n)).Learns (PMF.pure ()) {dictator} 0 0 := by
  rw [QueryLearner.learns_iff]
  rintro f rfl
  simp [eval_dictatorLearner]

/-- **The information-theoretic reduction.** The test accepts the dictator, so it accepts at most
half of all functions at some point: the advantage is at least `1 / 2`. -/
example : ∃ z : BitString (n + 1),
    (Finset.dens {g | (dictatorLearner (n := n)).agrees () z g = true} : ℝ) ≤ 1 / 2 := by
  obtain ⟨⟨⟩, -, z, hz⟩ := QueryLearner.exists_dens_agrees_sub_dens_agrees
    learns_dictatorLearner queriesAtMost_dictatorLearner (F := fun _ : Unit => dictator)
    (fun _ => rfl) zero_le_one le_rfl
  have h1 : (dictatorLearner (n := n)).agrees () z dictator = true := by
    rw [QueryLearner.agrees_eq_true_iff, eval_dictatorLearner]
  simp only [h1, Finset.filter_true, Finset.dens_univ, NNRat.cast_one, CharP.cast_eq_zero,
    zero_div, sub_zero, mul_one] at hz
  exact ⟨z, by linarith⟩

/-- **The reduction has teeth.** The family whose only member is the dictator is learnable, so it
is not `1 / 4`-secure against circuits with seven gates on truth tables. -/
example : ¬ (truthTableGenerator fun _ : Unit => (dictator : BooleanFunction (n + 1))).Secure
    (IsCircuitTest 7) (1 / 4) := by
  intro hG
  have h := learns_dictatorLearner.le_of_secure hasCircuit_dictatorLearner.hasCircuitTests
    (fun _ => rfl) hG zero_le_one le_rfl
  norm_num at h

/-- The sources of the adaptive queries: the second query reads the first answer at every bit,
the first is the point `0`. -/
private def adaptiveSource (i : Fin 2) (_ : Fin (n + 1)) : Fin i ⊕ Bool :=
  if h : (i : ℕ) = 1 then .inl ⟨0, by omega⟩ else .inr false

/-- The adaptive queries, as substitutions. -/
private def adaptiveQueries (i : Fin 2) : BitString i → BitString (n + 1) :=
  substitute (adaptiveSource i)

/-- Ask `0`, then the point all of whose bits are the first answer, and output the constant of the
second answer. -/
private noncomputable def adaptiveLearner : QueryLearner (Fin (n + 1)) Unit :=
  QueryLearner.ofAdaptive (fun _ => adaptiveQueries) fun _ a _ => a 1

/-- The adaptive learner outputs the constant `f (fun _ => f 0)`: its second query depends on its
first answer. -/
example (f : BooleanFunction (n + 1)) :
    (adaptiveLearner ()).eval f = fun _ => f fun _ => f 0 := by
  rw [adaptiveLearner, QueryLearner.eval_ofAdaptive]
  rfl

/-- The adaptive learner has adaptive circuits of four gates: two constants for each query and a
projection for the hypothesis. -/
private theorem hasAdaptiveCircuit_adaptiveLearner :
    (adaptiveLearner (n := n)).HasAdaptiveCircuit 2 4 := fun _ =>
  ⟨adaptiveQueries, fun a => a (Fin.castAdd (n + 1) 1),
    by
      have h := complexity_wiring (I := interpretation)
        fun _ : Fin 1 => (Fin.castAdd (n + 1) 1 : Fin (2 + (n + 1)))
      rw [Fin.sum_univ_two]
      exact Nat.add_le_add (Nat.add_le_add (complexity_substitute_le_two _)
        (complexity_substitute_le_two _)) h.le,
    fun f x => by
      rw [adaptiveLearner, QueryLearner.eval_ofAdaptive]
      exact (Fin.append_left _ x 1).symm⟩

/-- The tests of the adaptive learner are circuits on truth tables: reading its two answers costs
`2 (2 ^ (n + 1) (2 n + 5) + 1)` gates. -/
example : (adaptiveLearner (n := n)).HasCircuitTests 2
    (4 + 2 * (2 ^ (n + 1) * (2 * (n + 1) + 3) + 1) + 7) :=
  hasAdaptiveCircuit_adaptiveLearner.hasCircuitTests

/-- **Polynomial-size circuits are not learnable at error `1 / 10`.** From a subexponentially
secure family of generators of polynomial circuit complexity: for every `c`, for all large `n`, no
learner with at most `2 ^ (n - 1)` adaptive queries and circuits with `2 ^ (c n)` gates in all
learns the functions of circuit size `s n` with error and failure probability `1 / 10`. -/
example {G : ∀ k, PRG.Generator (BitString k) (BitString (2 * k))} {d : ℕ}
    (hsize : PolynomiallyBounded fun k => complexity interpretation ⇑(G k))
    (hG : PRG.IsSubexponentiallySecure G d) :
    ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ c : ℕ, ∀ᶠ n in atTop,
      ∀ (A : QueryLearner (Fin n) ℕ) (μ : PMF ℕ) (q S : ℕ), A.HasAdaptiveCircuit q S →
        2 * q ≤ 2 ^ n → S ≤ 2 ^ (c * n) →
        ¬ A.Learns μ {f | complexity interpretation (single f) ≤ s n} (1 / 10) (1 / 10) := by
  obtain ⟨s, hs, h⟩ := exists_eventually_not_learns_of_isSubexponentiallySecure.{0} hsize hG
  exact ⟨s, hs, fun c => (h c (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)).mono
    fun n hn A μ q S => hn A μ q S⟩

/-- **The non-adaptive case.** Learners with non-adaptive queries and a circuit of `S` gates have
adaptive circuits of `S + 2 q` gates, so they are covered too. -/
example {G : ∀ k, PRG.Generator (BitString k) (BitString (2 * k))} {d : ℕ}
    (hsize : PolynomiallyBounded fun k => complexity interpretation ⇑(G k))
    (hG : PRG.IsSubexponentiallySecure G d) :
    ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ c : ℕ, ∀ᶠ n in atTop,
      ∀ (A : QueryLearner (Fin n) ℕ) (μ : PMF ℕ) (q S : ℕ), A.HasCircuit q S →
        2 * q ≤ 2 ^ n → S + 2 * q ≤ 2 ^ (c * n) →
        ¬ A.Learns μ {f | complexity interpretation (single f) ≤ s n} (1 / 10) (1 / 10) := by
  obtain ⟨s, hs, h⟩ := exists_eventually_not_learns_of_isSubexponentiallySecure.{0} hsize hG
  exact ⟨s, hs, fun c => (h c (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)).mono
    fun n hn A μ q S hA => hn A μ q _ hA.hasAdaptiveCircuit⟩

end CslibFrontierTests.CryptoHardnessLearning
