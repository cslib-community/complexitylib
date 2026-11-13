/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRG.Circuit
public import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness
public import CslibFrontier.MachineLearning.UniformLearning.NonadaptiveCircuit
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Circuit.Boolean.Synthesis
import CslibFrontier.Computability.Circuit.Complexity
import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Sampling
import CslibFrontier.Foundations.Data.Finset.Density
import Cslib.Crypto.Primitives.PRG.Basic

/-!
# Learners with small circuits break pseudorandom functions against circuits

A keyed family `F` of Boolean functions on `n` bits is pseudorandom against circuits when no small
circuit reading the whole truth table distinguishes the truth table of `F key`, for a uniformly
random key, from a uniformly random truth table
(`Cslib.Crypto.PRG.truthTableGenerator`, `Cslib.Crypto.PRG.IsCircuitTest`). A membership-query
learner with `q` non-adaptive queries and a circuit of `S` gates
(`UniformLearning.QueryLearner.HasCircuit`) that learns a class containing every member of `F` is
such a circuit: fix its seed and a comparison point, read its queries from the truth table, and
compare its hypothesis with the truth table at the point
(`UniformLearning.QueryLearner.HasCircuit.isCircuitTest_agrees`, at most `S + 7` gates). Hence the
security of `F` bounds the accuracy of every such learner
(`UniformLearning.QueryLearner.Learns.le_of_secure`): if `F` resists circuits with `S + 7` gates
with advantage `η`, a learner with error `ε` and confidence `1 - δ` satisfies
`(1 - δ) (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + η`. For an exponentially secure family
(`Cslib.Crypto.PRG.IsExponentiallySecure`) this holds, for every `c`, for all large `n`, every
learner with `S + 7 ≤ 2 ^ (c n)` and `η = 2 ^ (-c n)`
(`UniformLearning.eventually_le_of_isExponentiallySecure`). This is the argument of
[Valiant1984] (locator unverified) for the nonuniform circuit model of
[RazborovRudich1997, Section 4]; the GGM instance is
`CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.GGM`.

The model differs from the classical statement as follows.
* **Circuit learners.** The learner is a circuit with non-adaptive queries on each seed, as in
  `UniformLearning.QueryLearner.HasCircuit`; its running time is not modelled. Adaptive learners
  are covered only by the information-theoretic bound of
  `UniformLearning.QueryLearner.exists_dens_agrees_sub_dens_agrees`.
* **Fixed seed and point.** The test fixes the learner's seed and the comparison point by
  averaging; it is the nonuniform test of the circuit model, not a uniform algorithm.

## Main results

* `Cslib.MachineLearning.UniformLearning.QueryLearner.HasCircuit.isCircuitTest_agrees`: the test of
  a learner with a circuit of `S` gates is a circuit of `S + 7` gates on truth tables.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.Learns.le_of_secure`: **a secure family
  bounds the accuracy of learners with small circuits**.
* `Cslib.MachineLearning.UniformLearning.eventually_le_of_isExponentiallySecure`: the asymptotic
  form for exponentially secure families.

## References

* [L. G. Valiant, *A theory of the learnable*][Valiant1984]
* [A. A. Razborov, S. Rudich, *Natural proofs*][RazborovRudich1997]
-/

public section

universe u

namespace Cslib.MachineLearning.UniformLearning

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.MCSP Cslib.Crypto.PRG Filter Finset PACLearning
open scoped NNReal

namespace QueryLearner

variable {n : ℕ} {Ω : Type*} {A : QueryLearner (Fin n) Ω} {q S : ℕ}

/-- A learner with a circuit has the hypotheses of a non-adaptive learner with at most `q`
queries: query the points of the circuit, then evaluate it. -/
private theorem HasCircuit.exists_queriesAtMost (hA : A.HasCircuit q S) :
    ∃ B : QueryLearner (Fin n) Ω, B.QueriesAtMost q ∧ ∀ ω f, (B ω).eval f = (A ω).eval f := by
  choose pts F _ hev using hA
  have hhyp (ω : Ω) (g g' : BooleanFunction n) (h : ∀ x ∈ List.ofFn (pts ω), g x = g' x) :
      (fun x => F ω (Fin.append (fun i => g (pts ω i)) x)) =
        fun x => F ω (Fin.append (fun i => g' (pts ω i)) x) := by
    funext x
    congr 2
    funext i
    exact h _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  refine ⟨ofNonadaptive (fun ω => List.ofFn (pts ω))
    (fun g ω x => F ω (Fin.append (fun i => g (pts ω i)) x)), fun ω => ?_, fun ω f => ?_⟩
  · exact (depth_ofNonadaptive_le _ _ ω).trans (by simp)
  · rw [eval_ofNonadaptive hhyp]
    funext x
    exact (hev ω f x).symm

/-- **The test of a learner with a circuit is a small circuit on truth tables.** If `A` has a
circuit with at most `S` gates, then for every seed `ω` and point `z` the test `A.agrees ω z`, read
on truth tables, is computed with at most `S + 7` gates: two constants for the queried values that
the substitution fixes, and five gates comparing the hypothesis with the truth table at `z`. -/
theorem HasCircuit.isCircuitTest_agrees (hA : A.HasCircuit q S) (ω : Ω) (z : BitString n) :
    IsCircuitTest (S + 7) fun T : BitString (2 ^ n) =>
      PMF.pure (A.agrees ω z ((truthTable n).symm T)) := by
  obtain ⟨pts, F, hF, hev⟩ := hA ω
  -- read the queries from the truth table and fix the point `z`
  let ρ : Fin (q + n) → Fin (2 ^ n) ⊕ Bool :=
    Fin.append (fun i => .inl (BitString.equivFin n (pts i))) fun i => .inr (z i)
  have hρ (T : BitString (2 ^ n)) :
      substitute ρ T = Fin.append (fun i => (truthTable n).symm T (pts i)) z := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [ρ, substitute]
  refine ⟨fun T => !(F (substitute ρ T) ^^ T (BitString.equivFin n z)), ?_, ?_⟩
  · calc complexity interpretation
          (single fun T => !(F (substitute ρ T) ^^ T (BitString.equivFin n z)))
        ≤ complexity interpretation
            (single fun T => F (substitute ρ T) ^^ T (BitString.equivFin n z)) + 1 :=
          complexity_not_le _
      _ ≤ complexity interpretation (single fun T => F (substitute ρ T)) +
            complexity interpretation
              (single fun T : BitString (2 ^ n) => T (BitString.equivFin n z)) + 4 + 1 :=
          Nat.add_le_add_right (complexity_xor_le _ _) 1
      _ ≤ S + 2 + 0 + 4 + 1 := by
          gcongr
          · exact (complexity_substitute_le ρ F).trans (Nat.add_le_add_right hF 2)
          · exact (complexity_single_proj _).le
      _ = S + 7 := by ring
  · funext T
    congr 1
    beta_reduce
    rw [hρ, ← hev ((truthTable n).symm T) z, Bool.eq_iff_iff, agrees_eq_true_iff,
      truthTable_symm_apply]
    cases (A ω).eval ((truthTable n).symm T) z <;> cases T (BitString.equivFin n z) <;> simp

variable {Key : Type*} [Fintype Key] [Nonempty Key]

/-- **A secure family bounds the accuracy of learners with small circuits** [Valiant1984] (locator
unverified). Let `A` have `q` non-adaptive queries and a circuit with at most `S`
gates, and learn, with error `ε ≤ 1` and confidence `1 - δ`, a class containing every member of
the keyed family `F` of Boolean functions on `n` bits. If no test computed with `S + 7` gates
distinguishes the truth table of `F key`, for a uniform key, from a uniform truth table with
advantage more than `η`, then `(1 - δ) (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + η`. -/
theorem Learns.le_of_secure {μ : PMF Ω} {C : ConceptClass (BitString n) Bool} {ε δ : ℝ}
    {F : Key → BooleanFunction n} {η : ℝ≥0} (hL : A.Learns μ C ε δ) (hA : A.HasCircuit q S)
    (hF : ∀ key, F key ∈ C) (hG : (truthTableGenerator F).Secure (IsCircuitTest (S + 7)) η)
    (hε : ε ≤ 1) (hδ : 0 ≤ δ) :
    (1 - δ) * (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + η := by
  obtain ⟨B, hBq, hB⟩ := hA.exists_queriesAtMost
  have hLB : B.Learns μ C ε δ := by
    rw [learns_iff] at hL ⊢
    simpa only [hB] using hL
  have hagree (ω : Ω) (z : BitString n) (g : BooleanFunction n) :
      B.agrees ω z g = A.agrees ω z g := by
    rw [Bool.eq_iff_iff, agrees_eq_true_iff, agrees_eq_true_iff, hB]
  obtain ⟨ω, -, z, hz⟩ := exists_dens_agrees_sub_dens_agrees hLB hBq hF hε hδ
  simp only [hagree, Fintype.card_fin] at hz
  have hadv := hG _ (hA.isCircuitTest_agrees ω z)
  rw [Generator.advantage, Generator.toReal_realExperiment_pure,
    Generator.toReal_idealExperiment_pure,
    Fintype.dens_filter_comp_equiv (truthTable n).symm fun g => A.agrees ω z g = true] at hadv
  simp only [truthTableGenerator_apply, Equiv.symm_apply_apply] at hadv
  linarith [le_abs_self ((dens {key | A.agrees ω z (F key) = true} : ℝ) -
    dens {g : BooleanFunction n | A.agrees ω z g = true})]

end QueryLearner

/-- **Exponentially secure families defeat learners with small circuits.** Let `F` be an
exponentially secure keyed family. For every `c`, for all large `n`, every learner with `q`
non-adaptive queries and a circuit with `S` gates, `S + 7 ≤ 2 ^ (c n)`, that learns a class
containing every member of `F n` with error `ε ≤ 1` and confidence `1 - δ` satisfies
`(1 - δ) (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + 2 ^ (-c n)`. -/
theorem eventually_le_of_isExponentiallySecure {Key : ℕ → Type*} [∀ n, Fintype (Key n)]
    [∀ n, Nonempty (Key n)] {F : ∀ n, Key n → BooleanFunction n} (hF : IsExponentiallySecure F)
    (c : ℕ) :
    ∀ᶠ n in atTop, ∀ {Ω : Type u} (A : QueryLearner (Fin n) Ω) (μ : PMF Ω)
      (C : ConceptClass (BitString n) Bool) (ε δ : ℝ) (q S : ℕ), A.HasCircuit q S →
      S + 7 ≤ 2 ^ (c * n) → A.Learns μ C ε δ → (∀ key, F n key ∈ C) → ε ≤ 1 → 0 ≤ δ →
      (1 - δ) * (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + ((2 : ℝ) ^ (c * n))⁻¹ := by
  filter_upwards [hF c] with n hn
  intro Ω A μ C ε δ q S hA hS hL hFC hε hδ
  have h := hL.le_of_secure hA hFC
    (Generator.Secure.of_admissible hn fun _ ⟨test, htest, h⟩ => ⟨test, htest.trans hS, h⟩) hε hδ
  push_cast at h
  exact h

end Cslib.MachineLearning.UniformLearning
