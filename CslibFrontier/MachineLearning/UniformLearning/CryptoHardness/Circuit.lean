/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRG.Circuit
public import CslibFrontier.MachineLearning.UniformLearning.AdaptiveCircuit
public import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness
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
learner *has circuit tests* of size `t` with `q` queries
(`UniformLearning.QueryLearner.HasCircuitTests`) when it agrees with a learner making at most `q`
queries and, for every seed and comparison point, its test (run the learner on the truth table and
compare its hypothesis with the table at the point) is computed by a circuit of at most `t` gates on
truth tables. Learners with circuits have circuit tests:
* with `q` non-adaptive queries and a circuit of `S` gates
  (`UniformLearning.QueryLearner.HasCircuit`), of size `S + 7`
  (`UniformLearning.QueryLearner.HasCircuit.isCircuitTest_agrees`,
  `UniformLearning.QueryLearner.HasCircuit.hasCircuitTests`);
* with `q` adaptive queries and circuits of `S` gates in all
  (`UniformLearning.QueryLearner.HasAdaptiveCircuit`), of size
  `S + q (2 ^ n (2 n + 3) + 1) + 7`, each query reading its answer from the table at the address
  its circuit computes (`UniformLearning.QueryLearner.HasAdaptiveCircuit.isCircuitTest_agrees`,
  `UniformLearning.QueryLearner.HasAdaptiveCircuit.hasCircuitTests`).

Hence the security of `F` bounds the accuracy of every learner with circuit tests that learns a
class containing every member of `F` (`UniformLearning.QueryLearner.Learns.le_of_secure`): if `F`
resists circuits with `t` gates with advantage `η`, a learner with error `ε` and confidence
`1 - δ` satisfies `(1 - δ) (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + η`. For an exponentially secure
family (`Cslib.Crypto.PRG.IsExponentiallySecure`) this holds, for every `c`, for all large `n`,
every learner with `t ≤ 2 ^ (c n)` and `η = 2 ^ (-c n)`
(`UniformLearning.eventually_le_of_isExponentiallySecure`). This is the argument of
[Valiant1984] (locator unverified) for the nonuniform circuit model of
[RazborovRudich1997, Section 4]; the GGM instance is
`CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.GGM`.

The model differs from the classical statement as follows.
* **Circuit learners.** The learner is a circuit on each seed; its running time is not modelled.
* **Fixed seed and point.** The test fixes the learner's seed and the comparison point by
  averaging; it is the nonuniform test of the circuit model, not a uniform algorithm.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.QueryLearner.HasCircuitTests`: the learner agrees with one
  making at most `q` queries, and its tests are circuits of at most `t` gates on truth tables.

## Main results

* `Cslib.MachineLearning.UniformLearning.QueryLearner.HasCircuit.isCircuitTest_agrees`,
  `Cslib.MachineLearning.UniformLearning.QueryLearner.HasCircuit.hasCircuitTests`: the tests of a
  non-adaptive learner with a circuit of `S` gates are circuits of `S + 7` gates.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.HasAdaptiveCircuit.isCircuitTest_agrees`,
  `Cslib.MachineLearning.UniformLearning.QueryLearner.HasAdaptiveCircuit.hasCircuitTests`: the tests
  of an adaptive learner with circuits of `S` gates are circuits of
  `S + q (2 ^ n (2 n + 3) + 1) + 7` gates.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.Learns.le_of_secure`: **a secure family
  bounds the accuracy of learners with small circuit tests**.
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

/-- The learner `A` *has circuit tests* of size `t` with `q` queries: it agrees with a learner
making at most `q` queries, and for every seed `ω` and point `z` its test `A.agrees ω z`, read on
truth tables, is computed by a circuit with at most `t` gates. -/
def HasCircuitTests (A : QueryLearner (Fin n) Ω) (q t : ℕ) : Prop :=
  (∃ B : QueryLearner (Fin n) Ω, B.QueriesAtMost q ∧ ∀ ω, (B ω).eval = (A ω).eval) ∧
    ∀ ω z, IsCircuitTest t fun T : BitString (2 ^ n) =>
      PMF.pure (A.agrees ω z ((truthTable n).symm T))

/-- A learner with circuit tests agrees with a learner making at most `q` queries. -/
theorem HasCircuitTests.exists_queriesAtMost {t : ℕ} (hA : A.HasCircuitTests q t) :
    ∃ B : QueryLearner (Fin n) Ω, B.QueriesAtMost q ∧ ∀ ω, (B ω).eval = (A ω).eval :=
  hA.1

/-- The tests of a learner with circuit tests of size `t` are circuits of at most `t` gates. -/
theorem HasCircuitTests.isCircuitTest {t : ℕ} (hA : A.HasCircuitTests q t) (ω : Ω)
    (z : BitString n) : IsCircuitTest t fun T : BitString (2 ^ n) =>
      PMF.pure (A.agrees ω z ((truthTable n).symm T)) :=
  hA.2 ω z

/-- **Comparing a hypothesis with an input costs seven gates.** The function reading `y`, feeding
`H` with the variables `σ` of `y` followed by the constants `z`, and accepting when the value of `H`
agrees with the variable `j` of `y`, costs at most seven more gates than `H`: the two constants of
the substitution and five gates for the comparison. -/
private theorem complexity_not_xor_substitute_le {d m p : ℕ} (H : BooleanFunction (d + p))
    (σ : Fin d → Fin m) (z : Fin p → Bool) (j : Fin m) :
    complexity interpretation
        (single fun y : Fin m → Bool => !(H (Fin.append (fun i => y (σ i)) z) ^^ y j)) ≤
      complexity interpretation (single H) + 7 := by
  let ρ : Fin (d + p) → Fin m ⊕ Bool := Fin.append (fun i => .inl (σ i)) fun i => .inr (z i)
  have hρ (y : Fin m → Bool) : substitute ρ y = Fin.append (fun i => y (σ i)) z := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp [ρ, substitute]
  have hfun : (fun y : Fin m → Bool => !(H (Fin.append (fun i => y (σ i)) z) ^^ y j)) =
      fun y => !(H (substitute ρ y) ^^ y j) :=
    funext fun y => by rw [hρ]
  rw [hfun]
  calc complexity interpretation (single fun y : Fin m → Bool => !(H (substitute ρ y) ^^ y j))
      ≤ complexity interpretation (single fun y : Fin m → Bool => H (substitute ρ y) ^^ y j) + 1 :=
        complexity_not_le _
    _ ≤ complexity interpretation (single fun y => H (substitute ρ y)) +
          complexity interpretation (single fun y : Fin m → Bool => y j) + 4 + 1 :=
        Nat.add_le_add_right (complexity_xor_le _ _) 1
    _ ≤ complexity interpretation (single H) + 2 + 0 + 4 + 1 := by
        gcongr
        · exact complexity_substitute_le ρ H
        · exact (complexity_single_proj _).le
    _ = complexity interpretation (single H) + 7 := by ring

/-- The test `A.agrees ω z` accepts `g` when the hypothesis agrees with `g` at `z`. -/
private theorem agrees_eq_not_xor (ω : Ω) (z : BitString n) (g : BooleanFunction n) :
    A.agrees ω z g = !((A ω).eval g z ^^ g z) := by
  rw [Bool.eq_iff_iff, agrees_eq_true_iff]
  cases (A ω).eval g z <;> cases g z <;> simp

/-- **The test of a learner with a circuit is a small circuit on truth tables.** If `A` has a
circuit with at most `S` gates, then for every seed `ω` and point `z` the test `A.agrees ω z`, read
on truth tables, is computed with at most `S + 7` gates: the circuit with its queried values wired
from the truth table and the coordinates of `z` fixed, which costs the two constants of the
substitution, and five gates comparing the hypothesis with the truth table at `z`. -/
theorem HasCircuit.isCircuitTest_agrees (hA : A.HasCircuit q S) (ω : Ω) (z : BitString n) :
    IsCircuitTest (S + 7) fun T : BitString (2 ^ n) =>
      PMF.pure (A.agrees ω z ((truthTable n).symm T)) := by
  obtain ⟨pts, F, hF, hev⟩ := hA ω
  refine ⟨fun T => !(F (Fin.append (fun i => T (BitString.equivFin n (pts i))) z) ^^
      T (BitString.equivFin n z)), ?_, ?_⟩
  · exact (complexity_not_xor_substitute_le F (fun i => BitString.equivFin n (pts i)) z _).trans
      (Nat.add_le_add_right hF 7)
  · funext T
    simp only [agrees_eq_not_xor, hev, truthTable_symm_apply]

/-- A learner with `q` non-adaptive queries and a circuit of `S` gates has circuit tests of size
`S + 7`. -/
theorem HasCircuit.hasCircuitTests (hA : A.HasCircuit q S) : A.HasCircuitTests q (S + 7) :=
  ⟨hA.hasAdaptiveCircuit.exists_queriesAtMost, hA.isCircuitTest_agrees⟩

/-- **The test of an adaptive learner with circuits is a small circuit on truth tables.** If `A`
has adaptive circuits with at most `S` gates in all, then for every seed `ω` and point `z` the test
`A.agrees ω z`, read on truth tables, is computed with at most `S + q (2 ^ n (2 n + 3) + 1) + 7`
gates: the answers read from the truth table at the addresses the query circuits compute
(`UniformLearning.QueryLearner.complexity_append_answers_le`), the hypothesis circuit with the
coordinates of `z` fixed, which costs the two constants of the substitution, and five gates
comparing the hypothesis with the truth table at `z`. -/
theorem HasAdaptiveCircuit.isCircuitTest_agrees (hA : A.HasAdaptiveCircuit q S) (ω : Ω)
    (z : BitString n) :
    IsCircuitTest (S + q * (2 ^ n * (2 * n + 3) + 1) + 7) fun T : BitString (2 ^ n) =>
      PMF.pure (A.agrees ω z ((truthTable n).symm T)) := by
  obtain ⟨Q, H, hQH, hev⟩ := hA ω
  -- the table followed by the answers
  let P : BitString (2 ^ n) → Fin (2 ^ n + q) → Bool := fun T =>
    Fin.append T (answersUpTo Q (fun x => T (BitString.equivFin n x)) q le_rfl)
  -- the hypothesis at the fixed point `z`, compared with the table at `z`
  let out : (Fin (2 ^ n + q) → Bool) → Bool := fun y =>
    !(H (Fin.append (fun i => y (Fin.natAdd (2 ^ n) i)) z) ^^
      y (Fin.castAdd q (BitString.equivFin n z)))
  refine ⟨fun T => out (P T), ?_, ?_⟩
  · calc complexity interpretation (single fun T => out (P T))
        = complexity interpretation (single out ∘ P) := rfl
      _ ≤ complexity interpretation P + complexity interpretation (single out) :=
          complexity_comp_le _ _
      _ ≤ (∑ i, complexity interpretation (Q i) + q * (2 ^ n * (2 * n + 3) + 1)) +
            (complexity interpretation (single H) + 7) :=
          add_le_add (complexity_append_answers_le Q)
            (complexity_not_xor_substitute_le H (Fin.natAdd (2 ^ n)) z _)
      _ ≤ S + q * (2 ^ n * (2 * n + 3) + 1) + 7 := by omega
  · funext T
    have htt : (truthTable n).symm T = fun x => T (BitString.equivFin n x) :=
      funext fun x => truthTable_symm_apply T x
    simp only [out, P, Fin.append_left, Fin.append_right, agrees_eq_not_xor, hev, htt]

/-- A learner with `q` adaptive queries and circuits of `S` gates in all has circuit tests of size
`S + q (2 ^ n (2 n + 3) + 1) + 7`. -/
theorem HasAdaptiveCircuit.hasCircuitTests (hA : A.HasAdaptiveCircuit q S) :
    A.HasCircuitTests q (S + q * (2 ^ n * (2 * n + 3) + 1) + 7) :=
  ⟨hA.exists_queriesAtMost, hA.isCircuitTest_agrees⟩

variable {Key : Type*} [Fintype Key] [Nonempty Key]

/-- **A secure family bounds the accuracy of learners with small circuit tests** [Valiant1984]
(locator unverified). Let `A` have circuit tests of size `t` with `q` queries, and learn, with error
`ε ≤ 1` and confidence `1 - δ`, a class containing every member of the keyed family `F` of Boolean
functions on `n` bits. If no test computed with `t` gates distinguishes the truth table of
`F key`, for a uniform key, from a uniform truth table with advantage more than `η`, then
`(1 - δ) (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + η`. -/
theorem Learns.le_of_secure {μ : PMF Ω} {C : ConceptClass (BitString n) Bool} {ε δ : ℝ} {t : ℕ}
    {F : Key → BooleanFunction n} {η : ℝ≥0} (hL : A.Learns μ C ε δ) (hA : A.HasCircuitTests q t)
    (hF : ∀ key, F key ∈ C) (hG : (truthTableGenerator F).Secure (IsCircuitTest t) η)
    (hε : ε ≤ 1) (hδ : 0 ≤ δ) :
    (1 - δ) * (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + η := by
  obtain ⟨⟨B, hBq, hB⟩, htest⟩ := hA
  have hB' (ω : Ω) (g : BooleanFunction n) : (B ω).eval g = (A ω).eval g := by rw [hB]
  have hLB : B.Learns μ C ε δ := by
    rw [learns_iff] at hL ⊢
    simpa only [hB'] using hL
  have hagree (ω : Ω) (z : BitString n) (g : BooleanFunction n) :
      B.agrees ω z g = A.agrees ω z g := by
    rw [Bool.eq_iff_iff, agrees_eq_true_iff, agrees_eq_true_iff, hB']
  obtain ⟨ω, -, z, hz⟩ := exists_dens_agrees_sub_dens_agrees hLB hBq hF hε hδ
  simp only [hagree, Fintype.card_fin] at hz
  have hadv := hG _ (htest ω z)
  rw [Generator.advantage, Generator.toReal_realExperiment_pure,
    Generator.toReal_idealExperiment_pure,
    Fintype.dens_filter_comp_equiv (truthTable n).symm fun g => A.agrees ω z g = true] at hadv
  simp only [truthTableGenerator_apply, Equiv.symm_apply_apply] at hadv
  linarith [le_abs_self ((dens {key | A.agrees ω z (F key) = true} : ℝ) -
    dens {g : BooleanFunction n | A.agrees ω z g = true})]

end QueryLearner

/-- **Exponentially secure families defeat learners with small circuit tests.** Let `F` be an
exponentially secure keyed family. For every `c`, for all large `n`, every learner with circuit
tests of size `t ≤ 2 ^ (c n)` with `q` queries that learns a class containing every member of
`F n` with error `ε ≤ 1` and confidence `1 - δ` satisfies
`(1 - δ) (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + 2 ^ (-c n)`. -/
theorem eventually_le_of_isExponentiallySecure {Key : ℕ → Type*} [∀ n, Fintype (Key n)]
    [∀ n, Nonempty (Key n)] {F : ∀ n, Key n → BooleanFunction n} (hF : IsExponentiallySecure F)
    (c : ℕ) :
    ∀ᶠ n in atTop, ∀ {Ω : Type u} (A : QueryLearner (Fin n) Ω) (μ : PMF Ω)
      (C : ConceptClass (BitString n) Bool) (ε δ : ℝ) (q t : ℕ), A.HasCircuitTests q t →
      t ≤ 2 ^ (c * n) → A.Learns μ C ε δ → (∀ key, F n key ∈ C) → ε ≤ 1 → 0 ≤ δ →
      (1 - δ) * (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + ((2 : ℝ) ^ (c * n))⁻¹ := by
  filter_upwards [hF c] with n hn
  intro Ω A μ C ε δ q t hA ht hL hFC hε hδ
  have h := hL.le_of_secure hA hFC
    (Generator.Secure.of_admissible hn fun _ ⟨test, htest, h⟩ => ⟨test, htest.trans ht, h⟩) hε hδ
  push_cast at h
  exact h

end Cslib.MachineLearning.UniformLearning
