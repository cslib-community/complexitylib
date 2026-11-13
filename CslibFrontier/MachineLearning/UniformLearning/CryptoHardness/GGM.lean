/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GGM.Circuit
public import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.Circuit
import Cslib.Crypto.Primitives.PRG.Basic

/-!
# Pseudorandom generators rule out learners for small circuits

The GGM functions built from a length-doubling generator `G` with seeds of `k` bits have circuits
of size `n (C + 4 k) + 2`, where `C` is the circuit complexity of `G`
(`Cslib.Crypto.GGM.complexity_booleanFamily_le`), and are pseudorandom against circuits when `G`
is (`Cslib.Crypto.GGM.secure_truthTableGenerator_booleanFamily`). A learner for the functions of
that circuit size breaks them (`UniformLearning.QueryLearner.Learns.le_of_secure`), so a secure
generator bounds the accuracy of every learner with small circuit tests for small circuits
[Valiant1984], [GGM1986] (locators unverified).

* **Concrete form** (`UniformLearning.QueryLearner.Learns.le_of_secure_generator`). If no test
  with `t + 2 ^ n (n C + 1)` gates distinguishes `G` from uniform with advantage more than `η`,
  then a learner with circuit tests of size `t` with `q` queries
  (`UniformLearning.QueryLearner.HasCircuitTests`) that learns the functions on `n` bits of
  circuit size at most `n (C + 4 k) + 2`, with error `ε ≤ 1` and confidence `1 - δ`, satisfies
  `(1 - δ) (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + (2 ^ n - 1) η`.
* **Asymptotic form** (`UniformLearning.eventually_le_of_isSubexponentiallySecure`). For a family
  of generators of polynomial circuit complexity that is subexponentially secure
  (`Cslib.Crypto.PRG.IsSubexponentiallySecure`), there is a polynomial `s` such that for every
  `c`, for all large `n`, every learner with circuit tests of size at most `2 ^ (c n)` for the
  functions on `n` bits of circuit size at most `s n` satisfies
  `(1 - δ) (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + 2 ^ (-c n)`.
* **Unlearnability** (`UniformLearning.exists_eventually_not_learns_of_isSubexponentiallySecure`).
  With the same `s`, for every `c` and all `ε ≤ 1`, `δ ≥ 0` with `(1 - δ) (1 - ε) > 3 / 4`, for
  all large `n` no learner with at most `2 ^ (n - 1)` adaptive queries and circuits of at most
  `2 ^ (c n)` gates in all (`UniformLearning.QueryLearner.HasAdaptiveCircuit`) learns the
  functions of circuit size at most `s n` with error `ε` and confidence `1 - δ`; for example
  `ε = δ = 1 / 10`. Non-adaptive learners with circuits are the special case of constant queries
  (`UniformLearning.QueryLearner.HasCircuit.hasAdaptiveCircuit`).

The learners are circuits with membership queries on each seed, of exponential size `2 ^ (c n)`;
their running time is not modelled. The tests are nonuniform, as in the natural proofs barrier
(`Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural_of_generator`), to which this is the
learning counterpart.

## Main results

* `Cslib.MachineLearning.UniformLearning.QueryLearner.Learns.le_of_secure_generator`: a secure
  generator bounds the accuracy of learners with small circuit tests for small circuits.
* `Cslib.MachineLearning.UniformLearning.eventually_le_of_isSubexponentiallySecure`: the asymptotic
  form for subexponentially secure generators.
* `Cslib.MachineLearning.UniformLearning.exists_eventually_not_learns_of_isSubexponentiallySecure`:
  **polynomial-size circuits are not learnable** by learners with small circuits and at most
  `2 ^ (n - 1)` adaptive queries, at any accuracy `(1 - δ) (1 - ε) > 3 / 4`.

## References

* [L. G. Valiant, *A theory of the learnable*][Valiant1984]
* [O. Goldreich, S. Goldwasser, S. Micali, *How to construct random functions*][GGM1986]
* [A. A. Razborov, S. Rudich, *Natural proofs*][RazborovRudich1997]
-/

public section

universe u

namespace Cslib.MachineLearning.UniformLearning

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto Cslib.Crypto.PRG Filter PACLearning
open scoped NNReal

/-- **A secure generator bounds the accuracy of learners for small circuits** [Valiant1984],
[GGM1986] (locators unverified). Let `G` be a length-doubling generator with seeds of `k ≥ 1` bits
and circuit complexity `C`, such that no test with `t + 2 ^ n (n C + 1)` gates distinguishes its
output from uniform with advantage more than `η`. Let `A` have circuit tests of size `t` with `q`
queries, and learn, with error `ε ≤ 1` and confidence `1 - δ`, a class containing every function on
`n` bits of circuit size at most `n (C + 4 k) + 2`. Then
`(1 - δ) (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + (2 ^ n - 1) η`. -/
theorem QueryLearner.Learns.le_of_secure_generator {k n : ℕ} [NeZero k]
    {G : PRG.Generator (BitString k) (BitString (2 * k))} {Ω : Type*} {A : QueryLearner (Fin n) Ω}
    {μ : PMF Ω} {C : ConceptClass (BitString n) Bool} {ε δ : ℝ} {q t : ℕ} {η : ℝ≥0}
    (hL : A.Learns μ C ε δ) (hA : A.HasCircuitTests q t)
    (hC : ∀ f : BooleanFunction n,
      complexity interpretation (single f) ≤ n * (complexity interpretation ⇑G + 4 * k) + 2 →
        f ∈ C)
    (hG : G.Secure (IsCircuitTest (t + 2 ^ n * (n * complexity interpretation ⇑G + 1))) η)
    (hε : ε ≤ 1) (hδ : 0 ≤ δ) :
    (1 - δ) * (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + (2 ^ n - 1) * η := by
  have h := hL.le_of_secure hA (fun seed => hC _ (GGM.complexity_booleanFamily_le G n seed))
    (GGM.secure_truthTableGenerator_booleanFamily hG) hε hδ
  rwa [NNReal.coe_mul, NNReal.coe_sub (one_le_pow₀ one_le_two), NNReal.coe_pow, NNReal.coe_ofNat,
    NNReal.coe_one] at h

/-- **Subexponentially secure generators rule out learners for polynomial-size circuits**
[Valiant1984], [GGM1986] (locators unverified). Let `G` be a family of length-doubling generators
of polynomial circuit complexity that is subexponentially secure with exponent `1 / d`. Then there
is a polynomially bounded `s` such that, for every `c`, for all large `n`, every learner with
circuit tests of size at most `2 ^ (c n)` with `q` queries that learns the functions on `n` bits of
circuit size at most `s n` with error `ε ≤ 1` and confidence `1 - δ` satisfies
`(1 - δ) (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + 2 ^ (-c n)`. The bound is
`s n = n (C + 4 k) + 2` for the GGM functions with keys of `k = (n + 1) ^ (2 d + 1)` bits, where
`C` is the circuit complexity of `G k`. -/
theorem eventually_le_of_isSubexponentiallySecure
    {G : ∀ k, PRG.Generator (BitString k) (BitString (2 * k))} {d : ℕ}
    (hsize : PolynomiallyBounded fun k => complexity interpretation ⇑(G k))
    (hG : PRG.IsSubexponentiallySecure G d) :
    ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ c : ℕ, ∀ᶠ n in atTop,
      ∀ {Ω : Type u} (A : QueryLearner (Fin n) Ω) (μ : PMF Ω)
        (C : ConceptClass (BitString n) Bool) (ε δ : ℝ) (q t : ℕ), A.HasCircuitTests q t →
        t ≤ 2 ^ (c * n) → A.Learns μ C ε δ →
        (∀ f : BooleanFunction n, complexity interpretation (single f) ≤ s n → f ∈ C) →
        ε ≤ 1 → 0 ≤ δ →
        (1 - δ) * (1 - ε) ≤ 1 / 2 + q / 2 ^ (n + 1) + ((2 : ℝ) ^ (c * n))⁻¹ := by
  have hkey : PolynomiallyBounded fun n => (n + 1) ^ (2 * d + 1) := by fun_prop
  have hcomp := hsize.comp hkey
  refine ⟨fun n =>
      n * (complexity interpretation ⇑(G ((n + 1) ^ (2 * d + 1))) + 4 * (n + 1) ^ (2 * d + 1)) + 2,
    by fun_prop, fun c => ?_⟩
  filter_upwards [eventually_le_of_isExponentiallySecure.{u}
    (GGM.isExponentiallySecure_booleanFamily hsize hG) c] with n hn
  intro Ω A μ C ε δ q t hA ht hL hC hε hδ
  exact hn A μ C ε δ q t hA ht hL (fun seed => hC _ (GGM.complexity_booleanFamily_le _ n seed)) hε
    hδ

/-- The test of an adaptive learner with at most `2 ^ (n - 1)` queries and circuits of at most
`2 ^ (c n)` gates has at most `2 ^ ((c + 4) n)` gates, for `n ≥ 4`. -/
private theorem testSize_le {n c q S : ℕ} (hn : 4 ≤ n) (hq : 2 * q ≤ 2 ^ n)
    (hS : S ≤ 2 ^ (c * n)) : S + q * (2 ^ n * (2 * n + 3) + 1) + 7 ≤ 2 ^ ((c + 4) * n) := by
  have hN : 16 ≤ 2 ^ n :=
    (show 16 = 2 ^ 4 by norm_num) ▸ Nat.pow_le_pow_right two_pos hn
  have hnN : n < 2 ^ n := Nat.lt_two_pow_self
  have hM : 1 ≤ 2 ^ (c * n) := Nat.one_le_two_pow
  have he : 2 ^ ((c + 4) * n) = 2 ^ (c * n) * (2 ^ n) ^ 4 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [he]
  generalize 2 ^ n = N at *
  generalize 2 ^ (c * n) = M at *
  have hX : N * (2 * n + 3) + 1 ≤ N * (2 * N + 1) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left N (by omega)) 1
  have hqX : 2 * (q * (N * (2 * n + 3) + 1)) ≤ N * (N * (2 * N + 1) + 1) := by
    rw [← mul_assoc]
    exact Nat.mul_le_mul hq hX
  have h2 : N * 16 ≤ N * N := Nat.mul_le_mul_left _ hN
  have h3 : N ^ 2 * 16 ≤ N ^ 2 * N := Nat.mul_le_mul_left _ hN
  have h4 : N ^ 3 * 16 ≤ N ^ 3 * N := Nat.mul_le_mul_left _ hN
  have hN4 : 2 * N ^ 3 + N ^ 2 + N + 14 ≤ N ^ 4 := by nlinarith
  have hMN : M + N ^ 4 ≤ 2 * (M * N ^ 4) := by nlinarith [Nat.one_le_pow 4 N (by omega)]
  nlinarith

/-- **Subexponentially secure generators make polynomial-size circuits unlearnable by learners
with small circuits** [Valiant1984], [GGM1986] (locators unverified). Let `G` be a family of
length-doubling generators of polynomial circuit complexity that is subexponentially secure. Then
there is a polynomially bounded `s` with the following property. For every `c` and every error
`ε ≤ 1` and confidence `1 - δ` with `(1 - δ) (1 - ε) > 3 / 4`, for all large `n`, no learner with
at most `2 ^ (n - 1)` adaptive queries and circuits of at most `2 ^ (c n)` gates in all learns the
functions on `n` bits of circuit size at most `s n` with error `ε` and confidence `1 - δ`. The
threshold `3 / 4` is `1 / 2` for guessing an unqueried value plus `1 / 4` for the chance that the
comparison point was queried. Non-adaptive learners with circuits are the special case of constant
queries (`UniformLearning.QueryLearner.HasCircuit.hasAdaptiveCircuit`). -/
theorem exists_eventually_not_learns_of_isSubexponentiallySecure
    {G : ∀ k, PRG.Generator (BitString k) (BitString (2 * k))} {d : ℕ}
    (hsize : PolynomiallyBounded fun k => complexity interpretation ⇑(G k))
    (hG : PRG.IsSubexponentiallySecure G d) :
    ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ (c : ℕ) (ε δ : ℝ), ε ≤ 1 → 0 ≤ δ →
      3 / 4 < (1 - δ) * (1 - ε) → ∀ᶠ n in atTop,
        ∀ {Ω : Type u} (A : QueryLearner (Fin n) Ω) (μ : PMF Ω) (q S : ℕ),
          A.HasAdaptiveCircuit q S → 2 * q ≤ 2 ^ n → S ≤ 2 ^ (c * n) →
          ¬ A.Learns μ {f | complexity interpretation (single f) ≤ s n} ε δ := by
  obtain ⟨s, hs, h⟩ := eventually_le_of_isSubexponentiallySecure.{u} hsize hG
  refine ⟨s, hs, fun c ε δ hε hδ hgap => ?_⟩
  -- the advantage of the generator eventually falls below the margin over `3 / 4`
  have hsmall : ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ n)⁻¹ < (1 - δ) * (1 - ε) - 3 / 4 :=
    (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)).eventually
      (gt_mem_nhds (by linarith))
  filter_upwards [h (c + 4), hsmall, eventually_ge_atTop 4] with n hn hn' hn4 Ω A μ q S hA hq hS hL
  have hb := hn A μ _ ε δ q _ hA.hasCircuitTests (testSize_le hn4 hq hS) hL (fun _ hf => hf) hε hδ
  have hq' : (q : ℝ) / 2 ^ (n + 1) ≤ 1 / 4 := by
    have : (2 * q : ℝ) ≤ 2 ^ n := by exact_mod_cast hq
    rw [div_le_iff₀ (by positivity), pow_succ]
    linarith
  have hpow : ((2 : ℝ) ^ ((c + 4) * n))⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (Nat.le_mul_of_pos_left n (by omega)))
  linarith

end Cslib.MachineLearning.UniformLearning
