/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GeneratorReindex
public import Complexity.Crypto.Computational.OneWay
public import Complexity.Crypto.Computational.OneWay.Normalize
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Map
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Weak One-Way Functions, Output Normalization, and Schedule Reindexing

This module defines $\alpha$-weak one-way functions (`Cslib.Crypto.WeakOneWayAt`) and weak one-way
functions (`Cslib.Crypto.WeakOneWay`) against uniform strict PPT inverters following
[Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020] (Definition 2.2,
§2.1, p. 7 of `arXiv:2009.11514v1`; FOCS 2020, p. 1246), originally due to [A. C. Yao][Yao1982] and
treated in [O. Goldreich, *Foundations of Cryptography, Volume 1*][Goldreich2001] (§2.2.2,
Definition 2.2.2).

In addition to basic monotonicity, `<` vs. `≤` equivalence bridges, strong-implies-weak
specialization (`Cslib.Crypto.OneWay.weakOneWay`), and negative nonvacuity witnesses
(`Cslib.Crypto.not_weakOneWay_const`), this module provides two structural transformations reused
by Yao's direct-product hardness amplification and the Liu–Pass Section 4 converse construction:

1. **Fixed-output-length normalization (`Cslib.Crypto.WeakOneWay.exists_fixedOutputLength`):**
   Every weak one-way function yields a weak one-way function whose output length depends only on
   the input length, reusing self-delimiting padding from
   `Complexity.Crypto.Computational.OneWay.Normalize`.
2. **Schedule reindexing (`Cslib.Crypto.OneWayReindex.reindex`):**
   Given an input-length schedule `m : ℕ → ℕ` with `m n ≥ n + 1` computable in unary polynomial
   time and a parameter-indexed family `core : ℕ → List Bool → List Bool` defined on inputs of
   length `m n`, `OneWayReindex.reindex m core` extends the family to all input lengths
   $M \in \mathbb{N}$ by finding the greatest parameter $n$ with $m(n) \le M$
   (`GeneratorReindex.parameter`), evaluating `core n` on the $m(n)$-bit prefix, and pairing the
   core output with the parameter $n$ in unary (`wrappedImage`). This is a library variant and
   generalization of the input-truncation padding trick in
   [Liu and Pass, Proof of Theorem 4.1, §4, p. 10 of `arXiv:2009.11514v1`][LiuPass2020] (cf. the
   length-extension convention of [Goldreich, Vol. 1, §2.2.3, Proposition 2.2.3][Goldreich2001]),
   with the parameter $n$ appended to the output so images from distinct parameters are disjoint
   and the reduction is lossless even for nonmonotone schedules. Both weak one-wayness
   (`OneWayReindex.weakOneWay`) and strong one-wayness (`OneWayReindex.oneWay`) transfer from the
   parameter-indexed game `familyInversionGame` to all input lengths.

## Main definitions

* `Cslib.Crypto.WeakOneWayAt`: $\alpha$-weak one-way function against uniform strict PPT inverters
  ([Liu and Pass, Definition 2.2, §2.1, p. 7 of `arXiv:2009.11514v1`][LiuPass2020]).
* `Cslib.Crypto.WeakOneWay`: weak one-way function ($\frac{1}{q(\cdot)}$-weak OWF for some positive
  polynomial $q$, [Liu and Pass, Definition 2.2, §2.1, p. 7 of `arXiv:2009.11514v1`][LiuPass2020]).
* `Cslib.Crypto.OneWayReindex.reindex`: extend a parameter-indexed family on input lengths `m n` to
  all binary strings.
* `Cslib.Crypto.OneWayReindex.familyInversionGame`: the parameter-indexed inversion experiment on
  inputs of length `m n`.

## Main results

* `Cslib.Crypto.weakOneWay_iff_le`, `Cslib.Crypto.WeakOneWay.of_le`: equivalence between
  `< 1 - 1/q(n)` and `≤ 1 - 1/q(n)` formulations of `WeakOneWay`.
* `Cslib.Crypto.WeakOneWay.exists_monotone_poly`: every weak OWF admits a monotone polynomial bound
  $q(n) \ge n + 1$.
* `Cslib.Crypto.OneWay.weakOneWay`: every strong one-way function is a weak one-way function.
* `Cslib.Crypto.not_weakOneWay_of_inverse`, `Cslib.Crypto.not_weakOneWay_const`: efficient
  right-inverses and constant functions refute weak one-wayness.
* `Cslib.Crypto.WeakOneWay.normalize`, `Cslib.Crypto.WeakOneWay.exists_fixedOutputLength`:
  output-length normalization preserves weak one-wayness.
* `Cslib.Crypto.OneWayReindex.exists_familyInverter_inversion_le`: any PPT inverter against
  `reindex m core` at length `M ≥ m 0` reduces without probability loss to a uniform PPT inverter in
  `familyInversionGame` at parameter `GeneratorReindex.parameter m M`.
* `Cslib.Crypto.OneWayReindex.weakOneWay`, `Cslib.Crypto.OneWayReindex.oneWay`: weak and strong
  one-wayness transfer from `familyInversionGame` on `m n` to `reindex m core` on all input lengths.

## References

* [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020],
  full version `arXiv:2009.11514v1` (Section 2.1, Definition 2.2 and Section 4, Theorem 4.1).
* [A. C. Yao, *Theory and Application of Trapdoor Functions*][Yao1982].
* [O. Goldreich, *Foundations of Cryptography, Volume 1*][Goldreich2001], Sections 2.2.2–2.2.3.
-/

@[expose] public section

namespace Cslib.Crypto

open Filter Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Weak one-way functions
([Liu and Pass, Definition 2.2, §2.1, p. 7 of `arXiv:2009.11514v1`][LiuPass2020]) -/

/-- **[Liu and Pass, Definition 2.2, §2.1, p. 7 of `arXiv:2009.11514v1`][LiuPass2020]:
$\alpha$-weak one-way function (`WeakOneWayAt`).**
A polynomial-time computable function $f : \{0, 1\}^* \to \{0, 1\}^*$ is an $\alpha$-weak one-way
function if for every uniform strict PPT inverter $\mathcal{A}$, for all sufficiently large
$n \in \mathbb{N}$,
$$\Pr_{x \leftarrow \{0, 1\}^n}[\mathcal{A}(1^n, f(x)) \in f^{-1}(f(x))] < 1 - \alpha(n).$$ -/
structure WeakOneWayAt (f : List Bool → List Bool) (α : ℕ → ℝ) : Prop where
  /-- A deterministic polynomial-time algorithm evaluates the function. -/
  polyTime : ComputableInPolyTime f encBits encBits
  /-- Every uniform strict PPT inverter succeeds with probability `< 1 - α n` eventually. -/
  weak : ∀ adversary : Inverter, IsPPT encBits adversary →
    ∀ᶠ n in atTop,
      (Game.succProbability (ProbComp.eval (inversionGame f adversary n)) : ℝ) < 1 - α n

/-- **[Liu and Pass, Definition 2.2, §2.1, p. 7 of `arXiv:2009.11514v1`][LiuPass2020]:
Weak one-way function (`WeakOneWay`).**
A function $f : \{0, 1\}^* \to \{0, 1\}^*$ is a weak one-way function if there exists a positive
polynomial $q \in \mathbb{N}[X]$ ($\forall n,\, 0 < q(n)$) such that $f$ is a
$\frac{1}{q(\cdot)}$-weak one-way function. -/
def WeakOneWay (f : List Bool → List Bool) : Prop :=
  ∃ q : Polynomial ℕ, (∀ n, 0 < q.eval n) ∧
    WeakOneWayAt f (fun n => 1 / ((q.eval n : ℕ) : ℝ))

/-- Extract the polynomial-time certificate from `WeakOneWay`. -/
theorem WeakOneWay.polyTime {f : List Bool → List Bool} (hf : WeakOneWay f) :
    ComputableInPolyTime f encBits encBits :=
  let ⟨_, _, h⟩ := hf
  h.polyTime

/-- Monotonicity of `WeakOneWayAt` in the failure threshold $\alpha$. -/
theorem WeakOneWayAt.mono {f : List Bool → List Bool} {α₁ α₂ : ℕ → ℝ}
    (hf : WeakOneWayAt f α₂) (hα : ∀ᶠ n in atTop, α₁ n ≤ α₂ n) :
    WeakOneWayAt f α₁ := by
  refine ⟨hf.polyTime, fun adversary hPPT => ?_⟩
  filter_upwards [hf.weak adversary hPPT, hα] with n hn hle
  linarith

/-- Establish `WeakOneWayAt f α₁` from a non-strict bound `≤ 1 - α₂ n` when `α₁ n < α₂ n`
eventually. -/
theorem WeakOneWayAt.of_le {f : List Bool → List Bool} {α₁ α₂ : ℕ → ℝ}
    (hf : ComputableInPolyTime f encBits encBits)
    (hα : ∀ᶠ n in atTop, α₁ n < α₂ n)
    (h : ∀ adversary : Inverter, IsPPT encBits adversary →
      ∀ᶠ n in atTop,
        (Game.succProbability (ProbComp.eval (inversionGame f adversary n)) : ℝ) ≤ 1 - α₂ n) :
    WeakOneWayAt f α₁ := by
  refine ⟨hf, fun adversary hPPT => ?_⟩
  filter_upwards [h adversary hPPT, hα] with n hn hlt
  linarith

/-- Establish `WeakOneWay f` from a non-strict bound `≤ 1 - 1 / q(n)` for a positive polynomial
$q$, by doubling the polynomial to $2 q$. -/
theorem WeakOneWay.of_le {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits)
    {q : Polynomial ℕ} (hq : ∀ n, 0 < q.eval n)
    (h : ∀ adversary : Inverter, IsPPT encBits adversary →
      ∀ᶠ n in atTop,
        (Game.succProbability (ProbComp.eval (inversionGame f adversary n)) : ℝ) ≤
          1 - 1 / ((q.eval n : ℕ) : ℝ)) :
    WeakOneWay f := by
  refine ⟨2 * q, fun n => by simp [hq n], ?_⟩
  refine WeakOneWayAt.of_le hf (Eventually.of_forall fun n => ?_) h
  have hpos : (0 : ℝ) < (q.eval n : ℕ) := Nat.cast_pos.mpr (hq n)
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Nat.cast_mul, Nat.cast_ofNat]
  exact one_div_lt_one_div_of_lt hpos (by linarith)

/-- Equivalence between the strict (`< 1 - 1 / q(n)`) and non-strict (`≤ 1 - 1 / q(n)`)
formulations of `WeakOneWay`. -/
theorem weakOneWay_iff_le {f : List Bool → List Bool} :
    WeakOneWay f ↔
      ComputableInPolyTime f encBits encBits ∧
        ∃ q : Polynomial ℕ, (∀ n, 0 < q.eval n) ∧
          ∀ adversary : Inverter, IsPPT encBits adversary →
            ∀ᶠ n in atTop,
              (Game.succProbability (ProbComp.eval (inversionGame f adversary n)) : ℝ) ≤
                1 - 1 / ((q.eval n : ℕ) : ℝ) := by
  constructor
  · rintro ⟨q, hq, hf⟩
    refine ⟨hf.polyTime, q, hq, fun adversary hPPT => ?_⟩
    filter_upwards [hf.weak adversary hPPT] with n hn
    exact hn.le
  · rintro ⟨hf, q, hq, h⟩
    exact WeakOneWay.of_le hf hq h

/-- Every weak one-way function admits a monotone polynomial $q \in \mathbb{N}[X]$ with
$q(n) \ge n + 1$ for all $n$ such that `WeakOneWayAt f (fun n => 1 / (q.eval n : ℝ))`. -/
theorem WeakOneWay.exists_monotone_poly {f : List Bool → List Bool} (hf : WeakOneWay f) :
    ∃ q : Polynomial ℕ, (∀ n, n + 1 ≤ q.eval n) ∧ Monotone q.eval ∧
      WeakOneWayAt f (fun n => 1 / ((q.eval n : ℕ) : ℝ)) := by
  obtain ⟨q₀, hq₀, hweak⟩ := hf
  let q : Polynomial ℕ := q₀ + Polynomial.X + 1
  have hq_eval (n : ℕ) : q.eval n = q₀.eval n + n + 1 := by simp [q]
  refine ⟨q, fun n => by rw [hq_eval]; omega, fun a b hab => Polynomial.eval_mono q hab,
    hweak.mono (Eventually.of_forall fun n => ?_)⟩
  exact one_div_le_one_div_of_le (Nat.cast_pos.mpr (hq₀ n))
    (Nat.cast_le.mpr (by rw [hq_eval]; omega))

/-- Every strong one-way function is a $\frac{1}{2}$-weak one-way function. -/
theorem OneWay.weakOneWayAt_half {f : List Bool → List Bool} (hf : OneWay f) :
    WeakOneWayAt f (fun _ => 1 / 2) := by
  refine ⟨hf.polyTime, fun adversary hPPT => ?_⟩
  have hneg := (hf.inversion_negligible adversary hPPT).eventually_le_inv_polynomial
    (PolynomiallyBounded.const 3) (fun _ => by omega)
  filter_upwards [hneg] with n hn
  have hn' : (Game.succProbability (ProbComp.eval (inversionGame f adversary n)) : ℝ) ≤ 1 / 3 := by
    exact_mod_cast hn
  linarith

/-- Every strong one-way function is a weak one-way function. -/
theorem OneWay.weakOneWay {f : List Bool → List Bool} (hf : OneWay f) : WeakOneWay f := by
  refine ⟨2, fun _ => by simp, ?_⟩
  simpa using hf.weakOneWayAt_half

/-! ### Negative / nonvacuity witnesses -/

/-- Efficiently finding any preimage, told the input length, refutes `WeakOneWayAt` whenever
$\alpha(n) > 0$ eventually. -/
theorem not_weakOneWayAt_of_inverse {f : List Bool → List Bool} {α : ℕ → ℝ}
    (hα : ∀ᶠ n in atTop, 0 < α n) (inverse : ℕ → List Bool → List Bool)
    (hPPT : IsPPT encBits (fun n y => pure (inverse n y)))
    (hinv : ∀ x, f (inverse x.length (f x)) = f x) : ¬ WeakOneWayAt f α := by
  intro hf
  have h := (hf.weak (fun n y => pure (inverse n y)) hPPT).and hα
  obtain ⟨n, hn, hpos⟩ := h.exists
  rw [Game.succProbability, eval_inversionGame_of_rightInverse f inverse hinv n,
    PMF.pure_apply_self, ENNReal.toNNReal_one, NNReal.coe_one] at hn
  linarith

/-- Efficiently finding any preimage, told the input length, refutes `WeakOneWay`. -/
theorem not_weakOneWay_of_inverse {f : List Bool → List Bool}
    (inverse : ℕ → List Bool → List Bool)
    (hPPT : IsPPT encBits (fun n y => pure (inverse n y)))
    (hinv : ∀ x, f (inverse x.length (f x)) = f x) : ¬ WeakOneWay f := by
  rintro ⟨q, hq, hf⟩
  refine not_weakOneWayAt_of_inverse (Eventually.of_forall fun n => ?_) inverse hPPT hinv hf
  exact one_div_pos.mpr (Nat.cast_pos.mpr (hq n))

/-- Constant functions are not weakly one-way: the empty word is always a preimage. -/
theorem not_weakOneWay_const (word : List Bool) : ¬ WeakOneWay (fun _ => word) :=
  not_weakOneWay_of_inverse (fun _ _ => [])
    (ComputableTidilyInPolyTime.const []).isPPT (fun _ => rfl)

/-! ### Output-length normalization for weak one-way functions -/

/-- Self-delimiting output padding preserves `WeakOneWayAt` against uniform strict PPT inverters. -/
theorem WeakOneWayAt.normalize {f : List Bool → List Bool} {α : ℕ → ℝ}
    (hf : WeakOneWayAt f α) (bound : ℕ → ℕ)
    (hbound : ComputableInPolyTime bound encUnary encUnary) :
    WeakOneWayAt (OneWayNormalization.normalize f bound) α := by
  have hbound_tidy := hbound.tidy
  refine ⟨OneWayNormalization.computableInPolyTime_normalize hf.polyTime hbound,
    fun adversary hPPT => ?_⟩
  have hreduce : IsPPT encBits (fun n image =>
      adversary n (BitString.padWord (bound n) image)) := by ppt
  filter_upwards [hf.weak _ hreduce] with n hn
  have hle : (Game.succProbability
        (ProbComp.eval (inversionGame (OneWayNormalization.normalize f bound) adversary n)) : ℝ) ≤
      (Game.succProbability (ProbComp.eval (inversionGame f
        (fun n image => adversary n (BitString.padWord (bound n) image)) n)) : ℝ) := by
    exact_mod_cast OneWayNormalization.inversion_le f bound adversary n
  exact hle.trans_lt hn

/-- Self-delimiting output padding preserves `WeakOneWay` against uniform strict PPT inverters. -/
theorem WeakOneWay.normalize {f : List Bool → List Bool} (hf : WeakOneWay f) (bound : ℕ → ℕ)
    (hbound : ComputableInPolyTime bound encUnary encUnary) :
    WeakOneWay (OneWayNormalization.normalize f bound) := by
  obtain ⟨q, hq, hweak⟩ := hf
  exact ⟨q, hq, hweak.normalize bound hbound⟩

/-- Every weak one-way function yields a weak one-way function whose output length depends only on
the input length, with a uniformly polynomial-time unary output-length function. -/
theorem WeakOneWay.exists_fixedOutputLength {f : List Bool → List Bool} (hf : WeakOneWay f) :
    ∃ (g : List Bool → List Bool) (length : ℕ → ℕ), WeakOneWay g ∧
      (∀ input, (g input).length = length input.length) ∧
      ComputableInPolyTime length encUnary encUnary := by
  obtain ⟨c, d, hsize⟩ := hf.polyTime.polyBounded_length.exists_le
  let bound (n : ℕ) := c * (n + 1) ^ d
  have hbound : ComputableTidilyInPolyTime bound encUnary encUnary := by
    unfold bound
    fun_prop
  have hlen : ComputableTidilyInPolyTime (fun n => 2 * bound n + 1) encUnary encUnary := by
    fun_prop
  refine ⟨OneWayNormalization.normalize f bound, fun n => 2 * bound n + 1,
    hf.normalize bound (.of_tidy hbound), ?_, .of_tidy hlen⟩
  intro input
  exact BitString.length_padWord (hsize input)

/-! ### Schedule reindexing for parameter-indexed one-way families
(Library variant of the padding trick in
[Liu and Pass, Proof of Theorem 4.1, §4, p. 10 of `arXiv:2009.11514v1`][LiuPass2020];
cf. [Goldreich, Vol. 1, §2.2.3, Proposition 2.2.3][Goldreich2001]) -/

namespace OneWayReindex

/-- Wrap a parameter `n` and a core image `y` into a single binary word via `encPair`. -/
def wrappedImage (n : ℕ) (y : List Bool) : List Bool :=
  encPair encUnary encBits (n, y)

@[simp]
theorem wrappedImage_inj {n₁ n₂ : ℕ} {y₁ y₂ : List Bool} :
    wrappedImage n₁ y₁ = wrappedImage n₂ y₂ ↔ n₁ = n₂ ∧ y₁ = y₂ := by
  rw [wrappedImage, wrappedImage, (encPair encUnary encBits).injective.eq_iff, Prod.mk.injEq]

/-- Extend a parameter-indexed family `core` on input lengths `m n` to all binary strings:
find the greatest parameter `n` with `m n ≤ x.length` (`GeneratorReindex.parameter`), evaluate
`core n` on the `m n`-bit prefix of `x`, and pair the result with `n` in unary (`wrappedImage`).
This is a library variant of the input-truncation padding trick in
[Liu and Pass, Proof of Theorem 4.1, §4, p. 10 of `arXiv:2009.11514v1`][LiuPass2020] (cf.
[Goldreich, Vol. 1, §2.2.3, Proposition 2.2.3][Goldreich2001]) that pairs the parameter `n` into
the output so images from distinct parameters are disjoint. -/
def reindex (m : ℕ → ℕ) (core : ℕ → List Bool → List Bool) (x : List Bool) : List Bool :=
  let n := GeneratorReindex.parameter m x.length
  wrappedImage n (core n (x.take (m n)))

private theorem computableTidilyInPolyTime_reindex {m : ℕ → ℕ} {core : ℕ → List Bool → List Bool}
    (hm : ComputableTidilyInPolyTime m encUnary encUnary)
    (hcore : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => core p.1 p.2)
      (encPair encUnary encBits) encBits) :
    ComputableTidilyInPolyTime (reindex m core) encBits encBits := by
  have hparam : ComputableTidilyInPolyTime
      (fun x : List Bool => GeneratorReindex.parameter m x.length) encBits encUnary :=
    (GeneratorReindex.isPolyTime_parameter (.of_tidy hm)
      (ComputableInPolyTime.encoding_length encBits)).tidy
  have htake : ComputableTidilyInPolyTime
      (fun x : List Bool => x.take (m (GeneratorReindex.parameter m x.length))) encBits encBits :=
    ComputableTidilyInPolyTime.bitsTakeWithInput ComputableTidilyInPolyTime.id' (hm.comp hparam)
  have hpair : ComputableTidilyInPolyTime
      (fun x : List Bool =>
        (GeneratorReindex.parameter m x.length,
          core (GeneratorReindex.parameter m x.length)
            (x.take (m (GeneratorReindex.parameter m x.length)))))
      encBits (encPair encUnary encBits) :=
    hparam.prod (hcore.comp (hparam.prod htake))
  exact hpair.of_enc_eq fun _ => rfl

/-- Reindexing preserves deterministic polynomial-time computability. -/
@[fun_prop]
theorem computableInPolyTime_reindex {m : ℕ → ℕ} {core : ℕ → List Bool → List Bool}
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hcore : ComputableInPolyTime (fun p : ℕ × List Bool => core p.1 p.2)
      (encPair encUnary encBits) encBits) :
    ComputableInPolyTime (reindex m core) encBits encBits :=
  .of_tidy (computableTidilyInPolyTime_reindex hm.tidy hcore.tidy)

/-- The parameter-indexed inversion game for `core` at input length `m n`.
Scores `core n (candidate.take (m n)) == core n input` by truncating the inverter's candidate to
`m n` bits; since composing any inverter with `List.take (m n)` preserves PPT computability,
bounding success in this game is no stronger a security hypothesis than the untruncated game. -/
noncomputable def familyInversionGame (m : ℕ → ℕ) (core : ℕ → List Bool → List Bool)
    (adversary : Inverter) (n : ℕ) : ProbComp Bool := do
  let input ← BitString.sampleList (m n)
  let candidate ← adversary n (core n input)
  return core n (candidate.take (m n)) == core n input

/-- Shared coin budget for simulating `adversary M (wrappedImage n y)` across all
`M ≤ m (n + 1)`. -/
private def coinBudget (m : ℕ → ℕ) (c d : ℕ) (n : ℕ) (y : List Bool) : ℕ :=
  c * (2 * m (n + 1) + 2 + (wrappedImage n y).length) ^ d

private theorem le_coinBudget (m : ℕ → ℕ) (c d : ℕ) {n M : ℕ} (y : List Bool)
    (hM : M ≤ m (n + 1)) :
    c * ((encPair encUnary encBits (M, wrappedImage n y)).length + 1) ^ d ≤
      coinBudget m c d n y := by
  rw [coinBudget, length_encPair]
  simp only [encUnary_apply, List.length_replicate, encBits_apply]
  refine Nat.mul_le_mul_left c (Nat.pow_le_pow_left ?_ d)
  omega

/-- Test whether a specific input length `M` yields a valid `core n` preimage of `y` under the
seeded evaluator `evaluate` and coin tape `coins`. -/
private def tryLength (m : ℕ → ℕ) (core : ℕ → List Bool → List Bool)
    (evaluate : (ℕ × List Bool) → List Bool → List Bool)
    (n : ℕ) (y coins : List Bool) (M : ℕ) : Bool :=
  core n ((evaluate (M, wrappedImage n y) coins).take (m n)) == y

/-- Bounded search for a length `M ≤ m (n + 1)` whose candidate inverts `y` under `core n`. -/
private def bestLength (m : ℕ → ℕ) (core : ℕ → List Bool → List Bool)
    (evaluate : (ℕ × List Bool) → List Bool → List Bool)
    (n : ℕ) (y coins : List Bool) : ℕ :=
  Nat.findGreatest (fun M => tryLength m core evaluate n y coins M = true) (m (n + 1))

/-- Deterministic candidate produced at parameter `n` on image `y` and coin tape `coins`. -/
private def searchCandidate (m : ℕ → ℕ) (core : ℕ → List Bool → List Bool)
    (evaluate : (ℕ × List Bool) → List Bool → List Bool)
    (n : ℕ) (y coins : List Bool) : List Bool :=
  evaluate (bestLength m core evaluate n y coins, wrappedImage n y) coins

private theorem searchCandidate_spec {m : ℕ → ℕ} {core : ℕ → List Bool → List Bool}
    {evaluate : (ℕ × List Bool) → List Bool → List Bool}
    {n M : ℕ} {y coins : List Bool} (hM : M ≤ m (n + 1))
    (h : core n ((evaluate (M, wrappedImage n y) coins).take (m n)) = y) :
    core n ((searchCandidate m core evaluate n y coins).take (m n)) = y := by
  have htry : tryLength m core evaluate n y coins M = true := by
    simp [tryLength, h]
  have hbest := Nat.findGreatest_spec
    (P := fun M => tryLength m core evaluate n y coins M = true) hM htry
  simpa [searchCandidate, bestLength, tryLength] using hbest

/-- The parameter-indexed inverter induced by an inverter for `reindex m core`. -/
private noncomputable def familyInverter (m : ℕ → ℕ) (core : ℕ → List Bool → List Bool)
    (c d : ℕ) (evaluate : (ℕ × List Bool) → List Bool → List Bool) : Inverter :=
  fun n y => searchCandidate m core evaluate n y <$> BitString.sampleList (coinBudget m c d n y)

private theorem isPPT_familyInverter {m : ℕ → ℕ} {core : ℕ → List Bool → List Bool}
    (hm : ComputableTidilyInPolyTime m encUnary encUnary)
    (hcore : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => core p.1 p.2)
      (encPair encUnary encBits) encBits)
    {c d : ℕ} {evaluate : (ℕ × List Bool) → List Bool → List Bool}
    (heval : ComputableTidilyInPolyTime (fun p : (ℕ × List Bool) × List Bool => evaluate p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBits) :
    IsPPT encBits (familyInverter m core c d evaluate) := by
  apply IsPPTOn.isPPT
  let E1 := encPair encUnary encBits
  let E2 := encPair E1 encBits
  let E3 := encPair E2 encUnary
  have hwrap : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool => wrappedImage p.1 p.2) E1 encBits :=
    ComputableTidilyInPolyTime.of_enc_eq ComputableTidilyInPolyTime.id' fun _ => rfl
  have hm_succ : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => m (p.1 + 1)) E1 encUnary := by
    fun_prop
  have hbudget : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool => coinBudget m c d p.1 p.2) E1 encUnary := by
    unfold coinBudget
    have hlen := (ComputableTidilyInPolyTime.encoding_length encBits).comp hwrap
    fun_prop
  have htry : ComputableTidilyInPolyTime
      (fun q : ((ℕ × List Bool) × List Bool) × ℕ =>
        decide (tryLength m core evaluate q.1.1.1 q.1.1.2 q.1.2 q.2 = true))
      E3 encBool := by
    simp only [tryLength]
    have hn : ComputableTidilyInPolyTime (fun q : ((ℕ × List Bool) × List Bool) × ℕ => q.1.1.1)
        E3 encUnary := (ComputableTidilyInPolyTime.fst _ _).fst'.fst'
    have hy : ComputableTidilyInPolyTime (fun q : ((ℕ × List Bool) × List Bool) × ℕ => q.1.1.2)
        E3 encBits := (ComputableTidilyInPolyTime.fst _ _).fst'.snd'
    have hcoins : ComputableTidilyInPolyTime (fun q : ((ℕ × List Bool) × List Bool) × ℕ => q.1.2)
        E3 encBits := (ComputableTidilyInPolyTime.fst _ _).snd'
    have hM : ComputableTidilyInPolyTime (fun q : ((ℕ × List Bool) × List Bool) × ℕ => q.2)
        E3 encUnary := ComputableTidilyInPolyTime.snd _ _
    have hw : ComputableTidilyInPolyTime
        (fun q : ((ℕ × List Bool) × List Bool) × ℕ => wrappedImage q.1.1.1 q.1.1.2)
        E3 encBits := hwrap.comp (ComputableTidilyInPolyTime.fst _ _).fst'
    have hev : ComputableTidilyInPolyTime
        (fun q : ((ℕ × List Bool) × List Bool) × ℕ =>
          evaluate (q.2, wrappedImage q.1.1.1 q.1.1.2) q.1.2)
        E3 encBits := heval.comp ((hM.prod hw).prod hcoins)
    have htk : ComputableTidilyInPolyTime
        (fun q : ((ℕ × List Bool) × List Bool) × ℕ =>
          (evaluate (q.2, wrappedImage q.1.1.1 q.1.1.2) q.1.2).take (m q.1.1.1))
        E3 encBits := ComputableTidilyInPolyTime.bitsTakeWithInput hev (hm.comp hn)
    have hcr : ComputableTidilyInPolyTime
        (fun q : ((ℕ × List Bool) × List Bool) × ℕ =>
          core q.1.1.1 ((evaluate (q.2, wrappedImage q.1.1.1 q.1.1.2) q.1.2).take (m q.1.1.1)))
        E3 encBits := hcore.comp (hn.prod htk)
    exact hcr.beq hy
  have hbest : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × List Bool =>
        bestLength m core evaluate p.1.1 p.1.2 p.2) E2 encUnary :=
    (ComputableInPolyTime.findGreatest
      (hm_succ.comp (ComputableTidilyInPolyTime.fst _ _)).computableInPolyTime
      htry.computableInPolyTime).tidy
  have hsearch : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × List Bool =>
        searchCandidate m core evaluate p.1.1 p.1.2 p.2) E2 encBits := by
    unfold searchCandidate
    have hw := hwrap.comp (ComputableTidilyInPolyTime.fst E1 encBits)
    have hcoins := ComputableTidilyInPolyTime.snd E1 encBits
    exact heval.comp ((hbest.prod hw).prod hcoins)
  exact IsPPTOn.map_with (ComputableInPolyTime.of_tidy hbudget).sampleList (.of_tidy hsearch)

/-- **Fundamental schedule-reindexing reduction
(`OneWayReindex.exists_familyInverter_inversion_le`).**
For any uniform strict PPT inverter `adversary` against `reindex m core`, there exists a uniform
strict PPT inverter `familyAdv` against `familyInversionGame m core` such that for every input
length `M ≥ m 0`, the inversion probability of `adversary` at length `M` is at most the inversion
probability of `familyAdv` at parameter `GeneratorReindex.parameter m M`. -/
theorem exists_familyInverter_inversion_le {m : ℕ → ℕ} {core : ℕ → List Bool → List Bool}
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hge : ∀ n, n + 1 ≤ m n)
    (hcore : ComputableInPolyTime (fun p : ℕ × List Bool => core p.1 p.2)
      (encPair encUnary encBits) encBits)
    (adversary : Inverter) (hPPT : IsPPT encBits adversary) :
    ∃ familyAdv : Inverter, IsPPT encBits familyAdv ∧
      ∀ {M : ℕ}, m 0 ≤ M →
        Game.succProbability (ProbComp.eval (inversionGame (reindex m core) adversary M)) ≤
          Game.succProbability (ProbComp.eval (familyInversionGame m core familyAdv
            (GeneratorReindex.parameter m M))) := by
  obtain ⟨c, d, evaluate, heval, _, hlaw⟩ := hPPT.on.exists_total_seeded_evaluator
  refine ⟨familyInverter m core c d evaluate, isPPT_familyInverter hm.tidy hcore.tidy heval,
    fun {M} hM0 => ?_⟩
  let n := GeneratorReindex.parameter m M
  have hfits : m n ≤ M := GeneratorReindex.parameter_fits hM0
  have hlt : M < m (n + 1) := GeneratorReindex.lt_length_succ_parameter hge M
  apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
  have hlhs : ProbComp.eval (inversionGame (reindex m core) adversary M) =
      (BitString.uniformList (m n)).bind (fun x₀ =>
        (ProbComp.eval (adversary M (wrappedImage n (core n x₀)))).map fun candidate =>
          reindex m core candidate == wrappedImage n (core n x₀)) := by
    have h1 : ProbComp.eval (inversionGame (reindex m core) adversary M) =
        ((BitString.uniformList M).map (List.take (m n))).bind (fun x₀ =>
          (ProbComp.eval (adversary M (wrappedImage n (core n x₀)))).map fun candidate =>
            reindex m core candidate == wrappedImage n (core n x₀)) := by
      rw [PMF.bind_map]
      simp only [inversionGame, ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure,
        PMF.map]
      apply PMF.bind_congr_on_support
      intro input hinput
      have hlen : input.length = M := BitString.length_of_mem_support_uniformList hinput
      simp [Function.comp_def, reindex, hlen, n]
    rwa [BitString.uniformList_take hfits] at h1
  have hrhs : ProbComp.eval (familyInversionGame m core (familyInverter m core c d evaluate) n) =
      (BitString.uniformList (m n)).bind (fun x₀ =>
        (BitString.uniformList (coinBudget m c d n (core n x₀))).map fun coins =>
          core n ((searchCandidate m core evaluate n (core n x₀) coins).take (m n)) ==
            core n x₀) := by
    simp [familyInversionGame, familyInverter, PMF.map]
  rw [hlhs, hrhs]
  apply PMF.bind_apply_mono_on_support _ true
  intro x₀ _
  set y := core n x₀
  have hlaw_M := hlaw (M, wrappedImage n y) (coinBudget m c d n y)
    (le_coinBudget m c d y hlt.le)
  rw [hlaw_M, PMF.map_comp]
  apply PMF.bind_apply_mono_on_support _ true
  intro coins _
  simp only [Function.comp_apply, PMF.pure_apply]
  by_cases h : reindex m core (evaluate (M, wrappedImage n y) coins) == wrappedImage n y
  · have heq : reindex m core (evaluate (M, wrappedImage n y) coins) = wrappedImage n y :=
      beq_iff_eq.mp h
    simp only [reindex, wrappedImage_inj] at heq
    obtain ⟨hn_eq, hcore_eq⟩ := heq
    rw [hn_eq] at hcore_eq
    have hspec := searchCandidate_spec hlt.le hcore_eq
    simp [h, hspec]
  · simp [h]

/-- **Weak one-wayness under schedule reindexing
(library generalization of the padding trick in
[Liu and Pass, Proof of Theorem 4.1, §4, p. 10 of `arXiv:2009.11514v1`][LiuPass2020];
cf. [Goldreich, Vol. 1, §2.2.3, Proposition 2.2.3][Goldreich2001]).**
If a parameter-indexed family `core` on input lengths `m n` (with `m n ≥ n + 1`) satisfies the
weak one-way bound `≤ 1 - 1 / q(n)` in `familyInversionGame` for a positive polynomial `q`, then
`reindex m core` is a weak one-way function on all input lengths. -/
theorem weakOneWay {m : ℕ → ℕ} {core : ℕ → List Bool → List Bool}
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hge : ∀ n, n + 1 ≤ m n)
    (hcore : ComputableInPolyTime (fun p : ℕ × List Bool => core p.1 p.2)
      (encPair encUnary encBits) encBits)
    {q : Polynomial ℕ} (hq : ∀ n, 0 < q.eval n)
    (hweak : ∀ adversary : Inverter, IsPPT encBits adversary →
      ∀ᶠ n in atTop,
        (Game.succProbability (ProbComp.eval (familyInversionGame m core adversary n)) : ℝ) ≤
          1 - 1 / ((q.eval n : ℕ) : ℝ)) :
    WeakOneWay (reindex m core) := by
  refine WeakOneWay.of_le (computableInPolyTime_reindex hm hcore) hq
    fun adversary hPPT => ?_
  obtain ⟨familyAdv, hfamilyPPT, hred⟩ :=
    exists_familyInverter_inversion_le hm hge hcore adversary hPPT
  have hev := (GeneratorReindex.parameter_tendsto m).eventually (hweak familyAdv hfamilyPPT)
  filter_upwards [hev, eventually_ge_atTop (m 0)] with M hM hM0
  have h1 : (Game.succProbability
        (ProbComp.eval (inversionGame (reindex m core) adversary M)) : ℝ) ≤
      (Game.succProbability (ProbComp.eval (familyInversionGame m core familyAdv
        (GeneratorReindex.parameter m M))) : ℝ) := by
    exact_mod_cast hred hM0
  have h2 : (1 : ℝ) - 1 / ((q.eval (GeneratorReindex.parameter m M) : ℕ) : ℝ) ≤
      1 - 1 / ((q.eval M : ℕ) : ℝ) := by
    have hparam_le : q.eval (GeneratorReindex.parameter m M) ≤ q.eval M :=
      Polynomial.eval_mono q (GeneratorReindex.parameter_le m M)
    have hdiv : 1 / ((q.eval M : ℕ) : ℝ) ≤
        1 / ((q.eval (GeneratorReindex.parameter m M) : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (Nat.cast_pos.mpr (hq _)) (Nat.cast_le.mpr hparam_le)
    linarith
  exact (h1.trans hM).trans h2

/-- **Strong one-wayness under schedule reindexing
(library generalization of the padding trick in
[Liu and Pass, Proof of Theorem 4.1, §4, p. 10 of `arXiv:2009.11514v1`][LiuPass2020];
cf. [Goldreich, Vol. 1, §2.2.3, Proposition 2.2.3][Goldreich2001]).**
If every uniform strict PPT inverter has negligible success probability in
`familyInversionGame m core`, then `reindex m core` is a strong one-way function on all input
lengths. -/
theorem oneWay {m : ℕ → ℕ} {core : ℕ → List Bool → List Bool}
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hge : ∀ n, n + 1 ≤ m n)
    (hcore : ComputableInPolyTime (fun p : ℕ × List Bool => core p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hsecure : ∀ adversary : Inverter, IsPPT encBits adversary →
      Negligible (fun n =>
        Game.succProbability (ProbComp.eval (familyInversionGame m core adversary n)))) :
    OneWay (reindex m core) := by
  apply OneWay.of_inversion_negligible (computableInPolyTime_reindex hm hcore)
  intro adversary hPPT
  obtain ⟨familyAdv, hfamilyPPT, hred⟩ :=
    exists_familyInverter_inversion_le hm hge hcore adversary hPPT
  have hneg := hsecure familyAdv hfamilyPPT
  have hdecay := hneg.comp_of_polynomial_bound (GeneratorReindex.parameter_tendsto m)
    (hm.tidy.polynomiallyBounded.comp (PolynomiallyBounded.id.add (.const 1)))
    (Eventually.of_forall fun M => (GeneratorReindex.lt_length_succ_parameter hge M).le)
  apply negligible_of_eventually_le hdecay
  filter_upwards [eventually_ge_atTop (m 0)] with M hM0
  exact hred hM0

end OneWayReindex

end Cslib.Crypto
