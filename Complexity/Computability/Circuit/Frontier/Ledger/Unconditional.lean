/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.Gaussian
public import Complexity.Computability.Circuit.Frontier.Layouts.General
public import Complexity.Computability.Circuit.Frontier.Ledger.LowerBound

/-!
# Unconditional frontier lower bounds with gates of unbounded fan-in

The frontier lower bounds with a ledger (`Cslib.Circuits.Frontier.eventually_lt_mul_card_of_ledger`)
and with aggregate gates (`Cslib.Circuits.Frontier.eventually_lt_mul_card_of_aggregates`) are
conditional on the layout hypothesis `LayoutBound (r + 1) A`. Spanning trees prove it with
coefficient `A = 1` in every degree (`Cslib.Circuits.Frontier.layoutBound_one`), and median
edge-score layouts prove it with `A = 2p` in degree three
(`Cslib.Circuits.Frontier.layoutBound_gaussian`), which removes the hypothesis.

Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over a finite alphabet `U` with at least two
symbols, with `log K_n = o(n)` and `n log |U| - log |S_n| = o(n)`, and let `β(n) = o(n)`. Then for
every fan-in `r ≥ 2`, every `ε > 0` and all large `n`, every circuit deciding `S_n`, over any
basis and interpretation on `U`, whose gates have fan-in at most `r` except for special gates of
any fan-in with a ledger in a monoid `M` with `log |M| ≤ β(n)`, has `s` ordinary inner gates with

`(r - 1) s > (2 - ε) n`,

and at fan-in `r = 2`,

`s > (L - ε) n` with `L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`.

For instance, `o(n)` gates of unbounded fan-in computing AND, OR, parity, or counts modulo a
fixed `m` cost nothing in the leading term.

## Main results

* `Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_card_of_ledger`: with a ledger.
* `Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_card_of_aggregates`: with aggregate
  gates.
* `Cslib.Circuits.Frontier.eventually_gaussian_sub_mul_lt_card_of_ledger`,
  `eventually_gaussian_sub_mul_lt_card_of_aggregates`: the Gaussian `(L - ε) n` bounds at ordinary
  fan-in two.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Filter Asymptotics

universe u v w

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- **The unconditional frontier lower bound with a ledger.** Let `r ≥ 2`, let `S_n ⊆ U^n` be
`K_n`-rectangle-free sets over a finite alphabet `U` with at least two symbols, with
`log K_n = o(n)` and `n log |U| - log |S_n| = o(n)`, and let `β(n) = o(n)`. Then for every
`ε > 0` and all large `n`, every circuit deciding `S_n`, over any basis and interpretation on
`U`, whose gates have fan-in at most `r` except for special gates of any fan-in with a ledger in a
finite commutative monoid `M` with `log |M| ≤ β(n)`, has `s` ordinary inner gates with
`(r - 1) s > (2 - ε) n`. -/
theorem eventually_two_sub_mul_lt_mul_card_of_ledger {r : ℕ} (hr : 2 ≤ r)
    (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (M : Type w)
      [CommMonoid M] [Finite M],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ r) →
        Ledger special c.program I M → Real.log (Nat.card M) ≤ β n → c.Decides I Acc (S n) →
          (2 - ε) * n < (r - 1) * (c.program.innerGates.filter fun g => ¬special g).card := by
  simpa only [div_one, one_add_one_eq_two] using
    eventually_lt_mul_card_of_ledger.{u, v, w} hr one_pos (layoutBound_one (r + 1)) hSK hβ hε

/-- **The unconditional frontier lower bound with aggregate gates.** Under the hypotheses of
`eventually_two_sub_mul_lt_mul_card_of_ledger`, for every `ε > 0` and all large `n`, every circuit
deciding `S_n`, over any basis and interpretation on `U`, whose gates have fan-in at most `r`
except for `k` special gates of any fan-in that aggregate in a finite commutative monoid `T`, with
`k log |T| ≤ β(n)`, has `s` ordinary inner gates with `(r - 1) s > (2 - ε) n`. -/
theorem eventually_two_sub_mul_lt_mul_card_of_aggregates {r : ℕ} (hr : 2 ≤ r)
    (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (T : Type w)
      [CommMonoid T] [Finite T],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ r) →
        (∀ g, special g → Aggregates (I (c.program.lines g).op) T) →
        Nat.card {g // special g} * Real.log (Nat.card T) ≤ β n →
        c.Decides I Acc (S n) →
          (2 - ε) * n < (r - 1) * (c.program.innerGates.filter fun g => ¬special g).card := by
  simpa only [div_one, one_add_one_eq_two] using
    eventually_lt_mul_card_of_aggregates.{u, v, w} hr one_pos (layoutBound_one (r + 1)) hSK hβ hε

/-- **The Gaussian frontier lower bound with a ledger, at ordinary fan-in two.** Under the
hypotheses of `eventually_two_sub_mul_lt_mul_card_of_ledger`, for every `ε > 0` and all large `n`,
every circuit deciding `S_n`, over any basis and interpretation on `U`, whose gates have fan-in at
most two except for special gates of any fan-in with a ledger in a finite commutative monoid `M`
with `log |M| ≤ β(n)`, has more than `(L - ε) n` ordinary inner gates, where
`L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem eventually_gaussian_sub_mul_lt_card_of_ledger
    (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (M : Type w)
      [CommMonoid M] [Finite M],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ 2) →
        Ledger special c.program I M → Real.log (Nat.card M) ≤ β n → c.Decides I Acc (S n) →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
            (c.program.innerGates.filter fun g => ¬special g).card := by
  have h := eventually_lt_mul_card_of_ledger.{u, v, w} (r := 2) le_rfl
    (mul_pos two_pos Gaussian.gaussianCoefficient_pos) layoutBound_gaussian hSK hβ hε
  rw [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h
  filter_upwards [h] with n hn σ I Acc c special _ M _ _ hfan hled hM hdec
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using
    hn σ I Acc c special M hfan hled hM hdec

/-- **The Gaussian frontier lower bound with aggregate gates, at ordinary fan-in two.** Under the
hypotheses of `eventually_gaussian_sub_mul_lt_card_of_ledger`, for every `ε > 0` and all large `n`,
every circuit deciding `S_n`, over any basis and interpretation on `U`, whose gates have fan-in at
most two except for `k` special gates of any fan-in that aggregate in a finite commutative monoid
`T`, with `k log |T| ≤ β(n)`, has more than `(L - ε) n` ordinary inner gates. -/
theorem eventually_gaussian_sub_mul_lt_card_of_aggregates
    (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (T : Type w)
      [CommMonoid T] [Finite T],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ 2) →
        (∀ g, special g → Aggregates (I (c.program.lines g).op) T) →
        Nat.card {g // special g} * Real.log (Nat.card T) ≤ β n →
        c.Decides I Acc (S n) →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
            (c.program.innerGates.filter fun g => ¬special g).card := by
  have h := eventually_lt_mul_card_of_aggregates.{u, v, w} (r := 2) le_rfl
    (mul_pos two_pos Gaussian.gaussianCoefficient_pos) layoutBound_gaussian hSK hβ hε
  rw [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h
  filter_upwards [h] with n hn σ I Acc c special _ T _ _ hfan hagg hT hdec
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using
    hn σ I Acc c special T hfan hagg hT hdec

end Cslib.Circuits.Frontier
