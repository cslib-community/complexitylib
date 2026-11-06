/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.ContractionCircuitCounting
import Complexity.Foundations.Data.Nat.SqrtLog.Budget
import Complexity.Foundations.Data.Nat.SqrtLog.Shifted

/-!
# The quantitative counting budget for circuit lower bounds

`ContractionCounting.exists_circuitSatCounter_sizeBudget` fixes one exact circuit counter and
constants `A, e, b` before the decoder overhead `D`. On a circuit with at most
`3 * (n * q(n) / (12 * (A + 1))) + D * (n + 1)` gates, where
`q(n) = Nat.sqrt (Nat.log 2 (n + 2))`, its time bound is at most
`2 ^ (n / 2)` times a polynomial in the circuit encoding length once
`q(n) ≥ 8 * A * (D + 1)` and `n ≥ 1`. Its space bound is polynomial throughout.

Here `n` is the input length of a prospective reduction, not the number of inputs of the
checker circuit. All divisions in the theorem are natural-number divisions. The existing
shifted-scale comparison permits a checker smaller than `n`: we take `A = 22 * A₀`, with
`A₀` from `exists_circuitSatCounter`. This fixed loss is independent of `D`; it avoids needing
to construct a padded circuit merely to apply a numerical inequality. `ComputableInO` retains
its fixed multiplicative machine constant, so `T` below is a certified asymptotic time bound,
not an exact number of transitions.

## The theoretical transfer

Corollary 1.4 of [OpenAI2026ETH] already states that some language in `E^NP` requires more
than `c n √log n` fan-in-two gates at infinitely many lengths, for some `c > 0`. Appendix C.1
(pp. 51–52) proves it using a quantitative version of Williams's witness-circuit argument
([Williams2010], Lemma 3.2 and Theorem 6.1). That appendix uses the local reduction of
Jahanjou–Miles–Viola and a unary hierarchy language. The following instead uses the standard
tableau variant from Williams's Theorem 6.1, with general inputs `x`, in the integer scale
of this library. The class separation itself is not proved in this module.

Fix any power overhead required by the machine simulations, then choose a nondeterministic
exponential-time language `H` with a time-hierarchy gap large enough to absorb it.
For `x` of length `n`, use a uniformly constructible succinct
3-CNF tableau `Φₓ`, satisfiable exactly when `x ∈ H`, padding unused clause indices with
tautologies. Its clause and variable indices have `O(n)` bits. Require a decoder circuit
with `O(n)` gates and a polynomial-time construction
of its code from `x`. A standard exponential-size tableau suffices: even a quadratic tableau
has only `O(n)`-bit indices, and its local constraints can be addressed with bit-field
operations. The linear gate bound and the uniform code construction are separate obligations.

Let `W(x, i)` be bit `i` of the lexicographically first satisfying assignment of `Φₓ`, with
zero as the value when no assignment exists. Fixed-width framing puts these inputs at
length `N = d * n` for a fixed positive integer `d`; unused encodings can be rejected.
Writing `Φₓ` explicitly and making exponentially many NP prefix-extension queries decides
`W` in deterministic exponential time with an NP oracle, so `W ∈ E^NP`.

Suppose, towards a contradiction, that `W` has circuits of size at most
`s(n) = n * q(n) / (12 * (A + 1))` at all sufficiently large lengths `d * n`. On input `x`,
guess a circuit of that size and hardwire its `x` input. Use three copies to obtain the
purported assignment values of a decoded clause. The circuit output is true exactly when
that clause is violated; decoding the clause, handling signs and combining the three values
cost at most `D * (n + 1)` further gates. Its total size is therefore at most
`3 * s(n) + D * (n + 1)`, retaining the separate coefficient of the guessed circuit.
Choose one fixed complete fan-in-two Boolean gate signature throughout, such as the signature
of all binary Boolean gates. Translating gate bases would require an additional fixed size
factor. The counter is available for every finite signature.

Accept the guessed circuit exactly when this checker has zero satisfying inputs. If `x ∈ H`,
the circuit for `W` supplies an accepting guess. If `x ∉ H`, every guessed circuit describes
an assignment violating some clause, so every guess is rejected. Soundness does not require
certifying that the guessed circuit computes the canonical witness.

The theorem below bounds the counting exponent by `n / 2`. The guessed and constructed
circuits have polynomial encoding length in `n`, so guessing, constructing and running the
counter cost `poly(n) * 2 ^ (n / 2)`, including its fixed multiplicative constant. This is
eventually at most `2 ^ n`. Finitely many smaller lengths can be hardwired, contradicting
the chosen hierarchy gap. If translating between machine conventions costs a fixed power,
choose the hierarchy gap before this argument to absorb that power.

Consequently the witness circuit complexity exceeds `s(n)` for infinitely many `n`.
`Nat.frequently_mul_sqrt_logb_div_lt`, in `Foundations.Data.Nat.SqrtLog.LowerBound`, converts
this integer lower bound at lengths `d * n` into the conventional real-valued bound with
the explicit coefficient `ε = 1 / (24 * (A + 1) * d)` for `log₂`. The overhead `D` affects
only the starting length: `n + 2 ≥ 2 ^ ((8 * A * (D + 1)) ^ 2)` suffices for the counting
budget. No numerical value for the counter constant `A` or framing constant `d` is claimed.
The quantifier order is counter and `A`, then fixed reduction and `d, D`, then `ε`, then
the hypothetical small circuits. This gives some positive `ε`, not every coefficient or
an almost-everywhere lower bound.

This file proves the counter application and uses checked integer arithmetic. The rescaling
inequality and polynomial-time computation of `s(n)` are proved in their respective
`SqrtLog.LowerBound` and `PolyTime.Nat.SqrtLog.Budget` modules. The full formal separation
still requires the hierarchy language, framing and preparation of the witness language, uniform
decoder/checker construction, and nondeterministic simulation to be connected. The existing
`preimage_witnessBit_mem_ENP` supplies a generic witness-bit bridge, using the canonical SAT
self-reduction assignment in place of the lexicographically first one; either choice suffices.
These remaining connections are part of #1539.

## Main results

* `ContractionCounting.exists_circuitSatCounter_sizeBudget`: one correct circuit counter with
  the quantitative time bound for three guessed circuits and linear decoding overhead.

## References

* [OpenAI2026ETH], Corollary 1.4 (p. 3), Appendix C.1 (pp. 51–52), source revision
  `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.
* [Williams2010], Lemma 3.2 (p. 11), Theorem 6.1 (p. 20), author's May 4, 2010 version.
-/

public section

namespace Cslib.Complexity.ContractionCounting

open Cslib.Circuits Cslib.Circuits.Frontier Turing.MultiTapeTM

/-- **A superlinear circuit-size budget for one fixed counter.** The counter and its constants
are chosen before the decoder overhead `D`. The reduction length `n` is independent of the
number of circuit inputs. The time bound includes the polynomial in the encoding length;
the theorem does not assert a complexity-class separation. -/
theorem exists_circuitSatCounter_sizeBudget {σ : Signature} [Finite σ.Op]
    (encOp : σ.Op ↪ List Bool) (I : Interpretation σ Bool) :
    ∃ (count T S : (Σ k, Circuit σ k 1) → ℕ) (A e b : ℕ),
      (∀ c, count c = c.2.satCount I) ∧
      ComputableInO count (Circuit.encCircuit encOp 1) encNat T S ∧
      (∀ c, S c = ((Circuit.encCircuit encOp 1 c).length + 1) ^ b) ∧
      ∀ D n : ℕ, 1 ≤ n → 8 * A * (D + 1) ≤ Nat.sqrt (Nat.log 2 (n + 2)) →
        ∀ c : Σ k, Circuit σ k 1,
          c.2.size ≤ 3 * (n * Nat.sqrt (Nat.log 2 (n + 2)) / (12 * (A + 1))) +
            D * (n + 1) →
          T c ≤ 2 ^ (n / 2) * ((Circuit.encCircuit encOp 1 c).length + 1) ^ e := by
  obtain ⟨count, A₀, e, b, hspec, hinO⟩ := exists_circuitSatCounter encOp I
  let A := A₀ * 22
  refine ⟨count, _, _, A, e, b, hspec, hinO, fun _ => rfl, ?_⟩
  intro D n hn hq c hc
  let M := 3 * (n * Nat.sqrt (Nat.log 2 (n + 2)) / (12 * (A + 1))) + D * (n + 1) + n
  have hnM : n ≤ M := Nat.le_add_left _ _
  have hcM : c.2.size ≤ 1 * M + 1 := by dsimp [M]; omega
  have hscale : A₀ * (c.2.size + 1) / Nat.sqrt (Nat.log 2 (c.2.size + 2)) ≤
      A * (M + 1) / Nat.sqrt (Nat.log 2 (M + 2)) :=
    Nat.mul_succ_div_sqrt_log_two_le (A := A₀) (C := 1) (x := M) hcM
  have hbudget : 2 * (A * (M + 1) / Nat.sqrt (Nat.log 2 (M + 2))) ≤ n :=
    Nat.two_mul_mul_succ_div_sqrt_log_two_le (A := A) (D := D) (n := n) (M := M)
      hn hnM (le_refl M) hq
  have hexponent : A₀ * (c.2.size + 1) / Nat.sqrt (Nat.log 2 (c.2.size + 2)) ≤ n / 2 := by
    exact hscale.trans ((Nat.le_div_iff_mul_le (by decide)).2 (by
      simpa only [Nat.mul_comm] using hbudget))
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hexponent)

end Cslib.Complexity.ContractionCounting
