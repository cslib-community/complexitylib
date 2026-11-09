/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.XorLemma

/-!
# Average-case hardness

A Boolean function `f` on `n` bits is *average-case hard* for size `s` (`IsAverageCaseHard f s`)
when every Boolean function of De Morgan circuit complexity at most `s` agrees with `f` on at most
a `1 / 2 + 1 / s` fraction of the inputs. This is the hardness `H_avg(f) ≥ s` of
[Arora and Barak, Chapter 19][AroraBarak09], except that the agreement bound is non-strict,
as in the conclusion of Yao's XOR lemma (`Cslib.Circuits.Boolean.card_eq_xorPower_div_le`). The
non-strict form is the weaker hypothesis; arguments that need a strict bound, such as the analysis
of the Nisan–Wigderson generator, obtain it from a little slack in the size
(`IsAverageCaseHard.div_lt`).

The XOR lemma turns mild hardness into average-case hardness
(`isAverageCaseHard_xorPower`): if every small circuit errs on a `δ` fraction of the inputs of
`f`, then the `k`-fold XOR of `f` is average-case hard for size `s` as soon as
`ε + (1 / 2 - ε) (1 - δ) ^ k ≤ 1 / s`. Everything is nonuniform, with sizes counted as in
`Cslib.Circuits.complexity`.

## Main definitions

* `Cslib.Circuits.Boolean.IsAverageCaseHard`: average-case hardness for a size.

## Main results

* `Cslib.Circuits.Boolean.IsAverageCaseHard.mono`: hardness for a size gives hardness for every
  smaller positive size.
* `Cslib.Circuits.Boolean.IsAverageCaseHard.div_lt`: with slack, the agreement bound is strict.
* `Cslib.Circuits.Boolean.isAverageCaseHard_xorPower`: Yao's XOR lemma in terms of average-case
  hardness.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
* [A. C. Yao, *Theory and applications of trapdoor functions*][Yao1982]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset

variable {n : ℕ}

/-- `f` is *average-case hard* for size `s`: every Boolean function of De Morgan circuit
complexity at most `s` agrees with `f` on at most a `1 / 2 + 1 / s` fraction of the inputs. -/
def IsAverageCaseHard (f : BooleanFunction n) (s : ℕ) : Prop :=
  ∀ g : BooleanFunction n, complexity interpretation (single g) ≤ s →
    (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 / 2 + 1 / s

namespace IsAverageCaseHard

variable {f : BooleanFunction n} {s s' : ℕ}

/-- Average-case hardness for a size gives average-case hardness for every smaller positive size:
there are fewer circuits, and the bound `1 / 2 + 1 / s'` is weaker. -/
theorem mono (hf : IsAverageCaseHard f s) (hs' : 0 < s') (h : s' ≤ s) :
    IsAverageCaseHard f s' := fun g hg =>
  (hf g (hg.trans h)).trans (by gcongr)

/-- **Slack.** If `f` is average-case hard for size `s` and `1 / s < δ`, then every Boolean
function of complexity at most `s` agrees with `f` on less than a `1 / 2 + δ` fraction of the
inputs. -/
theorem div_lt (hf : IsAverageCaseHard f s) {δ : ℝ} (hδ : 1 / (s : ℝ) < δ)
    {g : BooleanFunction n} (hg : complexity interpretation (single g) ≤ s) :
    (#{x | g x = f x} : ℝ) / 2 ^ n < 1 / 2 + δ := by
  have := hf g hg
  linarith

end IsAverageCaseHard

/-- **Yao's XOR lemma for average-case hardness** [Yao1982]. Let `0 < δ`, `0 < ε ≤ 1 / 2`, and
let `T` be a number of rounds with `1 ≤ 3 ε² δ² T`. If every Boolean function of complexity at
most `T (s + 3) + (2 + T (2 (T + 2)))` agrees with `f` on at most a `1 - δ` fraction of the
inputs, and `ε + (1 / 2 - ε) (1 - δ) ^ k ≤ 1 / s`, then the `k`-fold XOR of `f` is average-case
hard for size `s`. -/
theorem isAverageCaseHard_xorPower {f : BooleanFunction n} {s T : ℕ} {δ ε : ℝ} (hδ : 0 < δ)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hT : 1 ≤ 3 * ε ^ 2 * δ ^ 2 * T)
    (hf : ∀ g : BooleanFunction n,
      complexity interpretation (single g) ≤ T * (s + 3) + (2 + T * (2 * (T + 2))) →
        (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 - δ)
    {k : ℕ} (hk : ε + (1 / 2 - ε) * (1 - δ) ^ k ≤ 1 / s) :
    IsAverageCaseHard (xorPower f k) s := fun _ hg => by
  have := card_eq_xorPower_div_le hδ hε hε' hT hf k hg
  linarith

end Cslib.Circuits.Boolean
