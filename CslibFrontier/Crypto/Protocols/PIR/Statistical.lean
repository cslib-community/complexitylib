/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.Basic
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import Mathlib.Tactic.NormNum

/-!
# Statistical privacy and bounded-error recovery

`PIR.Basic` states privacy and correctness as exact equalities of laws. Lower bounds for private
information retrieval and locally decodable codes
[Goldreich, Karloff, Schulman and Trevisan, Section 7][GoldreichKarloffSchulmanTrevisan2006] also
use the relaxations of both notions:

* **`δ`-statistical privacy (`Scheme.IsStatPrivate δ`).** For every server, the query laws for any
  two indices are within statistical distance `δ` (`Probability.CloseTo`). At `δ = 0` this is
  perfect privacy (`Scheme.IsPrivate.isStatPrivate_zero`).
* **Closeness to a reference index (`Scheme.IsStatPrivateAt i₀ δ`).** For every server, the query
  law for each index is within `δ` of the law for `i₀`. The GKST decoder only uses this weaker
  form, and `δ`-statistical privacy gives it at every reference index
  (`Scheme.IsStatPrivate.isStatPrivateAt`).
* **Recovery with advantage `ε` (`Scheme.Recovers ε`).** On every database and index, a scheme for
  bits outputs the right bit with probability at least `1 / 2 + ε`. A perfectly correct scheme
  recovers with advantage `1 / 2` (`Scheme.IsCorrect.recovers`).

## Main definitions

* `Cslib.Crypto.Protocols.PIR.Scheme.IsStatPrivate`: `δ`-statistical privacy.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsStatPrivateAt`: query laws `δ`-close to those at `i₀`.
* `Cslib.Crypto.Protocols.PIR.Scheme.Recovers`: recovery with advantage `ε`.

## Main results

* `Cslib.Crypto.Protocols.PIR.Scheme.IsPrivate.isStatPrivate_zero`: perfect privacy is
  `0`-statistical privacy.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsStatPrivate.isStatPrivateAt`: pairwise closeness gives
  closeness to every reference index.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.recovers`: perfect correctness is recovery with
  advantage `1 / 2`.

## References

* [O. Goldreich, H. Karloff, L. J. Schulman, L. Trevisan, *Lower bounds for linear locally
  decodable codes and private information retrieval*][GoldreichKarloffSchulmanTrevisan2006],
  Section 7.1
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.PIR.Scheme

open Probability

variable {ι S R Q A β : Type}

/-- `δ`-statistical privacy: for every server, the query laws for any two indices are within
statistical distance `δ`. -/
def IsStatPrivate (P : Scheme ι S R Q A β) (δ : ℝ) : Prop :=
  ∀ s i i', CloseTo (ProbComp.eval (P.serverQuery s i)) (ProbComp.eval (P.serverQuery s i'))
    (ENNReal.ofReal δ)

/-- For every server, the query law for each index is within statistical distance `δ` of the law
for the reference index `i₀`. -/
def IsStatPrivateAt (P : Scheme ι S R Q A β) (i₀ : ι) (δ : ℝ) : Prop :=
  ∀ s i, CloseTo (ProbComp.eval (P.serverQuery s i)) (ProbComp.eval (P.serverQuery s i₀))
    (ENNReal.ofReal δ)

/-- Recovery with advantage `ε`: on every database and index, the user outputs the right bit with
probability at least `1 / 2 + ε`. -/
def Recovers (P : Scheme ι S R Q A) (ε : ℝ) : Prop :=
  ∀ x i, 1 / 2 + ε ≤ (ProbComp.eval (P.run x i) (x i)).toReal

/-- `δ`-statistical privacy gives closeness to every reference index. -/
theorem IsStatPrivate.isStatPrivateAt {P : Scheme ι S R Q A β} {δ : ℝ} (h : P.IsStatPrivate δ)
    (i₀ : ι) : P.IsStatPrivateAt i₀ δ :=
  fun s i => h s i i₀

/-- Perfect privacy is `0`-statistical privacy. -/
theorem IsPrivate.isStatPrivate_zero {P : Scheme ι S R Q A β} (h : P.IsPrivate) :
    P.IsStatPrivate 0 := fun s i i' => by
  rw [ENNReal.ofReal_zero, h.eval_serverQuery_eq s i i']
  exact CloseTo.refl _

/-- A perfectly correct scheme recovers with advantage `1 / 2`. -/
theorem IsCorrect.recovers {P : Scheme ι S R Q A} (h : P.IsCorrect) : P.Recovers (1 / 2) :=
  fun x i => by
    rw [P.isCorrect_iff_eval_run.mp h x i, PMF.pure_apply_self, ENNReal.toReal_one]
    norm_num

end Cslib.Crypto.Protocols.PIR.Scheme
