/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.LocalTest
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Independent repetition of local tests

`LocalTest.repeatAll` runs a local test on `k` independent uniform random strings and accepts
when every trial accepts. It is another local test, with random strings `Fin k → R` and queries
`Fin k × Q`. Its acceptance probability is the `k`-th power of the original probability. In
particular, zero trials accept every proof, including when the original random-string type is
empty. These are elementary constructions on the existing local-test model.

## Main definitions

* `Cslib.PCP.LocalTest.repeatAll`: independent repetition with conjunction of the outcomes.

## Main results

* `Cslib.PCP.LocalTest.passes_repeatAll`: all trials must pass.
* `Cslib.PCP.LocalTest.acceptProb_repeatAll`: exact acceptance probability of independent trials.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.PCP.LocalTest

open Finset
open scoped BigOperators

variable {P R Q Γ : Type*} (T : LocalTest P R Q Γ)

/-- Run `k` independent copies of `T` and accept exactly when every copy accepts. Uniform
sampling on `Fin k → R` supplies independent uniform strings to the trials. -/
def repeatAll (k : ℕ) : LocalTest P (Fin k → R) (Fin k × Q) Γ where
  query r iq := T.query (r iq.1) iq.2
  Accepts r a := ∀ i, T.Accepts (r i) fun q => a (i, q)

instance [∀ r a, Decidable (T.Accepts r a)] (k : ℕ) (r : Fin k → R)
    (a : Fin k × Q → Γ) : Decidable ((T.repeatAll k).Accepts r a) :=
  inferInstanceAs (Decidable (∀ i, T.Accepts (r i) fun q => a (i, q)))

/-- Repetition accepts a proof precisely when each of its trials accepts that proof. -/
@[simp]
theorem passes_repeatAll (k : ℕ) (π : P → Γ) (r : Fin k → R) :
    (T.repeatAll k).Passes π r ↔ ∀ i, T.Passes π (r i) :=
  Iff.rfl

/-- Independent repetition raises the acceptance probability to the number of trials. -/
theorem acceptProb_repeatAll [Fintype R] (k : ℕ) (π : P → Γ) :
    (T.repeatAll k).acceptProb π = T.acceptProb π ^ k := by
  classical
  simp only [acceptProb, passes_repeatAll]
  rw [Finset.expect_pow, Fintype.piFinset_univ]
  refine expect_congr rfl fun r _ => ?_
  rw [Fintype.prod_boole]
  split_ifs <;> rfl

end Cslib.PCP.LocalTest
