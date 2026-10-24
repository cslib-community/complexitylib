/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Nondeterminism
public import Complexity.Computability.Circuit.Boolean.AltFormula
public import Complexity.Computability.Circuit.Monotone.Basic
public import Complexity.Computability.Circuit.SourceComplexity

/-!
# Conondeterministic AND complexity

Minimize the native AND cost of a Boolean verifier over every finite number of auxiliary bits
and every verifier whose universal quantification is the target. Both polarities of every
primary and auxiliary bit are supplied for free. Constants and OR gates also have zero cost.
This is a circuit-size measure; it is not verifier runtime or a bound on auxiliary bit count.

## Main definitions

* `Cslib.Circuits.Boolean.econondeterministicAndComplexity`: minimum universal-verifier AND cost.

## Main results

* `Cslib.Circuits.Boolean.econondeterministicAndComplexity_le_cost`: any verifier gives a bound.
* `Cslib.Circuits.Boolean.le_econondeterministicAndComplexity_iff`: lower bounds hold precisely
  when they hold for every verifier circuit and every number of auxiliary bits.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*][CavalarOliveira2025], Theorem 45, credited there to Karchmer.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {n : ℕ}

/-- Minimum AND cost over all universally quantified verifiers. Constants, OR gates and
positive/negative input literals are free; the auxiliary count is unrestricted. -/
noncomputable def econondeterministicAndComplexity (f : BooleanFunction n) : ℕ∞ :=
  ⨅ a, ⨅ g : {g : BooleanFunction (n + a) // forallGuess g = f},
    ecomplexityFrom Monotone.interpretation Monotone.andCost (single g.val) AltFormula.literals

/-- A fixed universal verifier bounds the minimum over all verifier functions. -/
private theorem econondeterministicAndComplexity_le_ecomplexityFrom {f : BooleanFunction n} {a : ℕ}
    (g : BooleanFunction (n + a)) (hg : forallGuess g = f) :
    econondeterministicAndComplexity f ≤
      ecomplexityFrom Monotone.interpretation Monotone.andCost (single g) AltFormula.literals := by
  unfold econondeterministicAndComplexity
  apply iInf_le_of_le a
  exact iInf_le _ (⟨g, hg⟩ : {g : BooleanFunction (n + a) // forallGuess g = f})

/-- Every concrete universal verifier bounds conondeterministic AND complexity. -/
theorem econondeterministicAndComplexity_le_cost {f : BooleanFunction n} {a : ℕ}
    (g : BooleanFunction (n + a)) (hg : forallGuess g = f)
    (c : Circuit Monotone.signature ((n + a) + (n + a)) 1)
    (hc : c.ComputesFrom Monotone.interpretation (single g) AltFormula.literals) :
    econondeterministicAndComplexity f ≤ c.program.cost Monotone.andCost :=
  (econondeterministicAndComplexity_le_ecomplexityFrom g hg).trans
    (ecomplexityFrom_le_of_computesFrom c hc)

/-- Lower bounds must hold for every auxiliary count and every implementing verifier circuit. -/
theorem le_econondeterministicAndComplexity_iff {f : BooleanFunction n} {k : ℕ∞} :
    k ≤ econondeterministicAndComplexity f ↔
      ∀ a, ∀ g : BooleanFunction (n + a), forallGuess g = f →
        ∀ c : Circuit Monotone.signature ((n + a) + (n + a)) 1,
          c.ComputesFrom Monotone.interpretation (single g) AltFormula.literals →
          k ≤ c.program.cost Monotone.andCost := by
  simp only [econondeterministicAndComplexity, le_iInf_iff, Subtype.forall,
    le_ecomplexityFrom_iff]

end Cslib.Circuits.Boolean
