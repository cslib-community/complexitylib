/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Logics.Propositional.CNF.Johnson.PolyTime
public import CslibFrontier.Logics.Propositional.CNF.UnsatVal

/-!
# Polynomial-time approximation of MAX-SAT by Johnson's algorithm

Johnson's algorithm (`Cslib.Logic.PL.johnson`) on formulas over variables numbered by natural
numbers, encoded as for `Cslib.Complexity.SAT`, is polynomial-time
(`Cslib.Complexity.computableInPolyTime_johnson_encCNF`); its output is the list of variables it
sets to `true`. Hence one polynomial-time algorithm satisfies, on every formula whose clauses
have at least `k` distinct literals, at least the proportion `1 - 2 ^ -k` of the clauses, and at
least `1 - 2 ^ -k` times the largest proportion an assignment satisfies, `1 - unsatVal`
(`Cslib.Complexity.exists_polyTime_maxSAT_approx`) [Johnson1974]
[Williamson and Shmoys, Sections 5.1–5.2][WilliamsonShmoys2011]. For MAX-E3SAT with three
distinct variables per clause this is a `7 / 8`-approximation
(`Cslib.Complexity.exists_polyTime_maxExactThreeSAT_approx`), the constructive counterpart of
`Cslib.Logic.PL.CNF.IsExactThreeDistinct.unsatVal_le_one_eighth`. Håstad showed that `7 / 8` is
optimal unless `P = NP` [Hastad2001]; that hardness result is not formalized here.

These are statements about one explicit algorithm; the library has no general interface for
approximation ratios of optimization problems yet.

## Main results

* `Cslib.Complexity.computableInPolyTime_johnson_encCNF`: Johnson's algorithm on `encCNF`.
* `Cslib.Complexity.exists_polyTime_maxSAT_approx`: a polynomial-time `1 - 2 ^ -k`
  approximation for formulas with at least `k` distinct literals per clause.
* `Cslib.Complexity.exists_polyTime_maxExactThreeSAT_approx`: a polynomial-time `7 / 8`
  approximation for MAX-E3SAT with three distinct variables per clause.

## References

* [D. S. Johnson, *Approximation algorithms for combinatorial problems*][Johnson1974]
* [D. P. Williamson, D. B. Shmoys, *The Design of Approximation Algorithms*,
  Sections 5.1–5.2][WilliamsonShmoys2011]
* [J. Håstad, *Some optimal inapproximability results*][Hastad2001]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- **Johnson's algorithm is polynomial-time** on formulas encoded as for `SAT`, with its output,
the variables it sets to `true`, as a list of binary naturals. -/
theorem computableInPolyTime_johnson_encCNF :
    ComputableInPolyTime (johnson (V := ℕ)) encCNF (encList encNat) :=
  computableInPolyTime_johnson encNat

/-- **A polynomial-time approximation algorithm for MAX-SAT**: one polynomial-time algorithm,
whose output lists the variables to set to `true`, satisfies on every formula whose clauses have
at least `k` distinct literals at least the proportion `1 - 2 ^ -k` of the clauses, and at least
`1 - 2 ^ -k` times the largest proportion an assignment satisfies. -/
theorem exists_polyTime_maxSAT_approx :
    ∃ A : CNF ℕ → List ℕ, ComputableInPolyTime A encCNF (encList encNat) ∧
      ∀ (k : ℕ) (φ : CNF ℕ), (∀ c ∈ φ, k ≤ c.toFinset.card) →
        2 ^ k * φ.countUnsat (fun v => decide (v ∈ A φ)) ≤ φ.length ∧
        (1 - (2 : ℝ)⁻¹ ^ k) * (1 - φ.unsatVal) ≤
          1 - (φ.countUnsat (fun v => decide (v ∈ A φ)) : ℝ) / φ.length :=
  ⟨johnson, computableInPolyTime_johnson_encCNF, fun _ _ hk =>
    ⟨two_pow_mul_countUnsat_johnsonAssignment_le_length hk,
      one_sub_inv_two_pow_mul_le_johnsonAssignment hk⟩⟩

/-- **A polynomial-time `7 / 8`-approximation algorithm for MAX-E3SAT**: on every formula with
three distinct variables per clause, one polynomial-time algorithm satisfies at least `7 / 8` of
the clauses, and at least `7 / 8` times the largest proportion an assignment satisfies. -/
theorem exists_polyTime_maxExactThreeSAT_approx :
    ∃ A : CNF ℕ → List ℕ, ComputableInPolyTime A encCNF (encList encNat) ∧
      ∀ φ : CNF ℕ, φ.IsExactThreeDistinct →
        8 * φ.countUnsat (fun v => decide (v ∈ A φ)) ≤ φ.length ∧
        7 / 8 * (1 - φ.unsatVal) ≤
          1 - (φ.countUnsat (fun v => decide (v ∈ A φ)) : ℝ) / φ.length :=
  ⟨johnson, computableInPolyTime_johnson_encCNF, fun _ hφ =>
    ⟨hφ.eight_mul_countUnsat_johnsonAssignment_le,
      hφ.seven_div_eight_mul_le_johnsonAssignment⟩⟩

end Cslib.Complexity
