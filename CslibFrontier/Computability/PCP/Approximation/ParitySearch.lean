/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Logics.Propositional.CNF.ParitySearch.PolyTime

/-!
# Polynomial-time MAX-SAT approximation by a three-wise independent sample space

On formulas over variables numbered by natural numbers, encoded as for `Cslib.Complexity.SAT`,
exhaustive search of the three-wise independent sample space (`Cslib.Logic.PL.paritySearch`) is
polynomial-time (`Cslib.Complexity.computableInPolyTime_paritySearch_encCNF`). It is a second
deterministic `7 / 8`-approximation for MAX-E3SAT besides Johnson's algorithm
(`Cslib.Complexity.exists_polyTime_maxExactThreeSAT_approx`), and its candidate assignments do not
depend on the clauses: one polynomial-time map sends a list of `n ≥ 1` variables to fewer than
`4 n` assignments, one of which satisfies at least `1 - 2 ^ -k` of the clauses of every formula
on these variables with at least `k ≤ 3` distinct literals per clause
(`Cslib.Complexity.exists_polyTime_oblivious_maxSAT_assignments`), and at least `7 / 8` of the
clauses of every formula with three distinct variables per clause
(`Cslib.Complexity.exists_polyTime_oblivious_maxExactThreeSAT_assignments`)
[AlonBabaiItai1986] [Alon and Spencer, Section 16.2][AlonSpencer2016]. The sample space is not
four-wise independent, and the guarantee fails for `k = 4` (see the checked examples).

## Main results

* `Cslib.Complexity.computableInPolyTime_paritySearch_encCNF`: the search on `encCNF`.
* `Cslib.Complexity.exists_polyTime_oblivious_maxSAT_assignments`,
  `Cslib.Complexity.exists_polyTime_oblivious_maxExactThreeSAT_assignments`: polynomial-time lists
  of fewer than `4 n` assignments that serve every formula on `n` given variables.

## References

* [N. Alon, L. Babai, A. Itai, *A fast and simple randomized parallel algorithm for the maximal
  independent set problem*][AlonBabaiItai1986]
* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Section 16.2][AlonSpencer2016]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- **Searching the three-wise independent sample space is polynomial-time** on formulas encoded as
for `SAT`, with its output, the variables it sets to `true`, as a list of binary naturals. -/
theorem computableInPolyTime_paritySearch_encCNF :
    ComputableInPolyTime (paritySearch (V := ℕ)) encCNF (encList encNat) :=
  computableInPolyTime_paritySearch encNat

/-- **Polynomial-time oblivious assignments for MAX-SAT**: one polynomial-time map sends a list of
`n ≥ 1` variables to fewer than `4 n` assignments, each given by the variables it sets to `true`,
such that for every formula on these variables whose clauses have at least `k ≤ 3` distinct
literals, one of the assignments falsifies at most `2 ^ -k` of the clauses. -/
theorem exists_polyTime_oblivious_maxSAT_assignments :
    ∃ S : List ℕ → List (List ℕ),
      ComputableInPolyTime S (encList encNat) (encList (encList encNat)) ∧
      (∀ vs : List ℕ, vs ≠ [] → (S vs).length < 4 * vs.length) ∧
      ∀ (k : ℕ) (vs : List ℕ) (φ : CNF ℕ), k ≤ 3 → (∀ v ∈ φ.vars, v ∈ vs) →
        (∀ c ∈ φ, k ≤ c.toFinset.card) →
        ∃ T ∈ S vs, 2 ^ k * φ.countUnsat (fun v => decide (v ∈ T)) ≤ φ.length :=
  ⟨parityCandidates, computableInPolyTime_parityCandidates encNat,
    fun _ hvs => length_parityCandidates_lt hvs,
    fun _ _ _ hk3 hvs hk => exists_mem_parityCandidates_two_pow_mul_countUnsat_le hk3 hvs hk⟩

/-- **Polynomial-time oblivious assignments for MAX-E3SAT**: one polynomial-time map sends a list
of `n ≥ 1` variables to fewer than `4 n` assignments such that for every formula on these
variables with three distinct variables per clause, one of the assignments satisfies at least
`7 / 8` of the clauses. -/
theorem exists_polyTime_oblivious_maxExactThreeSAT_assignments :
    ∃ S : List ℕ → List (List ℕ),
      ComputableInPolyTime S (encList encNat) (encList (encList encNat)) ∧
      (∀ vs : List ℕ, vs ≠ [] → (S vs).length < 4 * vs.length) ∧
      ∀ (vs : List ℕ) (φ : CNF ℕ), φ.IsExactThreeDistinct → (∀ v ∈ φ.vars, v ∈ vs) →
        ∃ T ∈ S vs, 8 * φ.countUnsat (fun v => decide (v ∈ T)) ≤ φ.length :=
  ⟨parityCandidates, computableInPolyTime_parityCandidates encNat,
    fun _ hvs => length_parityCandidates_lt hvs,
    fun _ _ hφ hvs => exists_mem_parityCandidates_two_pow_mul_countUnsat_le (k := 3) le_rfl hvs
      fun _ hc => (hφ.card_toFinset_eq hc).ge⟩

end Cslib.Complexity
