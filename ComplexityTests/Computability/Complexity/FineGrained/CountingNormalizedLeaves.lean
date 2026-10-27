/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingTreeBound

/-!
# Counting providers promised only on normalized sparse leaves

The provider below deliberately returns a wrong, bounded result on long lists of duplicate
clauses. The normalized-leaf correctness theorem still proves the search correct: duplicate
clauses are removed before the provider is called. The zero-variable empty-clause control also
requires the additive `+ 1` in the leaf-length bound.
-/

@[expose] public section

namespace Cslib.Complexity.CountingNormalizedLeavesTests

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Logic.PL.CNF.Sparsification
open Cslib.Logic.PL.ClauseSet.Sparsification Cslib.Complexity.CountingSparsify

/-- A bounded declared-variable provider that is exact only below the promised leaf-length cap. -/
def boundedDeclared (K M : ℕ) (x : ℕ × CNF ℕ) : ℕ :=
  if x.2.length ≤ occBound K M * x.1 + 1 then
    x.2.modelCountOn (Finset.range x.1)
  else 2 ^ x.1

/-- Even on inputs outside its correctness promise, the provider respects the output bound. -/
theorem boundedDeclared_le (K M : ℕ) (x : ℕ × CNF ℕ) :
    boundedDeclared K M x ≤ 2 ^ x.1 := by
  unfold boundedDeclared
  split_ifs
  · unfold CNF.modelCountOn
    refine (Finset.card_filter_le _ _).trans ?_
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
      Finset.card_range, le_rfl]
  · exact le_rfl

/-- Long duplicate lists are sparse but violate the provider's size promise. In particular,
the unrestricted sparse-leaf correctness premise is false for this bounded provider. -/
example :
    isSparse (countingThreshold 2) 1 (List.replicate 4 [(0, true)] : CNF ℕ) = true ∧
    boundedDeclared 1 2 (1, List.replicate 4 [(0, true)]) = 2 ∧
    CNF.modelCountOn (List.replicate 4 [(0, true)]) (Finset.range 1) = 1 := by
  decide

private theorem treeBound : CountingTreeBound 2 1 1 0 (by decide) (by decide) :=
  countingTreeBound_of_budget (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem search_boundedDeclared (N : ℕ) {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 1) (hsub : φ.vars.toFinset ⊆ Finset.range N) :
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 1 1
      (normalizeDeclaredLeaf id (boundedDeclared 1 2)) N φ = φ.modelCountOn (Finset.range N) := by
  refine searchDeclaredWith_normalizeDeclaredLeaf_eq_modelCountOn_of_normalized
    (by decide) (by decide) (by decide) le_rfl treeBound ?_ hw hsub
  intro ψ _ _ _ _ hlen
  exact ite_eq_left hlen

/-- The theorem, rather than evaluation of the search, establishes correctness despite the
provider's wrong answer on the input itself. Two unused declared variables contribute a factor 4.
-/
example :
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 1 1
      (normalizeDeclaredLeaf id (boundedDeclared 1 2)) 3 (List.replicate 8 [(0, true)]) = 4 := by
  have h := search_boundedDeclared 3
    (φ := List.replicate 8 [(0, true)]) (by decide) (by decide)
  exact h.trans (by decide)

example : boundedDeclared 1 2 (3, List.replicate 8 [(0, true)]) = 8 := by decide

/-- A tautological clause disappears during normalization. The theorem preserves its variable's
contribution together with the two declared variables that never occurred in the formula. -/
example :
    searchDeclaredWith id (fun _ => 64) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id (boundedDeclared 2 64)) 3 [[(0, true), (0, false)]] = 8 := by
  have h :
      searchDeclaredWith id (fun _ => 64) (fun _ => 1) 2 2
        (normalizeDeclaredLeaf id (boundedDeclared 2 64)) 3 [[(0, true), (0, false)]] =
        CNF.modelCountOn [[(0, true), (0, false)]] (Finset.range 3) := by
    refine searchDeclaredWith_normalizeDeclaredLeaf_eq_modelCountOn_of_normalized
      (NOf := id) (MOf := fun _ : ℕ => 64) (BOf := fun _ : ℕ => 1)
      (K := 2) (k := 2) (p := 3) (φ := [[(0, true), (0, false)]])
      (h := boundedDeclared 2 64) (L_coeff := countingDepthCoeff 2 64)
      (by decide) (by decide) (by decide) le_rfl
      (countingTreeBound_of_budget (M := 64) (K := 2) (B := 1)
        (by decide) (by decide) (by decide) (by decide) (by decide))
      ?_ (by decide) (by decide)
    intro ψ _ _ _ _ hlen
    exact ite_eq_left hlen
  exact h.trans (by decide)

/-- With zero declared variables, the empty formula has one assignment, whereas the single
empty clause is an admissible one-clause leaf and has none. -/
example :
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 1 1
      (normalizeDeclaredLeaf id (boundedDeclared 1 2)) 0 [] = 1 ∧
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 1 1
      (normalizeDeclaredLeaf id (boundedDeclared 1 2)) 0 [[]] = 0 ∧
    boundedDeclared 1 2 (0, [[]]) = 0 := by
  decide

/-- The declared-input guard still rejects variable labels outside the declared range. -/
example :
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 1 1
      (normalizeDeclaredLeaf id (boundedDeclared 1 2)) 1 [[(1, true)]] = 0 := by
  decide

end Cslib.Complexity.CountingNormalizedLeavesTests
