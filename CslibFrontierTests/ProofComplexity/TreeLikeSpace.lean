/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.Propositional.Resolution.TreeLikeSpace
import CslibFrontier.Logics.Propositional.Resolution.TseitinSpace

/-!
# Tests: clause space of tree-like refutations

Strahler numbers and sizes of tree-like refutations of `x ∧ ¬x`, of the complete formula on two
variables, and of a unit-propagation chain, where the Strahler bound beats the logarithmic bound;
the Strahler number as a decision-tree rank; Esteban and Torán's bound, attained by `x ∧ ¬x`; the
bound `n + 2` for formulas on `n` variables, attained for `n = 1`; and a tree-like size lower bound
for the hard Tseitin family from its clause-space lower bound.
-/

namespace ComplexityTests.ProofComplexity.TreeLikeSpace

open Cslib Cslib.Logic.PL
open scoped Finset

/-! ### `x ∧ ¬x` -/

/-- `x₀ ∧ ¬x₀`. -/
private def ψ : CNF ℕ := [[(0, true)], [(0, false)]]

/-- The tree-like refutation of `x₀ ∧ ¬x₀`: one resolution step. -/
private def dψ : ψ.Derivation [] :=
  (CNF.Derivation.resolvent 0 (.mem (c := [(0, true)]) (by decide))
    (.mem (c := [(0, false)]) (by decide)) (by decide) (by decide) : ψ.Derivation _)

example : dψ.size = 3 ∧ dψ.strahler = 1 := ⟨rfl, rfl⟩

/-- Esteban and Torán's bound is attained: `x₀ ∧ ¬x₀` is not refutable in clause space `2`, and its
tree-like refutation has `2 ^ 2 - 1` nodes. -/
example : ¬ ψ.RefutableInSpace 2 ∧ 2 ^ 2 = dψ.size + 1 :=
  ⟨fun h => absurd (h.three_le (by decide)) (by decide), rfl⟩

example : ψ.RefutableInSpace 3 := dψ.refutableInSpace

example : ψ.RefutableInSpace 3 := dψ.refutableInSpace_log

/-- The bound `n + 2` for formulas on `n` variables is attained for `n = 1`. -/
example : ψ.RefutableInSpace (#ψ.vars.toFinset + 2) ∧ ¬ ψ.RefutableInSpace (#ψ.vars.toFinset + 1) :=
  ⟨CNF.refutableInSpace_of_not_satisfiable fun ⟨σ, hσ⟩ => by
      revert hσ
      cases h : σ 0 <;> simp [ψ, CNF.eval, Clause.eval, h],
    fun h => absurd (h.three_le (by decide)) (by decide)⟩

/-! ### The complete formula on two variables -/

/-- The four clauses on `x₀, x₁`. -/
private def κ : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)],
    [(0, false), (1, false)]]

/-- Resolve on `x₁` twice, then on `x₀`: a complete binary tree of height `2`. -/
private def dκ : κ.Derivation [] :=
  (CNF.Derivation.resolvent 0
    (CNF.Derivation.resolvent 1 (.mem (c := [(0, true), (1, true)]) (by decide))
      (.mem (c := [(0, true), (1, false)]) (by decide)) (by decide) (by decide))
    (CNF.Derivation.resolvent 1 (.mem (c := [(0, false), (1, true)]) (by decide))
      (.mem (c := [(0, false), (1, false)]) (by decide)) (by decide) (by decide))
    (by decide) (by decide) : κ.Derivation _)

example : dκ.size = 7 ∧ dκ.strahler = 2 := ⟨rfl, rfl⟩

example : κ.RefutableInSpace 4 := dκ.refutableInSpace_log

/-- The Strahler number is the rank of the decision tree of the derivation. -/
example : dκ.toDecisionTree.rank = 2 := by
  rw [← CNF.Derivation.strahler_eq_rank_toDecisionTree]; rfl

/-! ### A unit-propagation chain -/

/-- `x₀ ∧ (x₀ → x₁) ∧ (x₁ → x₂) ∧ ¬x₂`. -/
private def χ : CNF ℕ :=
  [[(0, true)], [(0, false), (1, true)], [(1, false), (2, true)], [(2, false)]]

/-- Unit propagation along the chain: each step resolves the current unit clause with the next
implication, so every resolution step has a leaf premise. -/
private def dχ : χ.Derivation [] :=
  (CNF.Derivation.resolvent 2
    (CNF.Derivation.resolvent 1
      (CNF.Derivation.resolvent 0 (.mem (c := [(0, true)]) (by decide))
        (.mem (c := [(0, false), (1, true)]) (by decide)) (by decide) (by decide))
      (.mem (c := [(1, false), (2, true)]) (by decide)) (by decide) (by decide))
    (.mem (c := [(2, false)]) (by decide)) (by decide) (by decide) : χ.Derivation _)

/-- A caterpillar of `7` nodes: unequal premises keep the Strahler number at `1`. -/
example : dχ.size = 7 ∧ dχ.strahler = 1 := ⟨rfl, rfl⟩

/-- The Strahler bound gives clause space `3`, which is optimal, while the logarithmic bound only
gives `log₂ 8 + 1 = 4`. -/
example : χ.RefutableInSpace 3 ∧ ¬ χ.RefutableInSpace 2 ∧ Nat.log 2 (dχ.size + 1) + 1 = 4 :=
  ⟨dχ.refutableInSpace, fun h => absurd (h.three_le (by decide)) (by decide),
    by rw [show dχ.size + 1 = 2 ^ 3 from rfl, Nat.log_pow (by norm_num)]⟩

/-! ### Tree-like size from clause space -/

/-- The hard Tseitin family at its least size needs clause space `122`, so its tree-like refutations
have at least `2 ^ 121 - 1` nodes. -/
example :
    ∃ m, ∃ φ : CNF (Fin m), ¬ φ.Satisfiable ∧ ∀ d : φ.Derivation [], 2 ^ 121 ≤ d.size + 1 := by
  obtain ⟨m, -, φ, -, -, hφ, hs⟩ := CNF.exists_forall_refutableInSpace_le 4392000 le_rfl
  exact ⟨m, φ, hφ, fun d => d.two_pow_le_size_add_one fun h => by have := hs _ h; omega⟩

end ComplexityTests.ProofComplexity.TreeLikeSpace
