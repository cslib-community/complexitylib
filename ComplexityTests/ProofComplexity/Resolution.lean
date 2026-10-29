/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.Resolution.TreeLike
import Complexity.Logics.Propositional.Resolution.SizeWidth

/-!
# Tests: resolution proofs, tree-like resolution and the size–width tradeoff

Widths of clauses with repeated literals; a concrete resolution refutation, its size and width;
a tree-like refutation, its decision tree and the decision tree's refutation; restrictions of a
proof; instances of the hypotheses of the size–width theorems; and the axioms of the headline
theorems.
-/

namespace ComplexityTests.ProofComplexity.Resolution

open Cslib Cslib.Logic Cslib.Logic.InferenceSystem Cslib.Logic.PL

/-! ### Width -/

/-- Repeated literals count once; complementary literals count twice. -/
example :
    Clause.width ([(0, true), (0, true), (1, false)] : Clause ℕ) = 2 ∧
    Clause.width ([(0, true), (0, false)] : Clause ℕ) = 2 := by
  decide

/-! ### A refutation -/

/-- `x₀ ∧ (¬x₀ ∨ x₁) ∧ ¬x₁`. -/
private def φ : CNF ℕ := [[(0, true)], [(0, false), (1, true)], [(1, false)]]

/-- Resolve `x₀` with `¬x₀ ∨ x₁` to `x₁`, and `x₁` with `¬x₁` to the empty clause. -/
private def proof : List (Clause ℕ) := [[], [(1, true)], [(1, false)], [(0, false), (1, true)],
  [(0, true)]]

example :
    Clause.resolvent ([(0, true)] : Clause ℕ) [(0, false), (1, true)] 0 = [(1, true)] ∧
    Clause.resolvent ([(1, true)] : Clause ℕ) [(1, false)] 1 = [] := by
  decide

private theorem isProof : φ.IsProof proof := by
  have h₃ : φ.IsProof [[(1, false)], [(0, false), (1, true)], [(0, true)]] :=
    ((CNF.IsProof.nil.mem (by decide)).mem (by decide)).mem (by decide)
  have h₄ := h₃.resolvent (c₁ := [(0, true)]) (c₂ := [(0, false), (1, true)]) 0 (by decide)
    (by decide) (by decide) (by decide)
  have h₅ := h₄.resolvent (c₁ := [(1, true)]) (c₂ := [(1, false)]) 1 (by decide) (by decide)
    (by decide) (by decide)
  exact h₅

example :
    φ.RefutableInSize 5 ∧
    φ.RefutableInWidth 2 ∧
    ¬ φ.Satisfiable ∧
    φ.restrict 1 false = [[(0, true)], [(0, false)]] :=
  ⟨⟨proof, isProof, by decide, le_rfl⟩,
    ⟨proof, isProof, by decide, by decide⟩,
    CNF.exists_refutableInSize_iff_not_satisfiable.1 ⟨5, proof, isProof, by decide, le_rfl⟩,
    by decide⟩

example : ∃ ls, (φ.restrict 1 false).IsProof ls ∧ [] ∈ ls ∧ ls.length ≤ 5 := by
  obtain ⟨ls, h, hlen, hsub, -⟩ := isProof.restrict 1 false
  obtain ⟨c, hc, hsub'⟩ := hsub [] (by decide) (by decide)
  obtain rfl : c = [] := List.eq_nil_iff_forall_not_mem.2 fun l hl => by simpa using hsub' l hl
  exact ⟨ls, h, hc, hlen.trans (by decide)⟩

/-- Restricting `φ` by the partial assignment fixing `x₁ ↦ false` gives the same two clauses. -/
example : φ.restrictBy (fun v => if v = 1 then some false else none) =
    [[(0, true)], [(0, false)]] := by
  decide

example : ∃ ls, (φ.restrictBy (fun v => if v = 1 then some false else none)).IsProof ls ∧
    [] ∈ ls ∧ ls.length ≤ 5 := by
  obtain ⟨ls, h, hsub, ks, hks, -, hF⟩ :=
    isProof.restrictBy (fun v => if v = 1 then some false else none)
  obtain ⟨c, hc, hsub'⟩ := hsub [] (by decide) (by decide)
  obtain rfl : c = [] := List.eq_nil_iff_forall_not_mem.2 fun l hl => by simpa using hsub' l hl
  exact ⟨ls, h, hc, hF.length_eq.trans_le (hks.length_le.trans (by decide))⟩

/-! ### Tree-like refutations and decision trees -/

/-- `x₀ ∧ ¬x₀`. -/
private def ψ : CNF ℕ := [[(0, true)], [(0, false)]]

/-- The tree-like refutation of `ψ`, resolving its two clauses. -/
private def treeRefutation : ψ.Derivation [] :=
  .resolvent (c₁ := [(0, true)]) (c₂ := [(0, false)]) 0 (.mem (by decide)) (.mem (by decide))
    (by decide) (by decide)

example :
    treeRefutation.size = 3 ∧
    treeRefutation.toDecisionTree = .node 0 (.leaf [(0, true)]) (.leaf [(0, false)]) ∧
    treeRefutation.toDecisionTree.FindsFalsifiedClause ψ :=
  ⟨rfl, rfl, treeRefutation.findsFalsifiedClause_toDecisionTree⟩

/-- A DPLL tree querying `x₀` twice finds a falsified clause; it gives a tree-like refutation. -/
private def dpllTree : DecisionTree ℕ (Clause ℕ) :=
  .node 0 (.leaf [(0, true)]) (.node 0 (.leaf [(0, true)]) (.leaf [(0, false)]))

private theorem findsFalsifiedClause_dpllTree : dpllTree.FindsFalsifiedClause ψ := fun σ => by
  cases h : σ 0 <;> simp [dpllTree, DecisionTree.eval, h, ψ]

example : ∃ d : ψ.Derivation [], d.size + 1 ≤ 6 :=
  findsFalsifiedClause_dpllTree.exists_derivation

/-! ### CSLib `InferenceSystem` bridge -/

private def inferenceRefutation : ⇓(ψ, ([] : Clause ℕ)) := treeRefutation

private def setRefutation : {d // d ∈ ψ}⇓([] : Clause ℕ) := treeRefutation

example :
    InferenceSystem.Derivable (ψ, ([] : Clause ℕ)) ∧
    InferenceSystem.DerivableIn {d | d ∈ ψ} ([] : Clause ℕ) ∧
    (ψ.Derives [] ↔ InferenceSystem.Derivable (ψ, ([] : Clause ℕ))) ∧
    (ψ.Derives [] ↔ InferenceSystem.DerivableIn {d | d ∈ ψ} ([] : Clause ℕ)) ∧
    ψ.Derives [] :=
  ⟨⟨inferenceRefutation⟩, ⟨setRefutation⟩, CNF.derives_iff_derivable, CNF.derives_iff_derivableIn,
    CNF.derives_iff_derivable.2 ⟨inferenceRefutation⟩⟩

/-! ### The size–width tradeoff -/

/-- Short tree-like refutations are narrow (`3 ≤ 2 ^ 2` nodes give width at most `1 + 2`), and the
size–width tradeoff bounds refutation width from refutation size. -/
example :
    ψ.RefutableInWidth 3 ∧
    ψ.RefutableInWidth (max 1 1 + 2) ∧
    ∃ w : ℕ, φ.RefutableInWidth w ∧ (w : ℝ) ≤ 2 + 2 * √(2 * 2 * Real.log 5) + 2 := by
  refine ⟨CNF.RefutableInWidth.of_derivation (k := 1) (b := 2) (by decide) treeRefutation
      rfl (by decide),
    CNF.RefutableInWidth.of_refutableInSize (s := 3) (N := 1) (by decide) (by decide)
      treeRefutation.refutableInSize (by decide), ?_⟩
  exact_mod_cast CNF.exists_refutableInWidth_le_of_refutableInSize (k := 2) (N := 2)
    (by decide) (by decide) ⟨proof, isProof, by decide, le_rfl⟩

/-- The size–width theorem includes the boundary case of no variables and one proof line. -/
example : ∃ w : ℕ, CNF.RefutableInWidth ([[]] : CNF ℕ) w ∧ (w : ℝ) ≤ 2 := by
  have hs : CNF.RefutableInSize ([[]] : CNF ℕ) 1 :=
    ⟨[[]], CNF.IsProof.nil.mem (by simp), by simp, le_rfl⟩
  simpa using CNF.exists_refutableInWidth_le_of_refutableInSize (k := 0) (N := 0)
    (by simp) (by decide) hs

/-- The empty, satisfiable formula has no resolution refutation. -/
example : ¬ ∃ s, CNF.RefutableInSize ([] : CNF ℕ) s := by
  rw [CNF.exists_refutableInSize_iff_not_satisfiable, not_not]
  exact ⟨fun _ => false, rfl⟩

/-! ### Axioms -/

/--
info: 'Cslib.Logic.PL.CNF.derives_iff_exists_isProof' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.derives_iff_exists_isProof

/--
info: 'Cslib.Logic.PL.CNF.Derivation.findsFalsifiedClause_toDecisionTree' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.Derivation.findsFalsifiedClause_toDecisionTree

/--
info: 'Cslib.Logic.PL.CNF.derives_iff_nonempty_derivation' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.derives_iff_nonempty_derivation

/--
info: 'Cslib.Logic.PL.CNF.derives_iff_derivableIn' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.derives_iff_derivableIn

/--
info: 'Cslib.Logic.PL.CNF.derives_iff_derivable' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.derives_iff_derivable

end ComplexityTests.ProofComplexity.Resolution
