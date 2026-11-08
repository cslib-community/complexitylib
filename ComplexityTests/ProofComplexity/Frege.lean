/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.Frege.Resolution

/-!
# Tests: Frege proofs

These tests cover:

* a five-line Frege proof of `p → p`, built from the constructors;
* clause formulas and their semantics;
* a concrete Frege refutation of `x ∧ ¬x` with an explicit line count, obtained from the
  simulation of a three-line resolution refutation;
* soundness: a satisfiable CNF has no Frege refutation;
* the general bound for one resolution step on wide clauses.
-/

namespace ComplexityTests.ProofComplexity.Frege

open Cslib Cslib.Logic.PL Cslib.Logic.PL.Frege Cslib.Logic.PL.Frege.Formula

/-! ### A proof of `p → p` -/

/-- The five-line proof of `p → p` from S, K, K and modus ponens, built from the constructors. -/
example (p : Formula ℕ) : IsProof [] [imp p p, imp p (imp p p), imp (imp p (imp p p)) (imp p p),
    imp p (imp (imp p p) p), imp (imp p (imp (imp p p) p)) (imp (imp p (imp p p)) (imp p p))] := by
  refine IsProof.mp ?_ (φ := imp p (imp p p)) (List.mem_cons_self) ?_
  · refine IsProof.ax ?_ (IsAxiom.k p p)
    refine IsProof.mp ?_ (φ := imp p (imp (imp p p) p)) (List.mem_cons_self) ?_
    · exact (IsProof.nil.ax (IsAxiom.s p (imp p p) p)).ax (IsAxiom.k p (imp p p))
    · simp
  · simp

/-! ### Clause formulas -/

/-- The formula of `x₀ ∨ ¬x₁` is `¬x₀ → x₁ → ⊥`. -/
example : Clause.toFormula [((0 : ℕ), true), (1, false)] =
    imp (Proposition.neg (var 0)) (imp (var 1) ⊥) := by
  decide

/-- A repeated literal is counted once. -/
example : Clause.toFormula [((0 : ℕ), true), (0, true)] = Clause.toFormula [((0 : ℕ), true)] := by
  decide

/-- The formula of `x₀ ∨ ¬x₁` holds where the clause does and fails where it does not. -/
example : (Clause.toFormula [((0 : ℕ), true), (1, false)]).eval (fun _ => false) = true ∧
    (Clause.toFormula [((0 : ℕ), true), (1, false)]).eval (fun v => v == 1) = false := by
  rw [Clause.eval_toFormula, Clause.eval_toFormula]
  decide

/-! ### A refutation of `x ∧ ¬x` -/

/-- `x₀ ∧ ¬x₀`. -/
private def ψ : CNF ℕ := [[(0, true)], [(0, false)]]

/-- The three-line resolution refutation of `ψ`. -/
private theorem ψ_refutable : ψ.RefutableInSize 3 := by
  refine ⟨[Clause.resolvent [(0, true)] [(0, false)] 0, [(0, false)], [(0, true)]], ?_, ?_, le_rfl⟩
  · refine CNF.IsProof.resolvent 0 ?_ (by simp) (by simp) (by simp) (by simp)
    exact (CNF.IsProof.nil.mem (by simp [ψ])).mem (by simp [ψ])
  · decide

/-- `ψ` has a Frege refutation from its clause formulas with at most `stepBound 2 * 3` lines. -/
example : ∃ L, IsProof (ψ.map Clause.toFormula) L ∧ (⊥ : Formula ℕ) ∈ L ∧
    L.length ≤ stepBound 2 * 3 := by
  obtain ⟨L, hL, hbot, hlen⟩ := ψ_refutable.frege
  refine ⟨L, hL, hbot, hlen.trans (Nat.mul_le_mul_right _ (stepBound_mono ?_))⟩
  decide

/-! ### Soundness -/

/-- `x₀ ∧ (¬x₀ ∨ x₁)` is satisfiable, so it has no Frege refutation. -/
example : ¬ ∃ L,
    IsProof (([[(0, true)], [(0, false), (1, true)]] : CNF ℕ).map Clause.toFormula) L ∧
    (⊥ : Formula ℕ) ∈ L := by
  rw [CNF.exists_frege_refutation_iff_not_satisfiable, not_not]
  exact ⟨fun _ => true, by decide⟩

/-! ### One resolution step on wide clauses -/

/-- Resolving `x₀ ∨ x₁ ∨ ⋯ ∨ x₉` with `¬x₀ ∨ x₁₀` costs at most `stepBound 10` Frege lines. -/
example : DerivableInSize [Clause.toFormula ((0 : ℕ) :: (List.range' 1 9) |>.map (·, true)),
    Clause.toFormula [(0, false), (10, true)]]
    (Clause.toFormula (Clause.resolvent ((0 : ℕ) :: (List.range' 1 9) |>.map (·, true))
      [(0, false), (10, true)] 0)) (stepBound 10) := by
  refine (derivableInSize_toFormula_resolvent _ _ 0).mono (stepBound_mono ?_)
  decide

end ComplexityTests.ProofComplexity.Frege
