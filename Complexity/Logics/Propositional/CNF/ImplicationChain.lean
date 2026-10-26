/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Mathlib.Data.List.Defs

/-!
# Directed implication chains

Each link uses one binary clause. The logical direction of a subdivided wire is chosen so that
truth of a literal at its clause endpoint implies truth of the source literal. Completeness
only needs the constant assignment along a wire; soundness only needs implication in this one
direction. No return wire is needed.

## Main definitions

* `Cslib.Logic.PL.CNF.implicationChain`: binary implications along consecutive listed variables.

## Main results

* `Cslib.Logic.PL.CNF.eval_implicationChain`: the individual link implications.
* `Cslib.Logic.PL.CNF.true_getLastD_of_eval_implicationChain`: truth propagates along a chain.
* `Cslib.Logic.PL.CNF.eval_implicationChain_of_constant`: constant signals satisfy all links.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

variable {V : Type*}

/-- One binary implication per consecutive pair; empty and singleton chains have no clauses. -/
def implicationChain (vs : List V) : CNF V :=
  vs.consecutivePairs.map fun p => Clause.imp [p.1] p.2

/-- A chain holds exactly when truth propagates across every consecutive link. -/
theorem eval_implicationChain (σ : V → Bool) (vs : List V) :
    (implicationChain vs).eval σ = true ↔
      ∀ p ∈ vs.consecutivePairs, σ p.1 = true → σ p.2 = true := by
  simp [implicationChain, eval_map_eq_true_iff, Clause.eval_imp]

/-- A true signal at the first variable propagates to the last variable. -/
theorem true_getLastD_of_eval_implicationChain (σ : V → Bool) (first : V) (rest : List V)
    (h : (implicationChain (first :: rest)).eval σ = true) (hf : σ first = true) :
    σ ((first :: rest).getLastD first) = true := by
  induction rest generalizing first with
  | nil => exact hf
  | cons next rest ih =>
    have hlinks := (eval_implicationChain σ _).1 h
    have hn : σ next = true := hlinks (first, next) (by
      change (first, next) ∈ (first, next) :: (next :: rest).consecutivePairs
      exact List.mem_cons_self) hf
    have ht : (implicationChain (next :: rest)).eval σ = true := by
      apply (eval_implicationChain σ _).2
      intro p hp
      exact hlinks p (by
        change p ∈ (first, next) :: (next :: rest).consecutivePairs
        exact List.mem_cons_of_mem _ hp)
    simpa only [List.getLastD_cons] using ih next ht hn

/-- Assigning one value to every variable on the chain satisfies all of its implications. -/
theorem eval_implicationChain_of_constant (σ : V → Bool) (vs : List V) (value : Bool)
    (h : ∀ v ∈ vs, σ v = value) : (implicationChain vs).eval σ = true := by
  apply (eval_implicationChain σ vs).2
  intro p hp hptrue
  obtain ⟨ha, hb⟩ := List.of_mem_zip hp
  rw [h p.2 (List.mem_of_mem_tail hb), ← h p.1 ha]
  exact hptrue

end Cslib.Logic.PL.CNF
