/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.DNF

/-!
# Evaluation of relabeled DNF predicates

Reuse the existing literal-list relabeling and DNF evaluator. This supplies coordinate transport
for explicit finite threshold-rule predicates without introducing another evaluator.
-/

public section

namespace Cslib.Logic.PL.DNF

/-- Relabeling the existing term lists composes their assignment, just as for CNF. -/
theorem eval_relabel {V W : Type*} (f : V → W) (y : W → Bool) (P : DNF V) :
    DNF.eval y (CNF.relabel f P) = DNF.eval (y ∘ f) P := by
  simp only [DNF.eval, CNF.relabel, Clause.relabel, Term.eval, List.any_map, List.all_map,
    Function.comp_def, Literal.eval, Prod.map, id_eq]
  rfl

end Cslib.Logic.PL.DNF

namespace Cslib.Logic.PL.Term

/-- Existing term negation commutes with the existing literal-list relabeling. -/
theorem negate_relabel {V W : Type*} (f : V → W) (t : Term V) :
    Clause.relabel f (Term.negate t) = Term.negate (Clause.relabel f t) := by
  simp only [Clause.relabel, Term.negate, List.map_map, Function.comp_def, Prod.map, id_eq]

end Cslib.Logic.PL.Term
