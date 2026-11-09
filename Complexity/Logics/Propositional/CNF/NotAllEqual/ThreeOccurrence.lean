/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.NotAllEqual
public import Complexity.Logics.Propositional.CNF.ThreeOccurrence

/-!
# Occurrence splitting for not-all-equal clauses

The ordinary occurrence splitter also preserves not-all-equal satisfiability. Its binary
implication cycles become equality constraints under NAE semantics. The existing width,
occurrence and polynomial-time bounds apply unchanged. Binary clauses are essential here.

## Main results

* `CNF.naeSatisfiable_toThreeOccurrence`: NAE satisfiability is preserved.
-/

public section

namespace Cslib.Logic.PL.CNF

variable {V : Type*}

/-- The existing occurrence splitter preserves not-all-equal satisfiability. -/
theorem naeSatisfiable_toThreeOccurrence [DecidableEq V] (φ : CNF V) :
    φ.toThreeOccurrence.NAESatisfiable ↔ φ.NAESatisfiable := by
  simp only [NAESatisfiable, evalNAE, Bool.and_eq_true]
  constructor
  · rintro ⟨τ, hp, hn⟩
    obtain ⟨σ, hσ, he⟩ := (eval_toThreeOccurrence_iff φ τ).mp hp
    refine ⟨σ, hσ, ?_⟩
    rw [toThreeOccurrence, eval_append, Bool.and_eq_true] at hn
    rw [← eval_occurrenceClauses φ (fun v => !σ v)]
    exact (eval_congr fun x hx => congrArg Bool.not (he x hx)).trans hn.1
  · rintro ⟨σ, hp, hn⟩
    refine ⟨σ ∘ Prod.fst, ?_, ?_⟩
    · exact (eval_toThreeOccurrence_iff φ _).mpr ⟨σ, hp, fun _ _ => rfl⟩
    · exact (eval_toThreeOccurrence_iff φ _).mpr
        ⟨fun v => !σ v, hn, fun _ _ => rfl⟩

end Cslib.Logic.PL.CNF
