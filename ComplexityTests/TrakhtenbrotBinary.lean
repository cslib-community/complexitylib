/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Trakhtenbrot.Binary
public import ComplexityTests.Trakhtenbrot

/-! # Trakhtenbrot's theorem for a binary relation: checked instances

Sentencehood on small examples, the existential closure, a concrete tuple gadget (a tuple of the
interpreted relation and a non-tuple), the reduction to one binary relation on a finitely
satisfiable formula and on the axiom of infinity, and the headline theorem specialised to a
concrete vocabulary. -/

@[expose] public section

namespace Cslib.Tests.TrakhtenbrotBinary

open Cslib.Logic.FO Cslib.Logic.FO.RawFormula Cslib.Tests.Trakhtenbrot

/-! ### Sentences -/

example : IsSentence (all 0 (rel 0 [0, 0])) := by decide

example : ¬IsSentence (rel 0 [0, 1]) := by decide

example : ¬IsSentence (all 0 (rel 0 [0, 1])) := by decide

example : IsSentence (exClosure (rel 0 [0, 1])) := by decide

example : IsSentence infAx := by decide

/-- A sentence over `{(0, 2)}`. -/
example : IsSentenceOver {(0, 2)} (all 0 (rel 0 [0, 0])) :=
  ⟨by decide, fun a ha => by simpa [atoms] using ha⟩

/-- A sentence whose atom `(1, 2)` is not in `{(0, 2)}`. -/
example : ¬IsSentenceOver {(0, 2)} (all 0 (rel 1 [0, 0])) := fun h => by
  have := h.2 (1, 2) (by simp [atoms])
  simp at this

/-! ### A tuple gadget -/

/-- The relation `{[0, 1]}` on `Fin 2`, as symbol `0`. -/
def pairInterp : ℕ → List (Fin 2) → Prop := fun _ l => l = [0, 1]

/-- The tuple `[0, 1]` of the interpreted relation is a tuple gadget of the tuple graph. -/
example : IsTupleGadget (tupleGraph pairInterp 2) ([0, 1].map Sum.inl) :=
  (isTupleGadget_tupleGraph_iff pairInterp 2 (by decide) (by decide)).2 rfl

/-- The reversed tuple `[1, 0]` is not in the relation, so it is not a tuple gadget. -/
example : ¬IsTupleGadget (tupleGraph pairInterp 2) ([1, 0].map Sum.inl) := fun h =>
  absurd ((isTupleGadget_tupleGraph_iff pairInterp 2 (by decide) (by decide)).1 h)
    (by simp [pairInterp])

/-! ### The reduction -/

/-- The reduction of the axiom of infinity has no finite model. -/
theorem not_finSat_binarize_infAx : ¬FinSat (binarize 0 infAx) :=
  fun h => not_finSat_infAx ((finSat_binarize 0 infAx).1 h)

/-- The reduction of `x₀ = x₀` has a finite model. -/
theorem finSat_binarize_equal : FinSat (binarize 0 (equal 0 0)) :=
  (finSat_binarize 0 _).2 finSat_equal

/-- The negated reduction of the axiom of infinity is a finitely valid sentence over `{(5, 2)}`. -/
example : IsSentenceOver {(5, 2)} (neg (binarize 5 infAx)) ∧ FinValid (neg (binarize 5 infAx)) :=
  ⟨isSentenceOver_neg.2 (isSentenceOver_binarize 5 infAx),
    (finValid_neg_iff _).2 fun h => not_finSat_infAx ((finSat_binarize 5 infAx).1 h)⟩

/-! ### The headline theorem for a concrete vocabulary -/

/-- One binary and one unary relation symbol: finite satisfiability is undecidable. -/
example : ¬∃ f : RawFormula → Bool, Computable f ∧
    ∀ φ, IsSentenceOver {(0, 2), (1, 1)} φ → (f φ = true ↔ FinSat φ) :=
  not_exists_computable_finSat_of_mem (s := 0) (by simp)

/-- A single binary relation symbol: finite validity is not r.e. -/
example : ¬∃ S : RawFormula → Prop, REPred S ∧
    ∀ φ, IsSentenceOver {(0, 2)} φ → (S φ ↔ FinValid φ) :=
  not_exists_rePred_finValid_of_mem rfl

end Cslib.Tests.TrakhtenbrotBinary
