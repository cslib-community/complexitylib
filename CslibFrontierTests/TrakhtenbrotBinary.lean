/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Trakhtenbrot.Binary
public import CslibFrontierTests.Trakhtenbrot

/-! # Trakhtenbrot's theorem for a fixed vocabulary: checked instances

Sentencehood on small examples, the existential closure, a concrete tuple gadget (a tuple of the
interpreted relation and a non-tuple), argument padding from arity `2` to higher arities (along with
non-binary and `l = 1` controls), the reduction to one relation symbol of arity `l ≥ 2` on a
finitely satisfiable formula and on the axiom of infinity, and the headline theorems specialised to
binary and ternary vocabularies. -/

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

/-! ### Argument padding -/

/-- Padding a binary atom to arity `2` leaves it unchanged. -/
example : padArgs 2 (rel 5 [0, 1]) = rel 5 [0, 1] := by simp

/-- Padding a binary atom to arity `3` repeats the second argument once. -/
example : padArgs 3 (rel 5 [0, 1]) = rel 5 [0, 1, 1] := by simp

/-- Padding distributes through quantifiers and pads binary atoms to arity `4`. -/
example : padArgs 4 (all 0 (rel 5 [0, 0])) = all 0 (rel 5 [0, 0, 0, 0]) := by simp

/-- Nullary, unary and quaternary atoms are not binary, so `padArgs` leaves them unchanged. -/
example : padArgs 3 (rel 5 []) = rel 5 [] := padArgs_rel_of_length_ne 3 5 (by decide)

example : padArgs 3 (rel 5 [0]) = rel 5 [0] := padArgs_rel_of_length_ne 3 5 (by decide)

example : padArgs 3 (rel 5 [0, 1, 2, 3]) = rel 5 [0, 1, 2, 3] :=
  padArgs_rel_of_length_ne 3 5 (by decide)

/-- Padding sends sentences over `{(5, 2)}` to sentences over `{(5, 4)}`. -/
example : IsSentenceOver {(5, 4)} (padArgs 4 (all 0 (rel 5 [0, 0]))) :=
  isSentenceOver_padArgs (by decide) ⟨by decide, fun a ha => by simpa [atoms] using ha⟩

/-- At `l = 1`, `padArgs 1` leaves binary atoms binary, so `2 ≤ l` cannot be dropped in
`isSentenceOver_padArgs`. -/
example : ¬IsSentenceOver {(5, 1)} (padArgs 1 (all 0 (rel 5 [0, 0]))) := fun h => by
  have := h.2 (5, 2) (by simp [atoms])
  simp at this

/-- Padding the axiom of infinity to arity `3` preserves finite unsatisfiability. -/
example : ¬FinSat (padArgs 3 infAx) := by
  have hbin : ∀ a ∈ infAx.atoms, a.2 = 2 := by decide
  exact fun h => not_finSat_infAx ((finSat_padArgs 3 hbin).1 h)

/-! ### The reduction -/

/-- The binary reduction of the axiom of infinity has no finite model. -/
theorem not_finSat_singleRel_two_infAx : ¬FinSat (singleRel 0 2 infAx) :=
  fun h => not_finSat_infAx ((finSat_singleRel 0 2 infAx).1 h)

/-- The ternary reduction of the axiom of infinity has no finite model. -/
theorem not_finSat_singleRel_three_infAx : ¬FinSat (singleRel 0 3 infAx) :=
  fun h => not_finSat_infAx ((finSat_singleRel 0 3 infAx).1 h)

/-- The reduction of `x₀ = x₀` has a finite model at arity `2` and at arity `4`. -/
theorem finSat_singleRel_two_equal : FinSat (singleRel 0 2 (equal 0 0)) :=
  (finSat_singleRel 0 2 _).2 finSat_equal

theorem finSat_singleRel_four_equal : FinSat (singleRel 0 4 (equal 0 0)) :=
  (finSat_singleRel 0 4 _).2 finSat_equal

/-- The negated binary reduction of the axiom of infinity is a finitely valid sentence over
`{(5, 2)}`. -/
example :
    IsSentenceOver {(5, 2)} (neg (singleRel 5 2 infAx)) ∧ FinValid (neg (singleRel 5 2 infAx)) :=
  ⟨isSentenceOver_neg.2 (isSentenceOver_singleRel le_rfl infAx),
    (finValid_neg_iff _).2 fun h => not_finSat_infAx ((finSat_singleRel 5 2 infAx).1 h)⟩

/-- The negated ternary reduction of the axiom of infinity is a finitely valid sentence over
`{(5, 3)}`. -/
example :
    IsSentenceOver {(5, 3)} (neg (singleRel 5 3 infAx)) ∧ FinValid (neg (singleRel 5 3 infAx)) :=
  ⟨isSentenceOver_neg.2 (isSentenceOver_singleRel (by decide) infAx),
    (finValid_neg_iff _).2 fun h => not_finSat_infAx ((finSat_singleRel 5 3 infAx).1 h)⟩

/-! ### The headline theorems for concrete vocabularies -/

/-- One binary and one unary relation symbol: finite satisfiability is undecidable. -/
example : ¬∃ f : RawFormula → Bool, Computable f ∧
    ∀ φ, IsSentenceOver {(0, 2), (1, 1)} φ → (f φ = true ↔ FinSat φ) :=
  not_exists_computable_finSat_of_mem (s := 0) (l := 2) (by simp) le_rfl

/-- A single binary relation symbol: finite validity is not r.e. -/
example : ¬∃ S : RawFormula → Prop, REPred S ∧
    ∀ φ, IsSentenceOver {(0, 2)} φ → (S φ ↔ FinValid φ) :=
  not_exists_rePred_finValid_of_mem rfl le_rfl

/-- A single ternary relation symbol (no binary symbol): finite satisfiability is undecidable. -/
example : ¬∃ f : RawFormula → Bool, Computable f ∧
    ∀ φ, IsSentenceOver {(7, 3)} φ → (f φ = true ↔ FinSat φ) :=
  not_exists_computable_finSat_of_mem rfl (by decide)

/-- A single ternary relation symbol (no binary symbol): finite validity is not r.e. -/
example : ¬∃ S : RawFormula → Prop, REPred S ∧
    ∀ φ, IsSentenceOver {(7, 3)} φ → (S φ ↔ FinValid φ) :=
  not_exists_rePred_finValid_of_mem rfl (by decide)

end Cslib.Tests.TrakhtenbrotBinary
