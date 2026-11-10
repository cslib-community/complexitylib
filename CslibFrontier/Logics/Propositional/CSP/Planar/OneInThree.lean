/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Constants
public import CslibFrontier.Logics.Propositional.CSP.Planar.NonSelfDual
public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive
public import CslibFrontier.Foundations.Data.BitString.DeltaMatroid.Composition
import Mathlib.Tactic.FinCases

/-!
# The ordered NAND triangle for one-in-three

The original reconstruction here combines a ternary relation containing all units and missing
zero with NAND on its three cyclic adjacent pairs. The target is the existing
`BitString.oneHotRelation (Fin 3)`. It gives an actual four-constraint
`CSP.PPGadget`, in exposed order `0,1,2`. `NonSelfDual.witnesses` derives the required relations
from independently selected language symbols, without assuming constants in the language.

[DvorakKupec2015], Lemma 4, printed pp. 438–439, states the planar expressibility conclusion
without its proof. The arbitrary-arity minor arguments and this triangle are original
reconstructions, not the omitted printed proof. Geometric interpretation of the finite
construction trees, substitution into a plane instance, hardness and runtime remain separate.

## Main definitions

* `Cslib.Logic.PL.CSP.NonSelfDual.triangle`: the actual four-constraint macro gadget.

## Main results

* `Cslib.Logic.PL.CSP.NonSelfDual.witnesses`: derive its macros without a constants premise.
-/

public section

namespace Cslib.Logic.PL.CSP.NonSelfDual

open Cslib.BitString RelationMinor

/-- The two macros in the triangle: its ordered ternary relation and binary NAND. -/
inductive TriangleSymbol where
  /-- The given ternary relation. -/
  | relation
  /-- Binary NAND. -/
  | nand
  deriving DecidableEq

/-- The widths of the triangle macros. -/
@[expose] def triangleArity : TriangleSymbol → ℕ
  | .relation => 3
  | .nand => 2

/-- Exact-width interpretation of the triangle macros. -/
@[expose] def triangleSem (R : Set (Fin 3 → Bool)) [DecidablePred (· ∈ R)] :
    TriangleSymbol → List Bool → Bool
  | .relation, [a, b, c] => decide (![a, b, c] ∈ R)
  | .nand, [a, b] => !(a && b)
  | _, _ => false

/-- The ordered inner ternary face and three cyclic binary digons. All three variables are
free; there are no macro auxiliary variables. The last binary scope is `(2,0)`. -/
@[expose] def triangleBody : CSP TriangleSymbol (Fin 3 ⊕ Fin 0) :=
  [(.relation, [.inl 0, .inl 1, .inl 2]),
   (.nand, [.inl 0, .inl 1]),
   (.nand, [.inl 1, .inl 2]),
   (.nand, [.inl 2, .inl 0])]

/-- The four macro constraints have exactly their declared widths. -/
theorem triangleBody_wellFormed : WellFormed triangleArity triangleBody := by
  intro c hc
  simp only [triangleBody, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> rfl

private theorem tuple_eq (x : Fin 3 → Bool) : x = ![x 0, x 1, x 2] := by
  ext i
  fin_cases i <;> rfl

/-- NAND on all three adjacent pairs leaves precisely the three units or zero. -/
theorem triangleBody_eval_iff (R : Set (Fin 3 → Bool)) [DecidablePred (· ∈ R)]
    (x : Fin 3 → Bool) (b : Fin 0 → Bool) :
    triangleBody.eval (triangleSem R) (Sum.elim x b) = true ↔
      x ∈ R ∧ (x = 0 ∨ x ∈ oneHotRelation (Fin 3)) := by
  simp only [triangleBody, eval, Constraint.eval, List.all_cons, List.all_nil,
    List.map_cons, List.map_nil, Sum.elim_inl, triangleSem, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff, and_true]
  rw [← tuple_eq x]
  have check : ∀ x : Fin 3 → Bool,
      ((x 0 = false ∨ x 1 = false) ∧ (x 1 = false ∨ x 2 = false) ∧
        (x 2 = false ∨ x 0 = false)) ↔ (x = 0 ∨ x ∈ oneHotRelation (Fin 3)) := by
    unfold oneHotRelation
    decide
  exact and_congr_right fun _ => check x

/-- The actual four-constraint triangle defines one-in-three for every ternary relation
containing the units and missing zero. No symmetry of that relation is assumed. -/
@[expose] def triangle (R : Set (Fin 3 → Bool)) [DecidablePred (· ∈ R)]
    (hz : (0 : Fin 3 → Bool) ∉ R) (hu : ∀ i, Pi.single i true ∈ R) :
    PPGadget triangleArity (triangleSem R) (oneHotRelation (Fin 3)) where
  numAux := 0
  body := triangleBody
  wellFormed := triangleBody_wellFormed
  correct x := by
    simp only [triangleBody_eval_iff]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨fun _ => false, ?_, .inr ⟨i, rfl⟩⟩
      have heq : (fun j : Fin 3 => decide (j = i)) = Pi.single i true := by
        ext j
        simp [Pi.single_apply, Bool.zero_eq_false]
      change (fun j : Fin 3 => decide (j = i)) ∈ R
      rw [heq]
      exact hu i
    · rintro ⟨_, hx, hzero | hone⟩
      · exact False.elim (hz (hzero ▸ hx))
      · exact hone

/-- The complete semantic witnesses for the nonselfdual construction. Disequality and both
pins are derived, and the parity and majority failure witnesses may be different symbols.
There is no constants premise or conditional minor oracle. -/
theorem witnesses {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    (h : ¬HasSchaeferPolymorphism arity sem)
    (hn : ¬HasPolymorphism arity sem (fun a : Fin 1 → Bool => !(a 0))) :
    Available arity sem disequality ∧ (∀ b, Available arity sem (pin b)) ∧
      Available arity sem nand ∧ ∃ R : Set (Fin 3 → Bool),
        Available arity sem R ∧ (0 : Fin 3 → Bool) ∉ R ∧
          (∀ i, Pi.single i true ∈ R) := by
  classical
  obtain ⟨⟨d⟩, pins⟩ := constants_of_not_hasSchaeferPolymorphism h hn
  let p (b : Bool) := Classical.choice (pins b)
  have hparity : ¬HasPolymorphism arity sem (Cslib.parity 3) :=
    fun hp => h (.inr (.inr (.inr (.inr (.inr hp)))))
  have hmajority : ¬HasPolymorphism arity sem (Cslib.majority 3) :=
    fun hm => h (.inr (.inr (.inr (.inr (.inl hm)))))
  simp only [HasPolymorphism, not_forall] at hparity hmajority
  obtain ⟨r, hr⟩ := hparity
  obtain ⟨s, hs⟩ := hmajority
  obtain ⟨t⟩ := exists_nand_trace hr
  obtain ⟨R, ⟨u⟩, hz, hu⟩ := exists_majority_minor hs
  exact ⟨⟨d⟩, pins, ⟨t.construction (.atom r) d p⟩,
    R, ⟨u.construction (.atom s) d p⟩, hz, hu⟩

end Cslib.Logic.PL.CSP.NonSelfDual
