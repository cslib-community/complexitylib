/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.FirstOrder.Projection.Graph

/-!
# Tests for first-order projections

Exercise a nonvacuous graph projection, product-coordinate composition, empty universes,
nullary relations, and the distinction from arbitrary quantifier-free formulas. The last test
proves that the conjunction of two independent nullary input relations is not a projection.
-/

namespace ComplexityTests.FirstOrderProjection

open FirstOrder Language Structure Cslib.Logic.FO

local instance {M : Type*} : Language.empty.Structure M := Language.emptyStructure

example : (Projection.offDiagonalComplement Language.empty).IsQF :=
  Projection.isQF_offDiagonalComplement _

example : ((Projection.offDiagonalComplement Language.empty).comp
    (Projection.offDiagonalComplement Language.empty)).IsQF :=
  (Projection.isQF_offDiagonalComplement _).comp (Projection.isQF_offDiagonalComplement _)

/-- Complement on the empty universe still has no elements: the output domain is not forced
nonempty by the interpretation API. -/
example : IsEmpty ((Projection.offDiagonalComplement Language.empty).numeric.Model (Fin 0)) := by
  exact ⟨fun x => (x.1 ()).elim0⟩

section Graph

variable {M : Type*} [Language.graph.Structure M]

/-- Loops are removed, regardless of the input relation. -/
example (a : M) : ¬ ((Projection.offDiagonalComplement Language.empty).rel .adj).toFormula.Realize
    (fun _ => a) := by
  rw [Projection.realize_offDiagonalComplement]
  simp

/-- The positive off-diagonal case is satisfiable, for example for the empty graph on two
vertices. It is not merely an implication with an impossible hypothesis. -/
example (a b : M) (hne : a ≠ b) (hedge : ¬ RelMap Language.adj ![a, b]) :
    ((Projection.offDiagonalComplement Language.empty).rel .adj).toFormula.Realize
      (fun p => ![a, b] p.1) := by
  rw [Projection.realize_offDiagonalComplement]
  exact ⟨hne, hedge⟩

end Graph

example :
    letI := (⊥ : SimpleGraph (Fin 2)).structure
    ((Projection.offDiagonalComplement Language.empty).rel .adj).toFormula.Realize
      (fun p => p.1) := by
  let := (⊥ : SimpleGraph (Fin 2)).structure
  rw [Projection.realize_offDiagonalComplement]
  exact ⟨by decide, by simp [RelMap]⟩

inductive BitRel : ℕ → Type where
  | left : BitRel 0
  | right : BitRel 0

def bits : Language := ⟨fun _ => Empty, BitRel⟩
  deriving IsRelational

@[instance_reducible]
def bitStructure (a b : Bool) : bits.Structure Unit where
  RelMap
    | .left, _ => a = true
    | .right, _ => b = true

/-- No projection formula, even with quantified numeric guards, computes the conjunction of
two independent input bits on a fixed numeric universe. -/
theorem not_twoBitConjunction :
    ¬ ∃ p : ProjectionFormula Language.empty bits Empty, ∀ a b : Bool,
      letI := bitStructure a b
      p.toFormula.Realize (Empty.elim : Empty → Unit) ↔ a = true ∧ b = true := by
  rintro ⟨p, hp⟩
  have h (a b : Bool) :
      letI := bitStructure a b
      (p.select (M := Unit) Empty.elim).Realize (Empty.elim : Empty → Unit) ↔
        a = true ∧ b = true := by
    let := bitStructure a b
    exact (p.realize_toFormula Empty.elim).symm.trans (hp a b)
  generalize p.select (M := Unit) Empty.elim = l at h
  cases l with
  | const c =>
    have h₀ := h false false
    have h₁ := h true true
    simp only [InputLiteral.Realize, Bool.false_eq_true, and_self, iff_false,
      iff_true] at h₀ h₁
    exact h₀ h₁
  | rel R args neg =>
    cases R <;> cases neg <;>
      have h₀ := h false true <;> have h₁ := h true false <;> have h₂ := h true true <;>
      simp [InputLiteral.Realize, RelMap] at h₀ h₁ h₂

/--
info: 'Cslib.Logic.FO.Projection.modelEquiv' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Projection.modelEquiv

end ComplexityTests.FirstOrderProjection
