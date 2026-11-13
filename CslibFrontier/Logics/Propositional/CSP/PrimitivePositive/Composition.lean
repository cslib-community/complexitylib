/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Operations

/-!
# Finite composition of primitive-positive gadgets

Atomic gadgets preserve the original constraint's port order. Conjunction appends bodies,
sharing only free ports: the left auxiliaries precede a disjoint block of right auxiliaries.
These operations give finite semantics, with no geometric or computability claim.
-/

public section

namespace Cslib.Logic.PL.CSP.PPGadget

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {n : ℕ} {R S : Set (Fin n → Bool)}

/-- Change the target by a pointwise equivalence, retaining the exact body and auxiliaries. -/
@[expose] def retarget (g : PPGadget arity sem R) (h : ∀ a, a ∈ S ↔ a ∈ R) :
    PPGadget arity sem S where
  numAux := g.numAux
  body := g.body
  wellFormed := g.wellFormed
  correct a := (h a).trans (g.correct a)

/-- A single original-language constraint, with its declared free-port order and no auxiliaries.
This also covers nullary constraints. -/
@[expose] def atom (r : Rel) : PPGadget arity sem (booleanRelation arity sem r) where
  numAux := 0
  body := [⟨r, List.ofFn Sum.inl⟩]
  wellFormed := by
    intro c hc
    simp only [List.mem_singleton] at hc
    subst c
    exact List.length_ofFn
  correct a := by
    simp [booleanRelation, eval, Constraint.eval, List.map_ofFn, Function.comp_def]

/-- Conjoin two gadgets on the same free ports. Each occurrence gets its own auxiliary block,
even when the two operands are the same gadget. Body order is left then right. -/
@[expose] def conj (g : PPGadget arity sem R) (h : PPGadget arity sem S) :
    PPGadget arity sem (R ∩ S) where
  numAux := g.numAux + h.numAux
  body := g.body.relabel (Sum.map id (Fin.castAdd h.numAux)) ++
    h.body.relabel (Sum.map id (Fin.natAdd g.numAux))
  wellFormed := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact g.wellFormed.relabel _ c hc
    · exact h.wellFormed.relabel _ c hc
  correct a := by
    change (a ∈ R ∧ a ∈ S) ↔ _
    rw [g.correct, h.correct]
    simp only [eval, List.all_append, Bool.and_eq_true]
    change ((∃ b, g.body.eval sem (Sum.elim a b) = true) ∧
      (∃ c, h.body.eval sem (Sum.elim a c) = true)) ↔ ∃ b,
        (g.body.relabel (Sum.map id (Fin.castAdd h.numAux))).eval sem
          (Sum.elim a b) = true ∧
        (h.body.relabel (Sum.map id (Fin.natAdd g.numAux))).eval sem
          (Sum.elim a b) = true
    simp only [eval_relabel]
    constructor
    · rintro ⟨⟨b, hb⟩, ⟨c, hc⟩⟩
      refine ⟨Fin.addCases b c, ?_, ?_⟩
      · convert hb using 2
        funext v
        cases v <;> simp
      · convert hc using 2
        funext v
        cases v <;> simp
    · rintro ⟨b, hb, hc⟩
      constructor
      · refine ⟨fun i => b (i.castAdd h.numAux), ?_⟩
        convert hb using 2
        funext v
        cases v <;> rfl
      · refine ⟨fun i => b (i.natAdd g.numAux), ?_⟩
        convert hc using 2
        funext v
        cases v <;> rfl

/-- Conjunction keeps every constraint of both operands, in their original order. -/
@[simp] theorem length_conj_body (g : PPGadget arity sem R) (h : PPGadget arity sem S) :
    (g.conj h).body.length = g.body.length + h.body.length := by
  simp [conj, relabel]

end Cslib.Logic.PL.CSP.PPGadget
